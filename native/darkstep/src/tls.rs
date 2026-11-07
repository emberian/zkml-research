//! Point-to-point TLS 1.3 between custodians with pinned self-signed certificates (rustls + ring, rcgen).
//! Each custodian makes a fresh ECDSA P-256 key and certificate per run (`generate`), and the certificates (public)
//! are copied to every seat. A connection is accepted only if the peer presents exactly the pinned certificate of
//! a party in the run; there is no CA, and names play no part. Both directions are authenticated (mutual TLS).
use rustls::client::danger::{HandshakeSignatureValid, ServerCertVerified, ServerCertVerifier};
use rustls::crypto::{verify_tls13_signature, CryptoProvider, WebPkiSupportedAlgorithms};
use rustls::pki_types::{CertificateDer, PrivateKeyDer, PrivatePkcs8KeyDer, ServerName, UnixTime};
use rustls::server::danger::{ClientCertVerified, ClientCertVerifier};
use rustls::{DigitallySignedStruct, DistinguishedName, Error, SignatureScheme};
use std::sync::Arc;

/// A custodian's TLS identity: its PKCS#8 private key and its self-signed certificate (DER).
pub struct Identity {
    pub key_der: Vec<u8>,
    pub cert_der: Vec<u8>,
}

impl Drop for Identity {
    fn drop(&mut self) {
        for b in self.key_der.iter_mut() {
            unsafe { std::ptr::write_volatile(b, 0) };
        }
    }
}

/// A fresh key pair and certificate for custodian `i` (subject alt name custodian-i).
pub fn generate(i: usize) -> Identity {
    let ck = rcgen::generate_simple_self_signed(vec![format!("custodian-{i}")]).expect("rcgen");
    Identity { key_der: ck.key_pair.serialize_der(), cert_der: ck.cert.der().to_vec() }
}

pub fn cert_fingerprint(der: &[u8]) -> String {
    use sha2::{Digest, Sha256};
    pycompat::repr::hex(&Sha256::digest(der))
}

fn provider() -> Arc<CryptoProvider> {
    Arc::new(rustls::crypto::ring::default_provider())
}

/// Accepts exactly the certificates in `pinned` (by DER bytes), and checks the handshake signature with its key.
#[derive(Debug)]
struct Pinned {
    pinned: Vec<Vec<u8>>,
    algs: WebPkiSupportedAlgorithms,
}

impl Pinned {
    fn check(&self, end_entity: &CertificateDer<'_>, intermediates: &[CertificateDer<'_>]) -> Result<(), Error> {
        if !intermediates.is_empty() || !self.pinned.iter().any(|c| c.as_slice() == end_entity.as_ref()) {
            return Err(Error::General("peer certificate is not pinned for this run".into()));
        }
        Ok(())
    }
}

impl ServerCertVerifier for Pinned {
    fn verify_server_cert(&self, ee: &CertificateDer<'_>, im: &[CertificateDer<'_>], _: &ServerName<'_>, _: &[u8], _: UnixTime) -> Result<ServerCertVerified, Error> {
        self.check(ee, im).map(|_| ServerCertVerified::assertion())
    }
    fn verify_tls12_signature(&self, _: &[u8], _: &CertificateDer<'_>, _: &DigitallySignedStruct) -> Result<HandshakeSignatureValid, Error> {
        Err(Error::General("TLS 1.2 is not offered".into()))
    }
    fn verify_tls13_signature(&self, m: &[u8], c: &CertificateDer<'_>, d: &DigitallySignedStruct) -> Result<HandshakeSignatureValid, Error> {
        verify_tls13_signature(m, c, d, &self.algs)
    }
    fn supported_verify_schemes(&self) -> Vec<SignatureScheme> {
        self.algs.supported_schemes()
    }
}

impl ClientCertVerifier for Pinned {
    fn root_hint_subjects(&self) -> &[DistinguishedName] {
        &[]
    }
    fn verify_client_cert(&self, ee: &CertificateDer<'_>, im: &[CertificateDer<'_>], _: UnixTime) -> Result<ClientCertVerified, Error> {
        self.check(ee, im).map(|_| ClientCertVerified::assertion())
    }
    fn verify_tls12_signature(&self, _: &[u8], _: &CertificateDer<'_>, _: &DigitallySignedStruct) -> Result<HandshakeSignatureValid, rustls::Error> {
        Err(Error::General("TLS 1.2 is not offered".into()))
    }
    fn verify_tls13_signature(&self, m: &[u8], c: &CertificateDer<'_>, d: &DigitallySignedStruct) -> Result<HandshakeSignatureValid, Error> {
        verify_tls13_signature(m, c, d, &self.algs)
    }
    fn supported_verify_schemes(&self) -> Vec<SignatureScheme> {
        self.algs.supported_schemes()
    }
}

fn key_of(id: &Identity) -> PrivateKeyDer<'static> {
    PrivateKeyDer::Pkcs8(PrivatePkcs8KeyDer::from(id.key_der.clone()))
}

/// The dialing side of the link to one peer: it must present `peer_cert`.
pub fn client_config(id: &Identity, peer_cert: &[u8]) -> Arc<rustls::ClientConfig> {
    let pv = provider();
    let v = Arc::new(Pinned { pinned: vec![peer_cert.to_vec()], algs: pv.signature_verification_algorithms });
    let cfg = rustls::ClientConfig::builder_with_provider(pv)
        .with_protocol_versions(&[&rustls::version::TLS13])
        .expect("tls13")
        .dangerous()
        .with_custom_certificate_verifier(v)
        .with_client_auth_cert(vec![CertificateDer::from(id.cert_der.clone())], key_of(id))
        .expect("client cert");
    Arc::new(cfg)
}

/// The accepting side: the dialer must present one of `peer_certs`, and its own certificate.
pub fn server_config(id: &Identity, peer_certs: &[Vec<u8>]) -> Arc<rustls::ServerConfig> {
    let pv = provider();
    let v = Arc::new(Pinned { pinned: peer_certs.to_vec(), algs: pv.signature_verification_algorithms });
    let mut cfg = rustls::ServerConfig::builder_with_provider(pv)
        .with_protocol_versions(&[&rustls::version::TLS13])
        .expect("tls13")
        .with_client_cert_verifier(v)
        .with_single_cert(vec![CertificateDer::from(id.cert_der.clone())], key_of(id))
        .expect("server cert");
    // the accepting side only reads after the handshake: no session tickets, no resumption
    cfg.send_tls13_tickets = 0;
    Arc::new(cfg)
}
