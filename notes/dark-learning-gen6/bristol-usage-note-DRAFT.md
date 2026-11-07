# Draft: usage report to the University of Bristol (MP-SPDZ / SPDZ-2 licence, ref. 1914)

Status: DRAFT for ember to send or not. Not sent. Written 2026-11-07 by the dark-learning lane.

Context: MP-SPDZ (CSIRO/Data61, BSD-3-Clause) includes parts under the University of Bristol's Open Access Software
Licence, which asks users to report scientific or commercial use for impact monitoring (ref. 1914). This is that report.

---

To: the University of Bristol (Research and Enterprise Development / the contact named in the SPDZ-2 licence, ref. 1914)

Subject: Use report for MP-SPDZ (SPDZ-2 components), ref. 1914

Hello,

We are reporting our use of MP-SPDZ v0.4.4, which includes components under Bristol's Open Access Software Licence
(ref. 1914), as the licence asks.

- Who: ember (https://ember.software), an independent research project.
- What: preprocessing for a three-party, dishonest-majority, maliciously secure computation that trains a small
  neural network on data that no single party sees. MP-SPDZ produces the authenticated multiplication triples,
  random bits and input masks (MASCOT with tau = 5 over a 61-bit prime field; LowGear at ring dimension 16,384), which our
  own online protocol and collaborative zero-knowledge proof consume.
- How: built from source with two parameter changes (MASCOT's combining parameter, and LowGear's minimum ring dimension
  raised so that the lattice estimator gives about 2^179 for the 312-bit modulus instead of about 2^87 at the default),
  plus a fix that retries interrupted socket reads after a process is stopped and continued.
- Nature of use: research and engineering, not a commercial product. No redistribution of MP-SPDZ.

Thank you for making the software available.

ember
