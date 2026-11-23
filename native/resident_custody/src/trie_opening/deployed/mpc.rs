//! Straight-line, public-shape ZKBoo evaluator. Clear evaluation uses the
//! same operations for witness preflight and for computing the tape length.
use super::{zk, Plan, View};
use crate::trie_opening::{NODE_HASH_DOMAIN, OUTER_HASH_DOMAIN};
use crate::Digest;

type Word<const N: usize> = [u64; N];
type Hash<const N: usize> = [Word<N>; 4];
fn xor<const N: usize>(x: Word<N>, y: Word<N>) -> Word<N> {
    std::array::from_fn(|i| x[i] ^ y[i])
}
fn constant<const N: usize>(d: &Digest) -> Hash<N> {
    std::array::from_fn(|i| [u64::from_le_bytes(d[8 * i..][..8].try_into().unwrap()); N])
}
fn pack<const N: usize>(bytes: &[Word<N>]) -> Word<N> {
    std::array::from_fn(|p| {
        bytes
            .iter()
            .enumerate()
            .fold(0, |v, (i, b)| v ^ ((b[p] & 255) << (8 * i)))
    })
}
fn bytes<const N: usize>(d: &Hash<N>) -> Vec<Word<N>> {
    (0..32)
        .map(|i| d[i / 8].map(|v| (v >> (8 * (i % 8))) & 255))
        .collect()
}
fn words<const N: usize>(d: &[Word<N>]) -> Hash<N> {
    std::array::from_fn(|i| pack(&d[8 * i..8 * i + 8]))
}
struct Eval<'a, const N: usize> {
    views: Option<&'a mut [View; N]>,
    neighbor: Option<&'a [u8]>,
    gates: usize,
}
impl<const N: usize> Eval<'_, N> {
    fn and(&mut self, x: Word<N>, y: Word<N>) -> Word<N> {
        let i = self.gates;
        self.gates += 1;
        let Some(v) = self.views.as_deref_mut() else {
            return [x[0] & y[0]; N];
        };
        let z = std::array::from_fn(|p| {
            if let Some(t) = self.neighbor.filter(|_| p + 1 == N) {
                u64::from_le_bytes(t[8 * i..][..8].try_into().unwrap())
            } else {
                let q = (p + 1) % N;
                (x[p] & y[p]) ^ (x[p] & y[q]) ^ (x[q] & y[p]) ^ v[p].masks[i] ^ v[q].masks[i]
            }
        });
        for (view, bits) in v.iter_mut().zip(z) {
            view.gates.extend(bits.to_le_bytes());
        }
        z
    }
    fn select(&mut self, flag: Word<N>, yes: Hash<N>, no: Hash<N>) -> Hash<N> {
        // Repeating one bit on all 64 coordinates is GF(2)-linear.
        let mask = flag.map(|x| 0u64.wrapping_sub(x & 1));
        std::array::from_fn(|i| xor(no[i], self.and(mask, xor(yes[i], no[i]))))
    }
    fn hash(&mut self, domain: &[u8], data: &[Word<N>]) -> Hash<N> {
        let mut s = zk::prefix(domain).map(|x| [x; N]);
        let mut padded = data.to_vec();
        padded.push([4; N]);
        padded.resize((data.len() / 136 + 1) * 136, [0; N]);
        let end = padded.last_mut().unwrap();
        *end = xor(*end, [128; N]);
        for block in padded.chunks_exact(136) {
            for (i, w) in block.chunks_exact(8).enumerate() {
                s[i] = xor(s[i], pack(w));
            }
            for rc in zk::RC {
                let b: [_; N] = std::array::from_fn(|p| zk::linear(s.map(|v| v[p])));
                for (i, out) in s.iter_mut().enumerate() {
                    let at = |j: usize| std::array::from_fn(|p| b[p][i / 5 * 5 + (i + j) % 5]);
                    let z = self.and(at(1).map(|v| !v), at(2));
                    *out = xor(at(0), z);
                }
                s[0] = xor(s[0], [rc; N]);
            }
        }
        s[..4].try_into().unwrap()
    }

    fn run(&mut self, plan: &Plan, data: &[Word<N>]) -> Vec<Word<N>> {
        let inner = words(&data[32..64]);
        let mut outer: Vec<_> = plan.frame.iter().map(|&x| [u64::from(x); N]).collect();
        outer.extend_from_slice(&data[..64]);
        let mut output = self.hash(OUTER_HASH_DOMAIN, &outer).to_vec();
        let mut rest = &data[64..];
        for job in &plan.jobs {
            let mut h = constant(&job.below);
            let mut terminal = [0; N];
            let mut path = &[][..];
            if job.count == 0 {
                terminal = take(&mut rest, 1)[0].map(|v| v & 1);
                path = take(&mut rest, 65);
                let content = take(&mut rest, 32);
                let mut input = vec![[0; N]];
                input.extend_from_slice(path);
                input[65] = input[65].map(|v| v & 240);
                input.extend_from_slice(content);
                let leaf = self.hash(NODE_HASH_DOMAIN, &input);
                h = self.select(terminal, leaf, h);
            }
            let mut steps = Vec::with_capacity(job.prefix.len());
            let mut prev = [1; N];
            let mut matches_prefix = [1; N];
            for (i, &b) in job.prefix.iter().enumerate() {
                let active = if job.count <= 1 {
                    let bit = take(&mut rest, 1)[0].map(|v| v & 1);
                    // The walk is an initial run of ones. Its length stays private.
                    output.push(self.and(bit, xor(prev, [1; N])));
                    prev = bit;
                    bit
                } else {
                    [1; N]
                };
                if job.count == 0 {
                    let diff = path[i / 8].map(|v| ((v >> (7 - i % 8)) & 1) ^ u64::from(b));
                    matches_prefix = self.and(matches_prefix, xor(diff, [1; N]));
                    let live = self.and(active, terminal);
                    output.push(self.and(live, diff));
                }
                steps.push((active, b, words(take(&mut rest, 32))));
            }
            if job.count == 0 {
                // A private singleton may stop above an empty requested prefix
                // only if its path lies outside that prefix.
                output.push(self.and(terminal, matches_prefix));
            }
            for (active, b, sibling) in steps.into_iter().rev() {
                let (left, right) = if b { (sibling, h) } else { (h, sibling) };
                let mut input = vec![[1; N]];
                input.extend(bytes(&left));
                input.extend(bytes(&right));
                let parent = self.hash(NODE_HASH_DOMAIN, &input);
                h = if job.count <= 1 {
                    self.select(active, parent, h)
                } else {
                    parent
                };
            }
            output.extend((0..4).map(|i| xor(h[i], inner[i])));
        }
        assert!(rest.is_empty());
        output
    }
}

fn take<'a, T>(data: &mut &'a [T], n: usize) -> &'a [T] {
    let (a, b) = data.split_at(n);
    *data = b;
    a
}
pub(super) fn clear(plan: &Plan, input: &[u8]) -> (Vec<u8>, usize) {
    let mut e = Eval {
        views: None,
        neighbor: None,
        gates: 0,
    };
    let input: Vec<_> = input.iter().map(|&v| [u64::from(v)]).collect();
    let output = e
        .run(plan, &input)
        .iter()
        .flat_map(|v| v[0].to_le_bytes())
        .collect();
    (output, e.gates)
}
pub(super) fn evaluate<const N: usize>(
    plan: &Plan,
    views: &mut [View; N],
    neighbor: Option<&[u8]>,
) {
    let input: Vec<_> = (0..plan.len)
        .map(|i| std::array::from_fn(|p| u64::from(views[p].input[i])))
        .collect();
    let mut e = Eval {
        views: Some(views),
        neighbor,
        gates: 0,
    };
    let output = e.run(plan, &input);
    for (p, v) in views.iter_mut().enumerate() {
        v.output = output.iter().flat_map(|w| w[p].to_le_bytes()).collect();
    }
}
