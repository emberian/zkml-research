//! pcs::write_carry / read_carry: a carried commitment survives its checkpoint (same root, same openings), and a
//! tampered checkpoint is refused.
use darkproof::pcs::{read_carry, write_carry, PcsParty};
use darkproof::rng::Det;
use std::collections::BTreeMap;

#[test]
fn carry_round_trip_and_tamper() {
    let pr = darkproof::Profile::demo();
    darkproof::field::set_p(darkproof::wire::he_field(&pr).unwrap());
    let share: Vec<u64> = (0..256u64).map(|v| v * 7919 + 3).collect();
    let mut carry = BTreeMap::new();
    for (k, i) in [("W1", 0usize), ("W2", 1)] {
        carry.insert(k.to_string(), PcsParty::commit(&pr, &share, k, i, &Det::off()));
    }
    let mut buf = Vec::new();
    write_carry(&carry, &mut buf).unwrap();
    let mut back = read_carry(&mut buf.as_slice(), &pr).unwrap();
    assert_eq!(back.len(), 2);
    for (k, c) in carry.iter_mut() {
        let b = back.get_mut(k).unwrap();
        assert_eq!(b.root, c.root);
        assert_eq!((b.label.as_str(), b.opened_lives, b.max_lives, b.shape.base), (c.label.as_str(), c.opened_lives, c.max_lives, c.shape.base));
        let js = [0usize, 5, 17];
        assert_eq!(b.open_batch(&js), c.open_batch(&js));
    }
    // one share word changed: its root no longer recomputes
    let mut bad = buf.clone();
    let off = 8 + 4 + (4 + 2) + (4 + 2) + 16 + 8;
    bad[off] ^= 1;
    let e = read_carry(&mut bad.as_slice(), &pr).err().unwrap();
    assert!(e.contains("recomputed root differs"), "{e}");
    // truncated, trailing bytes, bad magic
    assert!(read_carry(&mut &buf[..buf.len() - 1], &pr).is_err());
    let mut long = buf.clone();
    long.push(0);
    assert!(read_carry(&mut long.as_slice(), &pr).err().unwrap().contains("trailing"));
    let mut mg = buf.clone();
    mg[0] ^= 1;
    assert!(read_carry(&mut mg.as_slice(), &pr).err().unwrap().contains("magic"));
}
