// Small actual cached fhe-math API probe. No HE encryption or multiplication.
use fhe_math::zq::Modulus;
fn next(s: &mut u64) -> u64 { *s ^= *s << 13; *s ^= *s >> 7; *s ^= *s << 17; *s }
fn main() {
 let ps=[2u64,3,31,68719403009,68719230977,137438822401,4611686018427322369];
 let mut seed=0xa57a20260906u64;
 for p in ps {
  let m=Modulus::new(p).unwrap();
  for k in 0..272u64 {
   let a=match k {0=>0,1=>1,2=>p-1,3=>p,4=>u64::MAX,5=>1u64<<63,_=>next(&mut seed)};
   let b=match k {0=>0,1=>1,2=>p-1,3=>p-1,4=>p-1,5=>1,_=>next(&mut seed)%p};
   let s=m.shoup(b);let lazy=m.lazy_mul_shoup(a,b,s);let reduced=m.mul_shoup(a,b,s);
   let x=match k {0=>0,1=>1,2=>p as u128-1,3=>p as u128,4=>u128::MAX,5=>1u128<<127,_=>((next(&mut seed) as u128)<<64)|(next(&mut seed) as u128)};
   let br=m.lazy_reduce_u128(x);let red=m.reduce_u128(x);
   assert_eq!(reduced,((a as u128)*(b as u128)%(p as u128)) as u64);
   assert_eq!(red,(x%(p as u128)) as u64);
   println!("{{\"p\":{},\"a\":{},\"b\":{},\"shoup\":{},\"lazy_shoup\":{},\"mul_shoup\":{},\"x\":\"{}\",\"lazy_barrett\":{},\"reduce\":{}}}",p,a,b,s,lazy,reduced,x,br,red);
  }
 }
}
