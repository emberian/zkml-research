//! Core data types for lookup arguments.

use alloc::string::String;
use alloc::vec;
use alloc::vec::Vec;
use core::ops::Deref;

use p3_air::symbolic::AirLayout;
use p3_air::{Air, SymbolicExpression};
use p3_field::{ExtensionField, Field};
use serde::{Deserialize, Serialize};

use crate::builder::{SymbolicInteraction, SymbolicLocalInteraction};
use crate::symbolic::InteractionSymbolicBuilder;

/// Whether a lookup is local to one AIR or shared across AIRs.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Kind {
    /// Intra-AIR lookup. Running sum must return to zero.
    Local,
    /// Cross-AIR lookup on a named bus. Running sums are verified globally.
    Global(String),
}

/// A single lookup argument: element tuples, multiplicities, and one
/// auxiliary column in the permutation trace.
#[derive(Clone, Debug)]
pub struct Lookup<F: Field> {
    /// Local or global (with bus name).
    pub kind: Kind,
    /// Element tuples. Each inner `Vec` is one `(key0, key1, ...)` tuple.
    pub elements: Vec<Vec<SymbolicExpression<F>>>,
    /// Signed multiplicity per element tuple. Same length as `elements`.
    pub multiplicities: Vec<SymbolicExpression<F>>,
    /// Auxiliary column index in the permutation trace.
    pub column: usize,
}

/// All lookups for one AIR, with column indices assigned.
#[derive(Clone, Debug, Default)]
pub struct Lookups<F: Field>(Vec<Lookup<F>>);

impl<F: Field> Lookups<F> {
    /// Extract lookups from an AIR by running symbolic evaluation.
    pub fn from_air<EF, A>(air: &A) -> Self
    where
        EF: ExtensionField<F>,
        A: Air<InteractionSymbolicBuilder<F, EF>>,
        F: Clone + Send + Sync,
    {
        let mut builder = InteractionSymbolicBuilder::<F, EF>::new(AirLayout::from_air(air));
        air.eval(&mut builder);
        Self::from_interactions(builder.global_interactions(), builder.local_interactions())
    }

    /// Build from raw symbolic interactions.
    ///
    /// Local interactions first, then global — matching the LogUp column order.
    fn from_interactions(
        global: &[SymbolicInteraction<F>],
        local: &[SymbolicLocalInteraction<F>],
    ) -> Self {
        let mut lookups = Vec::with_capacity(local.len() + global.len());
        let mut col = 0;

        for i in local {
            let (elements, multiplicities) =
                i.tuples.iter().map(|(f, c)| (f.clone(), c.clone())).unzip();
            lookups.push(Lookup {
                kind: Kind::Local,
                elements,
                multiplicities,
                column: col,
            });
            col += 1;
        }

        // Opt-in nonlinear-performance successor: one running-sum column for
        // at most four CONSECUTIVE interactions on the SAME bus. The existing
        // LogUp evaluator handles vector elements and signed multiplicities.
        // Flattening these groups recovers every original tuple/count in order;
        // neither signs, table identities, nor local interactions are changed.
        // The batch prover/verifier derive the resulting higher degree normally.
        for i in global {
            if let Some(last) = lookups.last_mut()
                && matches!(&last.kind, Kind::Global(bus) if bus == &i.bus_name)
                && last.elements.len() < 4
            {
                last.elements.push(i.fields.clone());
                last.multiplicities.push(i.count.clone());
            } else {
                lookups.push(Lookup {
                    kind: Kind::Global(i.bus_name.clone()),
                    elements: vec![i.fields.clone()],
                    multiplicities: vec![i.count.clone()],
                    column: col,
                });
                col += 1;
            }
        }

        Self(lookups)
    }
}

impl<F: Field> Deref for Lookups<F> {
    type Target = [Lookup<F>];

    fn deref(&self) -> &[Lookup<F>] {
        &self.0
    }
}

impl<F: Field> AsRef<[Lookup<F>]> for Lookups<F> {
    fn as_ref(&self) -> &[Lookup<F>] {
        &self.0
    }
}

/// Prover-provided data for one global lookup interaction.
#[derive(Debug, Default, Clone, Serialize, Deserialize)]
pub struct LookupData<F> {
    /// Bus name.
    pub name: String,
    /// Auxiliary column index.
    pub aux_column: usize,
    /// Cumulative sum computed by the prover.
    pub cumulative_sum: F,
}

/// Lookup verification error.
#[derive(Debug)]
pub enum LookupError {
    /// Global cumulative sums do not balance to zero.
    GlobalCumulativeMismatch(Option<String>),
}


#[cfg(test)]
mod grouped_tests {
    use super::*;
    use alloc::format;
    use alloc::string::ToString;
    use p3_baby_bear::BabyBear;
    use p3_field::PrimeCharacteristicRing;

    #[test]
    fn grouped_preserves_flattened_tuples_counts_buses_and_local_prefix() {
        let buses = ["a", "a", "a", "a", "a", "b", "a", "a", "a", "a", "a", "a"];
        let global: Vec<SymbolicInteraction<BabyBear>> = buses.iter().enumerate().map(|(i,bus)| SymbolicInteraction {
            bus_name: bus.to_string(),
            fields: vec![SymbolicExpression::from(BabyBear::from_u64(i as u64 + 17))],
            count: SymbolicExpression::from(if i % 2 == 0 { BabyBear::ONE } else { BabyBear::NEG_ONE }),
            count_weight: (i % 2) as u32,
        }).collect();
        let local = vec![SymbolicLocalInteraction::<BabyBear> {
            tuples: vec![(vec![SymbolicExpression::from(BabyBear::from_u64(99))],SymbolicExpression::from(BabyBear::NEG_ONE))],
        }];
        let grouped = Lookups::from_interactions(&global, &local);
        assert_eq!(grouped.len(), 6);
        assert_eq!(grouped[0].kind, Kind::Local);
        assert_eq!(format!("{:?}", grouped[0].elements[0]), format!("{:?}", local[0].tuples[0].0));
        assert_eq!(format!("{:?}", grouped[0].multiplicities[0]), format!("{:?}", local[0].tuples[0].1));
        assert_eq!(grouped.iter().map(|g|g.elements.len()).collect::<Vec<_>>(), vec![1,4,1,1,4,2]);
        let mut at = 0;
        for (col, group) in grouped.iter().enumerate() {
            assert_eq!(group.column,col);
            assert_eq!(group.elements.len(),group.multiplicities.len());
            if col == 0 { continue; }
            for (fields,count) in group.elements.iter().zip(&group.multiplicities) {
                assert_eq!(group.kind,Kind::Global(global[at].bus_name.clone()));
                assert_eq!(format!("{fields:?}"),format!("{:?}",global[at].fields));
                assert_eq!(format!("{count:?}"),format!("{:?}",global[at].count));
                at+=1;
            }
        }
        assert_eq!(at,global.len());
    }

    #[test]
    fn grouped_empty_and_full_boundary() {
        let empty: Lookups<BabyBear> = Lookups::from_interactions(&[],&[]);
        assert!(empty.is_empty());
        let one=SymbolicInteraction::<BabyBear> { bus_name:"a".to_string(),fields:vec![SymbolicExpression::from(BabyBear::ONE)],count:SymbolicExpression::from(BabyBear::NEG_ONE),count_weight:0 };
        for n in [1,3,4,5,8,9,524] {
            let grouped=Lookups::from_interactions(&vec![one.clone();n],&[]);
            assert_eq!(grouped.len(),n.div_ceil(4));
            assert!(grouped.iter().all(|g| !g.elements.is_empty() && g.elements.len()<=4));
            assert_eq!(grouped.iter().map(|g|g.elements.len()).sum::<usize>(),n);
        }
    }
}
