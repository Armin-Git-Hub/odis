use std::collections::BTreeSet;

use crate::FormalContext;

fn next_concept<T>(
    context: &FormalContext<T>,
    a: &BTreeSet<usize>,
) -> Option<(BTreeSet<usize>, BTreeSet<usize>)> {
    let mut a_new = a.clone();
    let mut a_iter = a.iter().rev();
    let mut a_next = a_iter.next();
    for i in (0..context.attributes.len()).rev() {
        if Some(&i) == a_next {
            a_new.remove(&i);
            a_next = a_iter.next();
        } else {
            let mut b = a_new.clone();
            b.insert(i);
            let gs = context.index_attribute_derivation(&b);
            b = context.index_object_derivation(&gs);
            if *b.difference(&a_new).next().unwrap() >= i {
                return Some((gs, b));
            }
        }
    }

    return None;
}

pub fn concepts<'a, T>(
    context: &'a FormalContext<T>,
) -> impl Iterator<Item = (BTreeSet<usize>, BTreeSet<usize>)> + 'a {
    let gs = context.index_attribute_derivation(&BTreeSet::new());
    let ms = context.index_object_derivation(&gs);
    let mut next = Some((gs, ms));
    std::iter::from_fn(move || {
        if let Some((g, m)) = next.clone() {
            next = next_concept(context, &m);
            return Some((g, m));
        } else {
            return None;
        }
    })
}

#[cfg(test)]
mod tests {
    use std::{collections::BTreeSet, fs};

    use itertools::Itertools;

    use crate::{algorithms::next_closure::concepts, FormalContext};

    #[test]
    fn test_concepts() {
        let context = FormalContext::<String>::from(
            &fs::read("test_data/living_beings_and_water.cxt").unwrap(),
        )
        .unwrap();

        let concepts: BTreeSet<_> = concepts(&context).map(|(_, x)| x).collect();
        let mut concepts_val = BTreeSet::new();
        for ms in (0..context.attributes.len()).powerset() {
            let sub: BTreeSet<usize> = ms.into_iter().collect();
            let hull = context.index_attribute_hull(&sub);
            if sub == hull {
                concepts_val.insert(hull);
            }
        }
        assert_eq!(concepts, concepts_val);
    }
}
