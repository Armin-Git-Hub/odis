use std::collections::BTreeSet;

use crate::FormalContext;

fn next_intent<T>(context: &FormalContext<T>, a: &BTreeSet<usize>) -> Option<BTreeSet<usize>> {
    let mut a_new = a.clone();
    // let i_iter = ;
    let mut a_iter = a.iter().rev();
    let mut a_next = a_iter.next();
    for i in (0..context.attributes.len()).rev() {
        if Some(&i) == a_next {
            a_new.remove(&i);
            a_next = a_iter.next();
        } else {
            let mut b = a_new.clone();
            b.insert(i);
            b = context.index_attribute_hull(&b);
            if *b.difference(&a_new).next().unwrap() >= i {
                return Some(b);
            }
        }
    }

    return None;
}

pub fn index_intents<'a, T>(
    context: &'a FormalContext<T>,
) -> impl Iterator<Item = BTreeSet<usize>> + 'a {
    let mut next = Some(context.index_attribute_hull(&BTreeSet::new()));
    std::iter::from_fn(move || {
        if let Some(a) = next.clone() {
            next = next_intent(context, &a);
            return Some(a);
        } else {
            return None;
        }
    })
}

mod tests {
    use std::collections::BTreeSet;

    use crate::FormalContext;

    use super::index_intents;

    #[test]
    fn test_concepts() {
        let context =
            FormalContext::<String>::read("test_data/living_beings_and_water.cxt".to_string())
                .unwrap();
        let l: BTreeSet<_> = index_intents(&context).collect();
        println!("{:?}", l);
    }
}
