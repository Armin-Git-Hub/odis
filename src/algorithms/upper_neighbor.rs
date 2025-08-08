use bit_set::BitSet;

use crate::FormalContext;

pub fn upper_neighbor<T>(input: &BitSet, context: &FormalContext<T>) -> BitSet {
    let diff_set: BitSet = (0..context.objects.len())
        .collect::<BitSet>()
        .difference(input)
        .collect();

    let mut output = diff_set.clone();

    for m in &diff_set {
        let mut set_m = BitSet::new();
        set_m.insert(m);

        let hull_input_m =
            FormalContext::index_object_hull(context, &input.union(&set_m).collect());

        let hull_input_m_and_output = hull_input_m.intersection(&output).collect::<BitSet>();

        if hull_input_m_and_output != set_m {
            output.difference_with(&set_m);
        }
    }
    output
}
