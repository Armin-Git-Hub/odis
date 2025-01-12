use bit_set::BitSet;

use crate::FormalContext;

fn is_smallest_num(max: usize, input_set: &BitSet) -> bool {
    for n in 0..max {
        if input_set.contains(n) {
            return false;
        }
    }
    true
}

fn set_upto(n: usize) -> BitSet {
    let mut b = BitSet::new();
    for i in 0..n + 1 {
        b.insert(i);
    }
    b
}

fn implication_closure(implications: &Vec<(BitSet, BitSet)>, input: &BitSet) -> BitSet {
    let mut implications = implications.clone();
    let mut output = input.clone();
    loop {
        let mut indices = BitSet::new();
        let mut repeat = false;
        for (index, (premise, conclusion )) in implications.iter().enumerate() {
            if premise.is_subset(&output) {
                output.union_with(&conclusion);
                indices.insert(index);
                repeat = true;
            }
        }
        if !repeat {
            break;
        }
        let mut count = 0;
        implications.retain(|_|
            if indices.contains(count){
                count += 1;
                false
            } else {
                count += 1;
                true
            }
        );
    }
    output
}

fn next_preclosure<T>(
    context: &FormalContext<T>,
    implications: &Vec<(BitSet, BitSet)>,
    input: &BitSet,
) -> BitSet {
    let mut temp_set = input.clone();
    let mut current_attribute = BitSet::new();

    for n in (0..context.attributes.len()).rev() {
        current_attribute.insert(n);
        if temp_set.contains(n) {
            temp_set.remove(n);
        } else {
            let output: BitSet = implication_closure(implications, &temp_set.union(&current_attribute).collect());
            if is_smallest_num(n, &output.difference(&temp_set).collect()) {
                return output;
            }
        }
        current_attribute.clear();
    }
    return (0..context.attributes.len()).collect();
}

pub fn canonical_basis<T>(context: &FormalContext<T>) -> Vec<(BitSet, BitSet)> {
    let mut temp_set = BitSet::new();
    let mut implications: Vec<(BitSet, BitSet)> = Vec::new();

    while temp_set != set_upto(context.attributes.len() - 1) {
        let temp_set_hull = context.index_attribute_hull(&temp_set);
        if temp_set != temp_set_hull {
            implications.push((temp_set.clone(), temp_set_hull));
        }
        temp_set = next_preclosure(&context, &implications, &temp_set);
    }
    implications
}

#[cfg(test)]
mod tests {
    use std::fs;
    use bit_set::BitSet;
    use crate::algorithms::{canonical_basis::{canonical_basis, implication_closure, next_preclosure}, FormalContext};

    #[test]
    fn canonical_basis_test() {
        let context = FormalContext::<String>::from(
            &fs::read("test_data/triangles.cxt").unwrap(),
        ).unwrap();
        
        let output = canonical_basis(&context);

        let mut canonical_basis = Vec::new();
        // {3,4} -> {0,1,2,3,4}
        canonical_basis.push((BitSet::from_bytes(&[0b00011000]), BitSet::from_bytes(&[0b11111000])));
        // {2,4} -> {0,1,2,3,4}
        canonical_basis.push((BitSet::from_bytes(&[0b00101000]), BitSet::from_bytes(&[0b11111000])));
        // {2,3} -> {0,1,2,3,4}
        canonical_basis.push((BitSet::from_bytes(&[0b00110000]), BitSet::from_bytes(&[0b11111000])));
        // {0} -> {0,1,2}
        canonical_basis.push((BitSet::from_bytes(&[0b10000000]), BitSet::from_bytes(&[0b11100000])));

        assert_eq!(output, canonical_basis);
    }

    #[test]
    fn next_closure_test() {
        let context = FormalContext::<String>::from(
            &fs::read("test_data/triangles.cxt").unwrap(),
        ).unwrap();

        let mut canonical_basis = Vec::new();

        let input = BitSet::new();
        let output = next_preclosure(&context, &canonical_basis, &input);
        assert_eq!(output, BitSet::from_bytes(&[0b00001000]));

        let input = BitSet::from_bytes(&[0b00001000]);
        let output = next_preclosure(&context, &canonical_basis, &input);
        assert_eq!(output, BitSet::from_bytes(&[0b00010000]));

        let input = BitSet::from_bytes(&[0b00010000]);
        let output = next_preclosure(&context, &canonical_basis, &input);
        assert_eq!(output, BitSet::from_bytes(&[0b00011000]));

        // {3,4} -> {0,1,2,3,4}
        canonical_basis.push((BitSet::from_bytes(&[0b00011000]), BitSet::from_bytes(&[0b11111000])));
        let input = BitSet::from_bytes(&[0b00011000]);
        let output = next_preclosure(&context, &canonical_basis, &input);
        assert_eq!(output, BitSet::from_bytes(&[0b00100000]));
    }

    #[test]
    fn implication_closure_test() {
        let mut implications = Vec::new();
        // {1} -> {1,2,3}
        implications.push((BitSet::from_bytes(&[0b01000000]), BitSet::from_bytes(&[0b00110000])));
        // {4,5} -> {1,2,3,4,5}
        implications.push((BitSet::from_bytes(&[0b00001100]), BitSet::from_bytes(&[0b01111100])));
        // {3,5} -> {1,2,3,4,5}
        implications.push((BitSet::from_bytes(&[0b00010100]), BitSet::from_bytes(&[0b01111100])));
        // {3,4} -> {1,2,3,4,5}
        implications.push((BitSet::from_bytes(&[0b00011000]), BitSet::from_bytes(&[0b01111100])));

        let mut input = BitSet::new();
        input.insert(1);
        // {1,2,3}
        assert_eq!(implication_closure(&implications, &input), BitSet::from_bytes(&[0b01110000]));

        let mut input = BitSet::new();
        input.insert(4);
        input.insert(5);
        // {1,2,3,4,5}
        assert_eq!(implication_closure(&implications, &input), BitSet::from_bytes(&[0b01111100]));

        let mut input = BitSet::new();
        input.insert(3);
        input.insert(5);
        // {1,2,3,4,5}
        assert_eq!(implication_closure(&implications, &input), BitSet::from_bytes(&[0b01111100]));

        let mut input = BitSet::new();
        input.insert(3);
        input.insert(4);
        // {1,2,3,4,5}
        assert_eq!(implication_closure(&implications, &input), BitSet::from_bytes(&[0b01111100]));
    }
}
