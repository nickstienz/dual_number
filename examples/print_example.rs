use dual_number::*;

fn main() {
    let x = DualNumber::new(3, 2);
    let y = DualNumber::new(-9, -4);
    let z = DualNumber::new(5, 0);

    println!("{}", x);
    println!("{}", y);
    println!("{}", z);
}
