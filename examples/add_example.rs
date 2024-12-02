use dual_number::*;

fn main() {
    let x = DualNumber::new(5, 3);
    let y = DualNumber::new(10, 2);

    let ans = x + y;
    println!("{} + {} = {}", x, y, ans);
}
