use dual_number::*;

fn main() {
    let x = DualNumber::new(6, 17);
    let y = DualNumber::new(4, 20);

    let ans = x - y;
    println!("{} - {} = {}", x, y, ans);
}
