use hs_bindgen::*;

#[hs_bindgen]
fn hello(name: &str) {
    println!("Hello, {name}!");
}

#[hs_bindgen]
pub fn add(left: u32, right: u32) -> u32 {
    left + right
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn it_works() {
        let result = add(2, 2);
        assert_eq!(result, 4);
    }
}
