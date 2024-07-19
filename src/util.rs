pub(crate) fn alphabetize(n: usize) -> String{
    let alphabet: String = "ABCDEFGHIJKLMNOPQRSTUVWXYZ".to_string();
    let mut res = String::new();
    let mut i = n;
    loop {
        res.push(alphabet.chars().nth(i%26).unwrap());
        i /= 26;
        if i == 0 {
            return res;
        } else {
            i -= 1;
        }
    }
}
