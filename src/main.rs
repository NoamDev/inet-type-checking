use std::vec;

use lambda_optimization::lambda;
use lambda_optimization::net;
use slotmap::SlotMap;


fn main() {
    // for term in lambda::enumerate_terms(0, 4) {
    //     println!("{:?}", term.to_string());
    // }
    // println!("Hello, world!");
    let mut types = SlotMap::new();
    let type_id = types.insert(Option::None);
    let mut equations = SlotMap::new();
    let x = equations.insert_with_key(|key| net::Equation { missing: 2, trees: vec![], next: key, prev: key });
    let a = net::Tree::Eql(x);
    let b = net::Tree::Eql(x);
    let lam = net::Node::Con { a: Box::new(a), b: Box::new(b) };
    let mut redexes = Vec::new();
    let root = net::Node::Free { type_id };
    redexes.push(vec![root, lam]);
    
    let mut net = net::Net {
        types,
        equations,
        redexes,
    };
    while net.is_reducible() {
        net.reduce();
    }
    println!("type: {:?}", net.read_type(type_id, 0));
}
