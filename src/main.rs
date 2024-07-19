use std::vec;

use lambda_optimization::lambda;
use lambda_optimization::lambda::Expr;
use lambda_optimization::net;
use lambda_optimization::net::{Eql, Net, Node, PartialType, Tree};

fn main() {
    for term in lambda::enumerate_terms(1, 10) {
        infer(&term);
    }
}

pub fn add_lambda(net: &mut Net, lambda: &Expr, vars: &mut Vec<Eql>) -> Tree {
    match lambda {
        Expr::Lam(b) => {
            let eql = net.new_eql();
            let eql2 = net.add_eql(&eql);
            vars.push(eql2);
            let b_tree = add_lambda(net, b, vars);
            net.era_eql(vars.pop().unwrap());
            Tree::Node(
                Node::Con {
                    a: Box::new(Tree::Eql(eql)),
                    b: Box::new(b_tree)
                }
            )
        }
        Expr::App(f, v) => {
            let f_tree = add_lambda(net, f, vars);
            let v_tree = add_lambda(net, v, vars);
            let eql = net.new_eql();
            let eql2 = net.add_eql(&eql);

            let app = Tree::Node(Node::Con {
                a: Box::new(v_tree),
                b: Box::new(Tree::Eql(eql)),
            });
            net.link(vec![f_tree, app]);
            Tree::Eql(eql2)
        }
        Expr::Var(i) => {
            let eql = &vars[vars.len() - i - 1];
            Tree::Eql(net.add_eql(eql))
        }
    }
}

fn infer(term: &Expr) {
    let term_txt = term.to_string();
    println!("{}", term_txt);

    let mut net = Net::default();
    let type_id = net.types.insert(PartialType::Free(None));
    let lam = add_lambda(&mut net, &term, &mut vec![]);
    let root = net::Node::Free { type_id };
    net.assert_valid();
    net.link(vec![lam, net::Tree::Node(root)]);
    net.assert_valid();
    while net.is_reducible() {
        net.assign_free_vars();
        net.reduce();
        net.assert_valid();
    }

    if net.is_equated() {
        net.assign_free_vars();
        println!("type: {}", net.read_type(type_id).to_string());
    } else {
        println!("Not STLC typable");
    }
}
