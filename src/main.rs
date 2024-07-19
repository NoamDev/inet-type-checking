use std::vec;

use lambda_optimization::lambda;
use lambda_optimization::lambda::{app, Expr, lam, var};
use lambda_optimization::net::{Eql, Net, Node, Tree};

fn main() {
    for mut term in lambda::enumerate_terms(1, 10) {
        infer(&mut term);
    }
    // λ(0 λ0)
    // let term = lam(
    //     app(
    //         var(0),
    //         lam(var(0))
    //     )
    // );
    // println!("{}", term.to_string());
    // println!("{}", to_named_string(&term, &mut vec![]));
    // λ(λ(0 λ(1 λ1)) λ(0 (0 2)))
    let mut term = lam(
        app(
            lam(
                app(
                    var(0),
                    lam(
                        app(
                            var(1),
                            lam(var(1))
                        )
                    )
                )
            ),
            lam(
                app(
                    var(0),
                    app(var(0), var(1))
                )
            )
        )
    );
    infer(&mut term);
}

pub fn add_lambda(net: &mut Net, lambda: &mut Expr, vars: &mut Vec<Eql>) -> Tree {
    match lambda {
        Expr::Lam(b, type_key) => {
            let eql = net.new_eql();
            let eql2 = net.add_eql(&eql);
            vars.push(eql2);
            let b_tree = add_lambda(net, b, vars);
            net.era_eql(vars.pop().unwrap());
            let res = Tree::Node(
                Node::Con {
                    type_key: net.new_type(),
                    a: Box::new(Tree::Eql(eql)),
                    b: Box::new(b_tree)
                }
            );
            *type_key = Some(net.type_key(&res));
            res
        }
        Expr::App(f, v, type_key) => {
            let f_tree = add_lambda(net, f, vars);
            let v_tree = add_lambda(net, v, vars);
            let eql = net.new_eql();
            let eql2 = net.add_eql(&eql);

            let app = Tree::Node(Node::Con {
                type_key: net.new_type(),
                a: Box::new(v_tree),
                b: Box::new(Tree::Eql(eql)),
            });
            net.link(vec![f_tree, app]);
            let res = Tree::Eql(eql2);
            *type_key = Some(net.type_key(&res));
            res
        }
        Expr::Var(i, type_key) => {
            let eql = &vars[vars.len() - *i - 1];
            let res = Tree::Eql(net.add_eql(eql));
            *type_key = Some(net.type_key(&res));
            res
        }
    }
}

// fn annotate(expr: &Expr, net: &Net) -> String {
//     match expr {
//         Expr::Lam(_, _) => {}
//         Expr::App(_, _, _) => {}
//         Expr::Var(_, _) => {}
//     }
// }

fn infer(term: &mut Expr) {
    println!("{}", term.to_string());
    println!("{}", term.to_named_string(&mut vec![], &mut 0));

    let mut net = Net::default();
    let lam = add_lambda(&mut net, term, &mut vec![]);
    let type_key = net.type_key(&lam);
    net.assert_valid();
    net.link(vec![lam]);
    net.assert_valid();
    while net.is_reducible() {
        net.assign_free_vars();
        net.reduce();
        net.assert_valid();
    }

    if net.is_equated() {
        net.assign_free_vars();
        println!("type: {}", net.read_type(type_key).to_string());
        println!("{}", term.to_variable_annotated_string(&net, &mut vec![], &mut 0));
        println!("{}", term.to_annotated_string(&net, &mut vec![], &mut 0));
    } else {
        println!("Not STLC typable");
    }
}
