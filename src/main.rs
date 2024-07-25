use std::vec;

use lambda_optimization::lambda;
use lambda_optimization::lambda::{app, Expr, lam, NamedExpr, NamedExprParser, var};
use lambda_optimization::net::{App, Lam, Net, Node, Type, EdgeRef, Var};

fn main() {
    // for mut term in lambda::enumerate_terms(15, 20) {
    //     if infer(&mut term) {
    //         if ! safe_infer(&mut term) {
    //             let named_term = term.to_named(&mut vec![], &mut 0);
    //             println!("{}",named_term.to_string());
    //         }
    //         // println!("is_safe_reduced: {}", safe_infer(&mut term));
    //     }
    // }
    // let mut term = Expr::from_string("λx.(λn.λf.((f n) n) λn.λf.((f n) n))");
    // let mut term = Expr::from_string("λa.(λb.(b λc.(b λd.c)) λb.(b (b a)))");
    // let mut term = Expr::from_string("λx.(λf.((f x) x) λf.((f x) x))");
    // println!("{}", term);
    // if infer(&mut term) {
    //     let named_term = term.to_named(&mut vec![], &mut 0);
    //     println!("{}",named_term.to_string());
    //     println!("is_safe_reduced: {}", safe_infer(&mut term));
    // }
    let mut term = Expr::from_string("λx.x");
    if infer(&mut term) {
        println!("inferred!");
    }
}

pub fn add_lambda(net: &mut Net, lambda: &mut Expr, vars: &mut Vec<Var>) -> Var {
    match lambda {
        Expr::Lam(b, type_key) => {
            let var = net.new_var();
            vars.push(var);
            let b_var = add_lambda(net, b, vars);
            let var = vars.pop().unwrap();
            let ref_count = net.var_refs_count(&var);
            assert!(ref_count > 0);
            let occurrences = ref_count - 1;
            let fan_label = if occurrences < 2 {
                None
            } else {
               Some(net.new_label())
            };

            let res = net.wrap(
                Node::Lam (Lam {
                    a: var,
                    b: b_var
                })
            );

            *type_key = Some(net.type_key(&res));
            res
        }
        Expr::App(f, arg, type_key) => {
            let f_var = add_lambda(net, f, vars);
            let arg_var = add_lambda(net, arg, vars);

            let (w1, w2) = net.wire();
            let app = Node::App(App {
                a: arg_var,
                b: w1,
            });
            net.link_var_node(f_var, app);
            let res = w2;
            *type_key = Some(net.type_key(&res));
            res
        }
        Expr::Var(i, type_key) => {
            let eql = &vars[vars.len() - *i - 1];
            let res = net.add_var(eql);
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

fn infer(term: &mut Expr) -> bool {
    let mut net = Net::default();
    let lam = add_lambda(&mut net, term, &mut vec![]);
    let type_key = net.type_key(&lam);
    net.link(vec![], vec![lam]);
    while net.is_reducible() {
        net.assign_free_vars();
        net.reduce();
    }
    if net.is_equated() {
        net.assign_free_vars();
        let named = term.to_named();
        named.print_annotated_terms(&net);
        return true;
    } else {
        return false;
    }
}


// fn safe_infer(term: &mut Expr) -> bool {
//     let mut net = Net::default();
//     let lam = add_lambda(&mut net, term, &mut vec![]);
//     let type_key = net.type_key(&lam);
//     net.link(vec![Tree::Eql(lam)]);
//     // net.assign_free_vars();
//     // net.read();
//     while net.is_reducible() {
//         // net.assign_free_vars();
//         // net.read();
//         net.safe_reduce();
//         net.assert_valid();
//     }
//     // net.assign_free_vars();
//     // net.read();
//     if net.is_equated() {
//         net.assign_free_vars();
//         // let named_term = term.to_named(&mut vec![], &mut 0);
//         // println!("{}", named_term.to_annotated_string(&net));
//         // named_term.print_annotated_terms(&net);
//         return true;
//     } else {
//         return false;
//     }
// }

// fn is_safe_term(term: &Expr, net: &Net) -> bool {
//     match term {
//         Expr::Lam(b, type_key) => {
//             let term_type = net.read_type(type_key.unwrap());
//             is_safe_type(&term_type) && is_safe_term(b, &net)
//         }
//         Expr::App(f, v, type_key) => {
//             let term_type = net.read_type(type_key.unwrap());
//             is_safe_type(&term_type) && is_safe_term(f, &net) && is_safe_term(v, &net)
//         }
//         Expr::Var(i, type_key) => {
//             let term_type = net.read_type(type_key.unwrap());
//             is_safe_type(&term_type)
//         }
//     }
// }
//
// fn is_safe_type(term_type: &Type) -> bool {
//     match term_type {
//         Type::Arrow { a, b, fan_labels} => {
//             !contains_labels(a, fan_labels) && is_safe_type(a) && is_safe_type(b)
//         }
//         Type::Var(_) => {true}
//     }
// }
//
// fn contains_labels(term_type: &Type, labels: &Vec<usize>) -> bool {
//     match term_type {
//         Type::Arrow { a, b, fan_labels } => {
//             // println!("Checking if {fan_labels:?} contains {labels:?}");
//             labels.iter().any(|l| fan_labels.contains(l)) ||
//                 contains_labels(a, labels) ||
//                 contains_labels(b, labels)
//         }
//         Type::Var(_) => {
//             false
//         }
//     }
// }