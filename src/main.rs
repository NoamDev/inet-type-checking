use std::vec;

use lambda_optimization::lambda::Expr;
use lambda_optimization::net::{App, Lam, Net, Node, Type, Var};

fn main() {
    // let mut term = Expr::from_string("λx.(λn.λf.((f n) n) λn.λf.((f n) n))");
    // let mut term = Expr::from_string("λa.(λb.(b λc.(b λd.c)) λb.(b (b a)))");
    // let mut term = Expr::from_string("(λx.λf.((f x) x) λx.λf.((f x) x))");
    // let mut term = Expr::from_string("(λf.λh.((h ((f λc.λg.((g c) c)) λe.e)) ((f λe.e) λc.λg.((g c) c))) λa.λb.(a b))");
    let mut term = Expr::from_string("λx.(λn.λf.((f n) n) λn.λf.((f n) n))");
    infer(&mut term);
}

pub fn add_lambda(net: &mut Net, lambda: &mut Expr, vars: &mut Vec<(Var, usize)>) -> Var {
    match lambda {
        Expr::Lam(b, type_key) => {
            let a_var = net.new_var();
            vars.insert(0, (a_var, 0));
            let b_var = add_lambda(net, b, vars);
            let (a_var,occurrences) = vars.remove(0);
            let fan_label = if occurrences < 2 {
                None
            } else {
               Some(net.new_label())
            };
            let a_var = match fan_label {
                None => a_var,
                Some(_) => {
                    let (a1, a2) = net.wire();
                    net.link(vec![Node::AffChk, Node::AffAnn], vec![a_var, a1]);
                    a2
                }
            };

            let res = net.wrap(
                Node::Lam (Lam {
                    a: a_var,
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
            let (eql, occurrences) = &mut vars[*i];
            *occurrences += 1;
            let res = net.add_var(eql);
            *type_key = Some(net.type_key(&res));
            res
        }
    }
}

fn infer(term: &mut Expr) {
    let mut net = Net::default();
    let lam = add_lambda(&mut net, term, &mut vec![]);
    net.assert_valid();
    net.link(vec![], vec![lam]);
    while net.is_reducible() {
        net.reduce();
    }
    if net.is_equated() {
        net.assign_free_vars();
        let named_term = term.to_named();
        named_term.print_annotated_terms(&net);
        if is_dup_safe(term, &net) {
            println!("dup safe");
        } else {
            println!("not dup safe");
        }
    } else {
        println!("not stlc typable")
    }
}

fn is_dup_safe(term: &Expr, net: &Net) -> bool {
    match term {
        Expr::Lam(a, type_id) => {
            is_safe_type(&net.read_type(type_id.unwrap())) && is_dup_safe(a, net)
        }
        Expr::App(a, b, type_id) => {
            is_safe_type(&net.read_type(type_id.unwrap())) &&
                is_dup_safe(a, net) &&
                is_dup_safe(b, net)
        }
        Expr::Var(_i, type_id) => {
            is_safe_type(&net.read_type(type_id.unwrap()))
        }
    }
}

fn is_safe_type(t: &Type) -> bool {
    match t {
        Type::Arrow { a, b } => {
            is_safe_type(a) && is_safe_type(b)
        }
        Type::Cloneable { a } => {
            is_safe_type(a)
        }
        Type::Uncloneable { a } => {
            is_safe_type(a)
        }
        Type::Unsafe { .. } => {false}
        Type::Var(_) => {
            true
        }
    }
}