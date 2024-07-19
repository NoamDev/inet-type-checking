use std::fmt::Display;
use std::iter::zip;
use crate::net::{Net, PartialTypeKey, Type};
use crate::util::alphabetize;

#[derive(Debug)]
pub enum Expr {
    Lam (Box<Expr>, Option<PartialTypeKey>),
    App (Box<Expr>, Box<Expr>, Option<PartialTypeKey>),
    Var(usize, Option<PartialTypeKey>),
}

pub fn lam(e: Expr) -> Expr {
    Expr::Lam(Box::new(e), None)
}

pub fn app(f: Expr, v: Expr) -> Expr {
    Expr::App(Box::new(f), Box::new(v), None)
}

pub fn var(i: usize) -> Expr{
    Expr::Var(i, None)
}

impl Expr {
    pub fn to_named_string(&self, vars: &mut Vec<String>, next_variable: &mut usize) -> String {
        match self {
            Expr::Lam(body, _) => {
                let var = alphabetize(*next_variable).to_lowercase();
                *next_variable += 1;
                vars.push(var.clone());
                let body_str = body.to_named_string(vars, next_variable);
                assert_eq!(vars.pop().unwrap(), var);
                format!("λ{}.{}", var, body_str)
            }
            Expr::App(f, v, _) => {
                let f_str = f.to_named_string(vars, next_variable);
                let v_str = v.to_named_string(vars, next_variable);
                format!("({} {})", f_str, v_str)
            }
            Expr::Var(i, _) => {
                vars[vars.len() - i - 1].clone()
            }
        }
    }
    pub fn to_annotated_string(&self, net: &Net, vars: &mut Vec<String>, next_variable: &mut usize) -> String {
        match self {
            Expr::Lam(body, type_key) => {
                let var = alphabetize(*next_variable).to_lowercase();
                vars.push(var.clone());
                *next_variable += 1;
                let body_str = body.to_annotated_string(net, vars, next_variable);
                assert_eq!(vars.pop().unwrap(), var);
                let annotation = net.read_type(type_key.unwrap()).to_string();
                format!("{{λ{var}.{body_str} : {annotation}}}")
            }
            Expr::App(f, v, type_key) => {
                let f_str = f.to_annotated_string(net,vars, next_variable);
                let v_str = v.to_annotated_string(net, vars, next_variable);
                let annotation = net.read_type(type_key.unwrap()).to_string();
                format!("{{({f_str} {v_str}) : {annotation}}}")
            }
            Expr::Var(i, type_key) => {
                let var = vars[vars.len() - i - 1].clone();
                let annotation = net.read_type(type_key.unwrap()).to_string();
                format!("{{{var} : {annotation}}}")
            }
        }
    }
    pub fn to_variable_annotated_string(&self, net: &Net, vars: &mut Vec<String>, next_variable: &mut usize) -> String {
        match self {
            Expr::Lam(body, type_key) => {
                let var = alphabetize(*next_variable).to_lowercase();
                *next_variable += 1;
                vars.push(var.clone());
                let body_str = body.to_variable_annotated_string(net, vars, next_variable);
                assert_eq!(vars.pop().unwrap(), var);
                let lambda_type = net.read_type(type_key.unwrap());
                let variable_type = match lambda_type {
                    Type::Arrow(v, _b) => {*v}
                    Type::Var(_) => {
                        panic!("lambda has non lambda type");
                    }
                };
                let variable_annotation = variable_type.to_string();
                format!("λ{{{var}: {variable_annotation}}}.{body_str}")
            }
            Expr::App(f, v, _type_key) => {
                let f_str = f.to_variable_annotated_string(net,vars, next_variable);
                let v_str = v.to_variable_annotated_string(net, vars, next_variable);
                format!("({f_str} {v_str})")
            }
            Expr::Var(i, _type_key) => {
                let var = vars[vars.len() - i - 1].clone();
                format!("{var}")
            }
        }
    }
}

impl Display for Expr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let str = match self {
            Expr::Lam(body, ..) => format!("λ{}", body.to_string()),
            Expr::App(fun, arg, ..) => format!("({} {})", fun.to_string(), arg.to_string()),
            Expr::Var(i, ..) => i.to_string(),
        };
        write!(f, "{}", str)
    }
}

pub fn enumerate_terms_depth(depth: usize, lambda_depth: usize) ->  Box<dyn Iterator<Item = Expr>> {
    if depth == 1 {
        Box::new((0..lambda_depth).map(|i| Expr::Var(i, None)))
    } else {
        let lam =
            enumerate_terms_depth(
                depth-1, lambda_depth+1
            ).map(|e| lam(e));

        let expr = (1..depth).flat_map(move|d| {
            zip(
                enumerate_terms_depth(d, lambda_depth),
                enumerate_terms_depth(depth - d, lambda_depth),
            ).map(|(a, b)| app(a, b))
        });
        Box::new(lam.chain(expr))
    }
}

pub fn enumerate_terms(start: usize, end: usize) -> Box<dyn Iterator<Item = Expr>> {
    assert_ne!(start, 0);
    Box::new((start..end).flat_map(|i| enumerate_terms_depth(i, 0)))
}