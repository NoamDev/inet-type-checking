use std::collections::HashMap;
use std::fmt::Display;
use std::iter::zip;

use TSPL;
use TSPL::Parser;

use crate::net::{Net, PartialTypeKey};
use crate::util::alphabetize;

TSPL::new_parser!(NamedExprParser);

#[derive(Debug)]
pub enum Expr {
    Lam (Box<Expr>, Option<PartialTypeKey>),
    App (Box<Expr>, Box<Expr>, Option<PartialTypeKey>),
    Var(usize, Option<PartialTypeKey>),
}

#[derive(Debug)]
pub enum NamedExpr {
    Lam (String, Box<NamedExpr>, Option<PartialTypeKey>),
    App (Box<NamedExpr>, Box<NamedExpr>, Option<PartialTypeKey>),
    Var(String, Option<PartialTypeKey>),
}

impl NamedExpr {
    pub fn from_string(s: &str) -> Self {
        let mut parser = NamedExprParser::new(s);
        match parser.parse() {
            Ok(t) => {t}
            Err(msg) => {
                println!("{}", msg);
                panic!("{}", msg);
            }
        }
    }
    pub fn to_annotated_string(&self, net: &Net) -> String {
        match self {
            NamedExpr::Lam(var, body, type_key) => {
                let annotation = net.read_type(type_key.unwrap()).to_string();
                let body = body.to_annotated_string(net);
                format!("{{λ{var}.{body} : {annotation}}}")
            }
            NamedExpr::App(f, v, type_key) => {
                let f_str = f.to_annotated_string(net);
                let v_str = v.to_annotated_string(net);
                let annotation = net.read_type(type_key.unwrap()).to_string();
                format!("{{({f_str} {v_str}) : {annotation}}}")
            }
            NamedExpr::Var(var, type_key) => {
                let annotation = net.read_type(type_key.unwrap()).to_string();
                format!("{{{var} : {annotation}}}")
            }
        }
    }

    pub fn to_variable_annotated_string(&self, net: &Net) -> String {
        match self {
            NamedExpr::Lam(var, body, type_key) => {
                let body_str = body.to_variable_annotated_string(net);
                let lambda_type = net.read_type(type_key.unwrap());
                let variable_type = lambda_type.arg().expect("lambda has arrow type");
                let variable_annotation = variable_type.to_string();
                format!("λ{{{var}: {variable_annotation}}}.{body_str}")
            }
            NamedExpr::App(f, v, _type_key) => {
                let f_str = f.to_variable_annotated_string(net);
                let v_str = v.to_variable_annotated_string(net);
                format!("({f_str} {v_str})")
            }
            NamedExpr::Var(var, _type_key) => {
                format!("{var}")
            }
        }
    }

    pub fn print_annotated_terms(&self, net: &Net) {
        match self {
            NamedExpr::Lam(var, body, type_key) => {
                body.print_annotated_terms(net);
                let body_str = body.to_string();
                let lambda_type = net.read_type(type_key.unwrap());
                let annotation = lambda_type.to_string();
                println!("λ{var}.{body_str} : {annotation}")
            }
            NamedExpr::App(f, v, type_key) => {
                f.print_annotated_terms(net);
                v.print_annotated_terms(net);
                let f_str = f.to_string();
                let v_str = v.to_string();
                let annotation = net.read_type(type_key.unwrap()).to_string();
                println!("({f_str} {v_str}) : {annotation}")
            }
            NamedExpr::Var(var, type_key) => {
                let annotation = net.read_type(type_key.unwrap()).to_string();
                println!("{var}: {annotation}");
            }
        }
    }


    pub fn print_variable_annotated_terms(&self, net: &Net) {
        match self {
            NamedExpr::Lam(var, body, type_key) => {
                body.print_variable_annotated_terms(net);
                let body_str = body.to_variable_annotated_string(net);
                let lambda_type = net.read_type(type_key.unwrap());
                let annotation = lambda_type.to_string();
                println!("{}", annotation);
                let variable_type = lambda_type.arg().expect("lambda has arrow type");
                let variable_annotation = variable_type.to_string();
                println!("λ{{{var} : {variable_annotation}}}.{body_str} : {annotation}")
            }
            NamedExpr::App(f, v, type_key) => {
                f.print_variable_annotated_terms(net);
                v.print_variable_annotated_terms(net);
                let f_str = f.to_variable_annotated_string(net);
                let v_str = v.to_variable_annotated_string(net);
                let annotation = net.read_type(type_key.unwrap()).to_string();
                println!("({f_str} {v_str}) : {annotation}")
            }
            NamedExpr::Var(_var, _type_key) => {}
        }
    }

    pub fn to_debrujin(&self, depth: usize, variables: &mut HashMap<String, Vec<usize>>) -> Expr {
        match self {
            NamedExpr::Lam(name, body, type_key) => {
                let depths = variables.entry(name.clone()).or_default();
                depths.push(depth);
                let body_debrujin = body.to_debrujin(depth+1, variables);
                variables.get_mut(name).unwrap().pop();
                Expr::Lam(
                    Box::new(body_debrujin),
                    type_key.clone()
                )
            }
            NamedExpr::App(f, v, type_key) => {
                Expr::App(
                    Box::new((*f).to_debrujin(depth, variables)),
                    Box::new((*v).to_debrujin(depth, variables)),
                    type_key.clone()
                )
            }
            NamedExpr::Var(name, type_key) => {
                let depths = variables.get(name).unwrap();
                let lam_depth = depths.last().unwrap();
                Expr::Var(depth - lam_depth - 1, type_key.clone())
            }
        }
    }
}

impl<'i> NamedExprParser<'i> {
    pub fn parse(&mut self) -> Result<NamedExpr, String> {
        self.skip_trivia();
        match self.peek_one() {
            Some('λ') => {
                self.consume("λ")?;
                let name = self.take_while(|c| c != '.').to_string();
                self.consume(".")?;
                let body = Box::new(self.parse()?);
                Ok(NamedExpr::Lam( name, body, None ))
            }
            Some('(') => {
                self.consume("(")?;
                let func = Box::new(self.parse()?);
                let argm = Box::new(self.parse()?);
                self.consume(")")?;
                Ok(NamedExpr::App(func, argm, None))
            }
            _ => {
                let name = self.parse_name()?;
                Ok(NamedExpr::Var(name, None))
            }
        }
    }
}

impl Display for NamedExpr {
    fn fmt(&self, f1: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let str = match self {
            NamedExpr::Lam(var, body, _) => {
                let body_str = body.to_string();
                format!("λ{}.{}", var, body_str)
            }
            NamedExpr::App(f, v, _) => {
                let f_str = f.to_string();
                let v_str = v.to_string();
                format!("({} {})", f_str, v_str)
            }
            NamedExpr::Var(var, _) => {
                var.clone()
            }
        };
        write!(f1, "{}", str)
    }
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

    pub fn from_string(s: &str) -> Self {
        NamedExpr::from_string(s).to_debrujin(0, &mut Default::default())
    }
    pub fn to_named(&self) -> NamedExpr {
        self.to_named_free_vars(&mut vec![], &mut 0)
    }
    pub fn to_named_free_vars(&self, vars: &mut Vec<String>, next_variable: &mut usize) -> NamedExpr {
        match self {
            Expr::Lam(b, type_key) => {
                let var = alphabetize(*next_variable).to_lowercase();
                *next_variable += 1;
                vars.push(var.clone());
                let b_named = b.to_named_free_vars(vars, next_variable);
                assert_eq!(vars.pop().unwrap(), var);

                NamedExpr::Lam(var, Box::new(b_named), type_key.clone())
            }
            Expr::App(f, v, type_key) => {
                NamedExpr::App(Box::new(f.to_named_free_vars(vars, next_variable)), Box::new(v.to_named_free_vars(vars, next_variable)), type_key.clone())
            }
            Expr::Var(i, type_key) => {
                let var = vars[vars.len() - i - 1].clone();
                NamedExpr::Var(var, type_key.clone())
            }
        }
    }
    // pub fn print_annotated_term_by_term(&self, net: &Net, vars: &mut Vec<String>, next_variable: &mut usize) {
    //     match self {
    //         Expr::Lam(body, type_key) => {
    //             let var = alphabetize(*next_variable).to_lowercase();
    //             vars.push(var.clone());
    //             *next_variable += 1;
    //             let prev = next_variable.clone();
    //             let body_str = body.to_named_string(vars, next_variable);
    //             *next_variable = prev;
    //             body.print_annotated_term_by_term(net, vars, next_variable);
    //             assert_eq!(vars.pop().unwrap(), var);
    //             let annotation = net.read_type(type_key.unwrap()).to_string();
    //             println!("{{λ{var}.{body_str} : {annotation}}}")
    //         }
    //         Expr::App(f, v, type_key) => {
    //             let f_str = f.to_annotated_string(net,vars, next_variable);
    //             let v_str = v.to_annotated_string(net, vars, next_variable);
    //             let annotation = net.read_type(type_key.unwrap()).to_string();
    //             format!("{{({f_str} {v_str}) : {annotation}}}")
    //         }
    //         Expr::Var(i, type_key) => {
    //             let var = vars[vars.len() - i - 1].clone();
    //             let annotation = net.read_type(type_key.unwrap()).to_string();
    //             format!("{{{var} : {annotation}}}")
    //         }
    //     }
    // }
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