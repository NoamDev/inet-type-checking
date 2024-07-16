use std::{fmt::format, iter::zip};

#[derive(Debug)]
pub enum Expr {
    Lam (Box<Expr>),
    App (Box<Expr>, Box<Expr>),
    Var(usize),
}

impl Expr {
    pub fn to_string(&self) -> String {
        match self {
            Expr::Lam(body) => format!("λ{}", body.to_string()),
            Expr::App(fun, arg) => format!("({} {})", fun.to_string(), arg.to_string()),
            Expr::Var(i) => i.to_string(),
        }
    }

}

fn enumerate_terms_depth(depth: usize, lambda_depth: usize) ->  Box<dyn Iterator<Item = Expr>> {
    if depth == 0 {
        Box::new((0..lambda_depth).map(|i| Expr::Var(i)))
    } else {
        let lam = enumerate_terms_depth(depth-1, lambda_depth+1).map(|e| Expr::Lam(Box::new(e)));
        let expr = (0..depth).flat_map(move|d| {
            zip(
                enumerate_terms_depth(d, lambda_depth),
                enumerate_terms_depth(depth - d, lambda_depth),
            ).map(|(a, b)| Expr::App(Box::new(a), Box::new(b)))
        });
        Box::new(lam.chain(expr))
    }
}

pub fn enumerate_terms(start: usize, end: usize) -> Box<dyn Iterator<Item = Expr>> {
    Box::new((start..end).flat_map(|i| enumerate_terms_depth(i, 0)))
}