use std::fmt::Display;
use std::iter::zip;

#[derive(Debug)]
pub enum Expr {
    Lam (Box<Expr>),
    App (Box<Expr>, Box<Expr>),
    Var(usize),
}

pub fn lam(e: Expr) -> Expr {
    Expr::Lam(Box::new(e))
}

pub fn app(f: Expr, v: Expr) -> Expr {
    Expr::App(Box::new(f), Box::new(v))
}

pub fn var(i: usize) -> Expr{
    Expr::Var(i)
}


impl Display for Expr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let str = match self {
            Expr::Lam(body) => format!("λ{}", body.to_string()),
            Expr::App(fun, arg) => format!("({} {})", fun.to_string(), arg.to_string()),
            Expr::Var(i) => i.to_string(),
        };
        write!(f, "{}", str)
    }
}

pub fn enumerate_terms_depth(depth: usize, lambda_depth: usize) ->  Box<dyn Iterator<Item = Expr>> {
    if depth == 1 {
        Box::new((0..lambda_depth).map(|i| Expr::Var(i)))
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