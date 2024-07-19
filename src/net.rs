use std::collections::HashSet;
use std::fmt::Display;
use std::vec;

use slotmap::{new_key_type, SlotMap};

#[derive(Debug)]
pub enum Type {
    Arrow(Box<Type>, Box<Type>),
    Var(usize)
}

new_key_type! { pub struct PartialTypeKey; }
#[derive(Debug)]
pub enum PartialType {
    Arrow(PartialTypeKey, PartialTypeKey),
    Var(PartialTypeKey),
    Free(Option<usize>)
}

fn alphabetize(n: usize) -> String{
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

impl Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let str = match self {
            Type::Arrow(a, b) => {
                format!("({}->{})", a.to_string(), b.to_string())
            }
            Type::Var(i) => { alphabetize(*i) }
        };
        write!(f, "{}", str)
    }
}

#[derive(Debug)]
pub enum Node {
    Con {
        a: Box<Tree>,
        b: Box<Tree>,
    },
    Free {
        type_id: PartialTypeKey,
    },
}

#[derive(Debug)]
pub struct Eql {
    eq_ref: EquationRefKey
}

#[derive(Debug)]
pub enum Tree {
    Node(Node),
    Eql(Eql),
}

new_key_type! { struct EquationRefKey; }
#[derive(Debug)]
struct EquationRef {
    i: usize,
    key: EquationKey,
}

new_key_type! { struct EquationKey; }
#[derive(Debug)]
struct Equation {
    pub trees: Vec<Node>,
    pub refs: Vec<EquationRefKey>,
}

#[derive(Default, Debug)]
pub struct Net {
    pub equations: SlotMap<EquationKey, Equation>,
    pub equation_refs: SlotMap<EquationRefKey, EquationRef>,
    pub redexes: Vec<Vec<Node>>,
    pub types: SlotMap<PartialTypeKey, PartialType>,
}

impl Net {
    pub fn is_reducible(&self) -> bool {
        return self.redexes.len() > 0;
    }
    pub fn is_equated(&self) -> bool {
        self.equations.len() == 0
    }
    pub fn reduce(&mut self) {
        let  r = self.redexes.pop();
        if let Some(r) = r {
            let mut eq1_trees = vec![];
            let mut eq2_trees = vec![];
            let mut eq1_eqs = vec![];
            let mut eq2_eqs = vec![];
            let mut free = vec![];
            
            for t in r {
                match t {
                    Node::Con {a, b } => {
                        match *a {
                            Tree::Node(node) => eq1_trees.push(node),
                            Tree::Eql(e_key) => {
                                eq1_eqs.push(e_key);
                            },
                        }
                        match *b {
                            Tree::Node(node) => eq2_trees.push(node),
                            Tree::Eql(e_key) => {
                                eq2_eqs.push(e_key);
                            },
                        }
                    },
                    Node::Free { type_id } => {
                        free.push(type_id);
                    },
                }
            }

            if free.len() > 0 {
                if eq1_trees.len() == 0 && eq1_eqs.len() == 0 {
                    let combined = self.types.insert(PartialType::Free(None));
                    for f in free {
                        *(self.types.get_mut(f).unwrap()) = PartialType::Var(combined);
                    }
                } else {
                    let a = self.types.insert(PartialType::Free(None));
                    let b = self.types.insert(PartialType::Free(None));
                    for f in free {
                        *(self.types.get_mut(f).unwrap()) = PartialType::Arrow(a, b);
                    }
                    eq1_trees.push(Node::Free { type_id: a });
                    eq2_trees.push(Node::Free { type_id: b });
                }
            }

            if eq1_eqs.len() > 0 {
                self.merge_eq(eq1_eqs, eq1_trees);
            } else if eq1_trees.len() > 0 {
                self.redexes.push(eq1_trees);
            }
            if eq2_eqs.len() > 0 {
                self.merge_eq(eq2_eqs, eq2_trees);
            } else if eq2_trees.len() > 0 {
                self.redexes.push(eq2_trees);
            }
        }
        self.assert_valid();
    }
    pub fn read_type(&self, type_key: PartialTypeKey) -> Type {
        let t = self.types.get(type_key).unwrap();
        match t {
            PartialType::Arrow(a, b) => Type::Arrow(Box::new(self.read_type(a.clone())), Box::new(self.read_type(b.clone()))),
            PartialType::Var(key) => self.read_type(key.clone()),
            PartialType::Free(free_var) => Type::Var(free_var.unwrap()),
        }
    }
    pub fn assign_free_vars(&mut self) {
        let mut i = 0;
        for v in self.types.values_mut() {
            if let PartialType::Free(t) = v {
                *t = Some(i);
                i += 1;
            }
        }
    }
    pub fn new_eql(&mut self) -> Eql {
        let eq_key = self.equations.insert(Equation {trees: vec![], refs: vec![]});
        let eq_ref = self.equation_refs.insert(EquationRef {key: eq_key, i: 0});
        self.eq_mut(eq_key).refs.push(eq_ref);
        self.assert_valid();
        Eql {eq_ref}
    }
    pub fn add_eql(&mut self, eql: &Eql) -> Eql {
        let eq_key = self.eq_ref(eql.eq_ref).key;
        let ref_key = self.equation_refs.insert(
            EquationRef {key: eq_key, i: self.eq(eq_key).refs.len()}
        );
        self.eq_mut(eq_key).refs.push(ref_key);
        self.assert_valid();
        Eql {eq_ref: ref_key}
    }
    pub fn era_eql(&mut self, eql: Eql) {
        let eq_ref = self.equation_refs.remove(eql.eq_ref).unwrap();
        let eq = self.eq_mut(eq_ref.key);
        assert_eq!(eq.refs.remove(eq_ref.i), eql.eq_ref);
        let eq_refs = eq.refs.clone();
        if eq_refs.len() == 0 {
            let eq = self.equations.remove(eq_ref.key).unwrap();
            if eq.trees.len() > 0 {
                self.redexes.push(eq.trees);
            }
        } else {
            for (i,r_k) in eq_refs.iter().enumerate() {
                self.eq_ref_mut(*r_k).i = i;
            }
        }
        self.assert_valid();
    }
    pub fn link(&mut self, trees: Vec<Tree>) {
        let mut nodes = vec![];
        let mut refs = vec![];
        for t in trees {
            match t {
                Tree::Node(node) => {
                    nodes.push(node);
                }
                Tree::Eql(ref_key) => {
                    refs.push(ref_key);
                }
            }
        }
        if refs.len() == 0 {
            self.redexes.push(nodes);
        } else {
            self.merge_eq(refs, nodes);
        }
        self.assert_valid();
    }
    pub fn assert_valid(&self) {
        for redex in self.redexes.iter() {
            for node in redex.iter() {
                self.assert_valid_node(node);
            }
        }

        for (ref_key, eq_ref) in self.equation_refs.iter() {
            assert!(self.equations.contains_key(eq_ref.key));
            assert_eq!(self.eq(eq_ref.key).refs[eq_ref.i], ref_key);
        }

        for (eq_key, eq) in self.equations.iter() {
            assert!(eq.refs.len() > 0);
            let hs: HashSet<_> = eq.refs.iter().collect();
            assert_eq!(hs.len(), eq.refs.len());
            for (i,r_k) in eq.refs.iter().enumerate() {
                assert!(self.equation_refs.contains_key(*r_k));
                let eq_ref = self.eq_ref(*r_k);
                assert_eq!(eq_ref.key, eq_key);
                assert_eq!(eq_ref.i, i);
            }
            for node in eq.trees.iter() {
                self.assert_valid_node(node);
            }
        }
    }
    pub fn assert_valid_node(&self, node: &Node) {
        match node {
            Node::Con { a, b } => {
                self.assert_valid_tree(a);
                self.assert_valid_tree(b);
            }
            Node::Free { .. } => {
                ()
            }
        }
    }
    fn assert_valid_tree(&self, tree: &Tree) {
        match tree {
            Tree::Node(node) => {
                self.assert_valid_node(node)
            }
            Tree::Eql(r_k) => {
                assert!(self.equation_refs.contains_key(r_k.eq_ref));
            }
        }
    }
    fn eq(&self, k: EquationKey) -> &Equation {
        self.equations.get(k).unwrap()
    }
    fn eq_mut(&mut self, k: EquationKey) -> &mut Equation {
        self.equations.get_mut(k).unwrap()
    }
    fn eq_ref(&self, key: EquationRefKey) -> &EquationRef {
        self.equation_refs.get(key).unwrap()
    }
    fn eq_ref_mut(&mut self, key: EquationRefKey) -> &mut EquationRef {
        self.equation_refs.get_mut(key).unwrap()
    }
    fn merge_eq(&mut self, ref_keys: Vec<Eql>, trees: Vec<Node>) {
        let mut hs = HashSet::<_>::new();
        let mut erased_refs = HashSet::<_>::new();
        for eql in ref_keys.iter() {
            erased_refs.insert(eql.eq_ref);
            let eq_ref = self.equation_refs.remove(eql.eq_ref).unwrap();
            hs.insert(eq_ref.key);
        }

        let mut eqs = vec![];
        for eq_key in hs.iter() {
            let eq = self.equations.remove(*eq_key).unwrap();
            eqs.push(eq);
        }

        let mut eq_refs = vec![];
        let mut eq_trees = trees;
        for mut eq in eqs {
            for r_k in eq.refs {
                if !erased_refs.contains(&r_k) {
                    eq_refs.push(r_k);
                }
            }
            eq_trees.append(&mut eq.trees);
        }

        let eq_key = self.equations.insert(
            Equation{ refs: vec![], trees: eq_trees}
        );

        for (i,eq_ref) in eq_refs.iter().enumerate() {
            *(self.eq_ref_mut(*eq_ref)) = EquationRef {
                key: eq_key,
                i
            };
        }

        self.eq_mut(eq_key).refs = eq_refs;

        if self.eq(eq_key).refs.len() == 0 {
            let eq = self.equations.remove(eq_key).unwrap();
            self.redexes.push(eq.trees);
        }
        self.assert_valid();
    }
}
