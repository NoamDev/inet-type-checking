use std::collections::HashSet;
use std::fmt::Display;
use std::vec;

use slotmap::{new_key_type, SlotMap};

use crate::util::alphabetize;

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
        type_key: PartialTypeKey,
        a: Box<Tree>,
        b: Box<Tree>,
    }
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
    pub type_key: PartialTypeKey,
    pub trees: Vec<Node>,
    pub refs: Vec<EquationRefKey>,
}

#[derive(Default, Debug)]
pub struct Net {
    equations: SlotMap<EquationKey, Equation>,
    equation_refs: SlotMap<EquationRefKey, EquationRef>,
    redexes: Vec<(PartialTypeKey, Vec<Node>)>,
    types: SlotMap<PartialTypeKey, PartialType>,
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
        if let Some((redex_type_key, nodes)) = r {
            let mut a_nodes = vec![];
            let mut b_nodes = vec![];
            let mut a_eqls = vec![];
            let mut b_eqls = vec![];

            assert!(nodes.len() > 0);

            for t in nodes {
                match t {
                    Node::Con { type_key, a, b } => {
                        self.set_type(type_key, PartialType::Arrow(
                            self.type_key(&a),
                            self.type_key(&b),
                        ));
                        match *a {
                            Tree::Node(node) => a_nodes.push(node),
                            Tree::Eql(e_key) => {
                                a_eqls.push(e_key);
                            },
                        }
                        match *b {
                            Tree::Node(node) => b_nodes.push(node),
                            Tree::Eql(e_key) => {
                                b_eqls.push(e_key);
                            },
                        }
                    }
                }
            }

            let type_a = self.new_type();
            let type_b = self.new_type();
            self.set_type(redex_type_key, PartialType::Arrow(type_a, type_b));

            if a_eqls.len() > 0 {
                self.merge_eq(type_a, a_eqls, a_nodes);
            } else if a_nodes.len() > 0 {
                self.redexes.push((type_a, a_nodes));
            }

            if b_eqls.len() > 0 {
                self.merge_eq(type_b, b_eqls, b_nodes);
            } else if b_nodes.len() > 0 {
                self.redexes.push((type_b, b_nodes));
            }
        }
        self.assert_valid();
    }

    pub fn read_type(&self, type_key: PartialTypeKey) -> Type {
        let t = self.get_type(type_key);
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
        let eq_type = self.new_type();
        let eq_key = self.equations.insert(Equation { type_key: eq_type, trees: vec![], refs: vec![]});
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
                self.redexes.push((eq.type_key, eq.trees));
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
            if nodes.len() > 0 {
                let type_key = self.new_type();
                self.redexes.push((type_key, nodes));
            }
        } else {
            let type_key = self.new_type();
            self.merge_eq(type_key, refs, nodes);
        }
        self.assert_valid();
    }
    pub fn assert_valid(&self) {
        for (type_key, redex) in self.redexes.iter() {
            assert!(self.types.contains_key(*type_key));
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
            Node::Con { type_key: type_id, a, b } => {
                assert!(self.types.contains_key(*type_id));
                self.assert_valid_tree(a);
                self.assert_valid_tree(b);
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
    fn merge_eq(&mut self, eq_type: PartialTypeKey, ref_keys: Vec<Eql>, trees: Vec<Node>) {
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
            *(self.get_type_mut(eq.type_key)) = PartialType::Var(eq_type);
        }

        let eq_key = self.equations.insert(
            Equation{ type_key: eq_type, refs: vec![], trees: eq_trees}
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
            if eq.trees.len() > 0 {
                self.redexes.push((eq_type, eq.trees));
            }
        }
        self.assert_valid();
    }
    pub fn type_key(&self, tree: &Tree) -> PartialTypeKey{
        match tree {
            Tree::Node(node) => {
                match node {
                    Node::Con { type_key: type_id,.. } => {
                        *type_id
                    }
                }
            }
            Tree::Eql(eql, ..) => {
                self.eq(self.eq_ref(eql.eq_ref).key).type_key
            }
        }
    }
    pub fn new_type(&mut self) -> PartialTypeKey {
        self.types.insert(PartialType::Free(None))
    }
    fn get_type(&self, type_key: PartialTypeKey) -> &PartialType {
        self.types.get(type_key).unwrap()
    }
    fn get_type_mut(&mut self, type_key: PartialTypeKey) -> &mut PartialType {
        self.types.get_mut(type_key).unwrap()
    }
    fn set_type(&mut self, type_key: PartialTypeKey, type_to_set: PartialType){
        *(self.get_type_mut(type_key)) = type_to_set;
    }
}
