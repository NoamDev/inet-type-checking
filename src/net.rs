use std::{collections::HashSet, vec};

use slotmap::{DefaultKey as SlotKey, SlotMap};

#[derive(Debug)]
pub enum PartialType {
    Arrow(SlotKey, SlotKey),
    Var(SlotKey),
}

#[derive(Debug)]
pub enum Type {
    Arrow(Box<Type>, Box<Type>),
    Var(usize)
}

pub enum Node {
    Con {
        a: Box<Tree>,
        b: Box<Tree>,
    },
    Free {
        type_id: SlotKey,
    },
}

pub enum Tree {
    Node(Node),
    Eql(SlotKey),
}

pub struct Equation {
    pub missing: usize,
    pub trees: Vec<Node>,
    pub next: SlotKey,
    pub prev: SlotKey,
}

pub struct Net {
    pub equations: SlotMap<SlotKey, Equation>,
    pub redexes: Vec<Vec<Node>>,
    pub types: SlotMap<SlotKey, Option<PartialType>>,
}

impl Net {
    pub fn is_reducible(&self) -> bool {
        return self.redexes.len() > 0;
    }
    pub fn reduce(&mut self) {
        let  r = self.redexes.pop();
        if let Some(r) = r {
            let mut eq1_trees = vec![];
            let mut eq2_trees = vec![];
            let mut eq1_eqs = vec![];
            let mut eq2_eqs = vec![];
            
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
                        let a = self.types.insert(Option::None);
                        let b = self.types.insert(Option::None);
                        
                        eq1_trees.push(Node::Free { type_id: a });
                        eq2_trees.push(Node::Free { type_id: b });
                        *(self.types.get_mut(type_id).unwrap()) = Some(PartialType::Arrow(a, b));
                    },
                }
            }
            if eq1_eqs.len() > 0 {
                let eq1_key = self.equations.insert_with_key(|key| {
                    Equation {missing: eq1_eqs.len().len(), trees: eq1_trees, prev: key, next: key}
                });
                for e_key in eq1_eqs {
                    self.merge(eq1_key, e_key);
                }
            } else {
                self.redexes.push(eq1_trees);
            }
            if eq2_eqs.len() > 0 {
                let eq2_key = self.equations.insert_with_key(|key| {
                    Equation {missing:  eq2_eqs.len(), trees: eq2_trees, prev: key, next: key}
                });
                for e_key in eq2_eqs {
                    self.merge(eq2_key, e_key);
                }
            } else {
                self.redexes.push(eq2_trees);
            }
        }
    }

    fn link(&mut self, fst_key: SlotKey, snd_key: SlotKey) -> (SlotKey, SlotKey) {
        let fst = self.equations.get_mut(fst_key).unwrap();
        let fst_next = std::mem::replace(&mut fst.next, snd_key);
        let snd = self.equations.get_mut(snd_key).unwrap();
        let snd_prev = std::mem::replace(&mut snd.prev, fst_key);
        return (fst_next, snd_prev);
    }
    fn remove(&mut self, k: SlotKey) -> Vec<Node> {
        let eq = self.equations.remove(k).unwrap();
        self.equations.get_mut(eq.prev).unwrap().next = eq.next;
        self.equations.get_mut(eq.next).unwrap().next = eq.prev;
        return eq.trees;
    }
    fn merge(&mut self, a_key: SlotKey, b_key: SlotKey) {
        let a_missing = self.equations.get(a_key).unwrap().missing;
        let b_missing = self.equations.get(b_key).unwrap().missing;
        if a_missing == 1 && b_missing == 1 {
            
        } else if a_missing == 1 {
            let mut a_trees = self.remove(a_key);
            let b = self.equations.get_mut(b_key).unwrap();
            b.trees.append(&mut a_trees);
            b.missing -= 1;
        } else if b_missing == 1 {
            let mut b_trees = self.remove(b_key);
            let a = self.equations.get_mut(a_key).unwrap();
            a.trees.append(&mut b_trees);
            a.missing -= 1;
        } else {
            let (a_next, b_prev) = self.link(a_key, b_key);
            let (expected_b, expected_a) = self.link(b_prev, a_next);
            assert_eq!(a_key, expected_a);
            assert_eq!(b_key, expected_b);
            self.equations.get_mut(a_key).unwrap().missing -= 1;
            self.equations.get_mut(b_key).unwrap().missing -= 1;
        }
    }

    fn squash(&mut self, eq_key: SlotKey) {
        let mut eq = self.equations.get(eq_key).unwrap();
        let remove_eqs =  
        while eq.next != eq_key {
            if eq.missing == 0 {

            }
            eq = self.equations.get(eq_key).unwrap();
        }
    }

    pub fn read_type(&self, type_key: SlotKey, free_var: usize) -> Type {
        let t = self.types.get(type_key).unwrap();
        match t {
            Some(ty) => {
                match ty {
                    PartialType::Arrow(a, b) => Type::Arrow(Box::new(self.read_type(a.clone(), free_var*2)), Box::new(self.read_type(b.clone(), free_var*2+1))),
                    PartialType::Var(key) => self.read_type(key.clone(), free_var),
                }
            },
            None => Type::Var(free_var),
        }
    }
}
