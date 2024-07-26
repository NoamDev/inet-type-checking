use std::collections::HashSet;
use std::fmt::Display;
use std::iter::zip;
use std::{result, vec};

use slotmap::{new_key_type, SlotMap};

use crate::util::alphabetize;
use itertools::Itertools;

pub struct Var {
    edge_ref: EdgeRefKey,
}

new_key_type! { struct EdgeRefKey; }
pub struct EdgeRef {
    i: usize,
    edge: EdgeKey,
}

new_key_type! { struct EdgeKey; }
struct Edge {
    type_key: PartialTypeKey,
    refs: Vec<EdgeRefKey>,
    nodes: Vec<Node>,
}

#[derive(Debug)]
pub enum Type {
    Arrow {a: Box<Type>, b: Box<Type>},
    Cloneable {a: Box<Type>},
    Uncloneable {a: Box<Type>},
    Unsafe {a: Box<Type>},
    Var(usize)
}

new_key_type! { pub struct PartialTypeKey; }
#[derive(Debug)]
pub enum PartialType {
    Arrow {a: PartialTypeKey, b: PartialTypeKey},
    Cloneable {a: PartialTypeKey},
    Uncloneable {a: PartialTypeKey},
    Unsafe {a: PartialTypeKey},
    Var(PartialTypeKey),
    Free(Option<usize>)
}

impl Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let str = match self {
            Type::Arrow{a, b,..} => {
                format!("({}->{})", a.to_string(), b.to_string())
            }
            Type::Var(i) => { alphabetize(*i) }
            Type::Cloneable { a } => {
                format!("!{}", a.to_string())
            }
            Type::Uncloneable { a } => {
                format!("?{}", a.to_string())
            }
            Type::Unsafe {a} => {
                format!("#{}", a.to_string())
            }
        };
        write!(f, "{}", str)
    }
}

impl Type {
    pub(crate) fn arg(self) -> Option<Type> {
        match self {
            Type::Arrow { a, b } => Some(*a),
            Type::Cloneable { a } => a.arg(),
            Type::Uncloneable { a } => a.arg(),
            Type::Unsafe { a } => a.arg(),
            Type::Var(_) => None
        }
    }
}

pub struct Lam {
    pub a: Var,
    pub b: Var,
}
pub struct App {
    pub a: Var,
    pub b: Var,
}
pub struct AffAnn(pub Var);
pub struct AffChk(pub Var);
pub struct NAffAnn(pub Var);
pub struct NAffChk(pub Var);

pub enum Node {
    Lam(Lam),
    App(App),
    AffAnn (AffAnn),
    AffChk (AffChk),
    NAffAnn (NAffAnn),
    NAffChk (NAffChk),
}

#[derive(Default)]
pub struct Net {
    refs: SlotMap<EdgeRefKey, EdgeRef>,
    edges: SlotMap<EdgeKey, Edge>,
    redexes: Vec<(PartialTypeKey, Vec<Node>)>,
    types: SlotMap<PartialTypeKey, PartialType>,
    next_label: usize,
}

impl Net {
    pub fn is_reducible(&self) -> bool {
        return self.redexes.len() > 0;
    }
    pub fn is_equated(&self) -> bool {
        self.edges.len() == 0
    }
    pub fn reduce(&mut self) {
        let r = self.redexes.pop();
        if let Some((redex_type_key, nodes)) = r {
            let mut has_aff_ann = false;
            let mut has_aff_chk = false;
            let mut has_naff_ann = false;
            let mut has_naff_chk = false;
            for node in nodes.iter() {
                match node {
                    Node::Lam(_) => {}
                    Node::App(_) => {}
                    Node::AffAnn(_) => {
                        has_aff_ann = true;
                    }
                    Node::AffChk(_) => {
                        has_aff_chk = true;
                    }
                    Node::NAffAnn(_) => {
                        has_naff_ann = true;
                    }
                    Node::NAffChk(_) => {
                        has_naff_chk = true;
                    }
                }
            }

            if (has_aff_ann || has_aff_chk) && (has_naff_ann || has_naff_chk) {
                self.reduce_unsafe(redex_type_key, nodes);
            } else if has_aff_ann || has_aff_chk || has_naff_ann || has_naff_chk {
                self.reduce_decoration(
                    redex_type_key,
                    nodes,
                    has_aff_ann || has_aff_chk,
                    has_aff_ann || has_naff_ann,
                    has_aff_chk || has_naff_chk,
                );
            } else {
                self.reduce_cons(redex_type_key, nodes);
            }
        }
    }

    fn reduce_unsafe(&mut self, redex_type_key: PartialTypeKey, nodes: Vec<Node>) {
        let mut result_nodes = vec![];
        let mut result_vars = vec![];

        for node in nodes {
            match node {
                Node::Lam(lam) => result_nodes.push(Node::Lam(lam)),
                Node::App(app) => result_nodes.push(Node::App(app)),
                Node::AffAnn(AffAnn(var)) => result_vars.push(var),
                Node::AffChk(AffChk(var)) => result_vars.push(var),
                Node::NAffAnn(NAffAnn(var)) => result_vars.push(var),
                Node::NAffChk(NAffChk(var)) => result_vars.push(var),
            }
        }

        let type_key = self.link(result_nodes, result_vars);
        self.set_type(redex_type_key, PartialType::Unsafe {a: type_key});
    }

    fn reduce_decoration(&mut self, redex_type_key: PartialTypeKey, nodes: Vec<Node>, affine: bool, ann: bool, chk: bool) {
        let mut result_nodes = vec![];
        let mut result_vars = vec![];

        for node in nodes {
            match node {
                Node::Lam(lam) => {
                    let node = if chk {
                        if affine {
                            let (a1, a2) = self.wire();
                            self.link_var_node(lam.a, Node::NAffAnn(NAffAnn(a1)));
                            let (b1, b2) = self.wire();
                            self.link_var_node(lam.b, Node::AffChk(AffChk(b1)));
                            Node::Lam(Lam {
                                a: a2,
                                b: b2,
                            })
                        } else {
                            let (a1, a2) = self.wire();
                            self.link_var_node(lam.a, Node::AffAnn(AffAnn(a1)));
                            let (b1, b2) = self.wire();
                            self.link_var_node(lam.b, Node::NAffChk(NAffChk(b1)));
                            Node::Lam(Lam {
                                a: a2,
                                b: b2,
                            })
                        }
                    } else {
                        Node::Lam(lam)
                    };
                    result_nodes.push(node);
                },
                Node::App(app) => {
                    let node = if ann {
                        if affine {
                            let (a1, a2) = self.wire();
                            self.link_var_node(app.a, Node::NAffChk(NAffChk(a1)));
                            let (b1, b2) = self.wire();
                            self.link_var_node(app.b, Node::AffAnn(AffAnn(b1)));
                            Node::App(App {
                                a: a2,
                                b: b2,
                            })
                        } else {
                            let (a1, a2) = self.wire();
                            self.link_var_node(app.a, Node::AffChk(AffChk(a1)));
                            let (b1, b2) = self.wire();
                            self.link_var_node(app.b, Node::NAffAnn(NAffAnn(b1)));
                            Node::App(App {
                                a: a2,
                                b: b2,
                            })
                        }
                    } else {
                        Node::App(app)
                    };
                    result_nodes.push(node);

                },
                Node::AffAnn(AffAnn(var)) => result_vars.push(var),
                Node::AffChk(AffChk(var)) => result_vars.push(var),
                Node::NAffAnn(NAffAnn(var)) => result_vars.push(var),
                Node::NAffChk(NAffChk(var)) => result_vars.push(var),
            }
        }

        let type_key = self.link(result_nodes, result_vars);
        if affine {
            self.set_type(redex_type_key, PartialType::Cloneable { a: type_key });
        } else {
            self.set_type(redex_type_key, PartialType::Uncloneable { a: type_key });
        }
    }

    fn reduce_cons(&mut self, redex_type_key: PartialTypeKey, nodes: Vec<Node>) {
        let mut link_a_vars = vec![];
        let mut link_b_vars = vec![];

        for node in nodes {
            match node {
                Node::Lam(lam) => {
                    link_a_vars.push(lam.a);
                    link_b_vars.push(lam.b);
                }
                Node::App(app) => {
                    link_a_vars.push(app.a);
                    link_b_vars.push(app.b);
                }
                _ => unreachable!()
            }
        }

        let type_a = self.link(vec![], link_a_vars);
        let type_b = self.link(vec![], link_b_vars);

        self.set_type(redex_type_key, PartialType::Arrow {a: type_a, b: type_b});
    }
/*

    pub fn unsafe_reduce(&mut self) {
        let  r = self.redexes.pop();
        if let Some((redex_type_key, nodes)) = r {
            let mut a_eqls = vec![];
            let mut b_eqls = vec![];
            let mut dups = vec![];
            let mut puds = vec![];
            assert!(nodes.len() > 0);

            for t in nodes {
                match t {
                    Node::Con { a, b } => {
                        a_eqls.push(a);
                        b_eqls.push(b);
                    },
                    Node::Dup {a} => {
                        dups.push(a);
                    }
                    Node::Pud {a} => {
                        puds.push(a);
                    }
                }
            }

            if dups.len() > 0 && puds.len() > 0 {
                self.reduce_unsafe(redex_type_key, a_eqls, b_eqls, dups, puds);
            } else if dups.len() > 0 {
                self.reduce_unsafe(redex_type_key, a_eqls, b_eqls, dups, puds);
            } else if puds.len() > 0 {
                self.reduce_unsafe(redex_type_key, a_eqls, b_eqls, dups, puds);
            } else {
                self.reduce_cons(redex_type_key, a_eqls, b_eqls);
            }
        }
        self.assert_valid();
    }

    fn reduce_unsafe(&mut self, redex_type_key: PartialTypeKey, a_eqls: Vec<Eql>, b_eqls: Vec<Eql>, dups: Vec<Eql>, puds: Vec<Eql>) {
        let new_type = self.new_type();
        self.set_type(redex_type_key, PartialType::Unsafe {a: new_type});
        let cons: Vec<_> = zip(a_eqls, b_eqls).map(|(a, b)| Node::Con {a, b}).collect();
        let eqls: Vec<_> = dups.into_iter().chain(puds).collect();
        self.merge_eq(new_type, eqls, cons);
    }

    fn reduce_pud(&mut self, redex_type_key: PartialTypeKey, a_eqls: Vec<Eql>, b_eqls: Vec<Eql>, puds: Vec<Eql>) {
        let type_a = self.new_type();
        let type_b = self.new_type();
        self.set_type(redex_type_key, PartialType::Arrow { a: type_a, b: type_b });

        let mut a_nodes = vec![];
        let mut b_nodes = vec![];

        for e in puds {
            let (dup1, dup2) = self.wire();
            let (pud1, pud2) = self.wire();
            let dup = Node::Dup { a: dup1 };
            let pud = Node::Pud { a: pud1 };
            let con = Node::Con {
                a: dup2,
                b: pud2
            };
            self.link(vec![Tree::Node(con), Tree::Eql(e)]);
            a_nodes.push(dup);
            b_nodes.push(pud);
        }

        self.merge_eq(type_a, a_eqls, a_nodes);
        self.merge_eq(type_b, b_eqls, b_nodes);
    }
    fn reduce_dup(&mut self, redex_type_key: PartialTypeKey, a_eqls: Vec<Eql>, b_eqls: Vec<Eql>, dups: Vec<Eql>) {
        let type_a = self.new_type();
        let type_b = self.new_type();
        self.set_type(redex_type_key, PartialType::Arrow { a: type_a, b: type_b });

        let mut a_nodes = vec![];
        let mut b_nodes = vec![];

        for e in dups {
            let (dup1, dup2) = self.wire();
            let (pud1, pud2) = self.wire();
            let dup = Node::Dup { a: dup1 };
            let pud = Node::Pud { a: pud1 };
            let con = Node::Con {
                a: pud2,
                b: dup2
            };
            self.link(vec![Tree::Node(con), Tree::Eql(e)]);
            a_nodes.push(pud);
            b_nodes.push(dup);
        }

        self.merge_eq(type_a, a_eqls, a_nodes);
        self.merge_eq(type_b, b_eqls, b_nodes);
    }

    fn reduce_cons(&mut self, redex_type_key: PartialTypeKey, a_eqls: Vec<Eql>, b_eqls: Vec<Eql>) {
        let type_a = self.new_type();
        let type_b = self.new_type();
        self.set_type(redex_type_key, PartialType::Arrow {
            a: type_a,
            b: type_b,
        });

        if a_eqls.len() > 0 {
            self.merge_eq(type_a, a_eqls, vec![]);
        }

        if b_eqls.len() > 0 {
            self.merge_eq(type_b, b_eqls, vec![]);
        }
    }
*/
    pub fn read_type(&self, type_key: PartialTypeKey) -> Type {
        let t = self.get_type(type_key);
        match t {
            PartialType::Arrow {a, b } => Type::Arrow {
                a: Box::new(self.read_type(a.clone())),
                b: Box::new(self.read_type(b.clone())),
            },
            PartialType::Var(key) => self.read_type(key.clone()),
            PartialType::Free(free_var) => Type::Var(free_var.unwrap()),
            PartialType::Cloneable { a } => Type::Cloneable {
                a: Box::new(self.read_type(a.clone()))
            },
            PartialType::Uncloneable { a } => Type::Uncloneable {
                a: Box::new(self.read_type(a.clone()))
            },
            PartialType::Unsafe { a } => Type::Unsafe {
                a: Box::new(self.read_type(a.clone()))
            }
        }
    }

    pub fn read(&mut self) {
        println!("redexes:");
        for (type_key, nodes) in self.redexes.iter() {
            println!("{}", self.read_eq(*type_key, nodes, &vec![]));
        }
        println!("equations:");
        for (k, e) in self.edges.iter() {
            println!("{}", self.read_eq(e.type_key, &e.nodes, &e.refs));
        }
    }
    fn read_eq(&self, type_key: PartialTypeKey, trees: &Vec<Node>, refs: &Vec<EdgeRefKey>) -> String {
        let eq = trees.iter().map(|node| match node {
            Node::Lam(lam) => {
                let a_type = self.read_type(self.type_key(&lam.a));
                let b_type = self.read_type(self.type_key(&lam.b));
                format!("λ{a_type}.{b_type}")
            }
            Node::App(app) => {
                let a_type = self.read_type(self.type_key(&app.a));
                let b_type = self.read_type(self.type_key(&app.b));
                format!("({a_type} {b_type})")
            }
            Node::AffAnn(AffAnn(v)) => {
                let v_type = self.read_type(self.type_key(v));
                format!("!{v_type}")
            }
            Node::AffChk(AffChk(v)) => {
                let v_type = self.read_type(self.type_key(v));
                format!("!{v_type}")
            }
            Node::NAffAnn(NAffAnn(v)) => {
                let v_type = self.read_type(self.type_key(v));
                format!("?{v_type}")
            }
            Node::NAffChk(NAffChk(v)) => {
                let v_type = self.read_type(self.type_key(v));
                format!("?{v_type}")
            }
        }).join(" = ");
        let num_refs = refs.len();
        let eq_type = self.read_type(type_key);
        format!("{eq_type} := {eq}, {num_refs} refs")
    }

    pub fn link(&mut self, nodes: Vec<Node>, vars: Vec<Var>) -> PartialTypeKey {
        let mut edge_keys = HashSet::new();
        for var in vars {
            let edge_ref = self.refs.remove(var.edge_ref).unwrap();
            let edge = self.edges.get_mut(edge_ref.edge).unwrap();
            edge.refs.remove(edge_ref.i);
            edge_keys.insert(edge_ref.edge);
        }

        let mut link_nodes = nodes;
        let mut link_refs = vec![];

        let new_type = self.new_type();
        for edge_key in edge_keys {
            let mut edge = self.edges.remove(edge_key).unwrap();
            link_nodes.append(&mut edge.nodes);
            link_refs.append(&mut edge.refs);
            self.set_type(edge.type_key, PartialType::Var(new_type));
        }

        if link_refs.len() == 0 {
            if link_nodes.len() > 0 {
                self.redexes.push((new_type, link_nodes));
            }
        } else {
            let edge = self.edges.insert(Edge {
                type_key: new_type,
                refs: vec![],
                nodes: link_nodes,
            });
            for (i, edge_ref_key) in link_refs.iter().enumerate() {
                let edge_ref = self.refs.get_mut(*edge_ref_key).unwrap();
                edge_ref.i = i;
                edge_ref.edge = edge;
            }
            self.edges.get_mut(edge).unwrap().refs = link_refs;
        }
        new_type
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
    pub fn new_label(&mut self) -> usize {
        let res = self.next_label;
        self.next_label += 1;
        res
    }

    // pub fn assert_valid(&self) {
    //     for (type_key, redex) in self.redexes.iter() {
    //         assert!(self.types.contains_key(*type_key));
    //         for node in redex.iter() {
    //             self.assert_valid_node(node);
    //         }
    //     }
    //
    //     for (var_key, var_rc) in self.vars.iter() {
    //         assert!(var_rc.refs > 0);
    //         self.assert_valid_var(&Var { key: var_key });
    //     }
    // }
    // pub fn assert_valid_node(&self, node: &Node) {
    //     match node {
    //         Node::Lam(lam) => {
    //             self.assert_valid_var(&lam.a);
    //             self.assert_valid_var(&lam.b);
    //         }
    //
    //         Node::App(_) => {}
    //         Node::AffAnn(_) => {}
    //         Node::AffChk(_) => {}
    //         Node::NAffAnn(_) => {}
    //         Node::NAffChk(_) => {}
    //     }
    // }

    // pub fn assert_valid_var(&self, var: &Var) {
    //     assert!(self.vars.contains_key(var.key));
    //     let var_rc = self.vars.get(var.key).unwrap();
    //     assert!(var_rc.refs > 0);
    //     match &var_rc.value {
    //         VarValue::Ref { key } => {self.assert_valid_var(&Var { key: *key })}
    //         VarValue::Nodes { nodes, type_key } => {
    //             assert!(self.types.contains_key(*type_key));
    //             for node in nodes {
    //                 self.assert_valid_node(node);
    //             }
    //         }
    //     }
    // }

    /*
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
 */

    pub fn type_key(&self, var: &Var) -> PartialTypeKey{
        let edge_ref = self.refs.get(var.edge_ref).unwrap();
        self.edges.get(edge_ref.edge).unwrap().type_key
    }

    pub fn new_var(&mut self) -> Var {
        let new_type = self.new_type();
        let edge_ref = self.refs.insert(EdgeRef {
            i: 0,
            edge: EdgeKey::default(),
        });
        let edge = self.edges.insert(Edge {
            type_key: new_type,
            nodes: vec![],
            refs: vec![edge_ref]
        });
        self.refs.get_mut(edge_ref).unwrap().edge = edge;
        Var {
            edge_ref
        }
    }
    pub fn add_var(&mut self, var: &Var) -> Var {
        let edge_ref = self.refs.get(var.edge_ref).unwrap();
        let edge_key = edge_ref.edge;
        let new_edge_ref = self.refs.insert(EdgeRef {
            i: 0,
            edge: edge_key,
        });
        let edge = self.edges.get_mut(edge_key).unwrap();
        edge.refs.push(new_edge_ref);
        let i = edge.refs.len() - 1;
        self.refs.get_mut(new_edge_ref).unwrap().i = i;
        Var {edge_ref: new_edge_ref}
    }

    pub fn wire(&mut self) -> (Var, Var) {
        let new_type = self.new_type();
        let edge_ref1 = self.refs.insert(EdgeRef {
            i: 0,
            edge: EdgeKey::default(),
        });
        let edge_ref2 = self.refs.insert(EdgeRef {
            i: 1,
            edge: EdgeKey::default(),
        });
        let edge = self.edges.insert(Edge {
            type_key: new_type,
            nodes: vec![],
            refs: vec![edge_ref1, edge_ref2]
        });
        self.refs.get_mut(edge_ref1).unwrap().edge = edge;
        self.refs.get_mut(edge_ref2).unwrap().edge = edge;
        (Var { edge_ref: edge_ref1 }, Var { edge_ref: edge_ref2 })
    }

    pub fn wrap(&mut self, node: Node) -> Var {
        let new_type = self.new_type();
        let edge_ref = self.refs.insert(EdgeRef {
            i: 0,
            edge: Default::default(),
        });
        let edge= self.edges.insert(Edge {
            type_key: new_type,
            refs: vec![edge_ref],
            nodes: vec![node],
        });
        self.refs.get_mut(edge_ref).unwrap().edge =  edge;
        Var {edge_ref}
    }

    pub fn var_refs_count(&mut self, var: &Var) -> usize {
        let edge_ref = self.refs.get(var.edge_ref).unwrap();
        let edge = self.edges.get(edge_ref.edge).unwrap();
        edge.refs.len()
    }

    pub fn link_var_node(&mut self, var: Var, node: Node) {
        let edge_ref = self.refs.remove(var.edge_ref).unwrap();
        let edge = self.edges.get_mut(edge_ref.edge).unwrap();
        edge.refs.remove(edge_ref.i);
        edge.nodes.push(node);
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
