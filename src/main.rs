use std::collections::HashMap;
type Id = usize;

//enum StructualTerm { // ephterm? ephemeral? hard to hash cons stuff
//   Intern(Id),
//    App(f : String, args: Vec<EphTerm>),
//   Lam(body : Box<EphTerm>),
//   Var(id : usize),
// }

// struct Structural {f : Stiring, args : Vec<Id>} // Or really on Id?

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct App {
    f: String,
    args: Vec<Id>,
}

type Pos = Vec<(Id, usize)>; // 

#[derive(Debug, Clone, Copy)]
struct Eq {
    lhs: Id,
    rhs: Id,
}

#[derive(Debug, Clone, Copy)]
struct Rule {
    lhs: Id,
    rhs: Id,
}

struct TermBank {
    terms: Vec<App>, // HashMap<Id, Term>
    memo: HashMap<App, Id>,
    // size : Vec<usize>
}

impl TermBank {
    fn new() -> Self {
        TermBank {
            terms: vec![],
            memo: HashMap::new(),
        }
    }

    fn stringify(&self, e: Id) -> String {
        let t = &self.terms[e];
        let mut s = t.f.clone();
        if t.args.len() == 0 { return s }

        s.push_str("(");
        for (i, a) in t.args.iter().enumerate() {
            s.push_str(&self.stringify(*a));
            if i != t.args.len() - 1 {
                s.push_str(", ");
            }
        }
        s.push_str(")");

        s
    }

    fn stringify_eq(&self, eq: Eq) -> String {
        format!("{} = {}", self.stringify(eq.lhs), self.stringify(eq.rhs))
    }

    fn stringify_rule(&self, r: Rule) -> String {
        format!("{} -> {}", self.stringify(r.lhs), self.stringify(r.rhs))
    }

    fn app(&mut self, f: String, args: Vec<Id>) -> Id {
        let term = App { f, args };
        if let Some(&id) = self.memo.get(&term) {
            return id;
        }
        let id = self.terms.len();
        self.terms.push(term.clone());
        self.memo.insert(term, id);

        id
    }

    // Overlaps for simple ground terms are just the subterm relationship
    fn is_subterm(&self, big: Id, small: Id) -> bool {
        if big == small {
            return true;
        }
        for arg_id in &self.terms[big].args {
            if self.is_subterm(*arg_id, small) {
                return true;
            }
        }
        false
    }
    fn size(&self, t: Id) -> usize {
        let mut total = 1; // count the term itself
        for arg_id in &self.terms[t].args {
            total += self.size(*arg_id);
        }
        total
    }

    fn kbo(&self, e1: Id, e2: Id) -> std::cmp::Ordering {
        if self.size(e1) != self.size(e2) {
            // order by size
            return self.size(e1).cmp(&self.size(e2));
        } else {
            let t1 = &self.terms[e1];
            let t2 = &self.terms[e2];
            if t1.f != t2.f {
                // if sizes are equal, order by head symbol
                return t1.f.cmp(&t2.f);
            } else {
                // finally, compare arguments lexicographically
                for (arg1_id, arg2_id) in t1.args.iter().zip(t2.args.iter()) {
                    let ord = self.kbo(*arg1_id, *arg2_id);
                    if ord != std::cmp::Ordering::Equal {
                        return ord;
                    }
                }
                std::cmp::Ordering::Equal
            }
        }
    }

    fn substitute(&mut self, t: Id, rule: Rule) -> Id {
        if t == rule.lhs {
            return rule.rhs;
        } else {
            let term = self.terms[t].clone();
            let mut new_args = term
                .args
                .into_iter()
                .map(|arg_id| self.substitute(arg_id, rule.clone()))
                .collect::<Vec<Id>>();
            let new_id = self.app(term.f, new_args);
            return new_id;
        }
    }

    fn orient(&self, eq: Eq) -> Rule {
        match self.kbo(eq.lhs, eq.rhs) {
            std::cmp::Ordering::Greater => Rule {
                lhs: eq.lhs,
                rhs: eq.rhs,
            },
            std::cmp::Ordering::Less => Rule {
                lhs: eq.rhs,
                rhs: eq.lhs,
            },
            std::cmp::Ordering::Equal => panic!("Cannot orient equal terms"),
        }
    }

    fn all_subst(&mut self, t: Id, r: &Rule) -> Vec<Id> {
        if t == r.lhs {
            return vec![r.rhs];
        } else {
            let term = self.terms[t].clone();
            let mut results = vec![];
            for (m, arg_id) in term.args.iter().enumerate() {
                let sub_results = self.all_subst(*arg_id, r);
                for sub_id in sub_results {
                    let mut new_args = term.args.clone();
                    new_args[m] = sub_id;
                    let new_id = self.app(term.f.clone(), new_args);
                    results.push(new_id);
                }
            }
            return results;
        }
    }

    fn deduce(&mut self, r1: &Rule, r2: &Rule) -> Vec<Eq> {
        let (r1, r2) = if self.size(r1.lhs) < self.size(r2.lhs) {
            (r2, r1)
        } else {
            (r1, r2)
        };
        self.all_subst(r1.lhs, r2)
            .into_iter()
            .map(|new_lhs| Eq {
                lhs: new_lhs,
                rhs: r1.rhs,
            })
            .collect()
    }

    /*
    fn deduce(&self, r1: &Rule, r2: &Rule) -> Vec<Eq> {
        // deduce is the juice of congruence closure
        // It _is_ in some sense doing rebuild
        // Assume r1.lhs.size() >= r2.lhs.size()
        let mut pos = vec![];
        let mut res = vec![];
        let cur = r1.lhs;
        loop {


        }
    } */
}

#[cfg(test)]
mod kb_tests {
    use super::*;

    #[test]
    fn deduce_test() {

        //!(neweqs, vec![Eq {}])
    }
}

fn main() {
    let mut tb = TermBank::new();
    let a = tb.app("a".into(), vec![]);
    let b = tb.app("b".into(), vec![]);
    let c = tb.app("c".into(), vec![]);

    let f_a = tb.app("f".to_string(), vec![a]);
    let f_aa = tb.app("f".to_string(), vec![a, a]);
    let f_b = tb.app("f".to_string(), vec![b]);
    let g_a = tb.app("g".to_string(), vec![a]);
    let g_b = tb.app("g".to_string(), vec![b]);

    let neweqs = tb.deduce(&Rule { lhs: f_aa, rhs: b }, &Rule { lhs: a, rhs: c });
    for a in neweqs {
        println!("{}", tb.stringify_eq(a));
    }
}
