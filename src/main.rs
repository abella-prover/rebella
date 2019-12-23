use internship::IStr;
use std::collections::HashMap;
use std::fmt;
use std::rc::Rc;

#[derive(Debug, Clone)]
struct Term(pub Rc<Term_>);

impl Term {
  pub fn var(v: IStr) -> Term {
    Term(Rc::new(Var(v)))
  }
  pub fn var_(v: &'static str) -> Term {
    Term(Rc::new(Var(IStr::new(v))))
  }
  pub fn apply(f: IStr, ts: Vec<Term>) -> Term {
    Term(Rc::new(Apply(f, ts)))
  }
  pub fn apply_(f: &'static str, ts: Vec<Term>) -> Term {
    Term(Rc::new(Apply(IStr::new(f), ts)))
  }
}

#[derive(Debug, Clone)]
enum Term_ {
  Var(IStr),
  Apply(IStr, Vec<Term>),
}
use Term_::*;

impl fmt::Display for Term {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match self.0.as_ref() {
      Var(ref x) => write!(f, "{}", x),
      Apply(k, ts) => {
        if ts.len() == 0 {
          write!(f, "{}", k)
        } else {
          let mut it = ts.iter();
          write!(f, "{}(", k)?;
          if let Some(s) = it.next() {
            write!(f, "{}", s)?;
            for s in it {
              write!(f, ", ")?;
              write!(f, "{}", s)?;
            }
          }
          write!(f, ")")
        }
      }
    }
  }
}

fn occurs_check(x: &IStr, t: &Term) -> bool {
  match t.0.as_ref() {
    Var(ref y) => x.eq(y),
    Apply(_, ref ts) => {
      for t in ts {
        if occurs_check(x, t) {
          return true;
        }
      }
      return false;
    }
  }
}

#[derive(Debug, Clone)]
struct Subs(HashMap<IStr, Term>);

fn apply(sub: &Subs, s: Term) -> Term {
  match s.0.as_ref() {
    Var(ref x) => {
      let t = sub.0.get(x);
      t.unwrap_or(&s).clone()
    }
    Apply(ref f, ref ts) => {
      let uts: Vec<Term> = ts.iter().map(|t| apply(sub, t.clone())).collect();
      Term::apply(f.clone(), uts)
    }
  }
}

fn unify(s: Term, t: Term) -> Result<Subs, String> {
  let mut subs = Subs(HashMap::new());

  let mut worklist: Vec<(Term, Term)> = vec![(s, t)];
  while !worklist.is_empty() {
    let (s, t) = worklist.pop().unwrap();
    let s = apply(&subs, s);
    let t = apply(&subs, t);
    // println!("{} ?= {}", &s, &t);
    match (s.0.as_ref(), t.0.as_ref()) {
      (Var(ref x), Var(ref y)) => {
        if !x.eq(y) {
          subs.0.insert(x.clone(), t);
        }
      }
      (Var(ref x), _) => {
        if occurs_check(x, &t) {
          return Err(format!("{} occurs in {}", &x, &t));
        }
        subs.0.insert(x.clone(), t);
      }
      (_, Var(ref x)) => {
        if occurs_check(x, &s) {
          return Err(format!("{} occurs in {}", &x, &s));
        }
        subs.0.insert(x.clone(), s);
      }
      (Apply(f, f_args), Apply(g, g_args)) => {
        if !(f == g && f_args.len() == g_args.len()) {
          return Err(String::from("structure"));
        }
        for (s, t) in f_args.iter().zip(g_args) {
          worklist.push((s.clone(), t.clone()));
        }
      }
    }
  }

  Ok(subs)
}

fn main() {
  let e1 = Term::apply_(
    "f",
    vec![
      Term::var_("X"),
      Term::apply_("g", vec![Term::apply_("k", vec![]), Term::var_("Y")]),
    ],
  );
  println!("e1 = {}", e1);
  let e2 = Term::apply_("f", vec![Term::apply_("j", vec![]), Term::var_("Z")]);
  println!("e2 = {}", e2);
  let u = unify(e1, e2);
  println!("{:?}", u);
  let e1 = Term::var_("X");
  let e2 = Term::apply_("f", vec![Term::var_("X")]);
  println!("{:?}", unify(e1, e2));
}

#[cfg(test)]
mod tests {
  use crate::unify;
  use crate::Term;
  #[test]
  fn term_display() {
    assert_eq!(format!("{}", Term::apply_("k", vec![])), "k");
    assert_eq!(format!("{}", Term::var_("X")), "X");
    assert_eq!(
      format!("{}", Term::apply_("f", vec![Term::var_("X")])),
      "f(X)"
    );
    assert_eq!(
      format!(
        "{}",
        Term::apply_("f", vec![Term::var_("X"), Term::var_("Y")])
      ),
      "f(X, Y)"
    );
  }

  #[test]
  fn unify_test() {
    let e1 = Term::apply_(
      "f",
      vec![
        Term::var_("X"),
        Term::apply_("g", vec![Term::apply_("k", vec![]), Term::var_("Y")]),
      ],
    );
    // println!("e1 = {}", e1);
    let e2 = Term::apply_("f", vec![Term::apply_("j", vec![]), Term::var_("Z")]);
    // println!("e2 = {}", e2);
    let u = unify(e1, e2);
    // println!("{:?}", u);
    assert!(u.is_ok());
  }

  #[test]
  fn nonunify_test() {
    let e1 = Term::var_("X");
    let e2 = Term::apply_("f", vec![Term::var_("X")]);
    assert!(unify(e1, e2).is_err());
  }
}
