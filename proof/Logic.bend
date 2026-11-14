import Base

# The logic the proofs share: absurdity, clashes of constructors, and the
# cases of a Bool computed from other values. Nothing here is about FRP.

law ex_falso:
  for -G: Type
  for e: Empty
  G

def ex_falso(G, e):
  match e:

# False is not True
# -----------------

def disc(b: Bool) -> Type:
  match b:
    case True{}:
      Empty
    case False{}:
      Unit

law clash.empty:
  for h: {False{} == True{} : Bool}
  Empty

def clash.empty(h):
  %h : disc(_)
  Unit{}

law clash:
  for -G: Type
  for h: {False{} == True{} : Bool}
  G

def clash(G, h):
  ex_falso(G, clash.empty(h))

law clash.flip.empty:
  for h: {True{} == False{} : Bool}
  Empty

def clash.flip.empty(h):
  %h : disc(Bool.not(_))
  Unit{}

law clash.flip:
  for -G: Type
  for h: {True{} == False{} : Bool}
  G

def clash.flip(G, h):
  ex_falso(G, clash.flip.empty(h))

# Two values of one Bool that disagree.
law both:
  for -G: Type
  for -b: Bool
  for t: {b == True{} : Bool}
  for f: {b == False{} : Bool}
  G

def both(G, b, t, f):
  clash.flip(G, Equal.trans(Bool, True{}, b, False{}, Equal.sym(Bool, b, True{}, t), f))

# The cases of a Bool
# -------------------

law bool.cases:
  for b: Bool
  for -G: Type
  for kt: {b == True{} : Bool} -> G
  for kf: {b == False{} : Bool} -> G
  G

def bool.cases(b, G, kt, kf):
  match b:
    case True{}:
      kt({==})
    case False{}:
      kf({==})

law and.both:
  for b: Bool
  for -c: Bool
  for -G: Type
  for h: {(b && c) == True{} : Bool}
  for k: {b == True{} : Bool} -> {c == True{} : Bool} -> G
  G

def and.both(b, c, G, h, k):
  match b:
    case True{}:
      k({==}, h)
    case False{}:
      clash(G, h)

law and.intro:
  for b: Bool
  for -c: Bool
  for h1: {b == True{} : Bool}
  for h2: {c == True{} : Bool}
  {(b && c) == True{} : Bool}

def and.intro(b, c, h1, h2):
  match b:
    case True{}:
      h2
    case False{}:
      clash({(False{} && c) == True{} : Bool}, h1)

law not.true:
  for b: Bool
  for h: {Bool.not(b) == True{} : Bool}
  {b == False{} : Bool}

def not.true(b, h):
  match b:
    case True{}:
      clash({True{} == False{} : Bool}, h)
    case False{}:
      {==}

law not.of:
  for -b: Bool
  for h: {b == False{} : Bool}
  {Bool.not(b) == True{} : Bool}

def not.of(b, h):
  Equal.cong(Bool, Bool, x => Bool.not(x), b, False{}, h)

# LT, EQ and GT are three
# -----------------------

def cmp.not_lt(c: Cmp) -> Type:
  match c:
    case LT{}:
      Empty
    case EQ{}:
      Unit
    case GT{}:
      Unit

def cmp.not_eq(c: Cmp) -> Type:
  match c:
    case LT{}:
      Unit
    case EQ{}:
      Empty
    case GT{}:
      Unit

def cmp.not_gt(c: Cmp) -> Type:
  match c:
    case LT{}:
      Unit
    case EQ{}:
      Unit
    case GT{}:
      Empty

law cmp.ne_lt.empty:
  for -x: Cmp
  for h: {x == LT{} : Cmp}
  for u: cmp.not_lt(x)
  Empty

def cmp.ne_lt.empty(x, h, u):
  %h : cmp.not_lt(_)
  u

# x is LT, though it is another constructor (u: Unit{} when it is).
law cmp.ne_lt:
  for -G: Type
  for -x: Cmp
  for h: {x == LT{} : Cmp}
  for u: cmp.not_lt(x)
  G

def cmp.ne_lt(G, x, h, u):
  ex_falso(G, cmp.ne_lt.empty(x, h, u))

law cmp.ne_eq.empty:
  for -x: Cmp
  for h: {x == EQ{} : Cmp}
  for u: cmp.not_eq(x)
  Empty

def cmp.ne_eq.empty(x, h, u):
  %h : cmp.not_eq(_)
  u

law cmp.ne_eq:
  for -G: Type
  for -x: Cmp
  for h: {x == EQ{} : Cmp}
  for u: cmp.not_eq(x)
  G

def cmp.ne_eq(G, x, h, u):
  ex_falso(G, cmp.ne_eq.empty(x, h, u))

law cmp.ne_gt.empty:
  for -x: Cmp
  for h: {x == GT{} : Cmp}
  for u: cmp.not_gt(x)
  Empty

def cmp.ne_gt.empty(x, h, u):
  %h : cmp.not_gt(_)
  u

law cmp.ne_gt:
  for -G: Type
  for -x: Cmp
  for h: {x == GT{} : Cmp}
  for u: cmp.not_gt(x)
  G

def cmp.ne_gt(G, x, h, u):
  ex_falso(G, cmp.ne_gt.empty(x, h, u))

# A cons is equal where its tails are.
law cons_cong:
  for -A: Data
  for -h: A
  for -a: List<&2, A>
  for -b: List<&2, A>
  for e: {a == b : List<&2, A>}
  {h <> a == h <> b : List<&2, A>}

def cons_cong(A, h, a, b, e):
  %e : {h <> a == h <> _ : List<&2, A>}
  {==}

# Equalities in a row.
law chain5:
  for -T: Type
  for -a: T
  for -b: T
  for -c: T
  for -d: T
  for -e: T
  for -f: T
  for e1: {a == b : T}
  for e2: {b == c : T}
  for e3: {c == d : T}
  for e4: {d == e : T}
  for e5: {e == f : T}
  {a == f : T}

def chain5(T, a, b, c, d, e, f, e1, e2, e3, e4, e5):
  Equal.trans(T, a, b, f, e1, Equal.trans(T, b, c, f, e2, Equal.trans(T, c, d, f, e3, Equal.trans(T, d, e, f, e4, e5))))

law chain6:
  for -T: Type
  for -a: T
  for -b: T
  for -c: T
  for -d: T
  for -e: T
  for -f: T
  for -g: T
  for e1: {a == b : T}
  for e2: {b == c : T}
  for e3: {c == d : T}
  for e4: {d == e : T}
  for e5: {e == f : T}
  for e6: {f == g : T}
  {a == g : T}

def chain6(T, a, b, c, d, e, f, g, e1, e2, e3, e4, e5, e6):
  Equal.trans(T, a, b, g, e1, chain5(T, b, c, d, e, f, g, e2, e3, e4, e5, e6))

law not.false:
  for b: Bool
  for h: {Bool.not(b) == False{} : Bool}
  {b == True{} : Bool}

def not.false(b, h):
  match b:
    case True{}:
      {==}
    case False{}:
      clash.flip({False{} == True{} : Bool}, h)
