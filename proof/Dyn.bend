import Base
import ../Frp.bend as F
import ../Dyn.bend as D
import ./Logic.bend as L
import ./Order.bend as O

# Facts about Dyn the laws are proved from: a stepper at one occurrence, once
# whether it is before t is known; map, fold and zip against the meaning.

# A stepper's step, at a known Bool
# ---------------------------------

law if_true:
  for -A: Data
  for -X: A
  for -x: A
  for c: Bool
  for h: {c == True{} : Bool}
  {F.B.stepper.if(A, w => X, x, c) == X : A}

def if_true(A, X, x, c, h):
  match c:
    case True{}:
      {==}
    case False{}:
      L.clash({F.B.stepper.if(A, w => X, x, False{}) == X : A}, h)

law if_false:
  for -A: Data
  for -X: A
  for -x: A
  for c: Bool
  for h: {c == False{} : Bool}
  {F.B.stepper.if(A, w => X, x, c) == x : A}

def if_false(A, X, x, c, h):
  match c:
    case True{}:
      L.clash.flip({F.B.stepper.if(A, w => X, x, True{}) == x : A}, h)
    case False{}:
      {==}

law both_cong:
  for -A: Data
  for -B: Data
  for -p: A
  for -p2: A
  for -q: B
  for -q2: B
  for e1: {p == p2 : A}
  for e2: {q == q2 : B}
  {F.Both{p, q} == F.Both{p2, q2} : F.Both<A, B>}

def both_cong(A, B, p, p2, q, q2, e1, e2):
  %e1 : {F.Both{p, q} == F.Both{_, q2} : F.Both<A, B>}
  %e2 : {F.Both{p, q} == F.Both{p, _} : F.Both<A, B>}
  {==}

# A pair's stepper steps as its halves do.
law if_both:
  for -A: Data
  for -B: Data
  for c: Bool
  for -X: F.Both<A, B>
  for -P: A
  for -Q: B
  for -a: A
  for -b: B
  for ih: {X == F.Both{P, Q} : F.Both<A, B>}
  {F.B.stepper.if(F.Both<A, B>, w => X, F.Both{a, b}, c)
     == F.Both{F.B.stepper.if(A, w => P, a, c), F.B.stepper.if(B, w => Q, b, c)} : F.Both<A, B>}

def if_both(A, B, c, X, P, Q, a, b, ih):
  match c:
    case True{}:
      ih
    case False{}:
      {==}

law if_both_l:
  for -A: Data
  for -B: Data
  for c: Bool
  for -X: F.Both<A, B>
  for -P: A
  for -a: A
  for -b: B
  for ih: {X == F.Both{P, b} : F.Both<A, B>}
  {F.B.stepper.if(F.Both<A, B>, w => X, F.Both{a, b}, c) == F.Both{F.B.stepper.if(A, w => P, a, c), b} : F.Both<A, B>}

def if_both_l(A, B, c, X, P, a, b, ih):
  match c:
    case True{}:
      ih
    case False{}:
      {==}

law if_both_r:
  for -A: Data
  for -B: Data
  for c: Bool
  for -X: F.Both<A, B>
  for -Q: B
  for -a: A
  for -b: B
  for ih: {X == F.Both{a, Q} : F.Both<A, B>}
  {F.B.stepper.if(F.Both<A, B>, w => X, F.Both{a, b}, c) == F.Both{a, F.B.stepper.if(B, w => Q, b, c)} : F.Both<A, B>}

def if_both_r(A, B, c, X, Q, a, b, ih):
  match c:
    case True{}:
      ih
    case False{}:
      {==}

# map
# ---

law map.if:
  for ~A: Data
  for ~B: Data
  for ~f: A -> B
  for c: Bool
  for -X: B
  for -Y: A
  for -x: A
  for ih: {X == f(Y) : B}
  {F.B.stepper.if(B, w => X, f(x), c) == f(F.B.stepper.if(A, w => Y, x, c)) : B}

def map.if(A, B, f, c, X, Y, x, ih):
  match c:
    case True{}:
      ih
    case False{}:
      {==}

# A stepper of an event mapped is the map of the stepper.
law map_at:
  for ~A: Data
  for ~B: Data
  for ~f: A -> B
  for e: F.Events(A)
  for +t: F.Time
  for +x: A
  {F.B.stepper.at(B, F.E.map(~A, ~B, ~f, e), t, f(x)) == f(F.B.stepper.at(A, e, t, x)) : B}

def map_at(A, B, f, e, t, x):
  match e:
    case Nil{}:
      {==}
    case Con{F.Occ{+u, +y}, rest}:
      map.if(A, B, f, F.Time.lt(u, t), F.B.stepper.at(B, F.E.map(~A, ~B, ~f, rest), t, f(y)),
        F.B.stepper.at(A, rest, t, y), x, map_at(A, B, f, rest, t, y))

# fold
# ----

law fold.if:
  for ~A: Data
  for ~B: Data
  for ~f: B -> A -> B
  for c: Bool
  for -u: F.Time
  for -a: A
  for -X: B
  for -R: F.Events(A)
  for -x: B
  for ih: {X == F.E.fold(~A, ~B, ~f, R, f(x, a)) : B}
  {F.B.stepper.if(B, w => X, x, c) == F.E.fold(~A, ~B, ~f, F.E.before.if(A, w => F.Occ{u, a} <> R, c), x) : B}

def fold.if(A, B, f, c, u, a, X, R, x, ih):
  match c:
    case True{}:
      ih
    case False{}:
      {==}

# A stepper of the folds of an event is the fold of the values before t.
law fold_at:
  for ~A: Data
  for ~B: Data
  for ~f: B -> A -> B
  for e: F.Events(A)
  for +t: F.Time
  for +x: B
  {F.B.stepper.at(B, F.E.accum(~A, ~B, ~f, e, x), t, x) == F.E.fold(~A, ~B, ~f, F.E.before(A, e, t), x) : B}

def fold_at(A, B, f, e, t, x):
  match e:
    case Nil{}:
      {==}
    case Con{F.Occ{+u, +a}, rest}:
      +n = f(x, a)
      fold.if(A, B, f, F.Time.lt(u, t), u, a, F.B.stepper.at(B, F.E.accum(~A, ~B, ~f, rest, n), t, n),
        F.E.before(A, rest, t), x, fold_at(A, B, f, rest, t, n))

# zip
# ---

# The first change of each, by the order of their times.

law zip.lt:
  for -A: Data
  for -B: Data
  for +t1: F.Time
  for -x: A
  for -xs: F.Events(A)
  for +u: F.Time
  for -y: B
  for -ys: F.Events(B)
  for -a: A
  for -b: B
  for +t: F.Time
  for +e: {F.Time.cmp(t1, u) == LT{} : Cmp}
  for +ih: {F.B.stepper.at(F.Both<A, B>, D.Dyn.zip.go(A, B, xs, F.Occ{u, y} <> ys, x, b), t, F.Both{x, b})
              == F.Both{F.B.stepper.at(A, xs, t, x), F.B.stepper.at(B, F.Occ{u, y} <> ys, t, b)} : F.Both<A, B>}
  {F.B.stepper.at(F.Both<A, B>, F.Occ{t1, F.Both{x, b}} <> D.Dyn.zip.go(A, B, xs, F.Occ{u, y} <> ys, x, b), t, F.Both{a, b})
     == F.Both{F.B.stepper.at(A, F.Occ{t1, x} <> xs, t, a), F.B.stepper.at(B, F.Occ{u, y} <> ys, t, b)} : F.Both<A, B>}

def zip.lt(A, B, t1, x, xs, u, y, ys, a, b, t, e, ih):
  L.bool.cases(F.Time.lt(t1, t),
    {F.B.stepper.at(F.Both<A, B>, F.Occ{t1, F.Both{x, b}} <> D.Dyn.zip.go(A, B, xs, F.Occ{u, y} <> ys, x, b), t, F.Both{a, b})
       == F.Both{F.B.stepper.at(A, F.Occ{t1, x} <> xs, t, a), F.B.stepper.at(B, F.Occ{u, y} <> ys, t, b)} : F.Both<A, B>},
    +h => Equal.trans(F.Both<A, B>,
      F.B.stepper.if(F.Both<A, B>, w => F.B.stepper.at(F.Both<A, B>, D.Dyn.zip.go(A, B, xs, F.Occ{u, y} <> ys, x, b), t, F.Both{x, b}),
        F.Both{a, b}, F.Time.lt(t1, t)),
      F.B.stepper.at(F.Both<A, B>, D.Dyn.zip.go(A, B, xs, F.Occ{u, y} <> ys, x, b), t, F.Both{x, b}),
      F.Both{F.B.stepper.at(A, F.Occ{t1, x} <> xs, t, a), F.B.stepper.at(B, F.Occ{u, y} <> ys, t, b)},
      if_true(F.Both<A, B>, F.B.stepper.at(F.Both<A, B>, D.Dyn.zip.go(A, B, xs, F.Occ{u, y} <> ys, x, b), t, F.Both{x, b}),
        F.Both{a, b}, F.Time.lt(t1, t), h),
      Equal.trans(F.Both<A, B>,
        F.B.stepper.at(F.Both<A, B>, D.Dyn.zip.go(A, B, xs, F.Occ{u, y} <> ys, x, b), t, F.Both{x, b}),
        F.Both{F.B.stepper.at(A, xs, t, x), F.B.stepper.at(B, F.Occ{u, y} <> ys, t, b)},
        F.Both{F.B.stepper.at(A, F.Occ{t1, x} <> xs, t, a), F.B.stepper.at(B, F.Occ{u, y} <> ys, t, b)},
        ih,
        Equal.cong(A, F.Both<A, B>, z => F.Both{z, F.B.stepper.at(B, F.Occ{u, y} <> ys, t, b)},
          F.B.stepper.at(A, xs, t, x), F.B.stepper.if(A, w => F.B.stepper.at(A, xs, t, x), a, F.Time.lt(t1, t)),
          Equal.sym(A, F.B.stepper.if(A, w => F.B.stepper.at(A, xs, t, x), a, F.Time.lt(t1, t)), F.B.stepper.at(A, xs, t, x),
            if_true(A, F.B.stepper.at(A, xs, t, x), a, F.Time.lt(t1, t), h))))),
    +h => Equal.trans(F.Both<A, B>,
      F.B.stepper.if(F.Both<A, B>, w => F.B.stepper.at(F.Both<A, B>, D.Dyn.zip.go(A, B, xs, F.Occ{u, y} <> ys, x, b), t, F.Both{x, b}),
        F.Both{a, b}, F.Time.lt(t1, t)),
      F.Both{a, b},
      F.Both{F.B.stepper.at(A, F.Occ{t1, x} <> xs, t, a), F.B.stepper.at(B, F.Occ{u, y} <> ys, t, b)},
      if_false(F.Both<A, B>, F.B.stepper.at(F.Both<A, B>, D.Dyn.zip.go(A, B, xs, F.Occ{u, y} <> ys, x, b), t, F.Both{x, b}),
        F.Both{a, b}, F.Time.lt(t1, t), h),
      Equal.sym(F.Both<A, B>,
        F.Both{F.B.stepper.at(A, F.Occ{t1, x} <> xs, t, a), F.B.stepper.at(B, F.Occ{u, y} <> ys, t, b)}, F.Both{a, b},
        both_cong(A, B, F.B.stepper.at(A, F.Occ{t1, x} <> xs, t, a), a, F.B.stepper.at(B, F.Occ{u, y} <> ys, t, b), b,
          if_false(A, F.B.stepper.at(A, xs, t, x), a, F.Time.lt(t1, t), h),
          if_false(B, F.B.stepper.at(B, ys, t, y), b, F.Time.lt(u, t),
            L.bool.cases(F.Time.lt(u, t), {F.Time.lt(u, t) == False{} : Bool},
              k => L.both({F.Time.lt(u, t) == False{} : Bool}, F.Time.lt(t1, t),
                O.lt_trans(t1, u, t, O.is_lt_of(F.Time.cmp(t1, u), e), k), h),
              f => f))))))

law zip.gt:
  for -A: Data
  for -B: Data
  for +t1: F.Time
  for -x: A
  for -xs: F.Events(A)
  for +u: F.Time
  for -y: B
  for -ys: F.Events(B)
  for -a: A
  for -b: B
  for +t: F.Time
  for +e: {F.Time.cmp(t1, u) == GT{} : Cmp}
  for +ih: {F.B.stepper.at(F.Both<A, B>, D.Dyn.zip.go(A, B, F.Occ{t1, x} <> xs, ys, a, y), t, F.Both{a, y})
              == F.Both{F.B.stepper.at(A, F.Occ{t1, x} <> xs, t, a), F.B.stepper.at(B, ys, t, y)} : F.Both<A, B>}
  {F.B.stepper.at(F.Both<A, B>, F.Occ{u, F.Both{a, y}} <> D.Dyn.zip.go(A, B, F.Occ{t1, x} <> xs, ys, a, y), t, F.Both{a, b})
     == F.Both{F.B.stepper.at(A, F.Occ{t1, x} <> xs, t, a), F.B.stepper.at(B, F.Occ{u, y} <> ys, t, b)} : F.Both<A, B>}

def zip.gt(A, B, t1, x, xs, u, y, ys, a, b, t, e, ih):
  L.bool.cases(F.Time.lt(u, t),
    {F.B.stepper.at(F.Both<A, B>, F.Occ{u, F.Both{a, y}} <> D.Dyn.zip.go(A, B, F.Occ{t1, x} <> xs, ys, a, y), t, F.Both{a, b})
       == F.Both{F.B.stepper.at(A, F.Occ{t1, x} <> xs, t, a), F.B.stepper.at(B, F.Occ{u, y} <> ys, t, b)} : F.Both<A, B>},
    +h => Equal.trans(F.Both<A, B>,
      F.B.stepper.if(F.Both<A, B>, w => F.B.stepper.at(F.Both<A, B>, D.Dyn.zip.go(A, B, F.Occ{t1, x} <> xs, ys, a, y), t, F.Both{a, y}),
        F.Both{a, b}, F.Time.lt(u, t)),
      F.B.stepper.at(F.Both<A, B>, D.Dyn.zip.go(A, B, F.Occ{t1, x} <> xs, ys, a, y), t, F.Both{a, y}),
      F.Both{F.B.stepper.at(A, F.Occ{t1, x} <> xs, t, a), F.B.stepper.at(B, F.Occ{u, y} <> ys, t, b)},
      if_true(F.Both<A, B>, F.B.stepper.at(F.Both<A, B>, D.Dyn.zip.go(A, B, F.Occ{t1, x} <> xs, ys, a, y), t, F.Both{a, y}),
        F.Both{a, b}, F.Time.lt(u, t), h),
      Equal.trans(F.Both<A, B>,
        F.B.stepper.at(F.Both<A, B>, D.Dyn.zip.go(A, B, F.Occ{t1, x} <> xs, ys, a, y), t, F.Both{a, y}),
        F.Both{F.B.stepper.at(A, F.Occ{t1, x} <> xs, t, a), F.B.stepper.at(B, ys, t, y)},
        F.Both{F.B.stepper.at(A, F.Occ{t1, x} <> xs, t, a), F.B.stepper.at(B, F.Occ{u, y} <> ys, t, b)},
        ih,
        Equal.cong(B, F.Both<A, B>, z => F.Both{F.B.stepper.at(A, F.Occ{t1, x} <> xs, t, a), z},
          F.B.stepper.at(B, ys, t, y), F.B.stepper.if(B, w => F.B.stepper.at(B, ys, t, y), b, F.Time.lt(u, t)),
          Equal.sym(B, F.B.stepper.if(B, w => F.B.stepper.at(B, ys, t, y), b, F.Time.lt(u, t)), F.B.stepper.at(B, ys, t, y),
            if_true(B, F.B.stepper.at(B, ys, t, y), b, F.Time.lt(u, t), h))))),
    +h => Equal.trans(F.Both<A, B>,
      F.B.stepper.if(F.Both<A, B>, w => F.B.stepper.at(F.Both<A, B>, D.Dyn.zip.go(A, B, F.Occ{t1, x} <> xs, ys, a, y), t, F.Both{a, y}),
        F.Both{a, b}, F.Time.lt(u, t)),
      F.Both{a, b},
      F.Both{F.B.stepper.at(A, F.Occ{t1, x} <> xs, t, a), F.B.stepper.at(B, F.Occ{u, y} <> ys, t, b)},
      if_false(F.Both<A, B>, F.B.stepper.at(F.Both<A, B>, D.Dyn.zip.go(A, B, F.Occ{t1, x} <> xs, ys, a, y), t, F.Both{a, y}),
        F.Both{a, b}, F.Time.lt(u, t), h),
      Equal.sym(F.Both<A, B>,
        F.Both{F.B.stepper.at(A, F.Occ{t1, x} <> xs, t, a), F.B.stepper.at(B, F.Occ{u, y} <> ys, t, b)}, F.Both{a, b},
        both_cong(A, B, F.B.stepper.at(A, F.Occ{t1, x} <> xs, t, a), a, F.B.stepper.at(B, F.Occ{u, y} <> ys, t, b), b,
          if_false(A, F.B.stepper.at(A, xs, t, x), a, F.Time.lt(t1, t),
            L.bool.cases(F.Time.lt(t1, t), {F.Time.lt(t1, t) == False{} : Bool},
              k => L.both({F.Time.lt(t1, t) == False{} : Bool}, F.Time.lt(u, t),
                O.lt_trans(u, t1, t,
                  O.is_lt_of(F.Time.cmp(u, t1),
                    Equal.trans(Cmp, F.Time.cmp(u, t1), O.cmp.flip(F.Time.cmp(t1, u)), LT{}, O.time_cmp_flip(u, t1),
                      Equal.cong(Cmp, Cmp, z => O.cmp.flip(z), F.Time.cmp(t1, u), GT{}, e))), k), h),
              f => f)),
          if_false(B, F.B.stepper.at(B, ys, t, y), b, F.Time.lt(u, t), h)))))

law zip.eq:
  for -A: Data
  for -B: Data
  for +t1: F.Time
  for -x: A
  for -xs: F.Events(A)
  for +u: F.Time
  for -y: B
  for -ys: F.Events(B)
  for -a: A
  for -b: B
  for +t: F.Time
  for e: {F.Time.cmp(t1, u) == EQ{} : Cmp}
  for ih: {F.B.stepper.at(F.Both<A, B>, D.Dyn.zip.go(A, B, xs, ys, x, y), t, F.Both{x, y})
             == F.Both{F.B.stepper.at(A, xs, t, x), F.B.stepper.at(B, ys, t, y)} : F.Both<A, B>}
  {F.B.stepper.at(F.Both<A, B>, F.Occ{t1, F.Both{x, y}} <> D.Dyn.zip.go(A, B, xs, ys, x, y), t, F.Both{a, b})
     == F.Both{F.B.stepper.at(A, F.Occ{t1, x} <> xs, t, a), F.B.stepper.at(B, F.Occ{u, y} <> ys, t, b)} : F.Both<A, B>}

def zip.eq(A, B, t1, x, xs, u, y, ys, a, b, t, e, ih):
  Equal.trans(F.Both<A, B>,
    F.B.stepper.at(F.Both<A, B>, F.Occ{t1, F.Both{x, y}} <> D.Dyn.zip.go(A, B, xs, ys, x, y), t, F.Both{a, b}),
    F.Both{F.B.stepper.if(A, w => F.B.stepper.at(A, xs, t, x), a, F.Time.lt(t1, t)),
           F.B.stepper.if(B, w => F.B.stepper.at(B, ys, t, y), b, F.Time.lt(t1, t))},
    F.Both{F.B.stepper.at(A, F.Occ{t1, x} <> xs, t, a), F.B.stepper.at(B, F.Occ{u, y} <> ys, t, b)},
    if_both(A, B, F.Time.lt(t1, t), F.B.stepper.at(F.Both<A, B>, D.Dyn.zip.go(A, B, xs, ys, x, y), t, F.Both{x, y}),
      F.B.stepper.at(A, xs, t, x), F.B.stepper.at(B, ys, t, y), a, b, ih),
    Equal.cong(F.Time, F.Both<A, B>,
      z => F.Both{F.B.stepper.if(A, w => F.B.stepper.at(A, xs, t, x), a, F.Time.lt(t1, t)),
                  F.B.stepper.if(B, w => F.B.stepper.at(B, ys, t, y), b, F.Time.lt(z, t))},
      t1, u, O.time_cmp_eq(t1, u, e)))

law zip.cases:
  for -A: Data
  for -B: Data
  for c: Cmp
  for +t1: F.Time
  for -x: A
  for -xs: F.Events(A)
  for +u: F.Time
  for -y: B
  for -ys: F.Events(B)
  for -a: A
  for -b: B
  for +t: F.Time
  for e: {F.Time.cmp(t1, u) == c : Cmp}
  for ih_lt: {F.B.stepper.at(F.Both<A, B>, D.Dyn.zip.go(A, B, xs, F.Occ{u, y} <> ys, x, b), t, F.Both{x, b})
                == F.Both{F.B.stepper.at(A, xs, t, x), F.B.stepper.at(B, F.Occ{u, y} <> ys, t, b)} : F.Both<A, B>}
  for ih_gt: {F.B.stepper.at(F.Both<A, B>, D.Dyn.zip.go(A, B, F.Occ{t1, x} <> xs, ys, a, y), t, F.Both{a, y})
                == F.Both{F.B.stepper.at(A, F.Occ{t1, x} <> xs, t, a), F.B.stepper.at(B, ys, t, y)} : F.Both<A, B>}
  for ih_eq: {F.B.stepper.at(F.Both<A, B>, D.Dyn.zip.go(A, B, xs, ys, x, y), t, F.Both{x, y})
                == F.Both{F.B.stepper.at(A, xs, t, x), F.B.stepper.at(B, ys, t, y)} : F.Both<A, B>}
  {F.B.stepper.at(F.Both<A, B>,
     D.Dyn.zip.pick(A, B, c, t1, x, u, y, a, b,
       w => D.Dyn.zip.go(A, B, xs, F.Occ{u, y} <> ys, x, b),
       w => D.Dyn.zip.go(A, B, F.Occ{t1, x} <> xs, ys, a, y),
       w => D.Dyn.zip.go(A, B, xs, ys, x, y)), t, F.Both{a, b})
     == F.Both{F.B.stepper.at(A, F.Occ{t1, x} <> xs, t, a), F.B.stepper.at(B, F.Occ{u, y} <> ys, t, b)} : F.Both<A, B>}

def zip.cases(A, B, c, t1, x, xs, u, y, ys, a, b, t, e, ih_lt, ih_gt, ih_eq):
  match c:
    case LT{}:
      zip.lt(A, B, t1, x, xs, u, y, ys, a, b, t, e, ih_lt)
    case EQ{}:
      zip.eq(A, B, t1, x, xs, u, y, ys, a, b, t, e, ih_eq)
    case GT{}:
      zip.gt(A, B, t1, x, xs, u, y, ys, a, b, t, e, ih_gt)

# A stepper of two events zipped is the pair of their steppers.
law zip_at:
  for -A: Data
  for -B: Data
  for ea: F.Events(A)
  for eb: F.Events(B)
  for +a: A
  for +b: B
  for +t: F.Time
  {F.B.stepper.at(F.Both<A, B>, D.Dyn.zip.go(A, B, ea, eb, a, b), t, F.Both{a, b})
     == F.Both{F.B.stepper.at(A, ea, t, a), F.B.stepper.at(B, eb, t, b)} : F.Both<A, B>}

def zip_at(A, B, ea, eb, a, b, t):
  match ea eb:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{F.Occ{+u, +y}, +ys}:
      if_both_r(A, B, F.Time.lt(u, t), F.B.stepper.at(F.Both<A, B>, D.Dyn.zip.go(A, B, Nil{}, ys, a, y), t, F.Both{a, y}),
        F.B.stepper.at(B, ys, t, y), a, b, zip_at(A, B, Nil{}, ys, a, y, t))
    case Con{F.Occ{+t1, +x}, +xs} Nil{}:
      if_both_l(A, B, F.Time.lt(t1, t), F.B.stepper.at(F.Both<A, B>, D.Dyn.zip.go(A, B, xs, Nil{}, x, b), t, F.Both{x, b}),
        F.B.stepper.at(A, xs, t, x), a, b, zip_at(A, B, xs, Nil{}, x, b, t))
    case Con{F.Occ{+t1, +x}, +xs} Con{F.Occ{+u, +y}, +ys}:
      zip.cases(A, B, F.Time.cmp(t1, u), t1, x, xs, u, y, ys, a, b, t, {==},
        zip_at(A, B, xs, F.Occ{u, y} <> ys, x, b, t),
        zip_at(A, B, F.Occ{t1, x} <> xs, ys, a, y, t),
        zip_at(A, B, xs, ys, x, y, t))

# join
# ----

# A stepper's later branch, where the two agree.
law if_cong:
  for -A: Data
  for c: Bool
  for -X: A
  for -Y: A
  for -x: A
  for ih: {X == Y : A}
  {F.B.stepper.if(A, w => X, x, c) == F.B.stepper.if(A, w => Y, x, c) : A}

def if_cong(A, c, X, Y, x, ih):
  match c:
    case True{}:
      ih
    case False{}:
      {==}

# A stepper over Dyns started from either of two Dyns that agree at t agrees
# at t.
law swap.if:
  for -A: Data
  for c: Bool
  for -X: D.Dyn<A>
  for -d1: D.Dyn<A>
  for -d2: D.Dyn<A>
  for -t: F.Time
  for h: {D.Dyn.current(A, d1)(t) == D.Dyn.current(A, d2)(t) : A}
  {D.Dyn.current(A, F.B.stepper.if(D.Dyn<A>, w => X, d1, c))(t) == D.Dyn.current(A, F.B.stepper.if(D.Dyn<A>, w => X, d2, c))(t) : A}

def swap.if(A, c, X, d1, d2, t, h):
  match c:
    case True{}:
      {==}
    case False{}:
      h

law init_swap:
  for -A: Data
  for rest: F.Events(D.Dyn<A>)
  for +t: F.Time
  for -d1: D.Dyn<A>
  for -d2: D.Dyn<A>
  for h: {D.Dyn.current(A, d1)(t) == D.Dyn.current(A, d2)(t) : A}
  {D.Dyn.current(A, F.B.stepper.at(D.Dyn<A>, rest, t, d1))(t) == D.Dyn.current(A, F.B.stepper.at(D.Dyn<A>, rest, t, d2))(t) : A}

def init_swap(A, rest, t, d1, d2, h):
  match rest:
    case Nil{}:
      h
    case Con{F.Occ{+tr, d}, r}:
      swap.if(A, F.Time.lt(tr, t), F.B.stepper.at(D.Dyn<A>, r, t, d), d1, d2, t, h)

# After u < t: the stepper from the last value at or before u, over the rest,
# is the stepper over all.
law after_last.if:
  for -A: Data
  for c: Bool
  for +u: F.Time
  for -y: A
  for -r: F.Events(A)
  for +to: F.Time
  for +t: F.Time
  for -x: A
  for e: {F.Time.le(u, to) == c : Bool}
  for h: {F.Time.lt(to, t) == True{} : Bool}
  for ih: {F.B.stepper.at(A, D.Dyn.after(A, r, to), t, D.Dyn.last_le(A, r, to, y)) == F.B.stepper.at(A, r, t, y) : A}
  {F.B.stepper.at(A, D.Dyn.after.if(A, w => D.Dyn.after(A, r, to), F.Occ{u, y} <> r, c), t,
       F.B.stepper.if(A, w => D.Dyn.last_le(A, r, to, y), x, c))
     == F.B.stepper.if(A, w => F.B.stepper.at(A, r, t, y), x, F.Time.lt(u, t)) : A}

def after_last.if(A, c, u, y, r, to, t, x, e, h, ih):
  match c:
    case True{}:
      Equal.trans(A, F.B.stepper.at(A, D.Dyn.after(A, r, to), t, D.Dyn.last_le(A, r, to, y)),
        F.B.stepper.at(A, r, t, y), F.B.stepper.if(A, w => F.B.stepper.at(A, r, t, y), x, F.Time.lt(u, t)),
        ih,
        Equal.sym(A, F.B.stepper.if(A, w => F.B.stepper.at(A, r, t, y), x, F.Time.lt(u, t)), F.B.stepper.at(A, r, t, y),
          if_true(A, F.B.stepper.at(A, r, t, y), x, F.Time.lt(u, t),
            O.nlt_lt_trans(u, to, t, L.not.true(F.Time.lt(to, u), e), h))))
    case False{}:
      {==}

law after_last:
  for -A: Data
  for ic: F.Events(A)
  for +to: F.Time
  for +t: F.Time
  for +x: A
  for +h: {F.Time.lt(to, t) == True{} : Bool}
  {F.B.stepper.at(A, D.Dyn.after(A, ic, to), t, D.Dyn.last_le(A, ic, to, x)) == F.B.stepper.at(A, ic, t, x) : A}

def after_last(A, ic, to, t, x, h):
  match ic:
    case Nil{}:
      {==}
    case Con{F.Occ{+u, +y}, +r}:
      after_last.if(A, F.Time.le(u, to), u, y, r, to, t, x, {==}, h, after_last(A, r, to, t, y, h))

# t not after to: the occurrences up to to, then one at to, step as all do.
law upto_before.if:
  for -A: Data
  for c: Bool
  for +u: F.Time
  for -y: A
  for -r: F.Events(A)
  for +to: F.Time
  for -v: A
  for -J: F.Events(A)
  for +t: F.Time
  for -x: A
  for e: {F.Time.le(u, to) == c : Bool}
  for +h: {F.Time.lt(to, t) == False{} : Bool}
  for ih: {F.B.stepper.at(A, List.append(&2, F.Occ<A>, D.Dyn.upto(A, r, to), F.Occ{to, v} <> J), t, y) == F.B.stepper.at(A, r, t, y) : A}
  {F.B.stepper.at(A, List.append(&2, F.Occ<A>, F.E.before.if(A, w => F.Occ{u, y} <> D.Dyn.upto(A, r, to), c), F.Occ{to, v} <> J), t, x)
     == F.B.stepper.if(A, w => F.B.stepper.at(A, r, t, y), x, F.Time.lt(u, t)) : A}

def upto_before.if(A, c, u, y, r, to, v, J, t, x, e, h, ih):
  match c:
    case True{}:
      if_cong(A, F.Time.lt(u, t), F.B.stepper.at(A, List.append(&2, F.Occ<A>, D.Dyn.upto(A, r, to), F.Occ{to, v} <> J), t, y),
        F.B.stepper.at(A, r, t, y), x, ih)
    case False{}:
      Equal.trans(A, F.B.stepper.if(A, w => F.B.stepper.at(A, J, t, v), x, F.Time.lt(to, t)), x,
        F.B.stepper.if(A, w => F.B.stepper.at(A, r, t, y), x, F.Time.lt(u, t)),
        if_false(A, F.B.stepper.at(A, J, t, v), x, F.Time.lt(to, t), h),
        Equal.sym(A, F.B.stepper.if(A, w => F.B.stepper.at(A, r, t, y), x, F.Time.lt(u, t)), x,
          if_false(A, F.B.stepper.at(A, r, t, y), x, F.Time.lt(u, t),
            L.bool.cases(F.Time.lt(u, t), {F.Time.lt(u, t) == False{} : Bool},
              k => L.both({F.Time.lt(u, t) == False{} : Bool}, F.Time.lt(to, t),
                O.lt_trans(to, u, t, L.not.false(F.Time.lt(to, u), e), k), h),
              f => f))))

law upto_before:
  for -A: Data
  for ic: F.Events(A)
  for +to: F.Time
  for -v: A
  for -J: F.Events(A)
  for +t: F.Time
  for +x: A
  for +h: {F.Time.lt(to, t) == False{} : Bool}
  {F.B.stepper.at(A, List.append(&2, F.Occ<A>, D.Dyn.upto(A, ic, to), F.Occ{to, v} <> J), t, x) == F.B.stepper.at(A, ic, t, x) : A}

def upto_before(A, ic, to, v, J, t, x, h):
  match ic:
    case Nil{}:
      if_false(A, F.B.stepper.at(A, J, t, v), x, F.Time.lt(to, t), h)
    case Con{F.Occ{+u, +y}, +r}:
      upto_before.if(A, F.Time.le(u, to), u, y, r, to, v, J, t, x, {==}, h, upto_before(A, r, to, v, J, t, y, h))

# to before t: the occurrences up to to step to their last value.
law upto_after.if:
  for -A: Data
  for c: Bool
  for +u: F.Time
  for -y: A
  for -r: F.Events(A)
  for +to: F.Time
  for -R: F.Events(A)
  for +t: F.Time
  for -x: A
  for e: {F.Time.le(u, to) == c : Bool}
  for h: {F.Time.lt(to, t) == True{} : Bool}
  for ih: {F.B.stepper.at(A, List.append(&2, F.Occ<A>, D.Dyn.upto(A, r, to), R), t, y) == F.B.stepper.at(A, R, t, D.Dyn.last_le(A, r, to, y)) : A}
  {F.B.stepper.at(A, List.append(&2, F.Occ<A>, F.E.before.if(A, w => F.Occ{u, y} <> D.Dyn.upto(A, r, to), c), R), t, x)
     == F.B.stepper.at(A, R, t, F.B.stepper.if(A, w => D.Dyn.last_le(A, r, to, y), x, c)) : A}

def upto_after.if(A, c, u, y, r, to, R, t, x, e, h, ih):
  match c:
    case True{}:
      Equal.trans(A,
        F.B.stepper.if(A, w => F.B.stepper.at(A, List.append(&2, F.Occ<A>, D.Dyn.upto(A, r, to), R), t, y), x, F.Time.lt(u, t)),
        F.B.stepper.at(A, List.append(&2, F.Occ<A>, D.Dyn.upto(A, r, to), R), t, y),
        F.B.stepper.at(A, R, t, D.Dyn.last_le(A, r, to, y)),
        if_true(A, F.B.stepper.at(A, List.append(&2, F.Occ<A>, D.Dyn.upto(A, r, to), R), t, y), x, F.Time.lt(u, t),
          O.nlt_lt_trans(u, to, t, L.not.true(F.Time.lt(to, u), e), h)),
        ih)
    case False{}:
      {==}

law upto_after:
  for -A: Data
  for ic: F.Events(A)
  for +to: F.Time
  for -R: F.Events(A)
  for +t: F.Time
  for +x: A
  for +h: {F.Time.lt(to, t) == True{} : Bool}
  {F.B.stepper.at(A, List.append(&2, F.Occ<A>, D.Dyn.upto(A, ic, to), R), t, x) == F.B.stepper.at(A, R, t, D.Dyn.last_le(A, ic, to, x)) : A}

def upto_after(A, ic, to, R, t, x, h):
  match ic:
    case Nil{}:
      {==}
    case Con{F.Occ{+u, +y}, +r}:
      upto_after.if(A, F.Time.le(u, to), u, y, r, to, R, t, x, {==}, h, upto_after(A, r, to, R, t, y, h))

# One outer change, once whether it is before t is known.
law join.if:
  for -A: Data
  for c: Bool
  for +to: F.Time
  for +x2: A
  for +ic2: F.Events(A)
  for rest: F.Events(D.Dyn<A>)
  for +x: A
  for +ic: F.Events(A)
  for +t: F.Time
  for +e: {F.Time.lt(to, t) == c : Bool}
  for ih: {F.B.stepper.at(A, D.Dyn.join.go(A, rest, D.Dyn.after(A, ic2, to)), t, D.Dyn.last_le(A, ic2, to, x2))
             == D.Dyn.current(A, F.B.stepper.at(D.Dyn<A>, rest, t, D.Dyn{D.Dyn.last_le(A, ic2, to, x2), D.Dyn.after(A, ic2, to)}))(t) : A}
  {F.B.stepper.at(A, List.append(&2, F.Occ<A>, D.Dyn.upto(A, ic, to),
       F.Occ{to, D.Dyn.last_le(A, ic2, to, x2)} <> D.Dyn.join.go(A, rest, D.Dyn.after(A, ic2, to))), t, x)
     == D.Dyn.current(A, F.B.stepper.if(D.Dyn<A>, w => F.B.stepper.at(D.Dyn<A>, rest, t, D.Dyn{x2, ic2}), D.Dyn{x, ic}, c))(t) : A}

def join.if(A, c, to, x2, ic2, rest, x, ic, t, e, ih):
  match c:
    case True{}:
      L.chain5(A,
        F.B.stepper.at(A, List.append(&2, F.Occ<A>, D.Dyn.upto(A, ic, to),
          F.Occ{to, D.Dyn.last_le(A, ic2, to, x2)} <> D.Dyn.join.go(A, rest, D.Dyn.after(A, ic2, to))), t, x),
        F.B.stepper.at(A, F.Occ{to, D.Dyn.last_le(A, ic2, to, x2)} <> D.Dyn.join.go(A, rest, D.Dyn.after(A, ic2, to)), t,
          D.Dyn.last_le(A, ic, to, x)),
        F.B.stepper.at(A, D.Dyn.join.go(A, rest, D.Dyn.after(A, ic2, to)), t, D.Dyn.last_le(A, ic2, to, x2)),
        D.Dyn.current(A, F.B.stepper.at(D.Dyn<A>, rest, t, D.Dyn{D.Dyn.last_le(A, ic2, to, x2), D.Dyn.after(A, ic2, to)}))(t),
        D.Dyn.current(A, F.B.stepper.at(D.Dyn<A>, rest, t, D.Dyn{x2, ic2}))(t),
        D.Dyn.current(A, F.B.stepper.if(D.Dyn<A>, w => F.B.stepper.at(D.Dyn<A>, rest, t, D.Dyn{x2, ic2}), D.Dyn{x, ic}, True{}))(t),
        upto_after(A, ic, to, F.Occ{to, D.Dyn.last_le(A, ic2, to, x2)} <> D.Dyn.join.go(A, rest, D.Dyn.after(A, ic2, to)), t, x, e),
        if_true(A, F.B.stepper.at(A, D.Dyn.join.go(A, rest, D.Dyn.after(A, ic2, to)), t, D.Dyn.last_le(A, ic2, to, x2)),
          D.Dyn.last_le(A, ic, to, x), F.Time.lt(to, t), e),
        ih,
        init_swap(A, rest, t, D.Dyn{D.Dyn.last_le(A, ic2, to, x2), D.Dyn.after(A, ic2, to)}, D.Dyn{x2, ic2},
          after_last(A, ic2, to, t, x2, e)),
        {==})
    case False{}:
      upto_before(A, ic, to, D.Dyn.last_le(A, ic2, to, x2), D.Dyn.join.go(A, rest, D.Dyn.after(A, ic2, to)), t, x, e)

law join_at:
  for -A: Data
  for ds: F.Events(D.Dyn<A>)
  for +x: A
  for +ic: F.Events(A)
  for +t: F.Time
  {F.B.stepper.at(A, D.Dyn.join.go(A, ds, ic), t, x) == D.Dyn.current(A, F.B.stepper.at(D.Dyn<A>, ds, t, D.Dyn{x, ic}))(t) : A}

def join_at(A, ds, x, ic, t):
  match ds:
    case Nil{}:
      {==}
    case Con{F.Occ{+to, D.Dyn{+x2, +ic2}}, +rest}:
      join.if(A, F.Time.lt(to, t), to, x2, ic2, rest, x, ic, t, {==},
        join_at(A, rest, D.Dyn.last_le(A, ic2, to, x2), D.Dyn.after(A, ic2, to), t))

law join_pure_at:
  for ~A: Data
  for e: F.Events(A)
  {D.Dyn.join.go(A, F.E.map(~A, ~D.Dyn<A>, ~D.Dyn.pure(A), e), Nil{}) == e : F.Events(A)}

def join_pure_at(A, e):
  match e:
    case Nil{}:
      {==}
    case Con{F.Occ{+to, y}, rest}:
      L.cons_cong(F.Occ<A>, F.Occ{to, y}, D.Dyn.join.go(A, F.E.map(~A, ~D.Dyn<A>, ~D.Dyn.pure(A), rest), Nil{}), rest,
        join_pure_at(A, rest))
