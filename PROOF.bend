# The proofs of LAWS.bend. Nothing here is trusted: `bend PROOF.bend` checks
# every def.

import Base
import ./Frp.bend as F
import ./LAWS.bend as Laws

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

def Laws.b_map_id(A, b, t):
  {==}

def Laws.b_map_comp(A, B, C, f, g, b, t):
  {==}

def Laws.b_ap_pure(A, B, f, x, t):
  {==}

def Laws.e_map_id(A, e):
  match e:
    case Nil{}:
      {==}
    case Con{o, rest}:
      match o:
        case F.Occ{t, x}:
          cons_cong(F.Occ<A>, F.Occ{t, x}, F.E.map(~A, ~A, ~F.ident(A), rest), rest, Laws.e_map_id(A, rest))

def Laws.e_map_comp(A, B, C, f, g, e):
  match e:
    case Nil{}:
      {==}
    case Con{o, rest}:
      match o:
        case F.Occ{t, x}:
          cons_cong(F.Occ<C>, F.Occ{t, g(f(x))},
                    F.E.map(~B, ~C, ~g, F.E.map(~A, ~B, ~f, rest)), F.E.map(~A, ~C, ~F.comp(~A, ~B, ~C, ~f, ~g), rest),
                    Laws.e_map_comp(A, B, C, f, g, rest))

def Laws.e_filter_all(A, e):
  match e:
    case Nil{}:
      {==}
    case Con{o, rest}:
      cons_cong(F.Occ<A>, o, F.E.filter(~A, ~F.always(A), rest), rest, Laws.e_filter_all(A, rest))

def Laws.e_merge_never_l(A, e):
  {==}

def Laws.e_merge_never_r(A, e):
  match e:
    case Nil{}:
      {==}
    case Con{x, xs}:
      cons_cong(F.Occ<A>, x, F.E.merge(A, xs, Nil{}), xs, Laws.e_merge_never_r(A, xs))

def Laws.e_run_lift(A, B, f, e, s):
  match e:
    case Nil{}:
      {==}
    case Con{o, rest}:
      match o:
        case F.Occ{t, x}:
          cons_cong(F.Occ<B>, F.Occ{t, f(x)},
                    F.E.run(~Unit, ~A, ~B, ~F.lift.step(~A, ~B, ~f), rest, s), F.E.map(~A, ~B, ~f, rest),
                    Laws.e_run_lift(A, B, f, rest, s))

def Laws.e_run_accum(A, B, f, e, x):
  match e:
    case Nil{}:
      {==}
    case Con{o, rest}:
      match o:
        case F.Occ{t, a}:
          +n = f(x, a)
          cons_cong(F.Occ<B>, F.Occ{t, n},
                    F.E.run(~B, ~A, ~B, ~F.accum.step(~A, ~B, ~f), rest, n), F.E.accum(~A, ~B, ~f, rest, n),
                    Laws.e_run_accum(A, B, f, rest, n))

law then.l2:
  for ~S: Data
  for ~T: Data
  for ~A: Data
  for ~B: Data
  for ~C: Data
  for ~sa: S -> A -> S & B
  for ~sb: T -> B -> T & C
  for -u: U32
  for -rest: F.Events(A)
  for -s2: S
  for q: T & C
  for ih2: @t2:T -> {F.E.run(~F.Both<S, T>, ~A, ~C, ~F.then.step(~S, ~T, ~A, ~B, ~C, ~sa, ~sb), rest, F.Both{s2, t2})
                         == F.E.run(~T, ~B, ~C, ~sb, F.E.run(~S, ~A, ~B, ~sa, rest, s2), t2) : F.Events(C)}
  {F.E.push(F.Both<S, T>, C, u, F.then.b(S, T, C, s2, q),
            v => F.E.run(~F.Both<S, T>, ~A, ~C, ~F.then.step(~S, ~T, ~A, ~B, ~C, ~sa, ~sb), rest, v))
     == F.E.push(T, C, u, q, v => F.E.run(~T, ~B, ~C, ~sb, F.E.run(~S, ~A, ~B, ~sa, rest, s2), v)) : F.Events(C)}

def then.l2(S, T, A, B, C, sa, sb, u, rest, s2, q, ih2):
  match q:
    case (t2, z):
      cons_cong(F.Occ<C>, F.Occ{u, z},
                F.E.run(~F.Both<S, T>, ~A, ~C, ~F.then.step(~S, ~T, ~A, ~B, ~C, ~sa, ~sb), rest, F.Both{s2, t2}),
                F.E.run(~T, ~B, ~C, ~sb, F.E.run(~S, ~A, ~B, ~sa, rest, s2), t2),
                ih2(t2))

law then.l1:
  for ~S: Data
  for ~T: Data
  for ~A: Data
  for ~B: Data
  for ~C: Data
  for ~sa: S -> A -> S & B
  for ~sb: T -> B -> T & C
  for -u: U32
  for -rest: F.Events(A)
  for t: T
  for p: S & B
  for ih: @s2:S -> @t2:T -> {F.E.run(~F.Both<S, T>, ~A, ~C, ~F.then.step(~S, ~T, ~A, ~B, ~C, ~sa, ~sb), rest, F.Both{s2, t2})
                                   == F.E.run(~T, ~B, ~C, ~sb, F.E.run(~S, ~A, ~B, ~sa, rest, s2), t2) : F.Events(C)}
  {F.E.push(F.Both<S, T>, C, u, F.then.a(~S, ~T, ~B, ~C, ~sb, t, p),
            v => F.E.run(~F.Both<S, T>, ~A, ~C, ~F.then.step(~S, ~T, ~A, ~B, ~C, ~sa, ~sb), rest, v))
     == F.E.run(~T, ~B, ~C, ~sb, F.E.push(S, B, u, p, v => F.E.run(~S, ~A, ~B, ~sa, rest, v)), t) : F.Events(C)}

def then.l1(S, T, A, B, C, sa, sb, u, rest, t, p, ih):
  match p:
    case (s2, y):
      then.l2(S, T, A, B, C, sa, sb, u, rest, s2, sb(t, y), ih(s2))

def Laws.e_run_then(S, T, A, B, C, sa, sb, e, s, t):
  match e:
    case Nil{}:
      {==}
    case Con{o, rest}:
      match o:
        case F.Occ{u, x}:
          then.l1(S, T, A, B, C, sa, sb, u, rest, t, sa(s, x),
                  s2 => t2 => Laws.e_run_then(S, T, A, B, C, sa, sb, rest, s2, t2))

law each.done.flat:
  for -T: Data
  for -C: Data
  for -u: U32
  for -y: C
  for r: T & List<&2, C>
  for -k: T -> F.Events(List<&2, C>)
  {F.E.flat(C, F.E.push(T, List<&2, C>, u, F.each.done(T, C, y, r), k))
     == F.Occ{u, y} <> F.E.flat(C, F.E.push(T, List<&2, C>, u, r, k)) : F.Events(C)}

def each.done.flat(T, C, u, y, r, k):
  match r:
    case (t, ys):
      {==}

law each.push.flat:
  for ~T: Data
  for ~B: Data
  for ~C: Data
  for ~sb: T -> B -> T & C
  for -u: U32
  for more: List<&2, B>
  for -tail: F.Events(B)
  for -k: T -> F.Events(List<&2, C>)
  for p: T & C
  for ih: @t2:T -> {F.E.flat(C, F.E.push(T, List<&2, C>, u, F.each.go(~T, ~B, ~C, ~sb, more, t2), k))
                      == F.E.run(~T, ~B, ~C, ~sb, F.E.spread(B, u, more, tail), t2) : F.Events(C)}
  {F.E.flat(C, F.E.push(T, List<&2, C>, u, F.each.push(T, C, p, v => F.each.go(~T, ~B, ~C, ~sb, more, v)), k))
     == F.E.push(T, C, u, p, v => F.E.run(~T, ~B, ~C, ~sb, F.E.spread(B, u, more, tail), v)) : F.Events(C)}

def each.push.flat(T, B, C, sb, u, more, tail, k, p, ih):
  match p:
    case (+t2, y):
      Equal.trans(F.Events(C),
        F.E.flat(C, F.E.push(T, List<&2, C>, u, F.each.done(T, C, y, F.each.go(~T, ~B, ~C, ~sb, more, t2)), k)),
        F.Occ{u, y} <> F.E.flat(C, F.E.push(T, List<&2, C>, u, F.each.go(~T, ~B, ~C, ~sb, more, t2), k)),
        F.Occ{u, y} <> F.E.run(~T, ~B, ~C, ~sb, F.E.spread(B, u, more, tail), t2),
        each.done.flat(T, C, u, y, F.each.go(~T, ~B, ~C, ~sb, more, t2), k),
        cons_cong(F.Occ<C>, F.Occ{u, y},
                  F.E.flat(C, F.E.push(T, List<&2, C>, u, F.each.go(~T, ~B, ~C, ~sb, more, t2), k)),
                  F.E.run(~T, ~B, ~C, ~sb, F.E.spread(B, u, more, tail), t2),
                  ih(t2)))

law each.in:
  for ~T: Data
  for ~B: Data
  for ~C: Data
  for ~sb: T -> B -> T & C
  for -u: U32
  for xs: List<&2, B>
  for t: T
  for -tail: F.Events(B)
  for -k: T -> F.Events(List<&2, C>)
  for ih: @t2:T -> {F.E.flat(C, k(t2)) == F.E.run(~T, ~B, ~C, ~sb, tail, t2) : F.Events(C)}
  {F.E.flat(C, F.E.push(T, List<&2, C>, u, F.each.go(~T, ~B, ~C, ~sb, xs, t), k))
     == F.E.run(~T, ~B, ~C, ~sb, F.E.spread(B, u, xs, tail), t) : F.Events(C)}

def each.in(T, B, C, sb, u, xs, t, tail, k, ih):
  match xs:
    case Nil{}:
      ih(t)
    case Con{x, +more}:
      each.push.flat(T, B, C, sb, u, more, tail, k, sb(t, x),
                     t2 => each.in(T, B, C, sb, u, more, t2, tail, k, ih))

def Laws.e_run_each(T, B, C, sb, e, t):
  match e:
    case Nil{}:
      {==}
    case Con{o, rest}:
      match o:
        case F.Occ{u, xs}:
          each.in(T, B, C, sb, u, xs, t, F.E.flat(B, rest),
                  v => F.E.run(~T, ~List<&2, B>, ~List<&2, C>, ~F.each.step(~T, ~B, ~C, ~sb), rest, v),
                  t2 => Laws.e_run_each(T, B, C, sb, rest, t2))

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

law ex_falso:
  for -G: Type
  for e: Empty
  G

def ex_falso(G, e):
  match e:

law clash:
  for -G: Type
  for h: {False{} == True{} : Bool}
  G

def clash(G, h):
  ex_falso(G, clash.empty(h))

law stepper.if:
  for -A: Data
  for -x: A
  for -X: A
  for -Y: A
  for b: Bool
  for -c: Bool
  for h: {(b && c) == True{} : Bool}
  for ih: {c == True{} : Bool} -> {X == Y : A}
  {F.B.stepper.if(A, w => X, x, b) == Y : A}

def stepper.if(A, x, X, Y, b, c, h, ih):
  match b:
    case True{}:
      ih(h)
    case False{}:
      clash({F.B.stepper.if(A, w => X, x, False{}) == Y : A}, h)

def Laws.stepper_after(A, e, t, x, all):
  match e:
    case Nil{}:
      {==}
    case Con{o, rest}:
      match o:
        case F.Occ{u, y}:
          stepper.if(A, x, F.B.stepper.at(A, rest, t, y), F.E.last(A, rest, y), U32.is_lt(u, t),
                     F.E.all_before(A, rest, t), all, h => Laws.stepper_after(A, rest, t, y, h))
