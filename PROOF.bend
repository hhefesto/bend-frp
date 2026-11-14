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

# The same clash, the other way round.
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

# merge and filter at one step
# -----------------------------

# merge at two first occurrences, once the order of their times is known.
law merge.first.if:
  for -A: Data
  for b: Bool
  for -x: F.Occ<A>
  for -xs: F.Events(A)
  for -y: F.Occ<A>
  for -ys: F.Events(A)
  for h: {b == False{} : Bool}
  {F.E.merge.pick(A, b, x, y, r => F.E.merge(A, xs, r), ys, j => F.E.merge.in(A, x, ys, r => j(r)))
     == x <> F.E.merge(A, xs, y <> ys) : F.Events(A)}

def merge.first.if(A, b, x, xs, y, ys, h):
  match b:
    case True{}:
      clash.flip({F.E.merge.pick(A, True{}, x, y, r => F.E.merge(A, xs, r), ys, j => F.E.merge.in(A, x, ys, r => j(r)))
                    == x <> F.E.merge(A, xs, y <> ys) : F.Events(A)}, h)
    case False{}:
      {==}

law merge.later.if:
  for -A: Data
  for b: Bool
  for -x: F.Occ<A>
  for -xs: F.Events(A)
  for -y: F.Occ<A>
  for -ys: F.Events(A)
  for h: {b == True{} : Bool}
  {F.E.merge.pick(A, b, x, y, r => F.E.merge(A, xs, r), ys, j => F.E.merge.in(A, x, ys, r => j(r)))
     == y <> F.E.merge(A, x <> xs, ys) : F.Events(A)}

def merge.later.if(A, b, x, xs, y, ys, h):
  match b:
    case True{}:
      {==}
    case False{}:
      clash({F.E.merge.pick(A, False{}, x, y, r => F.E.merge(A, xs, r), ys, j => F.E.merge.in(A, x, ys, r => j(r)))
               == y <> F.E.merge(A, x <> xs, ys) : F.Events(A)}, h)

def Laws.e_merge_first(A, t, a, xs, u, b, ys, h):
  merge.first.if(A, U32.is_lt(u, t), F.Occ{t, a}, xs, F.Occ{u, b}, ys, h)

def Laws.e_merge_later(A, t, a, xs, u, b, ys, h):
  merge.later.if(A, U32.is_lt(u, t), F.Occ{t, a}, xs, F.Occ{u, b}, ys, h)

# filter at one occurrence, once whether its value passes is known.
law keep.hit:
  for -A: Data
  for -o: F.Occ<A>
  for -rest: F.Events(A)
  for b: Bool
  for h: {b == True{} : Bool}
  {F.E.keep(A, o, rest, b) == o <> rest : F.Events(A)}

def keep.hit(A, o, rest, b, h):
  match b:
    case True{}:
      {==}
    case False{}:
      clash({F.E.keep(A, o, rest, False{}) == o <> rest : F.Events(A)}, h)

law keep.miss:
  for -A: Data
  for -o: F.Occ<A>
  for -rest: F.Events(A)
  for b: Bool
  for h: {b == False{} : Bool}
  {F.E.keep(A, o, rest, b) == rest : F.Events(A)}

def keep.miss(A, o, rest, b, h):
  match b:
    case True{}:
      clash.flip({F.E.keep(A, o, rest, True{}) == rest : F.Events(A)}, h)
    case False{}:
      {==}

def Laws.e_filter_never(A, p):
  {==}

def Laws.e_filter_keep(A, p, t, a, e, h):
  keep.hit(A, F.Occ{t, a}, F.E.filter(~A, ~p, e), p(a), h)

def Laws.e_filter_drop(A, p, t, a, e, h):
  keep.miss(A, F.Occ{t, a}, F.E.filter(~A, ~p, e), p(a), h)


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

# par, snapshot and switch
# -------------------------

# par: the first half

law par.fst.l2:
  for ~S: Data
  for ~T: Data
  for ~A: Data
  for ~B: Data
  for ~C: Data
  for ~sa: S -> A -> S & B
  for ~sb: T -> A -> T & C
  for -u: U32
  for -rest: F.Events(A)
  for -s2: S
  for -y: B
  for q: T & C
  for ih: @t2:T -> {F.E.map(~F.Both<B, C>, ~B, ~F.Both.fst(B, C),
                       F.E.run(~F.Both<S, T>, ~A, ~F.Both<B, C>, ~(st => +x => F.par.step(~S, ~T, ~A, ~B, ~C, ~sa, ~sb, st, x)), rest, F.Both{s2, t2}))
                      == F.E.run(~S, ~A, ~B, ~sa, rest, s2) : F.Events(B)}
  {F.E.map(~F.Both<B, C>, ~B, ~F.Both.fst(B, C),
           F.E.push(F.Both<S, T>, F.Both<B, C>, u, F.par.b(S, T, B, C, s2, y, q),
                    v => F.E.run(~F.Both<S, T>, ~A, ~F.Both<B, C>, ~(st => +x => F.par.step(~S, ~T, ~A, ~B, ~C, ~sa, ~sb, st, x)), rest, v)))
     == F.Occ{u, y} <> F.E.run(~S, ~A, ~B, ~sa, rest, s2) : F.Events(B)}

def par.fst.l2(S, T, A, B, C, sa, sb, u, rest, s2, y, q, ih):
  match q:
    case (t2, z):
      cons_cong(F.Occ<B>, F.Occ{u, y},
                F.E.map(~F.Both<B, C>, ~B, ~F.Both.fst(B, C),
                  F.E.run(~F.Both<S, T>, ~A, ~F.Both<B, C>, ~(st => +x => F.par.step(~S, ~T, ~A, ~B, ~C, ~sa, ~sb, st, x)), rest, F.Both{s2, t2})),
                F.E.run(~S, ~A, ~B, ~sa, rest, s2),
                ih(t2))

law par.fst.l1:
  for ~S: Data
  for ~T: Data
  for ~A: Data
  for ~B: Data
  for ~C: Data
  for ~sa: S -> A -> S & B
  for ~sb: T -> A -> T & C
  for -u: U32
  for -rest: F.Events(A)
  for t: T
  for x: A
  for p: S & B
  for ih: @s2:S -> @t2:T -> {F.E.map(~F.Both<B, C>, ~B, ~F.Both.fst(B, C),
                                F.E.run(~F.Both<S, T>, ~A, ~F.Both<B, C>, ~(st => +x => F.par.step(~S, ~T, ~A, ~B, ~C, ~sa, ~sb, st, x)), rest, F.Both{s2, t2}))
                               == F.E.run(~S, ~A, ~B, ~sa, rest, s2) : F.Events(B)}
  {F.E.map(~F.Both<B, C>, ~B, ~F.Both.fst(B, C),
           F.E.push(F.Both<S, T>, F.Both<B, C>, u, F.par.a(~S, ~T, ~A, ~B, ~C, ~sb, t, x, p),
                    v => F.E.run(~F.Both<S, T>, ~A, ~F.Both<B, C>, ~(st => +x => F.par.step(~S, ~T, ~A, ~B, ~C, ~sa, ~sb, st, x)), rest, v)))
     == F.E.push(S, B, u, p, v => F.E.run(~S, ~A, ~B, ~sa, rest, v)) : F.Events(B)}

def par.fst.l1(S, T, A, B, C, sa, sb, u, rest, t, x, p, ih):
  match p:
    case (s2, y):
      par.fst.l2(S, T, A, B, C, sa, sb, u, rest, s2, y, sb(t, x), ih(s2))

def Laws.e_run_par_fst(S, T, A, B, C, sa, sb, e, s, t):
  match e:
    case Nil{}:
      {==}
    case Con{o, rest}:
      match o:
        case F.Occ{u, +x}:
          par.fst.l1(S, T, A, B, C, sa, sb, u, rest, t, x, sa(s, x),
                     s2 => t2 => Laws.e_run_par_fst(S, T, A, B, C, sa, sb, rest, s2, t2))

# par: the second half

law par.snd.l2:
  for ~S: Data
  for ~T: Data
  for ~A: Data
  for ~B: Data
  for ~C: Data
  for ~sa: S -> A -> S & B
  for ~sb: T -> A -> T & C
  for -u: U32
  for -rest: F.Events(A)
  for -s2: S
  for -y: B
  for q: T & C
  for ih: @t2:T -> {F.E.map(~F.Both<B, C>, ~C, ~F.Both.snd(B, C),
                       F.E.run(~F.Both<S, T>, ~A, ~F.Both<B, C>, ~(st => +x => F.par.step(~S, ~T, ~A, ~B, ~C, ~sa, ~sb, st, x)), rest, F.Both{s2, t2}))
                      == F.E.run(~T, ~A, ~C, ~sb, rest, t2) : F.Events(C)}
  {F.E.map(~F.Both<B, C>, ~C, ~F.Both.snd(B, C),
           F.E.push(F.Both<S, T>, F.Both<B, C>, u, F.par.b(S, T, B, C, s2, y, q),
                    v => F.E.run(~F.Both<S, T>, ~A, ~F.Both<B, C>, ~(st => +x => F.par.step(~S, ~T, ~A, ~B, ~C, ~sa, ~sb, st, x)), rest, v)))
     == F.E.push(T, C, u, q, v => F.E.run(~T, ~A, ~C, ~sb, rest, v)) : F.Events(C)}

def par.snd.l2(S, T, A, B, C, sa, sb, u, rest, s2, y, q, ih):
  match q:
    case (t2, z):
      cons_cong(F.Occ<C>, F.Occ{u, z},
                F.E.map(~F.Both<B, C>, ~C, ~F.Both.snd(B, C),
                  F.E.run(~F.Both<S, T>, ~A, ~F.Both<B, C>, ~(st => +x => F.par.step(~S, ~T, ~A, ~B, ~C, ~sa, ~sb, st, x)), rest, F.Both{s2, t2})),
                F.E.run(~T, ~A, ~C, ~sb, rest, t2),
                ih(t2))

law par.snd.l1:
  for ~S: Data
  for ~T: Data
  for ~A: Data
  for ~B: Data
  for ~C: Data
  for ~sa: S -> A -> S & B
  for ~sb: T -> A -> T & C
  for -u: U32
  for -rest: F.Events(A)
  for t: T
  for x: A
  for p: S & B
  for ih: @s2:S -> @t2:T -> {F.E.map(~F.Both<B, C>, ~C, ~F.Both.snd(B, C),
                                F.E.run(~F.Both<S, T>, ~A, ~F.Both<B, C>, ~(st => +x => F.par.step(~S, ~T, ~A, ~B, ~C, ~sa, ~sb, st, x)), rest, F.Both{s2, t2}))
                               == F.E.run(~T, ~A, ~C, ~sb, rest, t2) : F.Events(C)}
  {F.E.map(~F.Both<B, C>, ~C, ~F.Both.snd(B, C),
           F.E.push(F.Both<S, T>, F.Both<B, C>, u, F.par.a(~S, ~T, ~A, ~B, ~C, ~sb, t, x, p),
                    v => F.E.run(~F.Both<S, T>, ~A, ~F.Both<B, C>, ~(st => +x => F.par.step(~S, ~T, ~A, ~B, ~C, ~sa, ~sb, st, x)), rest, v)))
     == F.E.push(T, C, u, sb(t, x), v => F.E.run(~T, ~A, ~C, ~sb, rest, v)) : F.Events(C)}

def par.snd.l1(S, T, A, B, C, sa, sb, u, rest, t, x, p, ih):
  match p:
    case (s2, y):
      par.snd.l2(S, T, A, B, C, sa, sb, u, rest, s2, y, sb(t, x), ih(s2))

def Laws.e_run_par_snd(S, T, A, B, C, sa, sb, e, s, t):
  match e:
    case Nil{}:
      {==}
    case Con{o, rest}:
      match o:
        case F.Occ{u, +x}:
          par.snd.l1(S, T, A, B, C, sa, sb, u, rest, t, x, sa(s, x),
                     s2 => t2 => Laws.e_run_par_snd(S, T, A, B, C, sa, sb, rest, s2, t2))

# snapshot: the data form

def Laws.snapshot_stepper(A, B, C, f, x, d, e):
  match e:
    case Nil{}:
      {==}
    case Con{o, rest}:
      match o:
        case F.Occ{t, a}:
          cons_cong(F.Occ<C>, F.Occ{t, f(a, F.B.stepper.at(B, d, t, x))},
                    F.E.snapshot(~A, ~B, ~C, ~f, ~F.B.stepper(B, x, d), rest),
                    F.E.snapshot.stepper(~A, ~B, ~C, ~f, rest, x, d),
                    Laws.snapshot_stepper(A, B, C, f, x, d, rest))

# snapshot: the machine

# Both halves of a conjunction that holds.
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

# A stepper keeps its value while no value is set before t.
law snap.stay.if:
  for -A: Data
  for -x: A
  for -X: A
  for b: Bool
  for -c: Bool
  for h: {(Bool.not(b) && c) == True{} : Bool}
  {F.B.stepper.if(A, w => X, x, b) == x : A}

def snap.stay.if(A, x, X, b, c, h):
  match b:
    case True{}:
      clash({F.B.stepper.if(A, w => X, x, True{}) == x : A}, h)
    case False{}:
      {==}

law snap.stay:
  for -B: Data
  for d: F.Events(B)
  for +t: U32
  for -x: B
  for h: {F.E.none_before(B, d, t) == True{} : Bool}
  {F.B.stepper.at(B, d, t, x) == x : B}

def snap.stay(B, d, t, x, h):
  match d:
    case Nil{}:
      {==}
    case Con{o, +rest}:
      match o:
        case F.Occ{+u, y}:
          snap.stay.if(B, x, F.B.stepper.at(B, rest, t, y), U32.is_lt(u, t), F.E.none_before(B, rest, t), h)

# A value set before every sample is the stepper's value at each of them.
law snap.shift.if:
  for ~A: Data
  for ~B: Data
  for ~C: Data
  for ~f: A -> B -> C
  for -t: U32
  for -a: A
  for -s: B
  for -X: B
  for -L: F.Events(C)
  for -R: F.Events(C)
  for b: Bool
  for -c: Bool
  for h: {(b && c) == True{} : Bool}
  for ih: {c == True{} : Bool} -> {L == R : F.Events(C)}
  {F.Occ{t, f(a, F.B.stepper.if(B, w => X, s, b))} <> L == F.Occ{t, f(a, X)} <> R : F.Events(C)}

def snap.shift.if(A, B, C, f, t, a, s, X, L, R, b, c, h, ih):
  match b:
    case True{}:
      cons_cong(F.Occ<C>, F.Occ{t, f(a, X)}, L, R, ih(h))
    case False{}:
      clash({F.Occ{t, f(a, F.B.stepper.if(B, w => X, s, False{}))} <> L == F.Occ{t, f(a, X)} <> R : F.Events(C)}, h)

law snap.shift:
  for ~A: Data
  for ~B: Data
  for ~C: Data
  for ~f: A -> B -> C
  for fs: F.Events(A)
  for +u: U32
  for -s: B
  for -v: B
  for -ds: F.Events(B)
  for h: {F.E.all_after(A, fs, u) == True{} : Bool}
  {F.E.snapshot.stepper(~A, ~B, ~C, ~f, fs, s, F.Occ{u, v} <> ds) == F.E.snapshot.stepper(~A, ~B, ~C, ~f, fs, v, ds) : F.Events(C)}

def snap.shift(A, B, C, f, fs, u, s, v, ds, h):
  match fs:
    case Nil{}:
      {==}
    case Con{o, +rest}:
      match o:
        case F.Occ{+t, a}:
          snap.shift.if(A, B, C, f, t, a, s, F.B.stepper.at(B, ds, t, v),
                        F.E.snapshot.stepper(~A, ~B, ~C, ~f, rest, s, F.Occ{u, v} <> ds),
                        F.E.snapshot.stepper(~A, ~B, ~C, ~f, rest, v, ds),
                        U32.is_lt(u, t), F.E.all_after(A, rest, u), h,
                        h2 => snap.shift(A, B, C, f, rest, u, s, v, ds, h2))

def Laws.e_run_snap(A, B, C, f, i, x, ok):
  match i:
    case Nil{}:
      {==}
    case Con{o, +rest}:
      match o:
        case F.Occ{+t, s}:
          match s:
            case F.Fire{a}:
              and.both(F.E.none_before(B, F.E.sets(A, B, rest), t), F.snap.ok(A, B, rest),
                {F.Occ{t, f(a, x)} <> F.E.justs(C, F.E.run(~B, ~F.Side<A, B>, ~Maybe<&2, C>, ~(+s => i => F.snap.step(~A, ~B, ~C, ~f, s, i)), rest, x))
                   == F.Occ{t, f(a, F.B.stepper.at(B, F.E.sets(A, B, rest), t, x))}
                      <> F.E.snapshot.stepper(~A, ~B, ~C, ~f, F.E.fires(A, B, rest), x, F.E.sets(A, B, rest)) : F.Events(C)},
                ok,
                h1 => h2 =>
                  Equal.trans(F.Events(C),
                    F.Occ{t, f(a, x)} <> F.E.justs(C, F.E.run(~B, ~F.Side<A, B>, ~Maybe<&2, C>, ~(+s => i => F.snap.step(~A, ~B, ~C, ~f, s, i)), rest, x)),
                    F.Occ{t, f(a, x)} <> F.E.snapshot.stepper(~A, ~B, ~C, ~f, F.E.fires(A, B, rest), x, F.E.sets(A, B, rest)),
                    F.Occ{t, f(a, F.B.stepper.at(B, F.E.sets(A, B, rest), t, x))}
                      <> F.E.snapshot.stepper(~A, ~B, ~C, ~f, F.E.fires(A, B, rest), x, F.E.sets(A, B, rest)),
                    cons_cong(F.Occ<C>, F.Occ{t, f(a, x)},
                      F.E.justs(C, F.E.run(~B, ~F.Side<A, B>, ~Maybe<&2, C>, ~(+s => i => F.snap.step(~A, ~B, ~C, ~f, s, i)), rest, x)),
                      F.E.snapshot.stepper(~A, ~B, ~C, ~f, F.E.fires(A, B, rest), x, F.E.sets(A, B, rest)),
                      Laws.e_run_snap(A, B, C, f, rest, x, h2)),
                    Equal.cong(B, F.Events(C),
                      y => F.Occ{t, f(a, y)} <> F.E.snapshot.stepper(~A, ~B, ~C, ~f, F.E.fires(A, B, rest), x, F.E.sets(A, B, rest)),
                      x, F.B.stepper.at(B, F.E.sets(A, B, rest), t, x),
                      Equal.sym(B, F.B.stepper.at(B, F.E.sets(A, B, rest), t, x), x,
                        snap.stay(B, F.E.sets(A, B, rest), t, x, h1)))))
            case F.Set{v}:
              and.both(F.E.all_after(A, F.E.fires(A, B, rest), t), F.snap.ok(A, B, rest),
                {F.E.justs(C, F.E.run(~B, ~F.Side<A, B>, ~Maybe<&2, C>, ~(+s => i => F.snap.step(~A, ~B, ~C, ~f, s, i)), rest, v))
                   == F.E.snapshot.stepper(~A, ~B, ~C, ~f, F.E.fires(A, B, rest), x, F.Occ{t, v} <> F.E.sets(A, B, rest)) : F.Events(C)},
                ok,
                h1 => h2 =>
                  Equal.trans(F.Events(C),
                    F.E.justs(C, F.E.run(~B, ~F.Side<A, B>, ~Maybe<&2, C>, ~(+s => i => F.snap.step(~A, ~B, ~C, ~f, s, i)), rest, v)),
                    F.E.snapshot.stepper(~A, ~B, ~C, ~f, F.E.fires(A, B, rest), v, F.E.sets(A, B, rest)),
                    F.E.snapshot.stepper(~A, ~B, ~C, ~f, F.E.fires(A, B, rest), x, F.Occ{t, v} <> F.E.sets(A, B, rest)),
                    Laws.e_run_snap(A, B, C, f, rest, v, h2),
                    Equal.sym(F.Events(C),
                      F.E.snapshot.stepper(~A, ~B, ~C, ~f, F.E.fires(A, B, rest), x, F.Occ{t, v} <> F.E.sets(A, B, rest)),
                      F.E.snapshot.stepper(~A, ~B, ~C, ~f, F.E.fires(A, B, rest), v, F.E.sets(A, B, rest)),
                      snap.shift(A, B, C, f, F.E.fires(A, B, rest), t, x, v, F.E.sets(A, B, rest), h1))))

# switch

law switch.fire:
  for ~K: Data
  for ~S: Data
  for ~A: Data
  for ~B: Data
  for ~init: K -> S
  for ~step: K -> S -> A -> S & B
  for -t: U32
  for -rest: F.Events(F.Side<A, K>)
  for -k: K
  for p: S & B
  for ih: @s2:S -> {F.E.justs(B, F.E.run(~F.Both<K, S>, ~F.Side<A, K>, ~Maybe<&2, B>,
                                         ~(st => j => F.switch.step(~K, ~S, ~A, ~B, ~init, ~step, st, j)), rest, F.Both{k, s2}))
                      == F.E.switched(~K, ~S, ~A, ~B, ~init, ~step, rest, k, s2) : F.Events(B)}
  {F.E.justs(B, F.E.push(F.Both<K, S>, Maybe<&2, B>, t, F.switch.out(K, S, B, F.switch.keep(K, S, B, k, p)),
                         v => F.E.run(~F.Both<K, S>, ~F.Side<A, K>, ~Maybe<&2, B>,
                                      ~(st => j => F.switch.step(~K, ~S, ~A, ~B, ~init, ~step, st, j)), rest, v)))
     == List.append(&2, F.Occ<B>,
          F.E.push(F.Both<K, S>, B, t, F.switch.keep(K, S, B, k, p),
                   v => F.E.run(~F.Both<K, S>, ~A, ~B, ~F.switch.run(~K, ~S, ~A, ~B, ~step), F.E.upto(A, K, rest), v)),
          F.E.switched.after(~K, ~S, ~A, ~B, ~init, ~step, rest)) : F.Events(B)}

def switch.fire(K, S, A, B, init, step, t, rest, k, p, ih):
  match p:
    case (s2, y):
      cons_cong(F.Occ<B>, F.Occ{t, y},
                F.E.justs(B, F.E.run(~F.Both<K, S>, ~F.Side<A, K>, ~Maybe<&2, B>,
                                     ~(st => j => F.switch.step(~K, ~S, ~A, ~B, ~init, ~step, st, j)), rest, F.Both{k, s2})),
                F.E.switched(~K, ~S, ~A, ~B, ~init, ~step, rest, k, s2),
                ih(s2))

def Laws.e_run_switch(K, S, A, B, init, step, i, k, s):
  match i:
    case Nil{}:
      {==}
    case Con{o, rest}:
      match o:
        case F.Occ{t, x}:
          match x:
            case F.Fire{a}:
              switch.fire(K, S, A, B, init, step, t, rest, k, step(k, s, a),
                          s2 => Laws.e_run_switch(K, S, A, B, init, step, rest, k, s2))
            case F.Set{+k2}:
              Laws.e_run_switch(K, S, A, B, init, step, rest, k2, init(k2))

# Elliott's basic laws
# --------------------

def Laws.b_ap_id(A, v, t):
  {==}

def Laws.b_ap_comp(A, B, C, u, v, w, t):
  {==}

def Laws.b_ap_interchange(A, B, u, y, t):
  {==}

def Laws.b_map_ap(A, B, f, b, t):
  {==}

def Laws.b_time(t):
  {==}

def Laws.e_map_never(A, B, f):
  {==}

def Laws.e_map_occ(A, B, f, t, a, e):
  {==}

def Laws.e_snapshot_never(A, B, C, f, b):
  {==}

def Laws.e_snapshot_occ(A, B, C, f, b, t, a, e):
  {==}

def Laws.switcher_stepper(K, A, fam, k, e, t):
  {==}

# stepper at one occurrence: before t, the stepper goes on with its value, as
# the last of the occurrences before t does; at or after t, both stop at x.
law stepper.before.if:
  for -A: Data
  for -x: A
  for -y: A
  for -u: U32
  for -X: A
  for -R: F.Events(A)
  for b: Bool
  for ih: {X == F.E.last(A, R, y) : A}
  {F.B.stepper.if(A, w => X, x, b) == F.E.last(A, F.E.before.if(A, w => F.Occ{u, y} <> R, b), x) : A}

def stepper.before.if(A, x, y, u, X, R, b, ih):
  match b:
    case True{}:
      ih
    case False{}:
      {==}

def Laws.stepper_before(A, e, t, x):
  match e:
    case Nil{}:
      {==}
    case Con{o, rest}:
      match o:
        case F.Occ{u, y}:
          stepper.before.if(A, x, y, u, F.B.stepper.at(A, rest, t, y), F.E.before(A, rest, t), U32.is_lt(u, t),
                            Laws.stepper_before(A, rest, t, y))
