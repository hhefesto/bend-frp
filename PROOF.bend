# The proofs of LAWS.bend. Nothing here is trusted: `bend PROOF.bend` checks
# every def.

import Base
import ./Frp.bend as F
import ./Dyn.bend as D
import ./Ops.bend as Op
import ./LAWS.bend as Laws
import ./proof/Logic.bend as L
import ./proof/Order.bend as O
import ./proof/Events.bend as Ev
import ./proof/Dyn.bend as Dp
import ./proof/Ops.bend as Pp

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
          L.cons_cong(F.Occ<A>, F.Occ{t, x}, F.E.map(~A, ~A, ~F.ident(A), rest), rest, Laws.e_map_id(A, rest))

def Laws.e_map_comp(A, B, C, f, g, e):
  match e:
    case Nil{}:
      {==}
    case Con{o, rest}:
      match o:
        case F.Occ{t, x}:
          L.cons_cong(F.Occ<C>, F.Occ{t, g(f(x))},
                    F.E.map(~B, ~C, ~g, F.E.map(~A, ~B, ~f, rest)), F.E.map(~A, ~C, ~F.comp(~A, ~B, ~C, ~f, ~g), rest),
                    Laws.e_map_comp(A, B, C, f, g, rest))

def Laws.e_filter_all(A, e):
  match e:
    case Nil{}:
      {==}
    case Con{o, rest}:
      L.cons_cong(F.Occ<A>, o, F.E.filter(~A, ~F.always(A), rest), rest, Laws.e_filter_all(A, rest))

def Laws.e_merge_never_l(A, e):
  {==}

def Laws.e_merge_never_r(A, e):
  match e:
    case Nil{}:
      {==}
    case Con{x, xs}:
      L.cons_cong(F.Occ<A>, x, F.E.merge(A, xs, Nil{}), xs, Laws.e_merge_never_r(A, xs))

def Laws.e_run_lift(A, B, f, e, s):
  match e:
    case Nil{}:
      {==}
    case Con{o, rest}:
      match o:
        case F.Occ{t, x}:
          L.cons_cong(F.Occ<B>, F.Occ{t, f(x)},
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
          L.cons_cong(F.Occ<B>, F.Occ{t, n},
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
  for -u: F.Time
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
      L.cons_cong(F.Occ<C>, F.Occ{u, z},
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
  for -u: F.Time
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
  for -u: F.Time
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
  for -u: F.Time
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
        L.cons_cong(F.Occ<C>, F.Occ{u, y},
                  F.E.flat(C, F.E.push(T, List<&2, C>, u, F.each.go(~T, ~B, ~C, ~sb, more, t2), k)),
                  F.E.run(~T, ~B, ~C, ~sb, F.E.spread(B, u, more, tail), t2),
                  ih(t2)))

law each.in:
  for ~T: Data
  for ~B: Data
  for ~C: Data
  for ~sb: T -> B -> T & C
  for -u: F.Time
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

def Laws.e_merge_first(A, t, a, xs, u, b, ys, h):
  Ev.merge_first(A, t, a, xs, u, b, ys, h)

def Laws.e_merge_later(A, t, a, xs, u, b, ys, h):
  Ev.merge_later(A, t, a, xs, u, b, ys, h)

def Laws.e_filter_never(A, p):
  {==}

def Laws.e_filter_keep(A, p, t, a, e, h):
  Ev.keep.hit(A, F.Occ{t, a}, F.E.filter(~A, ~p, e), p(a), h)

def Laws.e_filter_drop(A, p, t, a, e, h):
  Ev.keep.miss(A, F.Occ{t, a}, F.E.filter(~A, ~p, e), p(a), h)


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
      L.clash({F.B.stepper.if(A, w => X, x, False{}) == Y : A}, h)

def Laws.stepper_after(A, e, t, x, all):
  match e:
    case Nil{}:
      {==}
    case Con{o, rest}:
      match o:
        case F.Occ{u, y}:
          stepper.if(A, x, F.B.stepper.at(A, rest, t, y), F.E.last(A, rest, y), F.Time.lt(u, t),
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
  for -u: F.Time
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
      L.cons_cong(F.Occ<B>, F.Occ{u, y},
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
  for -u: F.Time
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
  for -u: F.Time
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
      L.cons_cong(F.Occ<C>, F.Occ{u, z},
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
  for -u: F.Time
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
          L.cons_cong(F.Occ<C>, F.Occ{t, f(a, F.B.stepper.at(B, d, t, x))},
                    F.E.snapshot(~A, ~B, ~C, ~f, ~F.B.stepper(B, x, d), rest),
                    F.E.snapshot.stepper(~A, ~B, ~C, ~f, rest, x, d),
                    Laws.snapshot_stepper(A, B, C, f, x, d, rest))

# snapshot: the machine

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
      L.clash({F.B.stepper.if(A, w => X, x, True{}) == x : A}, h)
    case False{}:
      {==}

law snap.stay:
  for -B: Data
  for d: F.Events(B)
  for +t: F.Time
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
          snap.stay.if(B, x, F.B.stepper.at(B, rest, t, y), F.Time.lt(u, t), F.E.none_before(B, rest, t), h)

# A value set before every sample is the stepper's value at each of them.
law snap.shift.if:
  for ~A: Data
  for ~B: Data
  for ~C: Data
  for ~f: A -> B -> C
  for -t: F.Time
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
      L.cons_cong(F.Occ<C>, F.Occ{t, f(a, X)}, L, R, ih(h))
    case False{}:
      L.clash({F.Occ{t, f(a, F.B.stepper.if(B, w => X, s, False{}))} <> L == F.Occ{t, f(a, X)} <> R : F.Events(C)}, h)

law snap.shift:
  for ~A: Data
  for ~B: Data
  for ~C: Data
  for ~f: A -> B -> C
  for fs: F.Events(A)
  for +u: F.Time
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
                        F.Time.lt(u, t), F.E.all_after(A, rest, u), h,
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
              L.and.both(F.E.none_before(B, F.E.sets(A, B, rest), t), F.snap.ok(A, B, rest),
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
                    L.cons_cong(F.Occ<C>, F.Occ{t, f(a, x)},
                      F.E.justs(C, F.E.run(~B, ~F.Side<A, B>, ~Maybe<&2, C>, ~(+s => i => F.snap.step(~A, ~B, ~C, ~f, s, i)), rest, x)),
                      F.E.snapshot.stepper(~A, ~B, ~C, ~f, F.E.fires(A, B, rest), x, F.E.sets(A, B, rest)),
                      Laws.e_run_snap(A, B, C, f, rest, x, h2)),
                    Equal.cong(B, F.Events(C),
                      y => F.Occ{t, f(a, y)} <> F.E.snapshot.stepper(~A, ~B, ~C, ~f, F.E.fires(A, B, rest), x, F.E.sets(A, B, rest)),
                      x, F.B.stepper.at(B, F.E.sets(A, B, rest), t, x),
                      Equal.sym(B, F.B.stepper.at(B, F.E.sets(A, B, rest), t, x), x,
                        snap.stay(B, F.E.sets(A, B, rest), t, x, h1)))))
            case F.Set{v}:
              L.and.both(F.E.all_after(A, F.E.fires(A, B, rest), t), F.snap.ok(A, B, rest),
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
  for -t: F.Time
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
      L.cons_cong(F.Occ<B>, F.Occ{t, y},
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
  for -u: F.Time
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
          stepper.before.if(A, x, y, u, F.B.stepper.at(A, rest, t, y), F.E.before(A, rest, t), F.Time.lt(u, t),
                            Laws.stepper_before(A, rest, t, y))

# Time
# ----

def Laws.time_lt_irrefl(t):
  O.lt_irrefl(t)

def Laws.time_lt_trans(a, b, c, h1, h2):
  O.lt_trans(a, b, c, h1, h2)

def Laws.time_lt_total(a, b, h1, h2):
  O.lt_total(a, b, h1, h2)

def Laws.time_tick(t, h):
  O.tick_lt(t, h)

def Laws.time_after(last, now, h):
  O.after_lt(last, now, h)

def Laws.time_after_clock(last, now, h):
  O.after_now(last, now, h)

def Laws.b_warp_id(A, b, t):
  {==}

def Laws.b_warp_comp(A, f, g, b, t):
  {==}

def Laws.b_warp_time(f, t):
  {==}

def Laws.b_delay_warp(A, d, b, t):
  {==}

def Laws.b_faster_warp(A, k, b, t):
  {==}

# Time order
# ----------

def Laws.e_map_ordered(A, B, f, e):
  Ev.map_ordered(A, B, f, e)

def Laws.e_filter_ordered(A, p, e, h):
  Ev.filter_ordered(A, p, e, h)

def Laws.e_merge_ordered(A, e1, e2, h1, h2):
  Ev.merge_ordered(A, e1, e2, h1, h2)

def Laws.e_accum_ordered(A, B, f, e, x):
  Ev.accum_ordered(A, B, f, e, x)

def Laws.e_snapshot_ordered(A, B, C, f, b, e):
  Ev.snapshot_ordered(A, B, C, f, b, e)

def Laws.e_run_ordered(S, A, B, step, e, s):
  Ev.run_ordered(S, A, B, step, e, s)

def Laws.e_justs_ordered(C, e, h):
  Ev.justs_ordered(C, e, h)

def Laws.e_flat_ordered(A, e, h):
  Ev.flat_ordered(A, e, h)

def Laws.e_merge_assoc(A, a, b, c):
  Ev.merge_assoc(A, a, b, c)

# Dynamic values
# --------------

def Laws.dyn_hold_current(A, x, e, t):
  {==}

def Laws.dyn_hold_updated(A, x, e):
  {==}

def Laws.dyn_fold_current(A, B, f, e, x, t):
  Dp.fold_at(A, B, f, e, t, x)

def Laws.dyn_fold_updated(A, B, f, e, x):
  {==}

def Laws.dyn_pure_current(A, x, t):
  {==}

def Laws.dyn_pure_updated(A, x):
  {==}

def Laws.dyn_map_current(A, B, f, d, t):
  match d:
    case D.Dyn{+x, e}:
      Dp.map_at(A, B, f, e, t, x)

def Laws.dyn_map_updated(A, B, f, d):
  match d:
    case D.Dyn{x, e}:
      {==}

def Laws.dyn_map_id(A, d):
  match d:
    case D.Dyn{x, e}:
      Equal.cong(F.Events(A), D.Dyn<A>, z => D.Dyn{x, z}, F.E.map(~A, ~A, ~F.ident(A), e), e, Laws.e_map_id(A, e))

def Laws.dyn_map_comp(A, B, C, f, g, d):
  match d:
    case D.Dyn{x, e}:
      Equal.cong(F.Events(C), D.Dyn<C>, z => D.Dyn{g(f(x)), z},
        F.E.map(~B, ~C, ~g, F.E.map(~A, ~B, ~f, e)), F.E.map(~A, ~C, ~F.comp(~A, ~B, ~C, ~f, ~g), e),
        Laws.e_map_comp(A, B, C, f, g, e))

def Laws.dyn_zip_current(A, B, da, db, t):
  match da db:
    case D.Dyn{+a, ea} D.Dyn{+b, eb}:
      Dp.zip_at(A, B, ea, eb, a, b, t)

def Laws.dyn_zip_with_current(A, B, C, f, da, db, t):
  match da db:
    case D.Dyn{+a, +ea} D.Dyn{+b, +eb}:
      Equal.trans(C,
        F.B.stepper.at(C, F.E.map(~F.Both<A, B>, ~C, ~D.Dyn.zip_with.app(~A, ~B, ~C, ~f), D.Dyn.zip.go(A, B, ea, eb, a, b)), t,
          D.Dyn.zip_with.app(~A, ~B, ~C, ~f, F.Both{a, b})),
        D.Dyn.zip_with.app(~A, ~B, ~C, ~f, F.B.stepper.at(F.Both<A, B>, D.Dyn.zip.go(A, B, ea, eb, a, b), t, F.Both{a, b})),
        f(F.B.stepper.at(A, ea, t, a), F.B.stepper.at(B, eb, t, b)),
        Dp.map_at(F.Both<A, B>, C, D.Dyn.zip_with.app(~A, ~B, ~C, ~f), D.Dyn.zip.go(A, B, ea, eb, a, b), t, F.Both{a, b}),
        Equal.cong(F.Both<A, B>, C, p => D.Dyn.zip_with.app(~A, ~B, ~C, ~f, p),
          F.B.stepper.at(F.Both<A, B>, D.Dyn.zip.go(A, B, ea, eb, a, b), t, F.Both{a, b}),
          F.Both{F.B.stepper.at(A, ea, t, a), F.B.stepper.at(B, eb, t, b)},
          Dp.zip_at(A, B, ea, eb, a, b, t)))

def Laws.dyn_join_current(A, dd, t):
  match dd:
    case D.Dyn{d0, ds}:
      match d0:
        case D.Dyn{+x0, +ic0}:
          Dp.join_at(A, ds, x0, ic0, t)

def Laws.dyn_join_pure(A, d):
  match d:
    case D.Dyn{x, ic}:
      {==}

def Laws.dyn_join_map_pure(A, d):
  match d:
    case D.Dyn{x, e}:
      Equal.cong(F.Events(A), D.Dyn<A>, z => D.Dyn{x, z},
        D.Dyn.join.go(A, F.E.map(~A, ~D.Dyn<A>, ~D.Dyn.pure(A), e), Nil{}), e, Dp.join_pure_at(A, e))

# More event combinators
# ----------------------

def Laws.e_merge_with_never_l(A, f, e):
  {==}

def Laws.e_merge_with_never_r(A, f, e):
  match e:
    case Nil{}:
      {==}
    case Con{F.Occ{t, a}, xs}:
      {==}

def Laws.e_merge_with_first(A, f, t, a, xs, u, b, ys, h):
  Pp.mw.lt(A, f, F.Time.cmp(t, u), t, a, u, b, xs, ys, O.is_lt_true(F.Time.cmp(t, u), h))

def Laws.e_merge_with_later(A, f, t, a, xs, u, b, ys, h):
  Pp.mw.gt(A, f, F.Time.cmp(t, u), t, a, u, b, xs, ys,
    Equal.trans(Cmp, F.Time.cmp(t, u), O.cmp.flip(F.Time.cmp(u, t)), GT{}, O.time_cmp_flip(t, u),
      Equal.cong(Cmp, Cmp, z => O.cmp.flip(z), F.Time.cmp(u, t), LT{}, O.is_lt_true(F.Time.cmp(u, t), h))))

def Laws.e_merge_with_same(A, f, t, a, xs, b, ys):
  Pp.mw.eq(A, f, F.Time.cmp(t, t), t, a, b, xs, ys, O.time_cmp_refl(t))

def Laws.e_leftmost_same(A, t, a, xs, b, ys):
  Pp.mw.eq(A, Op.E.left(A), F.Time.cmp(t, t), t, a, b, xs, ys, O.time_cmp_refl(t))

def Laws.e_difference_never(A, B, e):
  Pp.difference_never(A, B, e)

def Laws.e_difference_keep(A, B, t, a, e1, e2, h):
  Ev.keep.hit(A, F.Occ{t, a}, Op.E.difference(A, B, e1, e2), Bool.not(Op.E.occurs(B, e2, t)), L.not.of(Op.E.occurs(B, e2, t), h))

def Laws.e_difference_drop(A, B, t, a, e1, e2, h):
  Ev.keep.miss(A, F.Occ{t, a}, Op.E.difference(A, B, e1, e2), Bool.not(Op.E.occurs(B, e2, t)),
    Equal.cong(Bool, Bool, x => Bool.not(x), Op.E.occurs(B, e2, t), True{}, h))

def Laws.e_gate_keep(A, b, t, a, e, h):
  Pp.gate.hit(A, b(t), t, a, F.E.snapshot(~A, ~Bool, ~Maybe<&2, A>, ~Op.E.gate.pick(A), ~b, e), h)

def Laws.e_gate_drop(A, b, t, a, e, h):
  Pp.gate.miss(A, b(t), t, a, F.E.snapshot(~A, ~Bool, ~Maybe<&2, A>, ~Op.E.gate.pick(A), ~b, e), h)

def Laws.e_gate_ordered(A, b, e, h):
  Ev.justs_ordered(A, F.E.snapshot(~A, ~Bool, ~Maybe<&2, A>, ~Op.E.gate.pick(A), ~b, e),
    Equal.trans(Bool, F.E.ordered(Maybe<&2, A>, F.E.snapshot(~A, ~Bool, ~Maybe<&2, A>, ~Op.E.gate.pick(A), ~b, e)),
      F.E.ordered(A, e), True{}, Ev.snapshot_ordered(A, Bool, Maybe<&2, A>, Op.E.gate.pick(A), b, e), h))

def Laws.e_head_tail(A, e):
  match e:
    case Nil{}:
      {==}
    case Con{o, rest}:
      {==}

def Laws.e_take_drop(A, e, n):
  Pp.take_drop(A, e, n)

law take_zero:
  for -A: Data
  for e: F.Events(A)
  {Op.E.take(A, e, 0n) == Nil{} : F.Events(A)}

def take_zero(A, e):
  match e:
    case Nil{}:
      {==}
    case Con{o, rest}:
      {==}

def Laws.e_head_take(A, e):
  match e:
    case Nil{}:
      {==}
    case Con{o, rest}:
      L.cons_cong(F.Occ<A>, o, Nil{}, Op.E.take(A, rest, 0n), Equal.sym(F.Events(A), Op.E.take(A, rest, 0n), Nil{}, take_zero(A, rest)))

def Laws.e_take_ordered(A, e, n, h):
  Pp.take_ordered(A, e, n, h)

def Laws.e_drop_ordered(A, e, n, h):
  Pp.drop_ordered(A, e, n, h)

def Laws.e_select_hit(K, A, same, t, k2, a, e, k, h):
  Ev.keep.hit(A, F.Occ{t, a}, Op.E.select(~K, ~A, ~same, e, k), same(k2, k), h)

def Laws.e_select_miss(K, A, same, t, k2, a, e, k, h):
  Ev.keep.miss(A, F.Occ{t, a}, Op.E.select(~K, ~A, ~same, e, k), same(k2, k), h)

def Laws.e_select_ordered(K, A, same, e, k, h):
  Pp.select_ordered(K, A, same, e, k, h)

def Laws.e_fan_ordered(K, A, e, h):
  Ev.flat_ordered(F.Both<K, A>, e, h)

def Laws.e_delay_never(A, d):
  {==}

def Laws.e_delay_occ(A, d, t, a, e):
  {==}

def Laws.e_debounce_never(A, d):
  {==}

def Laws.e_debounce_keep(A, d, t, a, e, h):
  Ev.keep.hit(A, F.Occ{F.Time.add(t, d), a}, Op.E.debounce(A, d, e), Op.E.quiet(A, e, F.Time.add(t, d)), h)

def Laws.e_debounce_drop(A, d, t, a, e, h):
  Ev.keep.miss(A, F.Occ{F.Time.add(t, d), a}, Op.E.debounce(A, d, e), Op.E.quiet(A, e, F.Time.add(t, d)), h)

def Laws.e_throttle_first(A, d, t, a, e):
  {==}

def Laws.e_throttle_open(A, d, from, t, a, e, h):
  Pp.throttle.hit(A, F.Time.le(from, t), t, a, Op.E.throttle.from(A, e, d, F.Time.add(t, d)), Op.E.throttle.from(A, e, d, from), h)

def Laws.e_throttle_shut(A, d, from, t, a, e, h):
  Pp.throttle.miss(A, F.Time.le(from, t), t, a, Op.E.throttle.from(A, e, d, F.Time.add(t, d)), Op.E.throttle.from(A, e, d, from), h)
