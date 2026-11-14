import Base
import ../Frp.bend as F
import ./Logic.bend as L
import ./Order.bend as O

# Facts about events the laws are proved from: merge and filter at one
# occurrence, that the operations keep time order (E.ordered), and that merge
# is associative.

def mg(-A: Data, p: F.Events(A), q: F.Events(A)) -> F.Events(A):
  F.E.merge(A, p, q)

# merge at two first occurrences, once the order of their times is known
# ----------------------------------------------------------------------

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
      L.clash.flip({F.E.merge.pick(A, True{}, x, y, r => F.E.merge(A, xs, r), ys, j => F.E.merge.in(A, x, ys, r => j(r)))
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
      L.clash({F.E.merge.pick(A, False{}, x, y, r => F.E.merge(A, xs, r), ys, j => F.E.merge.in(A, x, ys, r => j(r)))
                 == y <> F.E.merge(A, x <> xs, ys) : F.Events(A)}, h)

law merge_first:
  for -A: Data
  for +t: F.Time
  for -a: A
  for -xs: F.Events(A)
  for +u: F.Time
  for -b: A
  for -ys: F.Events(A)
  for h: {F.Time.lt(u, t) == False{} : Bool}
  {F.E.merge(A, F.Occ{t, a} <> xs, F.Occ{u, b} <> ys) == F.Occ{t, a} <> F.E.merge(A, xs, F.Occ{u, b} <> ys) : F.Events(A)}

def merge_first(A, t, a, xs, u, b, ys, h):
  merge.first.if(A, F.Time.lt(u, t), F.Occ{t, a}, xs, F.Occ{u, b}, ys, h)

law merge_later:
  for -A: Data
  for +t: F.Time
  for -a: A
  for -xs: F.Events(A)
  for +u: F.Time
  for -b: A
  for -ys: F.Events(A)
  for h: {F.Time.lt(u, t) == True{} : Bool}
  {F.E.merge(A, F.Occ{t, a} <> xs, F.Occ{u, b} <> ys) == F.Occ{u, b} <> F.E.merge(A, F.Occ{t, a} <> xs, ys) : F.Events(A)}

def merge_later(A, t, a, xs, u, b, ys, h):
  merge.later.if(A, F.Time.lt(u, t), F.Occ{t, a}, xs, F.Occ{u, b}, ys, h)

law merge_never_r:
  for -A: Data
  for e: F.Events(A)
  {F.E.merge(A, e, Nil{}) == e : F.Events(A)}

def merge_never_r(A, e):
  match e:
    case Nil{}:
      {==}
    case Con{x, xs}:
      L.cons_cong(F.Occ<A>, x, F.E.merge(A, xs, Nil{}), xs, merge_never_r(A, xs))

# filter at one occurrence, once whether its value passes is known
# -----------------------------------------------------------------

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
      L.clash({F.E.keep(A, o, rest, False{}) == o <> rest : F.Events(A)}, h)

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
      L.clash.flip({F.E.keep(A, o, rest, True{}) == rest : F.Events(A)}, h)
    case False{}:
      {==}

# Time order
# ----------

# A lower bound may be lowered.
law from_lower:
  for -A: Data
  for e: F.Events(A)
  for +t: F.Time
  for +u: F.Time
  for h: {F.Time.le(t, u) == True{} : Bool}
  for h2: {F.E.ordered_from(A, e, u) == True{} : Bool}
  {F.E.ordered_from(A, e, t) == True{} : Bool}

def from_lower(A, e, t, u, h, h2):
  match e:
    case Nil{}:
      {==}
    case Con{F.Occ{+v, x}, rest}:
      L.and.both(F.Time.le(u, v), F.E.ordered_from(A, rest, v),
        {(F.Time.le(t, v) && F.E.ordered_from(A, rest, v)) == True{} : Bool}, h2,
        a => b => L.and.intro(F.Time.le(t, v), F.E.ordered_from(A, rest, v), O.le_trans(t, u, v, h, a), b))

# In time order from some time: in time order.
law from_ordered:
  for -A: Data
  for e: F.Events(A)
  for t: F.Time
  for h: {F.E.ordered_from(A, e, t) == True{} : Bool}
  {F.E.ordered(A, e) == True{} : Bool}

def from_ordered(A, e, t, h):
  match e:
    case Nil{}:
      {==}
    case Con{F.Occ{+v, x}, rest}:
      L.and.both(F.Time.le(t, v), F.E.ordered_from(A, rest, v), {F.E.ordered_from(A, rest, v) == True{} : Bool}, h,
        a => b => b)

# map keeps times

law map_from:
  for ~A: Data
  for ~B: Data
  for ~f: A -> B
  for e: F.Events(A)
  for +t: F.Time
  {F.E.ordered_from(B, F.E.map(~A, ~B, ~f, e), t) == F.E.ordered_from(A, e, t) : Bool}

def map_from(A, B, f, e, t):
  match e:
    case Nil{}:
      {==}
    case Con{F.Occ{+u, x}, rest}:
      Equal.cong(Bool, Bool, z => F.Time.le(t, u) && z,
        F.E.ordered_from(B, F.E.map(~A, ~B, ~f, rest), u), F.E.ordered_from(A, rest, u), map_from(A, B, f, rest, u))

law map_ordered:
  for ~A: Data
  for ~B: Data
  for ~f: A -> B
  for e: F.Events(A)
  {F.E.ordered(B, F.E.map(~A, ~B, ~f, e)) == F.E.ordered(A, e) : Bool}

def map_ordered(A, B, f, e):
  match e:
    case Nil{}:
      {==}
    case Con{F.Occ{+u, x}, rest}:
      map_from(A, B, f, rest, u)

# filter keeps some occurrences, in place

law filter_from:
  for ~A: Data
  for ~p: A -> Bool
  for e: F.Events(A)
  for +t: F.Time
  for h: {F.E.ordered_from(A, e, t) == True{} : Bool}
  {F.E.ordered_from(A, F.E.filter(~A, ~p, e), t) == True{} : Bool}

def filter_from(A, p, e, t, h):
  match e:
    case Nil{}:
      {==}
    case Con{F.Occ{+u, +x}, +rest}:
      L.and.both(F.Time.le(t, u), F.E.ordered_from(A, rest, u),
        {F.E.ordered_from(A, F.E.keep(A, F.Occ{u, x}, F.E.filter(~A, ~p, rest), p(x)), t) == True{} : Bool}, h,
        +a => +b => L.bool.cases(p(x),
          {F.E.ordered_from(A, F.E.keep(A, F.Occ{u, x}, F.E.filter(~A, ~p, rest), p(x)), t) == True{} : Bool},
          hp => Equal.trans(Bool,
            F.E.ordered_from(A, F.E.keep(A, F.Occ{u, x}, F.E.filter(~A, ~p, rest), p(x)), t),
            F.E.ordered_from(A, F.Occ{u, x} <> F.E.filter(~A, ~p, rest), t), True{},
            Equal.cong(F.Events(A), Bool, z => F.E.ordered_from(A, z, t),
              F.E.keep(A, F.Occ{u, x}, F.E.filter(~A, ~p, rest), p(x)), F.Occ{u, x} <> F.E.filter(~A, ~p, rest),
              keep.hit(A, F.Occ{u, x}, F.E.filter(~A, ~p, rest), p(x), hp)),
            L.and.intro(F.Time.le(t, u), F.E.ordered_from(A, F.E.filter(~A, ~p, rest), u), a, filter_from(A, p, rest, u, b))),
          hp => Equal.trans(Bool,
            F.E.ordered_from(A, F.E.keep(A, F.Occ{u, x}, F.E.filter(~A, ~p, rest), p(x)), t),
            F.E.ordered_from(A, F.E.filter(~A, ~p, rest), t), True{},
            Equal.cong(F.Events(A), Bool, z => F.E.ordered_from(A, z, t),
              F.E.keep(A, F.Occ{u, x}, F.E.filter(~A, ~p, rest), p(x)), F.E.filter(~A, ~p, rest),
              keep.miss(A, F.Occ{u, x}, F.E.filter(~A, ~p, rest), p(x), hp)),
            from_lower(A, F.E.filter(~A, ~p, rest), t, u, a, filter_from(A, p, rest, u, b)))))

law filter_ordered:
  for ~A: Data
  for ~p: A -> Bool
  for e: F.Events(A)
  for +h: {F.E.ordered(A, e) == True{} : Bool}
  {F.E.ordered(A, F.E.filter(~A, ~p, e)) == True{} : Bool}

def filter_ordered(A, p, e, h):
  match e:
    case Nil{}:
      {==}
    case Con{F.Occ{+u, +x}, +rest}:
      L.bool.cases(p(x), {F.E.ordered(A, F.E.keep(A, F.Occ{u, x}, F.E.filter(~A, ~p, rest), p(x))) == True{} : Bool},
        hp => Equal.trans(Bool,
          F.E.ordered(A, F.E.keep(A, F.Occ{u, x}, F.E.filter(~A, ~p, rest), p(x))),
          F.E.ordered(A, F.Occ{u, x} <> F.E.filter(~A, ~p, rest)), True{},
          Equal.cong(F.Events(A), Bool, z => F.E.ordered(A, z),
            F.E.keep(A, F.Occ{u, x}, F.E.filter(~A, ~p, rest), p(x)), F.Occ{u, x} <> F.E.filter(~A, ~p, rest),
            keep.hit(A, F.Occ{u, x}, F.E.filter(~A, ~p, rest), p(x), hp)),
          filter_from(A, p, rest, u, h)),
        hp => Equal.trans(Bool,
          F.E.ordered(A, F.E.keep(A, F.Occ{u, x}, F.E.filter(~A, ~p, rest), p(x))),
          F.E.ordered(A, F.E.filter(~A, ~p, rest)), True{},
          Equal.cong(F.Events(A), Bool, z => F.E.ordered(A, z),
            F.E.keep(A, F.Occ{u, x}, F.E.filter(~A, ~p, rest), p(x)), F.E.filter(~A, ~p, rest),
            keep.miss(A, F.Occ{u, x}, F.E.filter(~A, ~p, rest), p(x), hp)),
          from_ordered(A, F.E.filter(~A, ~p, rest), u, filter_from(A, p, rest, u, h))))

# merge interleaves two events in time order

law merge_from:
  for -A: Data
  for e1: F.Events(A)
  for e2: F.Events(A)
  for +t: F.Time
  for h1: {F.E.ordered_from(A, e1, t) == True{} : Bool}
  for h2: {F.E.ordered_from(A, e2, t) == True{} : Bool}
  {F.E.ordered_from(A, F.E.merge(A, e1, e2), t) == True{} : Bool}

def merge_from(A, e1, e2, t, h1, h2):
  match e1:
    case Nil{}:
      h2
    case Con{F.Occ{+tx, +a}, +xs}:
      match e2:
        case Nil{}:
          Equal.trans(Bool, F.E.ordered_from(A, F.E.merge(A, F.Occ{tx, a} <> xs, Nil{}), t),
            F.E.ordered_from(A, F.Occ{tx, a} <> xs, t), True{},
            Equal.cong(F.Events(A), Bool, z => F.E.ordered_from(A, z, t),
              F.E.merge(A, F.Occ{tx, a} <> xs, Nil{}), F.Occ{tx, a} <> xs, merge_never_r(A, F.Occ{tx, a} <> xs)),
            h1)
        case Con{F.Occ{+ty, +b}, +ys}:
          L.and.both(F.Time.le(t, tx), F.E.ordered_from(A, xs, tx),
            {F.E.ordered_from(A, F.E.merge(A, F.Occ{tx, a} <> xs, F.Occ{ty, b} <> ys), t) == True{} : Bool}, h1,
            +a1 => +b1 => L.and.both(F.Time.le(t, ty), F.E.ordered_from(A, ys, ty),
              {F.E.ordered_from(A, F.E.merge(A, F.Occ{tx, a} <> xs, F.Occ{ty, b} <> ys), t) == True{} : Bool}, h2,
              +a2 => +b2 => L.bool.cases(F.Time.lt(ty, tx),
                {F.E.ordered_from(A, F.E.merge(A, F.Occ{tx, a} <> xs, F.Occ{ty, b} <> ys), t) == True{} : Bool},
                +hl => Equal.trans(Bool,
                  F.E.ordered_from(A, F.E.merge(A, F.Occ{tx, a} <> xs, F.Occ{ty, b} <> ys), t),
                  F.E.ordered_from(A, F.Occ{ty, b} <> F.E.merge(A, F.Occ{tx, a} <> xs, ys), t), True{},
                  Equal.cong(F.Events(A), Bool, z => F.E.ordered_from(A, z, t),
                    F.E.merge(A, F.Occ{tx, a} <> xs, F.Occ{ty, b} <> ys), F.Occ{ty, b} <> F.E.merge(A, F.Occ{tx, a} <> xs, ys),
                    merge_later(A, tx, a, xs, ty, b, ys, hl)),
                  L.and.intro(F.Time.le(t, ty), F.E.ordered_from(A, F.E.merge(A, F.Occ{tx, a} <> xs, ys), ty), a2,
                    merge_from(A, F.Occ{tx, a} <> xs, ys, ty,
                      L.and.intro(F.Time.le(ty, tx), F.E.ordered_from(A, xs, tx), O.le_of_lt(ty, tx, hl), b1), b2))),
                +hl => Equal.trans(Bool,
                  F.E.ordered_from(A, F.E.merge(A, F.Occ{tx, a} <> xs, F.Occ{ty, b} <> ys), t),
                  F.E.ordered_from(A, F.Occ{tx, a} <> F.E.merge(A, xs, F.Occ{ty, b} <> ys), t), True{},
                  Equal.cong(F.Events(A), Bool, z => F.E.ordered_from(A, z, t),
                    F.E.merge(A, F.Occ{tx, a} <> xs, F.Occ{ty, b} <> ys), F.Occ{tx, a} <> F.E.merge(A, xs, F.Occ{ty, b} <> ys),
                    merge_first(A, tx, a, xs, ty, b, ys, hl)),
                  L.and.intro(F.Time.le(t, tx), F.E.ordered_from(A, F.E.merge(A, xs, F.Occ{ty, b} <> ys), tx), a1,
                    merge_from(A, xs, F.Occ{ty, b} <> ys, tx, b1,
                      L.and.intro(F.Time.le(tx, ty), F.E.ordered_from(A, ys, ty), L.not.of(F.Time.lt(ty, tx), hl), b2)))))))

law merge_ordered:
  for -A: Data
  for e1: F.Events(A)
  for e2: F.Events(A)
  for +h1: {F.E.ordered(A, e1) == True{} : Bool}
  for +h2: {F.E.ordered(A, e2) == True{} : Bool}
  {F.E.ordered(A, F.E.merge(A, e1, e2)) == True{} : Bool}

def merge_ordered(A, e1, e2, h1, h2):
  match e1:
    case Nil{}:
      h2
    case Con{F.Occ{+tx, +a}, +xs}:
      match e2:
        case Nil{}:
          Equal.trans(Bool, F.E.ordered(A, F.E.merge(A, F.Occ{tx, a} <> xs, Nil{})), F.E.ordered(A, F.Occ{tx, a} <> xs), True{},
            Equal.cong(F.Events(A), Bool, z => F.E.ordered(A, z),
              F.E.merge(A, F.Occ{tx, a} <> xs, Nil{}), F.Occ{tx, a} <> xs, merge_never_r(A, F.Occ{tx, a} <> xs)),
            h1)
        case Con{F.Occ{+ty, +b}, +ys}:
          L.bool.cases(F.Time.lt(ty, tx),
            {F.E.ordered(A, F.E.merge(A, F.Occ{tx, a} <> xs, F.Occ{ty, b} <> ys)) == True{} : Bool},
            +hl => Equal.trans(Bool,
              F.E.ordered(A, F.E.merge(A, F.Occ{tx, a} <> xs, F.Occ{ty, b} <> ys)),
              F.E.ordered(A, F.Occ{ty, b} <> F.E.merge(A, F.Occ{tx, a} <> xs, ys)), True{},
              Equal.cong(F.Events(A), Bool, z => F.E.ordered(A, z),
                F.E.merge(A, F.Occ{tx, a} <> xs, F.Occ{ty, b} <> ys), F.Occ{ty, b} <> F.E.merge(A, F.Occ{tx, a} <> xs, ys),
                merge_later(A, tx, a, xs, ty, b, ys, hl)),
              merge_from(A, F.Occ{tx, a} <> xs, ys, ty,
                L.and.intro(F.Time.le(ty, tx), F.E.ordered_from(A, xs, tx), O.le_of_lt(ty, tx, hl), h1), h2)),
            +hl => Equal.trans(Bool,
              F.E.ordered(A, F.E.merge(A, F.Occ{tx, a} <> xs, F.Occ{ty, b} <> ys)),
              F.E.ordered(A, F.Occ{tx, a} <> F.E.merge(A, xs, F.Occ{ty, b} <> ys)), True{},
              Equal.cong(F.Events(A), Bool, z => F.E.ordered(A, z),
                F.E.merge(A, F.Occ{tx, a} <> xs, F.Occ{ty, b} <> ys), F.Occ{tx, a} <> F.E.merge(A, xs, F.Occ{ty, b} <> ys),
                merge_first(A, tx, a, xs, ty, b, ys, hl)),
              merge_from(A, xs, F.Occ{ty, b} <> ys, tx, h1,
                L.and.intro(F.Time.le(tx, ty), F.E.ordered_from(A, ys, ty), L.not.of(F.Time.lt(ty, tx), hl), h2))))

# accum, snapshot and any machine keep times

law accum_from:
  for ~A: Data
  for ~B: Data
  for ~f: B -> A -> B
  for e: F.Events(A)
  for +x: B
  for +t: F.Time
  {F.E.ordered_from(B, F.E.accum(~A, ~B, ~f, e, x), t) == F.E.ordered_from(A, e, t) : Bool}

def accum_from(A, B, f, e, x, t):
  match e:
    case Nil{}:
      {==}
    case Con{F.Occ{+u, a}, rest}:
      +n = f(x, a)
      Equal.cong(Bool, Bool, z => F.Time.le(t, u) && z,
        F.E.ordered_from(B, F.E.accum(~A, ~B, ~f, rest, n), u), F.E.ordered_from(A, rest, u), accum_from(A, B, f, rest, n, u))

law accum_ordered:
  for ~A: Data
  for ~B: Data
  for ~f: B -> A -> B
  for e: F.Events(A)
  for +x: B
  {F.E.ordered(B, F.E.accum(~A, ~B, ~f, e, x)) == F.E.ordered(A, e) : Bool}

def accum_ordered(A, B, f, e, x):
  match e:
    case Nil{}:
      {==}
    case Con{F.Occ{+u, a}, rest}:
      +n = f(x, a)
      accum_from(A, B, f, rest, n, u)

law snapshot_from:
  for ~A: Data
  for ~B: Data
  for ~C: Data
  for ~f: A -> B -> C
  for ~b: F.Behavior(B)
  for e: F.Events(A)
  for +t: F.Time
  {F.E.ordered_from(C, F.E.snapshot(~A, ~B, ~C, ~f, ~b, e), t) == F.E.ordered_from(A, e, t) : Bool}

def snapshot_from(A, B, C, f, b, e, t):
  match e:
    case Nil{}:
      {==}
    case Con{F.Occ{+u, a}, rest}:
      Equal.cong(Bool, Bool, z => F.Time.le(t, u) && z,
        F.E.ordered_from(C, F.E.snapshot(~A, ~B, ~C, ~f, ~b, rest), u), F.E.ordered_from(A, rest, u),
        snapshot_from(A, B, C, f, b, rest, u))

law snapshot_ordered:
  for ~A: Data
  for ~B: Data
  for ~C: Data
  for ~f: A -> B -> C
  for ~b: F.Behavior(B)
  for e: F.Events(A)
  {F.E.ordered(C, F.E.snapshot(~A, ~B, ~C, ~f, ~b, e)) == F.E.ordered(A, e) : Bool}

def snapshot_ordered(A, B, C, f, b, e):
  match e:
    case Nil{}:
      {==}
    case Con{F.Occ{+u, a}, rest}:
      snapshot_from(A, B, C, f, b, rest, u)

law run.from.l:
  for ~S: Data
  for ~A: Data
  for ~B: Data
  for ~step: S -> A -> S & B
  for +u: F.Time
  for -rest: F.Events(A)
  for +t: F.Time
  for p: S & B
  for ih: @s2:S -> {F.E.ordered_from(B, F.E.run(~S, ~A, ~B, ~step, rest, s2), u) == F.E.ordered_from(A, rest, u) : Bool}
  {F.E.ordered_from(B, F.E.push(S, B, u, p, v => F.E.run(~S, ~A, ~B, ~step, rest, v)), t)
     == (F.Time.le(t, u) && F.E.ordered_from(A, rest, u)) : Bool}

def run.from.l(S, A, B, step, u, rest, t, p, ih):
  match p:
    case (s2, y):
      Equal.cong(Bool, Bool, z => F.Time.le(t, u) && z,
        F.E.ordered_from(B, F.E.run(~S, ~A, ~B, ~step, rest, s2), u), F.E.ordered_from(A, rest, u), ih(s2))

law run_from:
  for ~S: Data
  for ~A: Data
  for ~B: Data
  for ~step: S -> A -> S & B
  for e: F.Events(A)
  for s: S
  for +t: F.Time
  {F.E.ordered_from(B, F.E.run(~S, ~A, ~B, ~step, e, s), t) == F.E.ordered_from(A, e, t) : Bool}

def run_from(S, A, B, step, e, s, t):
  match e:
    case Nil{}:
      {==}
    case Con{F.Occ{+u, x}, rest}:
      run.from.l(S, A, B, step, u, rest, t, step(s, x), s2 => run_from(S, A, B, step, rest, s2, u))

law run.ordered.l:
  for ~S: Data
  for ~A: Data
  for ~B: Data
  for ~step: S -> A -> S & B
  for +u: F.Time
  for -rest: F.Events(A)
  for p: S & B
  for ih: @s2:S -> {F.E.ordered_from(B, F.E.run(~S, ~A, ~B, ~step, rest, s2), u) == F.E.ordered_from(A, rest, u) : Bool}
  {F.E.ordered(B, F.E.push(S, B, u, p, v => F.E.run(~S, ~A, ~B, ~step, rest, v))) == F.E.ordered_from(A, rest, u) : Bool}

def run.ordered.l(S, A, B, step, u, rest, p, ih):
  match p:
    case (s2, y):
      ih(s2)

law run_ordered:
  for ~S: Data
  for ~A: Data
  for ~B: Data
  for ~step: S -> A -> S & B
  for e: F.Events(A)
  for s: S
  {F.E.ordered(B, F.E.run(~S, ~A, ~B, ~step, e, s)) == F.E.ordered(A, e) : Bool}

def run_ordered(S, A, B, step, e, s):
  match e:
    case Nil{}:
      {==}
    case Con{F.Occ{+u, x}, rest}:
      run.ordered.l(S, A, B, step, u, rest, step(s, x), s2 => run_from(S, A, B, step, rest, s2, u))

# justs and flat: some occurrences dropped, some spread at one time

law justs_from:
  for -C: Data
  for e: F.Events(Maybe<&2, C>)
  for +t: F.Time
  for h: {F.E.ordered_from(Maybe<&2, C>, e, t) == True{} : Bool}
  {F.E.ordered_from(C, F.E.justs(C, e), t) == True{} : Bool}

def justs_from(C, e, t, h):
  match e:
    case Nil{}:
      {==}
    case Con{F.Occ{+u, m}, +rest}:
      match m:
        case None{}:
          L.and.both(F.Time.le(t, u), F.E.ordered_from(Maybe<&2, C>, rest, u),
            {F.E.ordered_from(C, F.E.justs(C, rest), t) == True{} : Bool}, h,
            a => b => from_lower(C, F.E.justs(C, rest), t, u, a, justs_from(C, rest, u, b)))
        case Some{c}:
          L.and.both(F.Time.le(t, u), F.E.ordered_from(Maybe<&2, C>, rest, u),
            {(F.Time.le(t, u) && F.E.ordered_from(C, F.E.justs(C, rest), u)) == True{} : Bool}, h,
            a => b => L.and.intro(F.Time.le(t, u), F.E.ordered_from(C, F.E.justs(C, rest), u), a, justs_from(C, rest, u, b)))

law justs_ordered:
  for -C: Data
  for e: F.Events(Maybe<&2, C>)
  for h: {F.E.ordered(Maybe<&2, C>, e) == True{} : Bool}
  {F.E.ordered(C, F.E.justs(C, e)) == True{} : Bool}

def justs_ordered(C, e, h):
  match e:
    case Nil{}:
      {==}
    case Con{F.Occ{+u, m}, +rest}:
      match m:
        case None{}:
          from_ordered(C, F.E.justs(C, rest), u, justs_from(C, rest, u, h))
        case Some{c}:
          justs_from(C, rest, u, h)

law spread_from:
  for -A: Data
  for xs: List<&2, A>
  for +u: F.Time
  for r: F.Events(A)
  for +t: F.Time
  for h: {F.Time.le(t, u) == True{} : Bool}
  for h2: {F.E.ordered_from(A, r, u) == True{} : Bool}
  {F.E.ordered_from(A, F.E.spread(A, u, xs, r), t) == True{} : Bool}

def spread_from(A, xs, u, r, t, h, h2):
  match xs:
    case Nil{}:
      from_lower(A, r, t, u, h, h2)
    case Con{x, more}:
      L.and.intro(F.Time.le(t, u), F.E.ordered_from(A, F.E.spread(A, u, more, r), u), h,
        spread_from(A, more, u, r, u, O.le_refl(u), h2))

law flat_from:
  for -A: Data
  for e: F.Events(List<&2, A>)
  for +t: F.Time
  for h: {F.E.ordered_from(List<&2, A>, e, t) == True{} : Bool}
  {F.E.ordered_from(A, F.E.flat(A, e), t) == True{} : Bool}

def flat_from(A, e, t, h):
  match e:
    case Nil{}:
      {==}
    case Con{F.Occ{+u, xs}, +rest}:
      L.and.both(F.Time.le(t, u), F.E.ordered_from(List<&2, A>, rest, u),
        {F.E.ordered_from(A, F.E.spread(A, u, xs, F.E.flat(A, rest)), t) == True{} : Bool}, h,
        a => b => spread_from(A, xs, u, F.E.flat(A, rest), t, a, flat_from(A, rest, u, b)))

law spread_ordered:
  for -A: Data
  for xs: List<&2, A>
  for +u: F.Time
  for r: F.Events(A)
  for h: {F.E.ordered_from(A, r, u) == True{} : Bool}
  {F.E.ordered(A, F.E.spread(A, u, xs, r)) == True{} : Bool}

def spread_ordered(A, xs, u, r, h):
  match xs:
    case Nil{}:
      from_ordered(A, r, u, h)
    case Con{x, more}:
      spread_from(A, more, u, r, u, O.le_refl(u), h)

law flat_ordered:
  for -A: Data
  for e: F.Events(List<&2, A>)
  for h: {F.E.ordered(List<&2, A>, e) == True{} : Bool}
  {F.E.ordered(A, F.E.flat(A, e)) == True{} : Bool}

def flat_ordered(A, e, h):
  match e:
    case Nil{}:
      {==}
    case Con{F.Occ{+u, xs}, +rest}:
      spread_ordered(A, xs, u, F.E.flat(A, rest), flat_from(A, rest, u, h))

# merge is associative
# --------------------

# Three first occurrences x, y, z (times tx, ty, tz) and the order of their
# times decide each side's first; the rest is the induction (ih).

law assoc.a1:
  for -A: Data
  for +tx: F.Time
  for -va: A
  for -xs: F.Events(A)
  for +ty: F.Time
  for -vb: A
  for -ys: F.Events(A)
  for +tz: F.Time
  for -vc: A
  for -zs: F.Events(A)
  for +hyx: {F.Time.lt(ty, tx) == True{} : Bool}
  for +hzy: {F.Time.lt(tz, ty) == True{} : Bool}
  for ih: {mg(A, mg(A, F.Occ{tx, va} <> xs, F.Occ{ty, vb} <> ys), zs)
             == mg(A, F.Occ{tx, va} <> xs, mg(A, F.Occ{ty, vb} <> ys, zs)) : F.Events(A)}
  {mg(A, mg(A, F.Occ{tx, va} <> xs, F.Occ{ty, vb} <> ys), F.Occ{tz, vc} <> zs)
     == mg(A, F.Occ{tx, va} <> xs, mg(A, F.Occ{ty, vb} <> ys, F.Occ{tz, vc} <> zs)) : F.Events(A)}

def assoc.a1(A, tx, va, xs, ty, vb, ys, tz, vc, zs, hyx, hzy, ih):
  L.chain6(F.Events(A),
    mg(A, mg(A, F.Occ{tx, va} <> xs, F.Occ{ty, vb} <> ys), F.Occ{tz, vc} <> zs),
    mg(A, F.Occ{ty, vb} <> mg(A, F.Occ{tx, va} <> xs, ys), F.Occ{tz, vc} <> zs),
    F.Occ{tz, vc} <> mg(A, F.Occ{ty, vb} <> mg(A, F.Occ{tx, va} <> xs, ys), zs),
    F.Occ{tz, vc} <> mg(A, mg(A, F.Occ{tx, va} <> xs, F.Occ{ty, vb} <> ys), zs),
    F.Occ{tz, vc} <> mg(A, F.Occ{tx, va} <> xs, mg(A, F.Occ{ty, vb} <> ys, zs)),
    mg(A, F.Occ{tx, va} <> xs, F.Occ{tz, vc} <> mg(A, F.Occ{ty, vb} <> ys, zs)),
    mg(A, F.Occ{tx, va} <> xs, mg(A, F.Occ{ty, vb} <> ys, F.Occ{tz, vc} <> zs)),
    Equal.cong(F.Events(A), F.Events(A), w => mg(A, w, F.Occ{tz, vc} <> zs),
      mg(A, F.Occ{tx, va} <> xs, F.Occ{ty, vb} <> ys), F.Occ{ty, vb} <> mg(A, F.Occ{tx, va} <> xs, ys),
      merge_later(A, tx, va, xs, ty, vb, ys, hyx)),
    merge_later(A, ty, vb, mg(A, F.Occ{tx, va} <> xs, ys), tz, vc, zs, hzy),
    Equal.cong(F.Events(A), F.Events(A), w => F.Occ{tz, vc} <> mg(A, w, zs),
      F.Occ{ty, vb} <> mg(A, F.Occ{tx, va} <> xs, ys), mg(A, F.Occ{tx, va} <> xs, F.Occ{ty, vb} <> ys),
      Equal.sym(F.Events(A), mg(A, F.Occ{tx, va} <> xs, F.Occ{ty, vb} <> ys), F.Occ{ty, vb} <> mg(A, F.Occ{tx, va} <> xs, ys),
        merge_later(A, tx, va, xs, ty, vb, ys, hyx))),
    L.cons_cong(F.Occ<A>, F.Occ{tz, vc}, mg(A, mg(A, F.Occ{tx, va} <> xs, F.Occ{ty, vb} <> ys), zs),
      mg(A, F.Occ{tx, va} <> xs, mg(A, F.Occ{ty, vb} <> ys, zs)), ih),
    Equal.sym(F.Events(A), mg(A, F.Occ{tx, va} <> xs, F.Occ{tz, vc} <> mg(A, F.Occ{ty, vb} <> ys, zs)),
      F.Occ{tz, vc} <> mg(A, F.Occ{tx, va} <> xs, mg(A, F.Occ{ty, vb} <> ys, zs)),
      merge_later(A, tx, va, xs, tz, vc, mg(A, F.Occ{ty, vb} <> ys, zs), O.lt_trans(tz, ty, tx, hzy, hyx))),
    Equal.cong(F.Events(A), F.Events(A), w => mg(A, F.Occ{tx, va} <> xs, w),
      F.Occ{tz, vc} <> mg(A, F.Occ{ty, vb} <> ys, zs), mg(A, F.Occ{ty, vb} <> ys, F.Occ{tz, vc} <> zs),
      Equal.sym(F.Events(A), mg(A, F.Occ{ty, vb} <> ys, F.Occ{tz, vc} <> zs), F.Occ{tz, vc} <> mg(A, F.Occ{ty, vb} <> ys, zs),
        merge_later(A, ty, vb, ys, tz, vc, zs, hzy))))

law assoc.a2:
  for -A: Data
  for +tx: F.Time
  for -va: A
  for -xs: F.Events(A)
  for +ty: F.Time
  for -vb: A
  for -ys: F.Events(A)
  for +tz: F.Time
  for -vc: A
  for -zs: F.Events(A)
  for +hyx: {F.Time.lt(ty, tx) == True{} : Bool}
  for +hzy: {F.Time.lt(tz, ty) == False{} : Bool}
  for ih: {mg(A, mg(A, F.Occ{tx, va} <> xs, ys), F.Occ{tz, vc} <> zs)
             == mg(A, F.Occ{tx, va} <> xs, mg(A, ys, F.Occ{tz, vc} <> zs)) : F.Events(A)}
  {mg(A, mg(A, F.Occ{tx, va} <> xs, F.Occ{ty, vb} <> ys), F.Occ{tz, vc} <> zs)
     == mg(A, F.Occ{tx, va} <> xs, mg(A, F.Occ{ty, vb} <> ys, F.Occ{tz, vc} <> zs)) : F.Events(A)}

def assoc.a2(A, tx, va, xs, ty, vb, ys, tz, vc, zs, hyx, hzy, ih):
  L.chain5(F.Events(A),
    mg(A, mg(A, F.Occ{tx, va} <> xs, F.Occ{ty, vb} <> ys), F.Occ{tz, vc} <> zs),
    mg(A, F.Occ{ty, vb} <> mg(A, F.Occ{tx, va} <> xs, ys), F.Occ{tz, vc} <> zs),
    F.Occ{ty, vb} <> mg(A, mg(A, F.Occ{tx, va} <> xs, ys), F.Occ{tz, vc} <> zs),
    F.Occ{ty, vb} <> mg(A, F.Occ{tx, va} <> xs, mg(A, ys, F.Occ{tz, vc} <> zs)),
    mg(A, F.Occ{tx, va} <> xs, F.Occ{ty, vb} <> mg(A, ys, F.Occ{tz, vc} <> zs)),
    mg(A, F.Occ{tx, va} <> xs, mg(A, F.Occ{ty, vb} <> ys, F.Occ{tz, vc} <> zs)),
    Equal.cong(F.Events(A), F.Events(A), w => mg(A, w, F.Occ{tz, vc} <> zs),
      mg(A, F.Occ{tx, va} <> xs, F.Occ{ty, vb} <> ys), F.Occ{ty, vb} <> mg(A, F.Occ{tx, va} <> xs, ys),
      merge_later(A, tx, va, xs, ty, vb, ys, hyx)),
    merge_first(A, ty, vb, mg(A, F.Occ{tx, va} <> xs, ys), tz, vc, zs, hzy),
    L.cons_cong(F.Occ<A>, F.Occ{ty, vb}, mg(A, mg(A, F.Occ{tx, va} <> xs, ys), F.Occ{tz, vc} <> zs),
      mg(A, F.Occ{tx, va} <> xs, mg(A, ys, F.Occ{tz, vc} <> zs)), ih),
    Equal.sym(F.Events(A), mg(A, F.Occ{tx, va} <> xs, F.Occ{ty, vb} <> mg(A, ys, F.Occ{tz, vc} <> zs)),
      F.Occ{ty, vb} <> mg(A, F.Occ{tx, va} <> xs, mg(A, ys, F.Occ{tz, vc} <> zs)),
      merge_later(A, tx, va, xs, ty, vb, mg(A, ys, F.Occ{tz, vc} <> zs), hyx)),
    Equal.cong(F.Events(A), F.Events(A), w => mg(A, F.Occ{tx, va} <> xs, w),
      F.Occ{ty, vb} <> mg(A, ys, F.Occ{tz, vc} <> zs), mg(A, F.Occ{ty, vb} <> ys, F.Occ{tz, vc} <> zs),
      Equal.sym(F.Events(A), mg(A, F.Occ{ty, vb} <> ys, F.Occ{tz, vc} <> zs), F.Occ{ty, vb} <> mg(A, ys, F.Occ{tz, vc} <> zs),
        merge_first(A, ty, vb, ys, tz, vc, zs, hzy))))

law assoc.b1:
  for -A: Data
  for +tx: F.Time
  for -va: A
  for -xs: F.Events(A)
  for +ty: F.Time
  for -vb: A
  for -ys: F.Events(A)
  for +tz: F.Time
  for -vc: A
  for -zs: F.Events(A)
  for +hyx: {F.Time.lt(ty, tx) == False{} : Bool}
  for +hzx: {F.Time.lt(tz, tx) == True{} : Bool}
  for +hzy: {F.Time.lt(tz, ty) == True{} : Bool}
  for ih: {mg(A, mg(A, F.Occ{tx, va} <> xs, F.Occ{ty, vb} <> ys), zs)
             == mg(A, F.Occ{tx, va} <> xs, mg(A, F.Occ{ty, vb} <> ys, zs)) : F.Events(A)}
  {mg(A, mg(A, F.Occ{tx, va} <> xs, F.Occ{ty, vb} <> ys), F.Occ{tz, vc} <> zs)
     == mg(A, F.Occ{tx, va} <> xs, mg(A, F.Occ{ty, vb} <> ys, F.Occ{tz, vc} <> zs)) : F.Events(A)}

def assoc.b1(A, tx, va, xs, ty, vb, ys, tz, vc, zs, hyx, hzx, hzy, ih):
  L.chain6(F.Events(A),
    mg(A, mg(A, F.Occ{tx, va} <> xs, F.Occ{ty, vb} <> ys), F.Occ{tz, vc} <> zs),
    mg(A, F.Occ{tx, va} <> mg(A, xs, F.Occ{ty, vb} <> ys), F.Occ{tz, vc} <> zs),
    F.Occ{tz, vc} <> mg(A, F.Occ{tx, va} <> mg(A, xs, F.Occ{ty, vb} <> ys), zs),
    F.Occ{tz, vc} <> mg(A, mg(A, F.Occ{tx, va} <> xs, F.Occ{ty, vb} <> ys), zs),
    F.Occ{tz, vc} <> mg(A, F.Occ{tx, va} <> xs, mg(A, F.Occ{ty, vb} <> ys, zs)),
    mg(A, F.Occ{tx, va} <> xs, F.Occ{tz, vc} <> mg(A, F.Occ{ty, vb} <> ys, zs)),
    mg(A, F.Occ{tx, va} <> xs, mg(A, F.Occ{ty, vb} <> ys, F.Occ{tz, vc} <> zs)),
    Equal.cong(F.Events(A), F.Events(A), w => mg(A, w, F.Occ{tz, vc} <> zs),
      mg(A, F.Occ{tx, va} <> xs, F.Occ{ty, vb} <> ys), F.Occ{tx, va} <> mg(A, xs, F.Occ{ty, vb} <> ys),
      merge_first(A, tx, va, xs, ty, vb, ys, hyx)),
    merge_later(A, tx, va, mg(A, xs, F.Occ{ty, vb} <> ys), tz, vc, zs, hzx),
    Equal.cong(F.Events(A), F.Events(A), w => F.Occ{tz, vc} <> mg(A, w, zs),
      F.Occ{tx, va} <> mg(A, xs, F.Occ{ty, vb} <> ys), mg(A, F.Occ{tx, va} <> xs, F.Occ{ty, vb} <> ys),
      Equal.sym(F.Events(A), mg(A, F.Occ{tx, va} <> xs, F.Occ{ty, vb} <> ys), F.Occ{tx, va} <> mg(A, xs, F.Occ{ty, vb} <> ys),
        merge_first(A, tx, va, xs, ty, vb, ys, hyx))),
    L.cons_cong(F.Occ<A>, F.Occ{tz, vc}, mg(A, mg(A, F.Occ{tx, va} <> xs, F.Occ{ty, vb} <> ys), zs),
      mg(A, F.Occ{tx, va} <> xs, mg(A, F.Occ{ty, vb} <> ys, zs)), ih),
    Equal.sym(F.Events(A), mg(A, F.Occ{tx, va} <> xs, F.Occ{tz, vc} <> mg(A, F.Occ{ty, vb} <> ys, zs)),
      F.Occ{tz, vc} <> mg(A, F.Occ{tx, va} <> xs, mg(A, F.Occ{ty, vb} <> ys, zs)),
      merge_later(A, tx, va, xs, tz, vc, mg(A, F.Occ{ty, vb} <> ys, zs), hzx)),
    Equal.cong(F.Events(A), F.Events(A), w => mg(A, F.Occ{tx, va} <> xs, w),
      F.Occ{tz, vc} <> mg(A, F.Occ{ty, vb} <> ys, zs), mg(A, F.Occ{ty, vb} <> ys, F.Occ{tz, vc} <> zs),
      Equal.sym(F.Events(A), mg(A, F.Occ{ty, vb} <> ys, F.Occ{tz, vc} <> zs), F.Occ{tz, vc} <> mg(A, F.Occ{ty, vb} <> ys, zs),
        merge_later(A, ty, vb, ys, tz, vc, zs, hzy))))

law assoc.b2a:
  for -A: Data
  for +tx: F.Time
  for -va: A
  for -xs: F.Events(A)
  for +ty: F.Time
  for -vb: A
  for -ys: F.Events(A)
  for +tz: F.Time
  for -vc: A
  for -zs: F.Events(A)
  for +hyx: {F.Time.lt(ty, tx) == False{} : Bool}
  for +hzx: {F.Time.lt(tz, tx) == False{} : Bool}
  for +hzy: {F.Time.lt(tz, ty) == True{} : Bool}
  for ih: {mg(A, mg(A, xs, F.Occ{ty, vb} <> ys), F.Occ{tz, vc} <> zs)
             == mg(A, xs, mg(A, F.Occ{ty, vb} <> ys, F.Occ{tz, vc} <> zs)) : F.Events(A)}
  {mg(A, mg(A, F.Occ{tx, va} <> xs, F.Occ{ty, vb} <> ys), F.Occ{tz, vc} <> zs)
     == mg(A, F.Occ{tx, va} <> xs, mg(A, F.Occ{ty, vb} <> ys, F.Occ{tz, vc} <> zs)) : F.Events(A)}

def assoc.b2a(A, tx, va, xs, ty, vb, ys, tz, vc, zs, hyx, hzx, hzy, ih):
  L.chain6(F.Events(A),
    mg(A, mg(A, F.Occ{tx, va} <> xs, F.Occ{ty, vb} <> ys), F.Occ{tz, vc} <> zs),
    mg(A, F.Occ{tx, va} <> mg(A, xs, F.Occ{ty, vb} <> ys), F.Occ{tz, vc} <> zs),
    F.Occ{tx, va} <> mg(A, mg(A, xs, F.Occ{ty, vb} <> ys), F.Occ{tz, vc} <> zs),
    F.Occ{tx, va} <> mg(A, xs, mg(A, F.Occ{ty, vb} <> ys, F.Occ{tz, vc} <> zs)),
    F.Occ{tx, va} <> mg(A, xs, F.Occ{tz, vc} <> mg(A, F.Occ{ty, vb} <> ys, zs)),
    mg(A, F.Occ{tx, va} <> xs, F.Occ{tz, vc} <> mg(A, F.Occ{ty, vb} <> ys, zs)),
    mg(A, F.Occ{tx, va} <> xs, mg(A, F.Occ{ty, vb} <> ys, F.Occ{tz, vc} <> zs)),
    Equal.cong(F.Events(A), F.Events(A), w => mg(A, w, F.Occ{tz, vc} <> zs),
      mg(A, F.Occ{tx, va} <> xs, F.Occ{ty, vb} <> ys), F.Occ{tx, va} <> mg(A, xs, F.Occ{ty, vb} <> ys),
      merge_first(A, tx, va, xs, ty, vb, ys, hyx)),
    merge_first(A, tx, va, mg(A, xs, F.Occ{ty, vb} <> ys), tz, vc, zs, hzx),
    L.cons_cong(F.Occ<A>, F.Occ{tx, va}, mg(A, mg(A, xs, F.Occ{ty, vb} <> ys), F.Occ{tz, vc} <> zs),
      mg(A, xs, mg(A, F.Occ{ty, vb} <> ys, F.Occ{tz, vc} <> zs)), ih),
    Equal.cong(F.Events(A), F.Events(A), w => F.Occ{tx, va} <> mg(A, xs, w),
      mg(A, F.Occ{ty, vb} <> ys, F.Occ{tz, vc} <> zs), F.Occ{tz, vc} <> mg(A, F.Occ{ty, vb} <> ys, zs),
      merge_later(A, ty, vb, ys, tz, vc, zs, hzy)),
    Equal.sym(F.Events(A), mg(A, F.Occ{tx, va} <> xs, F.Occ{tz, vc} <> mg(A, F.Occ{ty, vb} <> ys, zs)),
      F.Occ{tx, va} <> mg(A, xs, F.Occ{tz, vc} <> mg(A, F.Occ{ty, vb} <> ys, zs)),
      merge_first(A, tx, va, xs, tz, vc, mg(A, F.Occ{ty, vb} <> ys, zs), hzx)),
    Equal.cong(F.Events(A), F.Events(A), w => mg(A, F.Occ{tx, va} <> xs, w),
      F.Occ{tz, vc} <> mg(A, F.Occ{ty, vb} <> ys, zs), mg(A, F.Occ{ty, vb} <> ys, F.Occ{tz, vc} <> zs),
      Equal.sym(F.Events(A), mg(A, F.Occ{ty, vb} <> ys, F.Occ{tz, vc} <> zs), F.Occ{tz, vc} <> mg(A, F.Occ{ty, vb} <> ys, zs),
        merge_later(A, ty, vb, ys, tz, vc, zs, hzy))))

law assoc.b2b:
  for -A: Data
  for +tx: F.Time
  for -va: A
  for -xs: F.Events(A)
  for +ty: F.Time
  for -vb: A
  for -ys: F.Events(A)
  for +tz: F.Time
  for -vc: A
  for -zs: F.Events(A)
  for +hyx: {F.Time.lt(ty, tx) == False{} : Bool}
  for +hzx: {F.Time.lt(tz, tx) == False{} : Bool}
  for +hzy: {F.Time.lt(tz, ty) == False{} : Bool}
  for ih: {mg(A, mg(A, xs, F.Occ{ty, vb} <> ys), F.Occ{tz, vc} <> zs)
             == mg(A, xs, mg(A, F.Occ{ty, vb} <> ys, F.Occ{tz, vc} <> zs)) : F.Events(A)}
  {mg(A, mg(A, F.Occ{tx, va} <> xs, F.Occ{ty, vb} <> ys), F.Occ{tz, vc} <> zs)
     == mg(A, F.Occ{tx, va} <> xs, mg(A, F.Occ{ty, vb} <> ys, F.Occ{tz, vc} <> zs)) : F.Events(A)}

def assoc.b2b(A, tx, va, xs, ty, vb, ys, tz, vc, zs, hyx, hzx, hzy, ih):
  L.chain6(F.Events(A),
    mg(A, mg(A, F.Occ{tx, va} <> xs, F.Occ{ty, vb} <> ys), F.Occ{tz, vc} <> zs),
    mg(A, F.Occ{tx, va} <> mg(A, xs, F.Occ{ty, vb} <> ys), F.Occ{tz, vc} <> zs),
    F.Occ{tx, va} <> mg(A, mg(A, xs, F.Occ{ty, vb} <> ys), F.Occ{tz, vc} <> zs),
    F.Occ{tx, va} <> mg(A, xs, mg(A, F.Occ{ty, vb} <> ys, F.Occ{tz, vc} <> zs)),
    F.Occ{tx, va} <> mg(A, xs, F.Occ{ty, vb} <> mg(A, ys, F.Occ{tz, vc} <> zs)),
    mg(A, F.Occ{tx, va} <> xs, F.Occ{ty, vb} <> mg(A, ys, F.Occ{tz, vc} <> zs)),
    mg(A, F.Occ{tx, va} <> xs, mg(A, F.Occ{ty, vb} <> ys, F.Occ{tz, vc} <> zs)),
    Equal.cong(F.Events(A), F.Events(A), w => mg(A, w, F.Occ{tz, vc} <> zs),
      mg(A, F.Occ{tx, va} <> xs, F.Occ{ty, vb} <> ys), F.Occ{tx, va} <> mg(A, xs, F.Occ{ty, vb} <> ys),
      merge_first(A, tx, va, xs, ty, vb, ys, hyx)),
    merge_first(A, tx, va, mg(A, xs, F.Occ{ty, vb} <> ys), tz, vc, zs, hzx),
    L.cons_cong(F.Occ<A>, F.Occ{tx, va}, mg(A, mg(A, xs, F.Occ{ty, vb} <> ys), F.Occ{tz, vc} <> zs),
      mg(A, xs, mg(A, F.Occ{ty, vb} <> ys, F.Occ{tz, vc} <> zs)), ih),
    Equal.cong(F.Events(A), F.Events(A), w => F.Occ{tx, va} <> mg(A, xs, w),
      mg(A, F.Occ{ty, vb} <> ys, F.Occ{tz, vc} <> zs), F.Occ{ty, vb} <> mg(A, ys, F.Occ{tz, vc} <> zs),
      merge_first(A, ty, vb, ys, tz, vc, zs, hzy)),
    Equal.sym(F.Events(A), mg(A, F.Occ{tx, va} <> xs, F.Occ{ty, vb} <> mg(A, ys, F.Occ{tz, vc} <> zs)),
      F.Occ{tx, va} <> mg(A, xs, F.Occ{ty, vb} <> mg(A, ys, F.Occ{tz, vc} <> zs)),
      merge_first(A, tx, va, xs, ty, vb, mg(A, ys, F.Occ{tz, vc} <> zs), hyx)),
    Equal.cong(F.Events(A), F.Events(A), w => mg(A, F.Occ{tx, va} <> xs, w),
      F.Occ{ty, vb} <> mg(A, ys, F.Occ{tz, vc} <> zs), mg(A, F.Occ{ty, vb} <> ys, F.Occ{tz, vc} <> zs),
      Equal.sym(F.Events(A), mg(A, F.Occ{ty, vb} <> ys, F.Occ{tz, vc} <> zs), F.Occ{ty, vb} <> mg(A, ys, F.Occ{tz, vc} <> zs),
        merge_first(A, ty, vb, ys, tz, vc, zs, hzy))))

law merge_assoc:
  for -A: Data
  for a: F.Events(A)
  for b: F.Events(A)
  for c: F.Events(A)
  {F.E.merge(A, F.E.merge(A, a, b), c) == F.E.merge(A, a, F.E.merge(A, b, c)) : F.Events(A)}

def merge_assoc(A, a, b, c):
  match a:
    case Nil{}:
      {==}
    case Con{F.Occ{+tx, +va}, +xs}:
      match b:
        case Nil{}:
          Equal.cong(F.Events(A), F.Events(A), w => mg(A, w, c),
            mg(A, F.Occ{tx, va} <> xs, Nil{}), F.Occ{tx, va} <> xs, merge_never_r(A, F.Occ{tx, va} <> xs))
        case Con{F.Occ{+ty, +vb}, +ys}:
          match c:
            case Nil{}:
              Equal.trans(F.Events(A), mg(A, mg(A, F.Occ{tx, va} <> xs, F.Occ{ty, vb} <> ys), Nil{}),
                mg(A, F.Occ{tx, va} <> xs, F.Occ{ty, vb} <> ys), mg(A, F.Occ{tx, va} <> xs, mg(A, F.Occ{ty, vb} <> ys, Nil{})),
                merge_never_r(A, mg(A, F.Occ{tx, va} <> xs, F.Occ{ty, vb} <> ys)),
                Equal.cong(F.Events(A), F.Events(A), w => mg(A, F.Occ{tx, va} <> xs, w),
                  F.Occ{ty, vb} <> ys, mg(A, F.Occ{ty, vb} <> ys, Nil{}),
                  Equal.sym(F.Events(A), mg(A, F.Occ{ty, vb} <> ys, Nil{}), F.Occ{ty, vb} <> ys,
                    merge_never_r(A, F.Occ{ty, vb} <> ys))))
            case Con{F.Occ{+tz, +vc}, +zs}:
              L.bool.cases(F.Time.lt(ty, tx),
                {mg(A, mg(A, F.Occ{tx, va} <> xs, F.Occ{ty, vb} <> ys), F.Occ{tz, vc} <> zs)
                   == mg(A, F.Occ{tx, va} <> xs, mg(A, F.Occ{ty, vb} <> ys, F.Occ{tz, vc} <> zs)) : F.Events(A)},
                +hyx => L.bool.cases(F.Time.lt(tz, ty),
                  {mg(A, mg(A, F.Occ{tx, va} <> xs, F.Occ{ty, vb} <> ys), F.Occ{tz, vc} <> zs)
                     == mg(A, F.Occ{tx, va} <> xs, mg(A, F.Occ{ty, vb} <> ys, F.Occ{tz, vc} <> zs)) : F.Events(A)},
                  hzy => assoc.a1(A, tx, va, xs, ty, vb, ys, tz, vc, zs, hyx, hzy,
                    merge_assoc(A, F.Occ{tx, va} <> xs, F.Occ{ty, vb} <> ys, zs)),
                  hzy => assoc.a2(A, tx, va, xs, ty, vb, ys, tz, vc, zs, hyx, hzy,
                    merge_assoc(A, F.Occ{tx, va} <> xs, ys, F.Occ{tz, vc} <> zs))),
                +hyx => L.bool.cases(F.Time.lt(tz, tx),
                  {mg(A, mg(A, F.Occ{tx, va} <> xs, F.Occ{ty, vb} <> ys), F.Occ{tz, vc} <> zs)
                     == mg(A, F.Occ{tx, va} <> xs, mg(A, F.Occ{ty, vb} <> ys, F.Occ{tz, vc} <> zs)) : F.Events(A)},
                  +hzx => L.bool.cases(F.Time.lt(tz, ty),
                    {mg(A, mg(A, F.Occ{tx, va} <> xs, F.Occ{ty, vb} <> ys), F.Occ{tz, vc} <> zs)
                       == mg(A, F.Occ{tx, va} <> xs, mg(A, F.Occ{ty, vb} <> ys, F.Occ{tz, vc} <> zs)) : F.Events(A)},
                    hzy => assoc.b1(A, tx, va, xs, ty, vb, ys, tz, vc, zs, hyx, hzx, hzy,
                      merge_assoc(A, F.Occ{tx, va} <> xs, F.Occ{ty, vb} <> ys, zs)),
                    hzy => L.both({mg(A, mg(A, F.Occ{tx, va} <> xs, F.Occ{ty, vb} <> ys), F.Occ{tz, vc} <> zs)
                                     == mg(A, F.Occ{tx, va} <> xs, mg(A, F.Occ{ty, vb} <> ys, F.Occ{tz, vc} <> zs)) : F.Events(A)},
                      F.Time.lt(ty, tx), O.nlt_lt_trans(ty, tz, tx, hzy, hzx), hyx)),
                  +hzx => L.bool.cases(F.Time.lt(tz, ty),
                    {mg(A, mg(A, F.Occ{tx, va} <> xs, F.Occ{ty, vb} <> ys), F.Occ{tz, vc} <> zs)
                       == mg(A, F.Occ{tx, va} <> xs, mg(A, F.Occ{ty, vb} <> ys, F.Occ{tz, vc} <> zs)) : F.Events(A)},
                    hzy => assoc.b2a(A, tx, va, xs, ty, vb, ys, tz, vc, zs, hyx, hzx, hzy,
                      merge_assoc(A, xs, F.Occ{ty, vb} <> ys, F.Occ{tz, vc} <> zs)),
                    hzy => assoc.b2b(A, tx, va, xs, ty, vb, ys, tz, vc, zs, hyx, hzx, hzy,
                      merge_assoc(A, xs, F.Occ{ty, vb} <> ys, F.Occ{tz, vc} <> zs)))))
