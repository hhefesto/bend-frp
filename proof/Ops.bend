import Base
import ../Frp.bend as F
import ../Ops.bend as P
import ./Logic.bend as L
import ./Order.bend as O
import ./Events.bend as Ev

# Facts about Ops.bend's combinators the laws are proved from.

# mergeWith at two first occurrences, once the order of their times is known

law mw.lt:
  for ~A: Data
  for ~f: A -> A -> A
  for c: Cmp
  for -t: F.Time
  for -a: A
  for -u: F.Time
  for -b: A
  for -xs: F.Events(A)
  for -ys: F.Events(A)
  for h: {c == LT{} : Cmp}
  {P.E.merge_with.pick(~A, ~f, c, t, a, u, b,
     w => P.E.merge_with(~A, ~f, xs, F.Occ{u, b} <> ys), w => P.E.merge_with(~A, ~f, F.Occ{t, a} <> xs, ys),
     w => P.E.merge_with(~A, ~f, xs, ys))
     == F.Occ{t, a} <> P.E.merge_with(~A, ~f, xs, F.Occ{u, b} <> ys) : F.Events(A)}

def mw.lt(A, f, c, t, a, u, b, xs, ys, h):
  match c:
    case LT{}:
      {==}
    case EQ{}:
      L.cmp.ne_lt({F.Occ{t, f(a, b)} <> P.E.merge_with(~A, ~f, xs, ys)
                     == F.Occ{t, a} <> P.E.merge_with(~A, ~f, xs, F.Occ{u, b} <> ys) : F.Events(A)}, EQ{}, h, Unit{})
    case GT{}:
      L.cmp.ne_lt({F.Occ{u, b} <> P.E.merge_with(~A, ~f, F.Occ{t, a} <> xs, ys)
                     == F.Occ{t, a} <> P.E.merge_with(~A, ~f, xs, F.Occ{u, b} <> ys) : F.Events(A)}, GT{}, h, Unit{})

law mw.gt:
  for ~A: Data
  for ~f: A -> A -> A
  for c: Cmp
  for -t: F.Time
  for -a: A
  for -u: F.Time
  for -b: A
  for -xs: F.Events(A)
  for -ys: F.Events(A)
  for h: {c == GT{} : Cmp}
  {P.E.merge_with.pick(~A, ~f, c, t, a, u, b,
     w => P.E.merge_with(~A, ~f, xs, F.Occ{u, b} <> ys), w => P.E.merge_with(~A, ~f, F.Occ{t, a} <> xs, ys),
     w => P.E.merge_with(~A, ~f, xs, ys))
     == F.Occ{u, b} <> P.E.merge_with(~A, ~f, F.Occ{t, a} <> xs, ys) : F.Events(A)}

def mw.gt(A, f, c, t, a, u, b, xs, ys, h):
  match c:
    case LT{}:
      L.cmp.ne_gt({F.Occ{t, a} <> P.E.merge_with(~A, ~f, xs, F.Occ{u, b} <> ys)
                     == F.Occ{u, b} <> P.E.merge_with(~A, ~f, F.Occ{t, a} <> xs, ys) : F.Events(A)}, LT{}, h, Unit{})
    case EQ{}:
      L.cmp.ne_gt({F.Occ{t, f(a, b)} <> P.E.merge_with(~A, ~f, xs, ys)
                     == F.Occ{u, b} <> P.E.merge_with(~A, ~f, F.Occ{t, a} <> xs, ys) : F.Events(A)}, EQ{}, h, Unit{})
    case GT{}:
      {==}

law mw.eq:
  for ~A: Data
  for ~f: A -> A -> A
  for c: Cmp
  for -t: F.Time
  for -a: A
  for -b: A
  for -xs: F.Events(A)
  for -ys: F.Events(A)
  for h: {c == EQ{} : Cmp}
  {P.E.merge_with.pick(~A, ~f, c, t, a, t, b,
     w => P.E.merge_with(~A, ~f, xs, F.Occ{t, b} <> ys), w => P.E.merge_with(~A, ~f, F.Occ{t, a} <> xs, ys),
     w => P.E.merge_with(~A, ~f, xs, ys))
     == F.Occ{t, f(a, b)} <> P.E.merge_with(~A, ~f, xs, ys) : F.Events(A)}

def mw.eq(A, f, c, t, a, b, xs, ys, h):
  match c:
    case LT{}:
      L.cmp.ne_eq({F.Occ{t, a} <> P.E.merge_with(~A, ~f, xs, F.Occ{t, b} <> ys)
                     == F.Occ{t, f(a, b)} <> P.E.merge_with(~A, ~f, xs, ys) : F.Events(A)}, LT{}, h, Unit{})
    case EQ{}:
      {==}
    case GT{}:
      L.cmp.ne_eq({F.Occ{t, b} <> P.E.merge_with(~A, ~f, F.Occ{t, a} <> xs, ys)
                     == F.Occ{t, f(a, b)} <> P.E.merge_with(~A, ~f, xs, ys) : F.Events(A)}, GT{}, h, Unit{})

# gate at one occurrence

law gate.hit:
  for -A: Data
  for c: Bool
  for -t: F.Time
  for -a: A
  for -R: F.Events(Maybe<&2, A>)
  for h: {c == True{} : Bool}
  {F.E.justs(A, F.Occ{t, P.E.gate.pick(A, a, c)} <> R) == F.Occ{t, a} <> F.E.justs(A, R) : F.Events(A)}

def gate.hit(A, c, t, a, R, h):
  match c:
    case True{}:
      {==}
    case False{}:
      L.clash({F.E.justs(A, F.Occ{t, P.E.gate.pick(A, a, False{})} <> R) == F.Occ{t, a} <> F.E.justs(A, R) : F.Events(A)}, h)

law gate.miss:
  for -A: Data
  for c: Bool
  for -t: F.Time
  for -a: A
  for -R: F.Events(Maybe<&2, A>)
  for h: {c == False{} : Bool}
  {F.E.justs(A, F.Occ{t, P.E.gate.pick(A, a, c)} <> R) == F.E.justs(A, R) : F.Events(A)}

def gate.miss(A, c, t, a, R, h):
  match c:
    case True{}:
      L.clash.flip({F.E.justs(A, F.Occ{t, P.E.gate.pick(A, a, True{})} <> R) == F.E.justs(A, R) : F.Events(A)}, h)
    case False{}:
      {==}

# throttle at one occurrence

law throttle.hit:
  for -A: Data
  for c: Bool
  for -t: F.Time
  for -a: A
  for -K: F.Events(A)
  for -D: F.Events(A)
  for h: {c == True{} : Bool}
  {P.E.throttle.pick(A, c, t, a, w => K, w => D) == F.Occ{t, a} <> K : F.Events(A)}

def throttle.hit(A, c, t, a, K, D, h):
  match c:
    case True{}:
      {==}
    case False{}:
      L.clash({P.E.throttle.pick(A, False{}, t, a, w => K, w => D) == F.Occ{t, a} <> K : F.Events(A)}, h)

law throttle.miss:
  for -A: Data
  for c: Bool
  for -t: F.Time
  for -a: A
  for -K: F.Events(A)
  for -D: F.Events(A)
  for h: {c == False{} : Bool}
  {P.E.throttle.pick(A, c, t, a, w => K, w => D) == D : F.Events(A)}

def throttle.miss(A, c, t, a, K, D, h):
  match c:
    case True{}:
      L.clash.flip({P.E.throttle.pick(A, True{}, t, a, w => K, w => D) == D : F.Events(A)}, h)
    case False{}:
      {==}

# difference against never

law occurs_never:
  for -B: Data
  for -t: F.Time
  {P.E.occurs(B, Nil{}, t) == False{} : Bool}

def occurs_never(B, t):
  {==}

law difference_never:
  for -A: Data
  for -B: Data
  for e: F.Events(A)
  {P.E.difference(A, B, e, Nil{}) == e : F.Events(A)}

def difference_never(A, B, e):
  match e:
    case Nil{}:
      {==}
    case Con{F.Occ{+t, +a}, rest}:
      L.cons_cong(F.Occ<A>, F.Occ{t, a}, P.E.difference(A, B, rest, Nil{}), rest, difference_never(A, B, rest))

# take and drop

law take_drop:
  for -A: Data
  for e: F.Events(A)
  for n: Nat
  {List.append(&2, F.Occ<A>, P.E.take(A, e, n), P.E.drop(A, e, n)) == e : F.Events(A)}

def take_drop(A, e, n):
  match e:
    case Nil{}:
      {==}
    case Con{o, rest}:
      match n:
        case 0n:
          {==}
        case 1n+p:
          L.cons_cong(F.Occ<A>, o, List.append(&2, F.Occ<A>, P.E.take(A, rest, p), P.E.drop(A, rest, p)), rest,
            take_drop(A, rest, p))

law take_from:
  for -A: Data
  for e: F.Events(A)
  for n: Nat
  for +t: F.Time
  for h: {F.E.ordered_from(A, e, t) == True{} : Bool}
  {F.E.ordered_from(A, P.E.take(A, e, n), t) == True{} : Bool}

def take_from(A, e, n, t, h):
  match e:
    case Nil{}:
      {==}
    case Con{F.Occ{+u, x}, +rest}:
      match n:
        case 0n:
          {==}
        case 1n+p:
          L.and.both(F.Time.le(t, u), F.E.ordered_from(A, rest, u),
            {(F.Time.le(t, u) && F.E.ordered_from(A, P.E.take(A, rest, p), u)) == True{} : Bool}, h,
            a => b => L.and.intro(F.Time.le(t, u), F.E.ordered_from(A, P.E.take(A, rest, p), u), a, take_from(A, rest, p, u, b)))

law take_ordered:
  for -A: Data
  for e: F.Events(A)
  for n: Nat
  for h: {F.E.ordered(A, e) == True{} : Bool}
  {F.E.ordered(A, P.E.take(A, e, n)) == True{} : Bool}

def take_ordered(A, e, n, h):
  match e:
    case Nil{}:
      {==}
    case Con{F.Occ{+u, x}, rest}:
      match n:
        case 0n:
          {==}
        case 1n+p:
          take_from(A, rest, p, u, h)

law drop_ordered:
  for -A: Data
  for e: F.Events(A)
  for n: Nat
  for h: {F.E.ordered(A, e) == True{} : Bool}
  {F.E.ordered(A, P.E.drop(A, e, n)) == True{} : Bool}

def drop_ordered(A, e, n, h):
  match e:
    case Nil{}:
      {==}
    case Con{F.Occ{+u, x}, +rest}:
      match n:
        case 0n:
          h
        case 1n+p:
          drop_ordered(A, rest, p, Ev.from_ordered(A, rest, u, h))

# select keeps some occurrences, in place

law select_from:
  for ~K: Data
  for ~A: Data
  for ~same: K -> K -> Bool
  for e: F.Events(F.Both<K, A>)
  for +k: K
  for +t: F.Time
  for h: {F.E.ordered_from(F.Both<K, A>, e, t) == True{} : Bool}
  {F.E.ordered_from(A, P.E.select(~K, ~A, ~same, e, k), t) == True{} : Bool}

def select_from(K, A, same, e, k, t, h):
  match e:
    case Nil{}:
      {==}
    case Con{F.Occ{+u, F.Both{+k2, +a}}, +rest}:
      L.and.both(F.Time.le(t, u), F.E.ordered_from(F.Both<K, A>, rest, u),
        {F.E.ordered_from(A, F.E.keep(A, F.Occ{u, a}, P.E.select(~K, ~A, ~same, rest, k), same(k2, k)), t) == True{} : Bool}, h,
        +x => +y => L.bool.cases(same(k2, k),
          {F.E.ordered_from(A, F.E.keep(A, F.Occ{u, a}, P.E.select(~K, ~A, ~same, rest, k), same(k2, k)), t) == True{} : Bool},
          hp => Equal.trans(Bool,
            F.E.ordered_from(A, F.E.keep(A, F.Occ{u, a}, P.E.select(~K, ~A, ~same, rest, k), same(k2, k)), t),
            F.E.ordered_from(A, F.Occ{u, a} <> P.E.select(~K, ~A, ~same, rest, k), t), True{},
            Equal.cong(F.Events(A), Bool, z => F.E.ordered_from(A, z, t),
              F.E.keep(A, F.Occ{u, a}, P.E.select(~K, ~A, ~same, rest, k), same(k2, k)), F.Occ{u, a} <> P.E.select(~K, ~A, ~same, rest, k),
              Ev.keep.hit(A, F.Occ{u, a}, P.E.select(~K, ~A, ~same, rest, k), same(k2, k), hp)),
            L.and.intro(F.Time.le(t, u), F.E.ordered_from(A, P.E.select(~K, ~A, ~same, rest, k), u), x,
              select_from(K, A, same, rest, k, u, y))),
          hp => Equal.trans(Bool,
            F.E.ordered_from(A, F.E.keep(A, F.Occ{u, a}, P.E.select(~K, ~A, ~same, rest, k), same(k2, k)), t),
            F.E.ordered_from(A, P.E.select(~K, ~A, ~same, rest, k), t), True{},
            Equal.cong(F.Events(A), Bool, z => F.E.ordered_from(A, z, t),
              F.E.keep(A, F.Occ{u, a}, P.E.select(~K, ~A, ~same, rest, k), same(k2, k)), P.E.select(~K, ~A, ~same, rest, k),
              Ev.keep.miss(A, F.Occ{u, a}, P.E.select(~K, ~A, ~same, rest, k), same(k2, k), hp)),
            Ev.from_lower(A, P.E.select(~K, ~A, ~same, rest, k), t, u, x, select_from(K, A, same, rest, k, u, y)))))

law select_ordered:
  for ~K: Data
  for ~A: Data
  for ~same: K -> K -> Bool
  for e: F.Events(F.Both<K, A>)
  for +k: K
  for +h: {F.E.ordered(F.Both<K, A>, e) == True{} : Bool}
  {F.E.ordered(A, P.E.select(~K, ~A, ~same, e, k)) == True{} : Bool}

def select_ordered(K, A, same, e, k, h):
  match e:
    case Nil{}:
      {==}
    case Con{F.Occ{+u, F.Both{+k2, +a}}, +rest}:
      L.bool.cases(same(k2, k),
        {F.E.ordered(A, F.E.keep(A, F.Occ{u, a}, P.E.select(~K, ~A, ~same, rest, k), same(k2, k))) == True{} : Bool},
        hp => Equal.trans(Bool,
          F.E.ordered(A, F.E.keep(A, F.Occ{u, a}, P.E.select(~K, ~A, ~same, rest, k), same(k2, k))),
          F.E.ordered(A, F.Occ{u, a} <> P.E.select(~K, ~A, ~same, rest, k)), True{},
          Equal.cong(F.Events(A), Bool, z => F.E.ordered(A, z),
            F.E.keep(A, F.Occ{u, a}, P.E.select(~K, ~A, ~same, rest, k), same(k2, k)), F.Occ{u, a} <> P.E.select(~K, ~A, ~same, rest, k),
            Ev.keep.hit(A, F.Occ{u, a}, P.E.select(~K, ~A, ~same, rest, k), same(k2, k), hp)),
          select_from(K, A, same, rest, k, u, h)),
        hp => Equal.trans(Bool,
          F.E.ordered(A, F.E.keep(A, F.Occ{u, a}, P.E.select(~K, ~A, ~same, rest, k), same(k2, k))),
          F.E.ordered(A, P.E.select(~K, ~A, ~same, rest, k)), True{},
          Equal.cong(F.Events(A), Bool, z => F.E.ordered(A, z),
            F.E.keep(A, F.Occ{u, a}, P.E.select(~K, ~A, ~same, rest, k), same(k2, k)), P.E.select(~K, ~A, ~same, rest, k),
            Ev.keep.miss(A, F.Occ{u, a}, P.E.select(~K, ~A, ~same, rest, k), same(k2, k), hp)),
          Ev.from_ordered(A, P.E.select(~K, ~A, ~same, rest, k), u, select_from(K, A, same, rest, k, u, h))))
