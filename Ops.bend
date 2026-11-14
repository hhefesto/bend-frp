import Base
import ./Frp.bend as F

# More event combinators, after reflex's: each is defined by what it does to
# occurrences, and LAWS.bend pins each down occurrence by occurrence.

# mergeWith: both events' occurrences in time order; where both occur at one
# time, one occurrence of f of the two values.
def E.merge_with.pick(~A: Data, ~f: A -> A -> A, c: Cmp, +t: F.Time, +a: A, +u: F.Time, +b: A,
                      lt: Unit -> F.Events(A), gt: Unit -> F.Events(A), eq: Unit -> F.Events(A)) -> F.Events(A):
  match c:
    case LT{}:
      F.Occ{t, a} <> lt(Unit{})
    case EQ{}:
      F.Occ{t, f(a, b)} <> eq(Unit{})
    case GT{}:
      F.Occ{u, b} <> gt(Unit{})

def E.merge_with(~A: Data, ~f: A -> A -> A, e1: F.Events(A), e2: F.Events(A)) -> F.Events(A):
  match e1 e2:
    case Nil{} ys:
      ys
    case Con{x, xs} Nil{}:
      x <> xs
    case Con{F.Occ{+t, +a}, +xs} Con{F.Occ{+u, +b}, +ys}:
      E.merge_with.pick(~A, ~f, F.Time.cmp(t, u), t, a, u, b,
        w => E.merge_with(~A, ~f, xs, F.Occ{u, b} <> ys),
        w => E.merge_with(~A, ~f, F.Occ{t, a} <> xs, ys),
        w => E.merge_with(~A, ~f, xs, ys))

# leftmost: both, and e1's value where both occur at one time.
def E.left(-A: Data, a: A, b: A) -> A:
  a

def E.leftmost(~A: Data, e1: F.Events(A), e2: F.Events(A)) -> F.Events(A):
  E.merge_with(~A, ~E.left(A), e1, e2)

# Whether e occurs at t.
def E.occurs(-A: Data, e: F.Events(A), +t: F.Time) -> Bool:
  match e:
    case Nil{}:
      False{}
    case Con{F.Occ{+u, x}, rest}:
      Cmp.is_eq(F.Time.cmp(u, t)) || E.occurs(A, rest, t)

# difference: e1's occurrences at times e2 does not occur.
def E.difference(-A: Data, -B: Data, e1: F.Events(A), +e2: F.Events(B)) -> F.Events(A):
  match e1:
    case Nil{}:
      Nil{}
    case Con{F.Occ{+t, +a}, rest}:
      F.E.keep(A, F.Occ{t, a}, E.difference(A, B, rest, e2), Bool.not(E.occurs(B, e2, t)))

# gate: e's occurrences at times b is True.
def E.gate.pick(-A: Data, a: A, open: Bool) -> Maybe<&2, A>:
  match open:
    case True{}:
      Some{a}
    case False{}:
      None{}

def E.gate(~A: Data, ~b: F.Behavior(Bool), e: F.Events(A)) -> F.Events(A):
  F.E.justs(A, F.E.snapshot(~A, ~Bool, ~Maybe<&2, A>, ~E.gate.pick(A), ~b, e))

# headE, tailE, take, drop: the first occurrence; all after it; the first n;
# all after the first n.
def E.head(-A: Data, e: F.Events(A)) -> F.Events(A):
  match e:
    case Nil{}:
      Nil{}
    case Con{o, rest}:
      o <> Nil{}

def E.tail(-A: Data, e: F.Events(A)) -> F.Events(A):
  match e:
    case Nil{}:
      Nil{}
    case Con{o, rest}:
      rest

def E.take(-A: Data, e: F.Events(A), n: Nat) -> F.Events(A):
  match e:
    case Nil{}:
      Nil{}
    case Con{o, rest}:
      match n:
        case 0n:
          Nil{}
        case 1n+p:
          o <> E.take(A, rest, p)

def E.drop(-A: Data, e: F.Events(A), n: Nat) -> F.Events(A):
  match e:
    case Nil{}:
      Nil{}
    case Con{o, rest}:
      match n:
        case 0n:
          o <> rest
        case 1n+p:
          E.drop(A, rest, p)

# fan and select: an event of keyed values, and the values at one key
# (same says when two keys are one). fan spreads an occurrence that carries
# many keyed values (reflex's Event (Map k v)) into one per key.
def E.select(~K: Data, ~A: Data, ~same: K -> K -> Bool, e: F.Events(F.Both<K, A>), +k: K) -> F.Events(A):
  match e:
    case Nil{}:
      Nil{}
    case Con{F.Occ{+t, F.Both{k2, +a}}, rest}:
      F.E.keep(A, F.Occ{t, a}, E.select(~K, ~A, ~same, rest, k), same(k2, k))

def E.fan(-K: Data, -A: Data, e: F.Events(List<&2, F.Both<K, A>>)) -> F.Events(F.Both<K, A>):
  F.E.flat(F.Both<K, A>, e)

# delay: each occurrence d later.
def E.delay(-A: Data, +d: F.Time, e: F.Events(A)) -> F.Events(A):
  match e:
    case Nil{}:
      Nil{}
    case Con{F.Occ{+t, a}, rest}:
      F.Occ{F.Time.add(t, d), a} <> E.delay(A, d, rest)

# debounce: an occurrence d later, if no other comes before then (the last
# of each burst, once it has been quiet for d).
def E.quiet(-A: Data, e: F.Events(A), +t: F.Time) -> Bool:
  match e:
    case Nil{}:
      True{}
    case Con{F.Occ{+u, x}, rest}:
      Bool.not(F.Time.lt(u, t))

def E.debounce(-A: Data, +d: F.Time, e: F.Events(A)) -> F.Events(A):
  match e:
    case Nil{}:
      Nil{}
    case Con{F.Occ{+t, +a}, +rest}:
      F.E.keep(A, F.Occ{F.Time.add(t, d), a}, E.debounce(A, d, rest), E.quiet(A, rest, F.Time.add(t, d)))

# throttle: an occurrence passes if it is at least d after the last that
# passed (the first passes); the others are dropped.
def E.throttle.pick(-A: Data, open: Bool, +t: F.Time, +a: A, kept: Unit -> F.Events(A), dropped: Unit -> F.Events(A)) -> F.Events(A):
  match open:
    case True{}:
      F.Occ{t, a} <> kept(Unit{})
    case False{}:
      dropped(Unit{})

def E.throttle.from(-A: Data, e: F.Events(A), +d: F.Time, +from: F.Time) -> F.Events(A):
  match e:
    case Nil{}:
      Nil{}
    case Con{F.Occ{+t, +a}, +rest}:
      E.throttle.pick(A, F.Time.le(from, t), t, a,
        w => E.throttle.from(A, rest, d, F.Time.add(t, d)),
        w => E.throttle.from(A, rest, d, from))

def E.throttle(-A: Data, +d: F.Time, e: F.Events(A)) -> F.Events(A):
  match e:
    case Nil{}:
      Nil{}
    case Con{F.Occ{+t, a}, rest}:
      F.Occ{t, a} <> E.throttle.from(A, rest, d, F.Time.add(t, d))
