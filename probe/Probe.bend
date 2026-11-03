import Base

# An occurrence: a value at a time (milliseconds of the runtime's clock).
type Occ<-A: Data> is Data:
  Occ{+at: U32, +val: A}

# E.map: each occurrence's value through f.
def E.map(~A: Data, ~B: Data, ~f: A -> B, e: List<&2, Occ<A>>) -> List<&2, Occ<B>>:
  match e:
    case Nil{}:
      Nil{}
    case Con{o, rest}:
      match o:
        case Occ{t, x}:
          Occ{t, f(x)} <> E.map(~A, ~B, ~f, rest)

# B.stepper sampled at t: x before e's first occurrence, then its latest
# value strictly before t.
def B.stepper.if(-A: Data, later: Unit -> A, now: A, before: Bool) -> A:
  match before:
    case True{}:
      later(Unit{})
    case False{}:
      now

def B.stepper.at(-A: Data, e: List<&2, Occ<A>>, +t: U32, x: A) -> A:
  match e:
    case Nil{}:
      x
    case Con{o, rest}:
      match o:
        case Occ{+u, y}:
          B.stepper.if(A, w => B.stepper.at(A, rest, t, y), x, U32.is_lt(u, t))

def inc(x: U32) -> U32:
  (x + 1 : U32)

def main() -> U32:
  e = {[Occ{10, 1}, Occ{20, 2}, Occ{30, 3}] : List<&2, Occ<U32>>}
  B.stepper.at(U32, E.map(~U32, ~U32, ~inc, e), 25, 0)
