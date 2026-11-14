import Base
import ../Frp.bend as F
import ../Ops.bend as P

# The combinators of Ops.bend, run on sample events. Each occurrence prints
# as half-seconds:value. Expected, worked out by hand from the meanings:
#   merge_with(+, e1, e2)  2:1 4:22 6:30 8:4
#   leftmost(e1, e2)       2:1 4:2 6:30 8:4
#   difference(e1, e2)     2:1 8:4
#   gate(t < 3 s, e1)      2:1 4:2
#   take(e1, 2), drop      2:1 4:2 | 8:4
#   select(key 7, keyed)   2:1 6:3
#   delay(1 s, e1)         4:1 6:2 10:4
#   debounce(1.5 s, c)     7:2 14:4 21:5
#   throttle(2 s, c)       2:1 10:3 18:5

def at(n: U32) -> F.Time:
  F.Time{n, 0}

def half(n: U32) -> F.Time:
  F.Time{n, 2147483648}

def e1() -> F.Events(U32):
  [F.Occ{at(1), 1}, F.Occ{at(2), 2}, F.Occ{at(4), 4}]

def e2() -> F.Events(U32):
  [F.Occ{at(2), 20}, F.Occ{at(3), 30}]

def clicks() -> F.Events(U32):
  [F.Occ{at(1), 1}, F.Occ{at(2), 2}, F.Occ{at(5), 3}, F.Occ{half(5), 4}, F.Occ{at(9), 5}]

def keyed() -> F.Events(F.Both<U32, U32>):
  [F.Occ{at(1), F.Both{7, 1}}, F.Occ{at(2), F.Both{8, 2}}, F.Occ{at(3), F.Both{7, 3}}]

def add(a: U32, b: U32) -> U32:
  (a + b : U32)

def early(t: F.Time) -> Bool:
  F.Time.lt(t, at(3))

def show(e: F.Events(U32)) -> String:
  match e:
    case Nil{}:
      ""
    case Con{F.Occ{F.Time{s, f}, v}, rest}:
      " " ++ U32.show(((s + s) + Bool.to_u32(U32.is_ge(f, 2147483648)) : U32)) ++ ":" ++ U32.show(v) ++ show(rest)

def main() -> List<&2, String>:
  [show(P.E.merge_with(~U32, ~add, e1(), e2())),
   show(P.E.leftmost(~U32, e1(), e2())),
   show(P.E.difference(U32, U32, e1(), e2())),
   show(P.E.gate(~U32, ~early, e1())),
   show(P.E.take(U32, e1(), 2n)) ++ " |" ++ show(P.E.drop(U32, e1(), 2n)),
   show(P.E.select(~U32, ~U32, ~U32.is_eq, keyed(), 7)),
   show(P.E.delay(U32, at(1), e1())),
   show(P.E.debounce(U32, half(1), clicks())),
   show(P.E.throttle(U32, at(2), clicks()))]
