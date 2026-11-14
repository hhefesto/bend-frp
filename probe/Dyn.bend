import Base
import ../Frp.bend as F
import ../Dyn.bend as D

# zip and join, run on sample Dyns and sampled at 0.5 s, 1.5 s, .., 7.5 s,
# against their meanings (the pair of currents; the current of the current).
# Prints four lists: zip's samples (as a * 100 + b), the meaning's; join's,
# the meaning's. Each pair is the same.

def ts() -> List<&2, F.Time>:
  [F.Time{0, 2147483648}, F.Time{1, 2147483648}, F.Time{2, 2147483648}, F.Time{3, 2147483648},
   F.Time{4, 2147483648}, F.Time{5, 2147483648}, F.Time{6, 2147483648}, F.Time{7, 2147483648}]

def da() -> D.Dyn<U32>:
  D.Dyn{0, [F.Occ{F.Time.secs(1), 1}, F.Occ{F.Time.secs(3), 3}, F.Occ{F.Time.secs(5), 5}]}

def db() -> D.Dyn<U32>:
  D.Dyn{0, [F.Occ{F.Time.secs(2), 2}, F.Occ{F.Time.secs(3), 4}]}

def dd() -> D.Dyn<D.Dyn<U32>>:
  D.Dyn{D.Dyn{0, [F.Occ{F.Time.secs(1), 1}, F.Occ{F.Time.secs(4), 4}]},
    [F.Occ{F.Time.secs(2), D.Dyn{100, [F.Occ{F.Time.secs(1), 101}, F.Occ{F.Time.secs(3), 103}, F.Occ{F.Time.secs(6), 106}]}},
     F.Occ{F.Time.secs(5), D.Dyn{200, [F.Occ{F.Time.secs(7), 207}]}}]}

def pair(p: F.Both<U32, U32>) -> U32:
  match p:
    case F.Both{a, b}:
      ((a * 100) + b : U32)

def zip.machine(ts: List<&2, F.Time>) -> List<&2, U32>:
  match ts:
    case Nil{}:
      Nil{}
    case Con{t, rest}:
      pair(D.Dyn.current(F.Both<U32, U32>, D.Dyn.zip(U32, U32, da(), db()))(t)) <> zip.machine(rest)

def zip.meaning(ts: List<&2, F.Time>) -> List<&2, U32>:
  match ts:
    case Nil{}:
      Nil{}
    case Con{+t, rest}:
      pair(F.Both{D.Dyn.current(U32, da())(t), D.Dyn.current(U32, db())(t)}) <> zip.meaning(rest)

def join.machine(ts: List<&2, F.Time>) -> List<&2, U32>:
  match ts:
    case Nil{}:
      Nil{}
    case Con{t, rest}:
      D.Dyn.current(U32, D.Dyn.join(U32, dd()))(t) <> join.machine(rest)

def join.meaning(ts: List<&2, F.Time>) -> List<&2, U32>:
  match ts:
    case Nil{}:
      Nil{}
    case Con{+t, rest}:
      D.Dyn.current(U32, D.Dyn.current(D.Dyn<U32>, dd())(t))(t) <> join.meaning(rest)

def main() -> List<&2, List<&2, U32>>:
  [zip.machine(ts()), zip.meaning(ts()), join.machine(ts()), join.meaning(ts())]
