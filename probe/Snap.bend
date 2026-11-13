import Base
import ../Frp.bend as F

# snap, run on one input event of samples (Fire) and values (Set), against
# its meaning: the samples snapshotted against the values' stepper. Prints
# the machine's samples, then the meaning's: the same list twice.

def add(a: U32, b: U32) -> U32:
  (a + b : U32)

def input() -> F.Events(F.Side<U32, U32>):
  [F.Occ{1, F.Fire{10}}, F.Occ{2, F.Set{5}}, F.Occ{3, F.Fire{20}},
   F.Occ{3, F.Set{7}}, F.Occ{4, F.Fire{30}}, F.Occ{6, F.Set{9}}]

def vals(e: F.Events(U32)) -> List<&2, U32>:
  match e:
    case Nil{}:
      Nil{}
    case Con{o, rest}:
      F.Occ.val(U32, o) <> vals(rest)

def machine() -> List<&2, U32>:
  vals(F.E.justs(U32, F.E.run(~U32, ~F.Side<U32, U32>, ~Maybe<&2, U32>, ~(+s => i => F.snap.step(~U32, ~U32, ~U32, ~add, s, i)), input(), 0)))

def meaning() -> List<&2, U32>:
  vals(F.E.snapshot.stepper(~U32, ~U32, ~U32, ~add, F.E.fires(U32, U32, input()), 0, F.E.sets(U32, U32, input())))

def main() -> List<&2, List<&2, U32>>:
  [machine(), meaning(), [Bool.to_u32(F.snap.ok(U32, U32, input()))]]
