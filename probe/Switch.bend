import Base
import ../Frp.bend as F

# switch, run on one input event of inputs (Fire) and keys (Set), against
# its meaning, E.switched. Machine 0 counts its inputs; machine 1 doubles
# each input and adds what it has seen so far. Prints the machine's outputs,
# then the meaning's: the same list twice.

def fam.init(k: U32) -> U32:
  0

def fam.pick(zero: Bool, +s: U32, +a: U32) -> U32 & U32:
  match zero:
    case True{}:
      ((s + 1 : U32), (s + 1 : U32))
    case False{}:
      ((s + a : U32), (a + a + s : U32))

def fam.step(k: U32, s: U32, a: U32) -> U32 & U32:
  fam.pick(U32.is_lt(k, 1), s, a)

def input() -> F.Events(F.Side<U32, U32>):
  [F.Occ{F.Time.secs(1), F.Fire{10}}, F.Occ{F.Time.secs(2), F.Fire{10}}, F.Occ{F.Time.secs(3), F.Set{1}}, F.Occ{F.Time.secs(4), F.Fire{5}},
   F.Occ{F.Time.secs(5), F.Fire{7}}, F.Occ{F.Time.secs(6), F.Set{0}}, F.Occ{F.Time.secs(7), F.Fire{9}}, F.Occ{F.Time.secs(8), F.Set{1}}, F.Occ{F.Time.secs(9), F.Fire{1}}]

def vals(e: F.Events(U32)) -> List<&2, U32>:
  match e:
    case Nil{}:
      Nil{}
    case Con{o, rest}:
      F.Occ.val(U32, o) <> vals(rest)

def machine() -> List<&2, U32>:
  vals(F.E.justs(U32, F.E.run(~F.Both<U32, U32>, ~F.Side<U32, U32>, ~Maybe<&2, U32>,
                              ~(st => j => F.switch.step(~U32, ~U32, ~U32, ~U32, ~fam.init, ~fam.step, st, j)),
                              input(), F.Both{0, fam.init(0)})))

def meaning() -> List<&2, U32>:
  vals(F.E.switched(~U32, ~U32, ~U32, ~U32, ~fam.init, ~fam.step, input(), 0, fam.init(0)))

def main() -> List<&2, List<&2, U32>>:
  [machine(), meaning()]
