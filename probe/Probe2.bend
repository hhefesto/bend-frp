import Base

# A running form: a state, and a step from an input to the next state and
# an output. Passed as a template (~), as Base's App is, so its step may be
# called again and again.
type Run<-S: Data, -A: Data, -B: Data> is Type:
  Run{init: S, step: S -> A -> S & B}

type Both<-S: Data, -T: Data> is Data:
  Both{+fst: S, +snd: T}

# accum: each input folded into the state, which is also the output.
def accum(~S: Data, ~A: Data, ~f: S -> A -> S, +x: S) -> Run<S, A, S>:
  Run{x, s => a => (+n = f(s, a); (n, n))}

def then.b(-S: Data, -T: Data, -C: Data, tz: T & C, s: S) -> Both<S, T> & C:
  match tz:
    case (t, z):
      (Both{s, t}, z)

def then.a(-S: Data, -T: Data, -B: Data, -C: Data, sy: S & B, t: T, sb: T -> B -> T & C) ->
  Both<S, T> & C:
  match sy:
    case (s, y):
      then.b(S, T, C, sb(t, y), s)

def then.go(-S: Data, -T: Data, -A: Data, -B: Data, -C: Data, st: Both<S, T>, x: A,
            sa: S -> A -> S & B, sb: T -> B -> T & C) -> Both<S, T> & C:
  match st:
    case Both{s, t}:
      then.a(S, T, B, C, sa(s, x), t, sb)

# then: b after a, a's output as b's input; the state is both states.
def then(-S: Data, -T: Data, -A: Data, -B: Data, -C: Data, a: Run<S, A, B>, b: Run<T, B, C>) ->
  Run<Both<S, T>, A, C>:
  Run{ia, sa} = a
  Run{ib, sb} = b
  Run{Both{ia, ib}, st => x => then.go(S, T, A, B, C, st, x, sa, sb)}

def go.push(-S: Data, -B: Data, sy: S & B, out: List<&2, B>) -> S & List<&2, B>:
  match sy:
    case (s, y):
      (s, y <> out)

def go.step(-S: Data, -A: Data, -B: Data, r: Run<S, A, B>, x: A, sy: S & List<&2, B>) ->
  S & List<&2, B>:
  Run{i, step} = r
  (s, out) = sy
  go.push(S, B, step(s, x), out)

def go(~S: Data, ~A: Data, ~B: Data, ~r: Run<S, A, B>, xs: List<&2, A>, sy: S & List<&2, B>) ->
  List<&2, B>:
  match xs:
    case Nil{}:
      (s, out) = sy
      List.reverse(&2, B, out)
    case Con{x, rest}:
      go(~S, ~A, ~B, ~r, rest, go.step(S, A, B, r, x, sy))

def add(s: U32, a: U32) -> U32:
  (s + a : U32)

def main() -> List<&2, U32>:
  go(~Both<U32, U32>, ~U32, ~U32,
     ~then(U32, U32, U32, U32, U32, accum(~U32, ~U32, ~add, 0), accum(~U32, ~U32, ~add, 100)),
     [1, 2, 3], (Both{0, 100}, []))
