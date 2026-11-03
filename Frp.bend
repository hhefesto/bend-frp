import Base

# bend-frp's core: what its words mean, and the machines that run them.
# README.md says why it has this shape; LAWS.bend says how the two agree.

# The meaning
# -----------

# Time is the runtime's clock. The meaning asks only that occurrences come in
# order; nothing here counts ticks.
def Time() -> Data:
  U32

# Behavior<A> means a function of time.
def Behavior(-A: Type) -> Type:
  Time() -> A

# An occurrence: a value at a time.
type Occ<-A: Data> is Data:
  Occ{+at: U32, +val: A}

# Events<A> means its occurrences, in time order.
def Events(-A: Data) -> Data:
  List<&2, Occ<A>>

def B.pure(-A: Type, x: A) -> Behavior(A):
  t => x

def B.time() -> Behavior(U32):
  t => t

def B.map(-A: Type, -B: Type, f: A -> B, b: Behavior(A)) -> Behavior(B):
  t => f(b(t))

def B.ap(-A: Type, -B: Type, bf: Behavior(A -> B), bx: Behavior(A)) -> Behavior(B):
  +t => bf(t)(bx(t))

def ident(-A: Data, x: A) -> A:
  x

def always(-A: Data, x: A) -> Bool:
  True{}

def comp(~A: Data, ~B: Data, ~C: Data, ~f: A -> B, ~g: B -> C, x: A) -> C:
  g(f(x))

def E.never(-A: Data) -> Events(A):
  Nil{}

def Occ.map(~A: Data, ~B: Data, ~f: A -> B, o: Occ<A>) -> Occ<B>:
  match o:
    case Occ{t, x}:
      Occ{t, f(x)}

def E.map(~A: Data, ~B: Data, ~f: A -> B, e: Events(A)) -> Events(B):
  match e:
    case Nil{}:
      Nil{}
    case Con{o, rest}:
      Occ.map(~A, ~B, ~f, o) <> E.map(~A, ~B, ~f, rest)

def E.keep(-A: Data, +o: Occ<A>, rest: Events(A), hit: Bool) -> Events(A):
  match hit:
    case True{}:
      o <> rest
    case False{}:
      rest

def Occ.val(-A: Data, o: Occ<A>) -> A:
  match o:
    case Occ{t, x}:
      x

def E.filter(~A: Data, ~p: A -> Bool, e: Events(A)) -> Events(A):
  match e:
    case Nil{}:
      Nil{}
    case Con{+o, rest}:
      E.keep(A, o, E.filter(~A, ~p, rest), p(Occ.val(A, o)))

def Occ.at(-A: Data, o: Occ<A>) -> U32:
  match o:
    case Occ{t, x}:
      t

# Both events' occurrences in time order, e1's first at equal times.
def E.merge.pick(-A: Data, later: Bool, x: Occ<A>, y: Occ<A>, k: Events(A) -> Events(A), ys: Events(A),
                 there: (Events(A) -> Events(A)) -> Events(A)) -> Events(A):
  match later:
    case True{}:
      y <> there(k)
    case False{}:
      x <> k(y <> ys)

def E.merge.in(-A: Data, +x: Occ<A>, e2: Events(A), k: Events(A) -> Events(A)) -> Events(A):
  match e2:
    case Nil{}:
      x <> k(Nil{})
    case Con{+y, +ys}:
      E.merge.pick(A, U32.is_lt(Occ.at(A, y), Occ.at(A, x)), x, y, k, ys, j => E.merge.in(A, x, ys, j))

def E.merge(-A: Data, e1: Events(A), e2: Events(A)) -> Events(A):
  match e1:
    case Nil{}:
      e2
    case Con{+x, xs}:
      E.merge.in(A, x, e2, r => E.merge(A, xs, r))

# B.stepper at t: x before e's first occurrence, then its latest value
# strictly before t.
def B.stepper.if(-A: Data, later: Unit -> A, now: A, before: Bool) -> A:
  match before:
    case True{}:
      later(Unit{})
    case False{}:
      now

def B.stepper.at(-A: Data, e: Events(A), +t: U32, x: A) -> A:
  match e:
    case Nil{}:
      x
    case Con{o, rest}:
      match o:
        case Occ{+u, y}:
          B.stepper.if(A, w => B.stepper.at(A, rest, t, y), x, U32.is_lt(u, t))

def B.stepper(-A: Data, x: A, e: Events(A)) -> Behavior(A):
  +t => B.stepper.at(A, e, t, x)

# Whether every occurrence is before t.
def E.all_before(-A: Data, e: Events(A), +t: U32) -> Bool:
  match e:
    case Nil{}:
      True{}
    case Con{o, rest}:
      U32.is_lt(Occ.at(A, o), t) && E.all_before(A, rest, t)

# The latest value of an event, or x when it has none.
def E.last(-A: Data, e: Events(A), x: A) -> A:
  match e:
    case Nil{}:
      x
    case Con{o, rest}:
      E.last(A, rest, Occ.val(A, o))

# An event with any number of values at each occurrence, spread into one
# occurrence for each.
def E.spread(-A: Data, +t: U32, xs: List<&2, A>, rest: Events(A)) -> Events(A):
  match xs:
    case Nil{}:
      rest
    case Con{x, more}:
      Occ{t, x} <> E.spread(A, t, more, rest)

def E.flat(-A: Data, e: Events(List<&2, A>)) -> Events(A):
  match e:
    case Nil{}:
      Nil{}
    case Con{o, rest}:
      match o:
        case Occ{+t, xs}:
          E.spread(A, t, xs, E.flat(A, rest))

# The folds of a history through a function, one for each occurrence.
def E.accum(~A: Data, ~B: Data, ~f: B -> A -> B, e: Events(A), +x: B) -> Events(B):
  match e:
    case Nil{}:
      Nil{}
    case Con{o, rest}:
      match o:
        case Occ{t, a}:
          +n = f(x, a)
          Occ{t, n} <> E.accum(~A, ~B, ~f, rest, n)

# The machines
# ------------

# A running form: a state, and a step from an input to the next state and an
# output. Passed as a template (~), as Base's App is, so its step may be
# called again and again.
type Run<-S: Data, -A: Data, -B: Data> is Type:
  Run{init: S, step: S -> A -> S & B}

type Both<-S: Data, -T: Data> is Data:
  Both{+fst: S, +snd: T}

def Run.init(-S: Data, -A: Data, -B: Data, r: Run<S, A, B>) -> S:
  match r:
    case Run{i, s}:
      i

def Run.step(-S: Data, -A: Data, -B: Data, r: Run<S, A, B>) -> S -> A -> S & B:
  match r:
    case Run{i, s}:
      s

# What a machine does to a list of inputs from a state: one output each.
def Run.push(-S: Data, -B: Data, sy: S & B, k: S -> List<&2, B>) -> List<&2, B>:
  (s, y) = sy
  y <> k(s)

def Run.from(~S: Data, ~A: Data, ~B: Data, ~step: S -> A -> S & B, xs: List<&2, A>, s: S) -> List<&2, B>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, rest}:
      Run.push(S, B, step(s, x), t => Run.from(~S, ~A, ~B, ~step, rest, t))

# each: a machine over the values of an occurrence, in order, its state
# carried from one to the next.
def each.done(-T: Data, -C: Data, y: C, r: T & List<&2, C>) -> T & List<&2, C>:
  (t, ys) = r
  (t, y <> ys)

def each.push(-T: Data, -C: Data, p: T & C, k: T -> T & List<&2, C>) -> T & List<&2, C>:
  (t, y) = p
  each.done(T, C, y, k(t))

def each.go(~T: Data, ~B: Data, ~C: Data, ~sb: T -> B -> T & C, xs: List<&2, B>, t: T) -> T & List<&2, C>:
  match xs:
    case Nil{}:
      (t, Nil{})
    case Con{x, rest}:
      each.push(T, C, sb(t, x), u => each.go(~T, ~B, ~C, ~sb, rest, u))

def each.step(~T: Data, ~B: Data, ~C: Data, ~sb: T -> B -> T & C, t: T, xs: List<&2, B>) -> T & List<&2, C>:
  each.go(~T, ~B, ~C, ~sb, xs, t)

def each(~T: Data, ~B: Data, ~C: Data, ~b: Run<T, B, C>) -> Run<T, List<&2, B>, List<&2, C>>:
  Run{Run.init(T, B, C, b), t => xs => each.step(~T, ~B, ~C, ~Run.step(T, B, C, b), t, xs)}

# The steps by name, so laws can speak of them.
def lift.step(~A: Data, ~B: Data, ~f: A -> B, s: Unit, x: A) -> Unit & B:
  (s, f(x))

def accum.step(~A: Data, ~B: Data, ~f: B -> A -> B, s: B, a: A) -> B & B:
  +n = f(s, a)
  (n, n)

# lift: no state; each input through f.
def lift(~A: Data, ~B: Data, ~f: A -> B) -> Run<Unit, A, B>:
  Run{Unit{}, s => x => lift.step(~A, ~B, ~f, s, x)}

# accum: each input folded into the state, which is also the output.
def accum(~A: Data, ~B: Data, ~f: B -> A -> B, +x: B) -> Run<B, A, B>:
  Run{x, s => a => accum.step(~A, ~B, ~f, s, a)}

# then: b after a, a's output as b's input; the state is both states.
def then.b(-S: Data, -T: Data, -C: Data, s: S, tz: T & C) -> Both<S, T> & C:
  (t, z) = tz
  (Both{s, t}, z)

def then.a(~S: Data, ~T: Data, ~B: Data, ~C: Data, ~sb: T -> B -> T & C, t: T, sy: S & B) ->
  Both<S, T> & C:
  (s, y) = sy
  then.b(S, T, C, s, sb(t, y))

def then.step(~S: Data, ~T: Data, ~A: Data, ~B: Data, ~C: Data,
              ~sa: S -> A -> S & B, ~sb: T -> B -> T & C, st: Both<S, T>, x: A) -> Both<S, T> & C:
  match st:
    case Both{s, t}:
      then.a(~S, ~T, ~B, ~C, ~sb, t, sa(s, x))

def then(~S: Data, ~T: Data, ~A: Data, ~B: Data, ~C: Data, ~a: Run<S, A, B>, ~b: Run<T, B, C>) ->
  Run<Both<S, T>, A, C>:
  Run{Both{Run.init(S, A, B, a), Run.init(T, B, C, b)},
      then.step(~S, ~T, ~A, ~B, ~C, ~Run.step(S, A, B, a), ~Run.step(T, B, C, b))}

# par: both on the same input; the output is both outputs.
def par.b(-S: Data, -T: Data, -B: Data, -C: Data, s: S, y: B, tz: T & C) -> Both<S, T> & Both<B, C>:
  (t, z) = tz
  (Both{s, t}, Both{y, z})

def par.a(~S: Data, ~T: Data, ~A: Data, ~B: Data, ~C: Data, ~sb: T -> A -> T & C, t: T, +x: A, sy: S & B) ->
  Both<S, T> & Both<B, C>:
  (s, y) = sy
  par.b(S, T, B, C, s, y, sb(t, x))

def par.step(~S: Data, ~T: Data, ~A: Data, ~B: Data, ~C: Data,
             ~sa: S -> A -> S & B, ~sb: T -> A -> T & C, st: Both<S, T>, +x: A) -> Both<S, T> & Both<B, C>:
  match st:
    case Both{s, t}:
      par.a(~S, ~T, ~A, ~B, ~C, ~sb, t, x, sa(s, x))

def par(~S: Data, ~T: Data, ~A: Data, ~B: Data, ~C: Data, ~a: Run<S, A, B>, ~b: Run<T, A, C>) ->
  Run<Both<S, T>, A, Both<B, C>>:
  Run{Both{Run.init(S, A, B, a), Run.init(T, A, C, b)},
      s => +x => par.step(~S, ~T, ~A, ~B, ~C, ~Run.step(S, A, B, a), ~Run.step(T, A, C, b), s, x)}

# A machine over an event: the same occurrences, their values through it.
def E.push(-S: Data, -B: Data, +t: U32, sy: S & B, k: S -> Events(B)) -> Events(B):
  (s, y) = sy
  Occ{t, y} <> k(s)

def E.run(~S: Data, ~A: Data, ~B: Data, ~step: S -> A -> S & B, e: Events(A), s: S) -> Events(B):
  match e:
    case Nil{}:
      Nil{}
    case Con{o, rest}:
      match o:
        case Occ{t, x}:
          E.push(S, B, t, step(s, x), u => E.run(~S, ~A, ~B, ~step, rest, u))

# The running form's history: the machine, from its first state, over a list.
def run(~S: Data, ~A: Data, ~B: Data, ~r: Run<S, A, B>, xs: List<&2, A>) -> List<&2, B>:
  Run.from(~S, ~A, ~B, ~Run.step(S, A, B, r), xs, Run.init(S, A, B, r))
