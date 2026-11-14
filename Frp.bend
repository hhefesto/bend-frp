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

# The continuation is passed eta-expanded (r => j(r)): the checker expands j
# where a law states it, and BendTT's kernel compares terms without eta, so
# this form lets the kernel see merge's laws hold (LAWS.e_merge_first, _later).
def E.merge.in(-A: Data, +x: Occ<A>, e2: Events(A), k: Events(A) -> Events(A)) -> Events(A):
  match e2:
    case Nil{}:
      x <> k(Nil{})
    case Con{+y, +ys}:
      E.merge.pick(A, U32.is_lt(Occ.at(A, y), Occ.at(A, x)), x, y, k, ys, j => E.merge.in(A, x, ys, r => j(r)))

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


# The occurrences strictly before t. An event is in time order, so they are
# the ones ahead of its first at or after t.
def E.before.if(-A: Data, more: Unit -> Events(A), before: Bool) -> Events(A):
  match before:
    case True{}:
      more(Unit{})
    case False{}:
      Nil{}

def E.before(-A: Data, e: Events(A), +t: U32) -> Events(A):
  match e:
    case Nil{}:
      Nil{}
    case Con{o, rest}:
      match o:
        case Occ{+u, y}:
          E.before.if(A, w => Occ{u, y} <> E.before(A, rest, t), U32.is_lt(u, t))
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

# Both's halves.
def Both.fst(-S: Data, -T: Data, p: Both<S, T>) -> S:
  match p:
    case Both{s, t}:
      s

def Both.snd(-S: Data, -T: Data, p: Both<S, T>) -> T:
  match p:
    case Both{s, t}:
      t

# Sampling
# --------

# E.snapshot(f, e, b): each occurrence (t, a) of e as (t, f(a, b(t))). Bend
# lets a def call a closure once, so the meaning takes the behavior as a
# template, which it may sample at every occurrence.
def E.snapshot(~A: Data, ~B: Data, ~C: Data, ~f: A -> B -> C, ~b: Behavior(B), e: Events(A)) -> Events(C):
  match e:
    case Nil{}:
      Nil{}
    case Con{o, rest}:
      match o:
        case Occ{+t, a}:
          Occ{t, f(a, b(t))} <> E.snapshot(~A, ~B, ~C, ~f, ~b, rest)

# The same against B.stepper(x, d), a behavior described by data: each
# occurrence (t, a) as (t, f(a, B.stepper(x, d)(t))).
def E.snapshot.stepper(~A: Data, ~B: Data, ~C: Data, ~f: A -> B -> C, e: Events(A), +x: B, +d: Events(B)) ->
  Events(C):
  match e:
    case Nil{}:
      Nil{}
    case Con{o, rest}:
      match o:
        case Occ{+t, a}:
          Occ{t, f(a, B.stepper.at(B, d, t, x))} <> E.snapshot.stepper(~A, ~B, ~C, ~f, rest, x, d)

# One event carrying two: the occurrences to sample at, and a stepper's
# values. A network has one input event (the page's), so this is how a
# machine sees both.
type Side<-A: Data, -B: Data> is Data:
  Fire{+value: A}
  Set{+value: B}

def E.fires(-A: Data, -B: Data, i: Events(Side<A, B>)) -> Events(A):
  match i:
    case Nil{}:
      Nil{}
    case Con{o, rest}:
      match o:
        case Occ{t, s}:
          match s:
            case Fire{a}:
              Occ{t, a} <> E.fires(A, B, rest)
            case Set{v}:
              E.fires(A, B, rest)

def E.sets(-A: Data, -B: Data, i: Events(Side<A, B>)) -> Events(B):
  match i:
    case Nil{}:
      Nil{}
    case Con{o, rest}:
      match o:
        case Occ{t, s}:
          match s:
            case Fire{a}:
              E.sets(A, B, rest)
            case Set{v}:
              Occ{t, v} <> E.sets(A, B, rest)

# The occurrences that carry a value.
def E.justs(-C: Data, e: Events(Maybe<&2, C>)) -> Events(C):
  match e:
    case Nil{}:
      Nil{}
    case Con{o, rest}:
      match o:
        case Occ{t, m}:
          match m:
            case None{}:
              E.justs(C, rest)
            case Some{c}:
              Occ{t, c} <> E.justs(C, rest)

# Whether no occurrence is before t.
def E.none_before(-A: Data, e: Events(A), +t: U32) -> Bool:
  match e:
    case Nil{}:
      True{}
    case Con{o, rest}:
      Bool.not(U32.is_lt(Occ.at(A, o), t)) && E.none_before(A, rest, t)

# Whether every occurrence is after u.
def E.all_after(-A: Data, e: Events(A), +u: U32) -> Bool:
  match e:
    case Nil{}:
      True{}
    case Con{o, rest}:
      U32.is_lt(u, Occ.at(A, o)) && E.all_after(A, rest, u)

# Whether a Side event's order is its times' order where it matters: no value
# is set before (in time) a sample listed ahead of it, and every sample
# listed after a value is set comes later in time. (Two time-ordered events
# merged, samples first at equal times, as E.merge(fires, sets) does.)
def snap.ok(-A: Data, -B: Data, i: Events(Side<A, B>)) -> Bool:
  match i:
    case Nil{}:
      True{}
    case Con{o, +rest}:
      match o:
        case Occ{+t, s}:
          match s:
            case Fire{a}:
              E.none_before(B, E.sets(A, B, rest), t) && snap.ok(A, B, rest)
            case Set{v}:
              E.all_after(A, E.fires(A, B, rest), t) && snap.ok(A, B, rest)

# snap: a stepper's value as the state; a sample is f of its value and the
# state, a set is no output.
def snap.step(~A: Data, ~B: Data, ~C: Data, ~f: A -> B -> C, +s: B, i: Side<A, B>) -> B & Maybe<&2, C>:
  match i:
    case Fire{a}:
      (s, Some{f(a, s)})
    case Set{v}:
      (v, None{})

def snap(~A: Data, ~B: Data, ~C: Data, ~f: A -> B -> C, +x: B) -> Run<B, Side<A, B>, Maybe<&2, C>>:
  Run{x, s => i => snap.step(~A, ~B, ~C, ~f, s, i)}

# Switching
# ---------

# B.switcher(fam, k, e): fam(k) until e's first occurrence, then fam of the
# latest value e delivered (strictly before t, as B.stepper). A behavior is
# a closure, which an occurrence (data) cannot carry, so e carries keys into
# a family of behaviors.
def B.switcher(~K: Data, ~A: Type, ~fam: K -> Behavior(A), +k: K, +e: Events(K)) -> Behavior(A):
  +t => fam(B.stepper.at(K, e, t, k))(t)

# A family of machines over one state type: machine k starts from init(k)
# and steps by step(k). Its running form holds its key beside its state,
# and its step never changes the key.
def switch.keep(-K: Data, -S: Data, -B: Data, k: K, sy: S & B) -> Both<K, S> & B:
  (s, y) = sy
  (Both{k, s}, y)

def switch.run(~K: Data, ~S: Data, ~A: Data, ~B: Data, ~step: K -> S -> A -> S & B, st: Both<K, S>, a: A) ->
  Both<K, S> & B:
  match st:
    case Both{+k, s}:
      switch.keep(K, S, B, k, step(k, s, a))

def switch.out(-K: Data, -S: Data, -B: Data, p: Both<K, S> & B) -> Both<K, S> & Maybe<&2, B>:
  (st, y) = p
  (st, Some{y})

# switch: over one event of inputs (Fire) and keys (Set), the family's
# machine for the latest key, started afresh at each key.
def switch.step(~K: Data, ~S: Data, ~A: Data, ~B: Data, ~init: K -> S, ~step: K -> S -> A -> S & B,
                st: Both<K, S>, i: Side<A, K>) -> Both<K, S> & Maybe<&2, B>:
  match i:
    case Fire{a}:
      switch.out(K, S, B, switch.run(~K, ~S, ~A, ~B, ~step, st, a))
    case Set{+k}:
      (Both{k, init(k)}, None{})

def switch(~K: Data, ~S: Data, ~A: Data, ~B: Data, ~init: K -> S, ~step: K -> S -> A -> S & B, +k: K) ->
  Run<Both<K, S>, Side<A, K>, Maybe<&2, B>>:
  Run{Both{k, init(k)}, st => i => switch.step(~K, ~S, ~A, ~B, ~init, ~step, st, i)}

# What a switch means. The inputs before the first key, through the machine
# it is running; then, from each key on, the inputs before the next key,
# through that key's machine from its start; the outputs in that order.
def E.upto(-A: Data, -K: Data, i: Events(Side<A, K>)) -> Events(A):
  match i:
    case Nil{}:
      Nil{}
    case Con{o, rest}:
      match o:
        case Occ{t, s}:
          match s:
            case Fire{a}:
              Occ{t, a} <> E.upto(A, K, rest)
            case Set{k}:
              Nil{}

def E.switched.after(~K: Data, ~S: Data, ~A: Data, ~B: Data, ~init: K -> S, ~step: K -> S -> A -> S & B,
                     i: Events(Side<A, K>)) -> Events(B):
  match i:
    case Nil{}:
      Nil{}
    case Con{o, +rest}:
      match o:
        case Occ{t, s}:
          match s:
            case Fire{a}:
              E.switched.after(~K, ~S, ~A, ~B, ~init, ~step, rest)
            case Set{+k}:
              List.append(&2, Occ<B>,
                E.run(~Both<K, S>, ~A, ~B, ~switch.run(~K, ~S, ~A, ~B, ~step), E.upto(A, K, rest), Both{k, init(k)}),
                E.switched.after(~K, ~S, ~A, ~B, ~init, ~step, rest))

def E.switched(~K: Data, ~S: Data, ~A: Data, ~B: Data, ~init: K -> S, ~step: K -> S -> A -> S & B,
               +i: Events(Side<A, K>), k: K, s: S) -> Events(B):
  List.append(&2, Occ<B>,
    E.run(~Both<K, S>, ~A, ~B, ~switch.run(~K, ~S, ~A, ~B, ~step), E.upto(A, K, i), Both{k, s}),
    E.switched.after(~K, ~S, ~A, ~B, ~init, ~step, i))
