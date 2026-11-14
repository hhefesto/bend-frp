import Base
import ./Frp.bend as F

# Dynamic values: Reflex's Dynamic, Elliott's reactive value (a value and an
# event of later values, in "Push-pull functional reactive programming").
#
# The meaning: a Dyn is a value that changes only when an event says, so it
# is the pair of a behavior and an event,
#   current(d) = B.stepper(init, changes)    (a function of time)
#   updated(d) = changes                     (when and to what it changes)
# and it is held as just that data: its first value and its changes. Every
# operation is defined by what it does to current and updated, and LAWS.bend
# says that each agrees (Elliott's type class morphisms: current of a map is
# the map of current, current of a zip is the pair of currents).

type Dyn<-A: Data> is Data:
  Dyn{+init: A, +changes: List<&2, F.Occ<A>>}

# The behavior: at t, the latest value changed to strictly before t, or the
# first value.
def Dyn.current(-A: Data, d: Dyn<A>) -> F.Behavior(A):
  match d:
    case Dyn{x, e}:
      F.B.stepper(A, x, e)

# The event of its changes.
def Dyn.updated(-A: Data, d: Dyn<A>) -> F.Events(A):
  match d:
    case Dyn{x, e}:
      e

# holdDyn: x, then each value e delivers.
def Dyn.hold(-A: Data, x: A, e: F.Events(A)) -> Dyn<A>:
  Dyn{x, e}

# foldDyn: x, then f folded over the values e delivers, one change each.
def Dyn.fold(~A: Data, ~B: Data, ~f: B -> A -> B, +x: B, e: F.Events(A)) -> Dyn<B>:
  Dyn{x, F.E.accum(~A, ~B, ~f, e, x)}

# constDyn: x, never changing.
def Dyn.pure(-A: Data, x: A) -> Dyn<A>:
  Dyn{x, Nil{}}

# fmap: every value through f.
def Dyn.map(~A: Data, ~B: Data, ~f: A -> B, d: Dyn<A>) -> Dyn<B>:
  match d:
    case Dyn{x, e}:
      Dyn{f(x), F.E.map(~A, ~B, ~f, e)}

# zipDyn: both values, as a pair; it changes when either does (once, when
# both change at one time).
def Dyn.zip.pick(-A: Data, -B: Data, c: Cmp, +t: F.Time, +x: A, +u: F.Time, +y: B, +a: A, +b: B,
                 lt: Unit -> F.Events(F.Both<A, B>), gt: Unit -> F.Events(F.Both<A, B>),
                 eq: Unit -> F.Events(F.Both<A, B>)) -> F.Events(F.Both<A, B>):
  match c:
    case LT{}:
      F.Occ{t, F.Both{x, b}} <> lt(Unit{})
    case EQ{}:
      F.Occ{t, F.Both{x, y}} <> eq(Unit{})
    case GT{}:
      F.Occ{u, F.Both{a, y}} <> gt(Unit{})

def Dyn.zip.go(-A: Data, -B: Data, ea: F.Events(A), eb: F.Events(B), +a: A, +b: B) -> F.Events(F.Both<A, B>):
  match ea eb:
    case Nil{} Nil{}:
      Nil{}
    case Nil{} Con{F.Occ{+u, +y}, ys}:
      F.Occ{u, F.Both{a, y}} <> Dyn.zip.go(A, B, Nil{}, ys, a, y)
    case Con{F.Occ{+t, +x}, xs} Nil{}:
      F.Occ{t, F.Both{x, b}} <> Dyn.zip.go(A, B, xs, Nil{}, x, b)
    case Con{F.Occ{+t, +x}, +xs} Con{F.Occ{+u, +y}, +ys}:
      Dyn.zip.pick(A, B, F.Time.cmp(t, u), t, x, u, y, a, b,
        w => Dyn.zip.go(A, B, xs, F.Occ{u, y} <> ys, x, b),
        w => Dyn.zip.go(A, B, F.Occ{t, x} <> xs, ys, a, y),
        w => Dyn.zip.go(A, B, xs, ys, x, y))

def Dyn.zip(-A: Data, -B: Data, da: Dyn<A>, db: Dyn<B>) -> Dyn<F.Both<A, B>>:
  match da db:
    case Dyn{+a, ea} Dyn{+b, eb}:
      Dyn{F.Both{a, b}, Dyn.zip.go(A, B, ea, eb, a, b)}

# zipDynWith: f of both values.
def Dyn.zip_with.app(~A: Data, ~B: Data, ~C: Data, ~f: A -> B -> C, p: F.Both<A, B>) -> C:
  match p:
    case F.Both{a, b}:
      f(a, b)

def Dyn.zip_with(~A: Data, ~B: Data, ~C: Data, ~f: A -> B -> C, da: Dyn<A>, db: Dyn<B>) -> Dyn<C>:
  Dyn.map(~F.Both<A, B>, ~C, ~Dyn.zip_with.app(~A, ~B, ~C, ~f), Dyn.zip(A, B, da, db))

# join: a Dyn of Dyns as one, which at t is the value at t of the Dyn the
# outer one holds at t (Reflex's join for Dynamic). Its changes: the inner
# Dyn's, until the outer changes; then, at that time, the new inner's value
# there, and its later changes.

# The occurrences ahead of the first after u (at or before u, for an event in
# time order).
def Dyn.upto(-A: Data, e: F.Events(A), +u: F.Time) -> F.Events(A):
  match e:
    case Nil{}:
      Nil{}
    case Con{F.Occ{+v, y}, rest}:
      F.E.before.if(A, w => F.Occ{v, y} <> Dyn.upto(A, rest, u), F.Time.le(v, u))

# The value of the last of them, or x.
def Dyn.last_le(-A: Data, e: F.Events(A), +u: F.Time, x: A) -> A:
  match e:
    case Nil{}:
      x
    case Con{F.Occ{+v, y}, rest}:
      F.B.stepper.if(A, w => Dyn.last_le(A, rest, u, y), x, F.Time.le(v, u))

# The rest.
def Dyn.after.if(-A: Data, more: Unit -> F.Events(A), here: F.Events(A), past: Bool) -> F.Events(A):
  match past:
    case True{}:
      more(Unit{})
    case False{}:
      here

def Dyn.after(-A: Data, e: F.Events(A), +u: F.Time) -> F.Events(A):
  match e:
    case Nil{}:
      Nil{}
    case Con{F.Occ{+v, +y}, +rest}:
      Dyn.after.if(A, w => Dyn.after(A, rest, u), F.Occ{v, y} <> rest, F.Time.le(v, u))

def Dyn.join.go(-A: Data, ds: F.Events(Dyn<A>), ic: F.Events(A)) -> F.Events(A):
  match ds:
    case Nil{}:
      ic
    case Con{F.Occ{+to, Dyn{x2, +ic2}}, rest}:
      List.append(&2, F.Occ<A>, Dyn.upto(A, ic, to),
        F.Occ{to, Dyn.last_le(A, ic2, to, x2)} <> Dyn.join.go(A, rest, Dyn.after(A, ic2, to)))

def Dyn.join(-A: Data, dd: Dyn<Dyn<A>>) -> Dyn<A>:
  match dd:
    case Dyn{d0, ds}:
      match d0:
        case Dyn{x0, ic0}:
          Dyn{x0, Dyn.join.go(A, ds, ic0)}
