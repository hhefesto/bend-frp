# The claims of bend-frp: what its words mean, and that its machines do that.
# The human owns this file. PROOF.bend proves it; a law that turns out false
# is reported, not reworded.

import Base
import ./Frp.bend as F
import ./Dyn.bend as D
import ./Ops.bend as Op
import ./Web.bend as W

# Behaviors: instances agree with the meaning's, pointwise
# --------------------------------------------------------

law b_map_id:
  for -A: Data
  for -b: F.Behavior(A)
  for -t: F.Time
  {F.B.map(A, A, x => x, b)(t) == b(t) : A}

law b_map_comp:
  for -A: Data
  for -B: Data
  for -C: Data
  for -f: A -> B
  for -g: B -> C
  for -b: F.Behavior(A)
  for -t: F.Time
  {F.B.map(B, C, g, F.B.map(A, B, f, b))(t) == g(f(b(t))) : C}

law b_ap_pure:
  for -A: Data
  for -B: Data
  for -f: A -> B
  for -x: A
  for -t: F.Time
  {F.B.ap(A, B, F.B.pure(A -> B, f), F.B.pure(A, x))(t) == f(x) : B}


# The rest of Elliott's applicative laws for behaviors (b_ap_pure above is the
# homomorphism law), map as pure-then-ap, and time's meaning. A behavior means
# a function of time, so each holds pointwise, at every t.
law b_ap_id:
  for -A: Data
  for -v: F.Behavior(A)
  for -t: F.Time
  {F.B.ap(A, A, F.B.pure(A -> A, x => x), v)(t) == v(t) : A}

law b_ap_comp:
  for -A: Data
  for -B: Data
  for -C: Data
  for -u: F.Behavior(B -> C)
  for -v: F.Behavior(A -> B)
  for -w: F.Behavior(A)
  for -t: F.Time
  {F.B.ap(A, C, F.B.ap(A -> B, A -> C, F.B.ap(B -> C, (A -> B) -> A -> C,
       F.B.pure((B -> C) -> (A -> B) -> A -> C, g => f => x => g(f(x))), u), v), w)(t)
     == F.B.ap(B, C, u, F.B.ap(A, B, v, w))(t) : C}

law b_ap_interchange:
  for -A: Data
  for -B: Data
  for -u: F.Behavior(A -> B)
  for -y: A
  for -t: F.Time
  {F.B.ap(A, B, u, F.B.pure(A, y))(t) == F.B.ap(A -> B, B, F.B.pure((A -> B) -> B, f => f(y)), u)(t) : B}

law b_map_ap:
  for -A: Data
  for -B: Data
  for -f: A -> B
  for -b: F.Behavior(A)
  for -t: F.Time
  {F.B.map(A, B, f, b)(t) == F.B.ap(A, B, F.B.pure(A -> B, f), b)(t) : B}

law b_time:
  for -t: F.Time
  {F.B.time()(t) == t : F.Time}
# Events
# ------

law e_map_id:
  for ~A: Data
  for e: F.Events(A)
  {F.E.map(~A, ~A, ~F.ident(A), e) == e : F.Events(A)}

law e_map_comp:
  for ~A: Data
  for ~B: Data
  for ~C: Data
  for ~f: A -> B
  for ~g: B -> C
  for e: F.Events(A)
  {F.E.map(~B, ~C, ~g, F.E.map(~A, ~B, ~f, e)) == F.E.map(~A, ~C, ~F.comp(~A, ~B, ~C, ~f, ~g), e) : F.Events(C)}

# map's meaning (Elliott's): each occurrence keeps its time, its value goes
# through f. These two pin map down, by induction on the event.
law e_map_never:
  for ~A: Data
  for ~B: Data
  for ~f: A -> B
  {F.E.map(~A, ~B, ~f, F.E.never(A)) == F.E.never(B) : F.Events(B)}

law e_map_occ:
  for ~A: Data
  for ~B: Data
  for ~f: A -> B
  for -t: F.Time
  for -a: A
  for -e: F.Events(A)
  {F.E.map(~A, ~B, ~f, F.Occ{t, a} <> e) == F.Occ{t, f(a)} <> F.E.map(~A, ~B, ~f, e) : F.Events(B)}

law e_filter_all:
  for ~A: Data
  for e: F.Events(A)
  {F.E.filter(~A, ~F.always(A), e) == e : F.Events(A)}

law e_merge_never_l:
  for -A: Data
  for -e: F.Events(A)
  {F.E.merge(A, F.E.never(A), e) == e : F.Events(A)}

law e_merge_never_r:
  for -A: Data
  for e: F.Events(A)
  {F.E.merge(A, e, F.E.never(A)) == e : F.Events(A)}

# merge is Elliott's: of two first occurrences the earlier goes first, e1's at
# equal times. With never on either side (above), these pin merge down: any
# two events have one merge, by induction on both.
law e_merge_first:
  for -A: Data
  for +t: F.Time
  for -a: A
  for -xs: F.Events(A)
  for +u: F.Time
  for -b: A
  for -ys: F.Events(A)
  for h: {F.Time.lt(u, t) == False{} : Bool}
  {F.E.merge(A, F.Occ{t, a} <> xs, F.Occ{u, b} <> ys) == F.Occ{t, a} <> F.E.merge(A, xs, F.Occ{u, b} <> ys) : F.Events(A)}

law e_merge_later:
  for -A: Data
  for +t: F.Time
  for -a: A
  for -xs: F.Events(A)
  for +u: F.Time
  for -b: A
  for -ys: F.Events(A)
  for h: {F.Time.lt(u, t) == True{} : Bool}
  {F.E.merge(A, F.Occ{t, a} <> xs, F.Occ{u, b} <> ys) == F.Occ{u, b} <> F.E.merge(A, F.Occ{t, a} <> xs, ys) : F.Events(A)}

# filter keeps exactly the occurrences whose value passes p, at their times,
# in their order. These three pin filter down, by induction on the event.
law e_filter_never:
  for ~A: Data
  for ~p: A -> Bool
  {F.E.filter(~A, ~p, F.E.never(A)) == F.E.never(A) : F.Events(A)}

law e_filter_keep:
  for ~A: Data
  for ~p: A -> Bool
  for -t: F.Time
  for a: A
  for -e: F.Events(A)
  for h: {p(a) == True{} : Bool}
  {F.E.filter(~A, ~p, F.Occ{t, a} <> e) == F.Occ{t, a} <> F.E.filter(~A, ~p, e) : F.Events(A)}

law e_filter_drop:
  for ~A: Data
  for ~p: A -> Bool
  for -t: F.Time
  for a: A
  for -e: F.Events(A)
  for h: {p(a) == False{} : Bool}
  {F.E.filter(~A, ~p, F.Occ{t, a} <> e) == F.E.filter(~A, ~p, e) : F.Events(A)}

# Machines agree with the meaning
# -------------------------------

law e_run_lift:
  for ~A: Data
  for ~B: Data
  for ~f: A -> B
  for e: F.Events(A)
  for s: Unit
  {F.E.run(~Unit, ~A, ~B, ~F.lift.step(~A, ~B, ~f), e, s) == F.E.map(~A, ~B, ~f, e) : F.Events(B)}

law e_run_accum:
  for ~A: Data
  for ~B: Data
  for ~f: B -> A -> B
  for e: F.Events(A)
  for x: B
  {F.E.run(~B, ~A, ~B, ~F.accum.step(~A, ~B, ~f), e, x) == F.E.accum(~A, ~B, ~f, e, x) : F.Events(B)}

law e_run_then:
  for ~S: Data
  for ~T: Data
  for ~A: Data
  for ~B: Data
  for ~C: Data
  for ~sa: S -> A -> S & B
  for ~sb: T -> B -> T & C
  for e: F.Events(A)
  for s: S
  for t: T
  {F.E.run(~F.Both<S, T>, ~A, ~C, ~F.then.step(~S, ~T, ~A, ~B, ~C, ~sa, ~sb), e, F.Both{s, t})
     == F.E.run(~T, ~B, ~C, ~sb, F.E.run(~S, ~A, ~B, ~sa, e, s), t) : F.Events(C)}

# A machine over each value of an occurrence: the event of its outputs, spread,
# is the machine over the event spread.
law e_run_each:
  for ~T: Data
  for ~B: Data
  for ~C: Data
  for ~sb: T -> B -> T & C
  for e: F.Events(List<&2, B>)
  for t: T
  {F.E.flat(C, F.E.run(~T, ~List<&2, B>, ~List<&2, C>, ~F.each.step(~T, ~B, ~C, ~sb), e, t))
     == F.E.run(~T, ~B, ~C, ~sb, F.E.flat(B, e), t) : F.Events(C)}

# stepper, sampled after all of an event, is the event's last value.
law stepper_after:
  for -A: Data
  for e: F.Events(A)
  for +t: F.Time
  for -x: A
  for all: {F.E.all_before(A, e, t) == True{} : Bool}
  {F.B.stepper(A, x, e)(t) == F.E.last(A, e, x) : A}

# stepper's meaning (Elliott's): at t, the value of the last occurrence
# strictly before t, or x when there is none.
law stepper_before:
  for -A: Data
  for e: F.Events(A)
  for +t: F.Time
  for -x: A
  {F.B.stepper(A, x, e)(t) == F.E.last(A, F.E.before(A, e, t), x) : A}

# switcher's meaning: at t, the family's behavior for the key the keys'
# stepper holds at t, sampled at t.
law switcher_stepper:
  for ~K: Data
  for ~A: Data
  for ~fam: K -> F.Behavior(A)
  for -k: K
  for -e: F.Events(K)
  for -t: F.Time
  {F.B.switcher(~K, ~A, ~fam, k, e)(t) == fam(F.B.stepper(K, k, e)(t))(t) : A}

# par: each half of its output is that machine alone
# -------------------------------------------------

law e_run_par_fst:
  for ~S: Data
  for ~T: Data
  for ~A: Data
  for ~B: Data
  for ~C: Data
  for ~sa: S -> A -> S & B
  for ~sb: T -> A -> T & C
  for e: F.Events(A)
  for s: S
  for t: T
  {F.E.map(~F.Both<B, C>, ~B, ~F.Both.fst(B, C),
           F.E.run(~F.Both<S, T>, ~A, ~F.Both<B, C>, ~(st => +x => F.par.step(~S, ~T, ~A, ~B, ~C, ~sa, ~sb, st, x)), e, F.Both{s, t}))
     == F.E.run(~S, ~A, ~B, ~sa, e, s) : F.Events(B)}

law e_run_par_snd:
  for ~S: Data
  for ~T: Data
  for ~A: Data
  for ~B: Data
  for ~C: Data
  for ~sa: S -> A -> S & B
  for ~sb: T -> A -> T & C
  for e: F.Events(A)
  for s: S
  for t: T
  {F.E.map(~F.Both<B, C>, ~C, ~F.Both.snd(B, C),
           F.E.run(~F.Both<S, T>, ~A, ~F.Both<B, C>, ~(st => +x => F.par.step(~S, ~T, ~A, ~B, ~C, ~sa, ~sb, st, x)), e, F.Both{s, t}))
     == F.E.run(~T, ~A, ~C, ~sb, e, t) : F.Events(C)}

# snapshot
# --------

# snapshot's meaning (Elliott's): each occurrence keeps its time and pairs its
# value with the behavior's at that time. These two pin snapshot down.
law e_snapshot_never:
  for ~A: Data
  for ~B: Data
  for ~C: Data
  for ~f: A -> B -> C
  for ~b: F.Behavior(B)
  {F.E.snapshot(~A, ~B, ~C, ~f, ~b, F.E.never(A)) == F.E.never(C) : F.Events(C)}

law e_snapshot_occ:
  for ~A: Data
  for ~B: Data
  for ~C: Data
  for ~f: A -> B -> C
  for ~b: F.Behavior(B)
  for -t: F.Time
  for -a: A
  for -e: F.Events(A)
  {F.E.snapshot(~A, ~B, ~C, ~f, ~b, F.Occ{t, a} <> e) == F.Occ{t, f(a, b(t))} <> F.E.snapshot(~A, ~B, ~C, ~f, ~b, e) : F.Events(C)}

# The data form is the meaning at a stepper.
law snapshot_stepper:
  for ~A: Data
  for ~B: Data
  for ~C: Data
  for ~f: A -> B -> C
  for ~x: B
  for ~d: F.Events(B)
  for e: F.Events(A)
  {F.E.snapshot(~A, ~B, ~C, ~f, ~F.B.stepper(B, x, d), e) == F.E.snapshot.stepper(~A, ~B, ~C, ~f, e, x, d) : F.Events(C)}

# The machine agrees with the meaning: snap over one event of samples and
# values, ordered as snap.ok says, is the samples snapshotted against the
# stepper of the values.
law e_run_snap:
  for ~A: Data
  for ~B: Data
  for ~C: Data
  for ~f: A -> B -> C
  for i: F.Events(F.Side<A, B>)
  for x: B
  for ok: {F.snap.ok(A, B, i) == True{} : Bool}
  {F.E.justs(C, F.E.run(~B, ~F.Side<A, B>, ~Maybe<&2, C>, ~(+s => i => F.snap.step(~A, ~B, ~C, ~f, s, i)), i, x))
     == F.E.snapshot.stepper(~A, ~B, ~C, ~f, F.E.fires(A, B, i), x, F.E.sets(A, B, i)) : F.Events(C)}

# switch
# ------

# The machine agrees with the meaning: over any event of inputs and keys,
# switch's outputs are E.switched's.
law e_run_switch:
  for ~K: Data
  for ~S: Data
  for ~A: Data
  for ~B: Data
  for ~init: K -> S
  for ~step: K -> S -> A -> S & B
  for i: F.Events(F.Side<A, K>)
  for +k: K
  for s: S
  {F.E.justs(B, F.E.run(~F.Both<K, S>, ~F.Side<A, K>, ~Maybe<&2, B>,
                        ~(st => j => F.switch.step(~K, ~S, ~A, ~B, ~init, ~step, st, j)), i, F.Both{k, s}))
     == F.E.switched(~K, ~S, ~A, ~B, ~init, ~step, i, k, s) : F.Events(B)}

# Time
# ----

# Time's order is a strict total order, as the reals' is: no time is before
# itself, before is transitive, and two times neither before the other are
# one time.
law time_lt_irrefl:
  for +t: F.Time
  {F.Time.lt(t, t) == False{} : Bool}

law time_lt_trans:
  for +a: F.Time
  for +b: F.Time
  for +c: F.Time
  for h1: {F.Time.lt(a, b) == True{} : Bool}
  for h2: {F.Time.lt(b, c) == True{} : Bool}
  {F.Time.lt(a, c) == True{} : Bool}

law time_lt_total:
  for +a: F.Time
  for +b: F.Time
  for h1: {F.Time.lt(a, b) == False{} : Bool}
  for h2: {F.Time.lt(b, a) == False{} : Bool}
  {a == b : F.Time}

# The runtime stamps each input with Time.after(last, clock): the clock's
# reading when it is past the last input's time, else the next time after
# that. So inputs come in time order and no two share a time, whatever the
# clock does (short of the end of time, 136 years on).
law time_tick:
  for t: F.Time
  for h: {F.Time.lt(t, F.Time.end()) == True{} : Bool}
  {F.Time.lt(t, F.Time.tick(t)) == True{} : Bool}

law time_after:
  for +last: F.Time
  for +now: F.Time
  for h: {F.Time.lt(last, F.Time.end()) == True{} : Bool}
  {F.Time.lt(last, F.Time.after(last, now)) == True{} : Bool}

law time_after_clock:
  for +last: F.Time
  for +now: F.Time
  for h: {F.Time.lt(last, now) == True{} : Bool}
  {F.Time.after(last, now) == now : F.Time}

# Elliott's time transformation: warping by the identity changes nothing,
# two warps are one by the composite clock, time warped is the warp itself,
# and delay and faster are warps.
law b_warp_id:
  for -A: Data
  for -b: F.Behavior(A)
  for -t: F.Time
  {F.B.warp(A, x => x, b)(t) == b(t) : A}

law b_warp_comp:
  for -A: Data
  for -f: F.Time -> F.Time
  for -g: F.Time -> F.Time
  for -b: F.Behavior(A)
  for -t: F.Time
  {F.B.warp(A, f, F.B.warp(A, g, b))(t) == F.B.warp(A, x => g(f(x)), b)(t) : A}

law b_warp_time:
  for -f: F.Time -> F.Time
  for -t: F.Time
  {F.B.warp(F.Time, f, F.B.time())(t) == f(t) : F.Time}

law b_delay_warp:
  for -A: Data
  for -d: F.Time
  for -b: F.Behavior(A)
  for -t: F.Time
  {F.B.delay(A, d, b)(t) == F.B.warp(A, x => F.Time.sub(x, d), b)(t) : A}

law b_faster_warp:
  for -A: Data
  for -k: F.Time
  for -b: F.Behavior(A)
  for -t: F.Time
  {F.B.faster(A, k, b)(t) == F.B.warp(A, x => F.Time.mul(k, x), b)(t) : A}

# Time order
# ----------

# An event means occurrences in time order (F.E.ordered), and every operation
# keeps it: map, accum, snapshot and any machine keep each time, so the order
# is the one they were given; filter and justs only drop occurrences; merge
# interleaves two events in order; flat spreads values at one time.
law e_map_ordered:
  for ~A: Data
  for ~B: Data
  for ~f: A -> B
  for e: F.Events(A)
  {F.E.ordered(B, F.E.map(~A, ~B, ~f, e)) == F.E.ordered(A, e) : Bool}

law e_filter_ordered:
  for ~A: Data
  for ~p: A -> Bool
  for e: F.Events(A)
  for +h: {F.E.ordered(A, e) == True{} : Bool}
  {F.E.ordered(A, F.E.filter(~A, ~p, e)) == True{} : Bool}

law e_merge_ordered:
  for -A: Data
  for e1: F.Events(A)
  for e2: F.Events(A)
  for +h1: {F.E.ordered(A, e1) == True{} : Bool}
  for +h2: {F.E.ordered(A, e2) == True{} : Bool}
  {F.E.ordered(A, F.E.merge(A, e1, e2)) == True{} : Bool}

law e_accum_ordered:
  for ~A: Data
  for ~B: Data
  for ~f: B -> A -> B
  for e: F.Events(A)
  for +x: B
  {F.E.ordered(B, F.E.accum(~A, ~B, ~f, e, x)) == F.E.ordered(A, e) : Bool}

law e_snapshot_ordered:
  for ~A: Data
  for ~B: Data
  for ~C: Data
  for ~f: A -> B -> C
  for ~b: F.Behavior(B)
  for e: F.Events(A)
  {F.E.ordered(C, F.E.snapshot(~A, ~B, ~C, ~f, ~b, e)) == F.E.ordered(A, e) : Bool}

law e_run_ordered:
  for ~S: Data
  for ~A: Data
  for ~B: Data
  for ~step: S -> A -> S & B
  for e: F.Events(A)
  for s: S
  {F.E.ordered(B, F.E.run(~S, ~A, ~B, ~step, e, s)) == F.E.ordered(A, e) : Bool}

law e_justs_ordered:
  for -C: Data
  for e: F.Events(Maybe<&2, C>)
  for h: {F.E.ordered(Maybe<&2, C>, e) == True{} : Bool}
  {F.E.ordered(C, F.E.justs(C, e)) == True{} : Bool}

law e_flat_ordered:
  for -A: Data
  for e: F.Events(List<&2, A>)
  for h: {F.E.ordered(List<&2, A>, e) == True{} : Bool}
  {F.E.ordered(A, F.E.flat(A, e)) == True{} : Bool}

# merge is associative: three events merge into one, however grouped.
law e_merge_assoc:
  for -A: Data
  for a: F.Events(A)
  for b: F.Events(A)
  for c: F.Events(A)
  {F.E.merge(A, F.E.merge(A, a, b), c) == F.E.merge(A, a, F.E.merge(A, b, c)) : F.Events(A)}

# Dynamic values (Dyn.bend)
# -------------------------

# A Dyn means a behavior and the event of its changes: current is the stepper
# of its first value and its changes; updated is its changes. hold (holdDyn)
# is that pair.
law dyn_hold_current:
  for -A: Data
  for -x: A
  for -e: F.Events(A)
  for -t: F.Time
  {D.Dyn.current(A, D.Dyn.hold(A, x, e))(t) == F.B.stepper(A, x, e)(t) : A}

law dyn_hold_updated:
  for -A: Data
  for -x: A
  for -e: F.Events(A)
  {D.Dyn.updated(A, D.Dyn.hold(A, x, e)) == e : F.Events(A)}

# fold (foldDyn): at t, f folded over the values e delivered strictly before
# t; it changes at each of e's occurrences, to the fold so far.
law dyn_fold_current:
  for ~A: Data
  for ~B: Data
  for ~f: B -> A -> B
  for e: F.Events(A)
  for +x: B
  for +t: F.Time
  {D.Dyn.current(B, D.Dyn.fold(~A, ~B, ~f, x, e))(t) == F.E.fold(~A, ~B, ~f, F.E.before(A, e, t), x) : B}

law dyn_fold_updated:
  for ~A: Data
  for ~B: Data
  for ~f: B -> A -> B
  for -e: F.Events(A)
  for -x: B
  {D.Dyn.updated(B, D.Dyn.fold(~A, ~B, ~f, x, e)) == F.E.accum(~A, ~B, ~f, e, x) : F.Events(B)}

# pure (constDyn): always x, never changing.
law dyn_pure_current:
  for -A: Data
  for -x: A
  for -t: F.Time
  {D.Dyn.current(A, D.Dyn.pure(A, x))(t) == x : A}

law dyn_pure_updated:
  for -A: Data
  for -x: A
  {D.Dyn.updated(A, D.Dyn.pure(A, x)) == F.E.never(A) : F.Events(A)}

# map: current of a map is the map of current, and it changes when d does;
# the functor laws.
law dyn_map_current:
  for ~A: Data
  for ~B: Data
  for ~f: A -> B
  for d: D.Dyn<A>
  for +t: F.Time
  {D.Dyn.current(B, D.Dyn.map(~A, ~B, ~f, d))(t) == f(D.Dyn.current(A, d)(t)) : B}

law dyn_map_updated:
  for ~A: Data
  for ~B: Data
  for ~f: A -> B
  for d: D.Dyn<A>
  {D.Dyn.updated(B, D.Dyn.map(~A, ~B, ~f, d)) == F.E.map(~A, ~B, ~f, D.Dyn.updated(A, d)) : F.Events(B)}

law dyn_map_id:
  for ~A: Data
  for d: D.Dyn<A>
  {D.Dyn.map(~A, ~A, ~F.ident(A), d) == d : D.Dyn<A>}

law dyn_map_comp:
  for ~A: Data
  for ~B: Data
  for ~C: Data
  for ~f: A -> B
  for ~g: B -> C
  for d: D.Dyn<A>
  {D.Dyn.map(~B, ~C, ~g, D.Dyn.map(~A, ~B, ~f, d)) == D.Dyn.map(~A, ~C, ~F.comp(~A, ~B, ~C, ~f, ~g), d) : D.Dyn<C>}

# zip (zipDyn): current of a zip is the pair of currents; zip_with
# (zipDynWith) is f of both.
law dyn_zip_current:
  for -A: Data
  for -B: Data
  for da: D.Dyn<A>
  for db: D.Dyn<B>
  for +t: F.Time
  {D.Dyn.current(F.Both<A, B>, D.Dyn.zip(A, B, da, db))(t) == F.Both{D.Dyn.current(A, da)(t), D.Dyn.current(B, db)(t)} : F.Both<A, B>}

law dyn_zip_with_current:
  for ~A: Data
  for ~B: Data
  for ~C: Data
  for ~f: A -> B -> C
  for da: D.Dyn<A>
  for db: D.Dyn<B>
  for +t: F.Time
  {D.Dyn.current(C, D.Dyn.zip_with(~A, ~B, ~C, ~f, da, db))(t) == f(D.Dyn.current(A, da)(t), D.Dyn.current(B, db)(t)) : C}

# join: at t, the value at t of the Dyn the outer one holds at t; and pure is
# its unit on both sides (Dyn is a monad).
law dyn_join_current:
  for -A: Data
  for dd: D.Dyn<D.Dyn<A>>
  for +t: F.Time
  {D.Dyn.current(A, D.Dyn.join(A, dd))(t) == D.Dyn.current(A, D.Dyn.current(D.Dyn<A>, dd)(t))(t) : A}

law dyn_join_pure:
  for -A: Data
  for d: D.Dyn<A>
  {D.Dyn.join(A, D.Dyn.pure(D.Dyn<A>, d)) == d : D.Dyn<A>}

law dyn_join_map_pure:
  for ~A: Data
  for d: D.Dyn<A>
  {D.Dyn.join(A, D.Dyn.map(~A, ~D.Dyn<A>, ~D.Dyn.pure(A), d)) == d : D.Dyn<A>}

# More event combinators (Ops.bend)
# ---------------------------------

# merge_with (mergeWith): both in time order, and f of the two values where
# both occur at one time. These pin it down. leftmost keeps e1's value.
law e_merge_with_never_l:
  for ~A: Data
  for ~f: A -> A -> A
  for -e: F.Events(A)
  {Op.E.merge_with(~A, ~f, F.E.never(A), e) == e : F.Events(A)}

law e_merge_with_never_r:
  for ~A: Data
  for ~f: A -> A -> A
  for e: F.Events(A)
  {Op.E.merge_with(~A, ~f, e, F.E.never(A)) == e : F.Events(A)}

law e_merge_with_first:
  for ~A: Data
  for ~f: A -> A -> A
  for +t: F.Time
  for -a: A
  for -xs: F.Events(A)
  for +u: F.Time
  for -b: A
  for -ys: F.Events(A)
  for h: {F.Time.lt(t, u) == True{} : Bool}
  {Op.E.merge_with(~A, ~f, F.Occ{t, a} <> xs, F.Occ{u, b} <> ys) == F.Occ{t, a} <> Op.E.merge_with(~A, ~f, xs, F.Occ{u, b} <> ys) : F.Events(A)}

law e_merge_with_later:
  for ~A: Data
  for ~f: A -> A -> A
  for +t: F.Time
  for -a: A
  for -xs: F.Events(A)
  for +u: F.Time
  for -b: A
  for -ys: F.Events(A)
  for h: {F.Time.lt(u, t) == True{} : Bool}
  {Op.E.merge_with(~A, ~f, F.Occ{t, a} <> xs, F.Occ{u, b} <> ys) == F.Occ{u, b} <> Op.E.merge_with(~A, ~f, F.Occ{t, a} <> xs, ys) : F.Events(A)}

law e_merge_with_same:
  for ~A: Data
  for ~f: A -> A -> A
  for +t: F.Time
  for -a: A
  for -xs: F.Events(A)
  for -b: A
  for -ys: F.Events(A)
  {Op.E.merge_with(~A, ~f, F.Occ{t, a} <> xs, F.Occ{t, b} <> ys) == F.Occ{t, f(a, b)} <> Op.E.merge_with(~A, ~f, xs, ys) : F.Events(A)}

law e_leftmost_same:
  for ~A: Data
  for +t: F.Time
  for -a: A
  for -xs: F.Events(A)
  for -b: A
  for -ys: F.Events(A)
  {Op.E.leftmost(~A, F.Occ{t, a} <> xs, F.Occ{t, b} <> ys) == F.Occ{t, a} <> Op.E.leftmost(~A, xs, ys) : F.Events(A)}

# difference: e1's occurrences at times e2 does not occur.
law e_difference_never:
  for -A: Data
  for -B: Data
  for e: F.Events(A)
  {Op.E.difference(A, B, e, F.E.never(B)) == e : F.Events(A)}

law e_difference_keep:
  for -A: Data
  for -B: Data
  for +t: F.Time
  for -a: A
  for -e1: F.Events(A)
  for +e2: F.Events(B)
  for h: {Op.E.occurs(B, e2, t) == False{} : Bool}
  {Op.E.difference(A, B, F.Occ{t, a} <> e1, e2) == F.Occ{t, a} <> Op.E.difference(A, B, e1, e2) : F.Events(A)}

law e_difference_drop:
  for -A: Data
  for -B: Data
  for +t: F.Time
  for -a: A
  for -e1: F.Events(A)
  for +e2: F.Events(B)
  for h: {Op.E.occurs(B, e2, t) == True{} : Bool}
  {Op.E.difference(A, B, F.Occ{t, a} <> e1, e2) == Op.E.difference(A, B, e1, e2) : F.Events(A)}

# gate: e's occurrences at times b is True, in time order.
law e_gate_keep:
  for ~A: Data
  for ~b: F.Behavior(Bool)
  for +t: F.Time
  for +a: A
  for -e: F.Events(A)
  for h: {b(t) == True{} : Bool}
  {Op.E.gate(~A, ~b, F.Occ{t, a} <> e) == F.Occ{t, a} <> Op.E.gate(~A, ~b, e) : F.Events(A)}

law e_gate_drop:
  for ~A: Data
  for ~b: F.Behavior(Bool)
  for +t: F.Time
  for +a: A
  for -e: F.Events(A)
  for h: {b(t) == False{} : Bool}
  {Op.E.gate(~A, ~b, F.Occ{t, a} <> e) == Op.E.gate(~A, ~b, e) : F.Events(A)}

law e_gate_ordered:
  for ~A: Data
  for ~b: F.Behavior(Bool)
  for +e: F.Events(A)
  for h: {F.E.ordered(A, e) == True{} : Bool}
  {F.E.ordered(A, Op.E.gate(~A, ~b, e)) == True{} : Bool}

# head (headE), tail (tailE), take, drop: the first occurrence and the
# rest; the first n and the rest; each in time order.
law e_head_tail:
  for -A: Data
  for e: F.Events(A)
  {List.append(&2, F.Occ<A>, Op.E.head(A, e), Op.E.tail(A, e)) == e : F.Events(A)}

law e_take_drop:
  for -A: Data
  for e: F.Events(A)
  for n: Nat
  {List.append(&2, F.Occ<A>, Op.E.take(A, e, n), Op.E.drop(A, e, n)) == e : F.Events(A)}

law e_head_take:
  for -A: Data
  for e: F.Events(A)
  {Op.E.head(A, e) == Op.E.take(A, e, 1n) : F.Events(A)}

law e_take_ordered:
  for -A: Data
  for e: F.Events(A)
  for n: Nat
  for h: {F.E.ordered(A, e) == True{} : Bool}
  {F.E.ordered(A, Op.E.take(A, e, n)) == True{} : Bool}

law e_drop_ordered:
  for -A: Data
  for e: F.Events(A)
  for n: Nat
  for h: {F.E.ordered(A, e) == True{} : Bool}
  {F.E.ordered(A, Op.E.drop(A, e, n)) == True{} : Bool}

# select (fan's selector): the values of the occurrences with key k, in
# place; fan spreads keyed values in time order.
law e_select_hit:
  for ~K: Data
  for ~A: Data
  for ~same: K -> K -> Bool
  for +t: F.Time
  for +k2: K
  for +a: A
  for -e: F.Events(F.Both<K, A>)
  for +k: K
  for h: {same(k2, k) == True{} : Bool}
  {Op.E.select(~K, ~A, ~same, F.Occ{t, F.Both{k2, a}} <> e, k) == F.Occ{t, a} <> Op.E.select(~K, ~A, ~same, e, k) : F.Events(A)}

law e_select_miss:
  for ~K: Data
  for ~A: Data
  for ~same: K -> K -> Bool
  for +t: F.Time
  for +k2: K
  for +a: A
  for -e: F.Events(F.Both<K, A>)
  for +k: K
  for h: {same(k2, k) == False{} : Bool}
  {Op.E.select(~K, ~A, ~same, F.Occ{t, F.Both{k2, a}} <> e, k) == Op.E.select(~K, ~A, ~same, e, k) : F.Events(A)}

law e_select_ordered:
  for ~K: Data
  for ~A: Data
  for ~same: K -> K -> Bool
  for e: F.Events(F.Both<K, A>)
  for +k: K
  for +h: {F.E.ordered(F.Both<K, A>, e) == True{} : Bool}
  {F.E.ordered(A, Op.E.select(~K, ~A, ~same, e, k)) == True{} : Bool}

law e_fan_ordered:
  for -K: Data
  for -A: Data
  for e: F.Events(List<&2, F.Both<K, A>>)
  for h: {F.E.ordered(List<&2, F.Both<K, A>>, e) == True{} : Bool}
  {F.E.ordered(F.Both<K, A>, Op.E.fan(K, A, e)) == True{} : Bool}

# delay: each occurrence d later.
law e_delay_never:
  for -A: Data
  for -d: F.Time
  {Op.E.delay(A, d, F.E.never(A)) == F.E.never(A) : F.Events(A)}

law e_delay_occ:
  for -A: Data
  for -d: F.Time
  for -t: F.Time
  for -a: A
  for -e: F.Events(A)
  {Op.E.delay(A, d, F.Occ{t, a} <> e) == F.Occ{F.Time.add(t, d), a} <> Op.E.delay(A, d, e) : F.Events(A)}

# debounce: an occurrence fires d later when the next does not come before
# then, and is dropped when it does.
law e_debounce_never:
  for -A: Data
  for -d: F.Time
  {Op.E.debounce(A, d, F.E.never(A)) == F.E.never(A) : F.Events(A)}

law e_debounce_keep:
  for -A: Data
  for +d: F.Time
  for +t: F.Time
  for +a: A
  for +e: F.Events(A)
  for h: {Op.E.quiet(A, e, F.Time.add(t, d)) == True{} : Bool}
  {Op.E.debounce(A, d, F.Occ{t, a} <> e) == F.Occ{F.Time.add(t, d), a} <> Op.E.debounce(A, d, e) : F.Events(A)}

law e_debounce_drop:
  for -A: Data
  for +d: F.Time
  for +t: F.Time
  for +a: A
  for +e: F.Events(A)
  for h: {Op.E.quiet(A, e, F.Time.add(t, d)) == False{} : Bool}
  {Op.E.debounce(A, d, F.Occ{t, a} <> e) == Op.E.debounce(A, d, e) : F.Events(A)}

# throttle: the first occurrence passes, and then each at least d after the
# last that passed; the others are dropped.
law e_throttle_first:
  for -A: Data
  for -d: F.Time
  for -t: F.Time
  for -a: A
  for -e: F.Events(A)
  {Op.E.throttle(A, d, F.Occ{t, a} <> e) == F.Occ{t, a} <> Op.E.throttle.from(A, e, d, F.Time.add(t, d)) : F.Events(A)}

law e_throttle_open:
  for -A: Data
  for +d: F.Time
  for +from: F.Time
  for +t: F.Time
  for +a: A
  for +e: F.Events(A)
  for h: {F.Time.le(from, t) == True{} : Bool}
  {Op.E.throttle.from(A, F.Occ{t, a} <> e, d, from) == F.Occ{t, a} <> Op.E.throttle.from(A, e, d, F.Time.add(t, d)) : F.Events(A)}

law e_throttle_shut:
  for -A: Data
  for +d: F.Time
  for +from: F.Time
  for +t: F.Time
  for +a: A
  for +e: F.Events(A)
  for h: {F.Time.le(from, t) == False{} : Bool}
  {Op.E.throttle.from(A, F.Occ{t, a} <> e, d, from) == Op.E.throttle.from(A, e, d, from) : F.Events(A)}

# The page's diff (Web.bend)
# --------------------------

# What runtime.js does to the DOM is Web.bend's diff of the last view and the
# new one. Applying diff(a, b) to a gives b (and for children,
# diff.kids then apply.kids gives the new children); diff(a, a) is Keep.
law page_diff_apply:
  for +a: W.Html
  for +b: W.Html
  {W.apply(W.diff(a, b), a) == b : W.Html}

law page_diff_kids_apply:
  for olds: List<&2, W.Html>
  for news: List<&2, W.Html>
  {W.apply.kids(W.diff.kids(olds, news), olds) == news : List<&2, W.Html>}

law page_diff_self:
  for +a: W.Html
  {W.diff(a, a) == W.EKeep{} : W.Edit}
