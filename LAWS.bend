# The claims of bend-frp: what its words mean, and that its machines do that.
# The human owns this file. PROOF.bend proves it; a law that turns out false
# is reported, not reworded.

import Base
import ./Frp.bend as F

# Behaviors: instances agree with the meaning's, pointwise
# --------------------------------------------------------

law b_map_id:
  for -A: Data
  for -b: F.Behavior(A)
  for -t: U32
  {F.B.map(A, A, x => x, b)(t) == b(t) : A}

law b_map_comp:
  for -A: Data
  for -B: Data
  for -C: Data
  for -f: A -> B
  for -g: B -> C
  for -b: F.Behavior(A)
  for -t: U32
  {F.B.map(B, C, g, F.B.map(A, B, f, b))(t) == g(f(b(t))) : C}

law b_ap_pure:
  for -A: Data
  for -B: Data
  for -f: A -> B
  for -x: A
  for -t: U32
  {F.B.ap(A, B, F.B.pure(A -> B, f), F.B.pure(A, x))(t) == f(x) : B}

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
  for +t: U32
  for -x: A
  for all: {F.E.all_before(A, e, t) == True{} : Bool}
  {F.B.stepper(A, x, e)(t) == F.E.last(A, e, x) : A}

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
