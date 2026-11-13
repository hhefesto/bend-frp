# Laws proposed for LAWS.bend, about what Frp.bend added since: par, and
# snapshot. LAWS.bend is the human's, so they wait here until the human moves
# them there (or rewords or drops them). PROOF.bend proves them as it proves
# LAWS.bend's.

import Base
import ./Frp.bend as F

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
