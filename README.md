# bend-frp

Functional reactive programming in [Bend](https://bend-lang.com), after
Conal Elliott: a precise meaning first, and an implementation proved to
agree with it. A web layer on top (as reflex-dom is to reflex) builds pages
whose state is a behavior of their input events. First user: mugen-web's
chat, ported from Reflex-DOM.

The name says what it is: FRP for Bend.

Status: the core is proved (`bend PROOF.bend --verdict` prints ALL PROOFS
CHECK) and the web layer runs a real page: mugen-web's chat
([`bend` branch](https://github.com/hhefesto/mugen-web/tree/bend), `web/`). A small
one is in `examples/todo`.

## The meaning

- `Time` means a real number of seconds: dense, so between any two moments
  there is another (see "Time" below for how it is held).
- `Behavior<A>` means a function `Time -> A`.
- `Event<A>` means a list of occurrences `(Time, A)` in time order.

Every operation is defined by what it does to meanings, and every instance
agrees with the meaning's own (Elliott's type class morphisms):

| bend-frp | its meaning |
|---|---|
| `B.map(f, b)` | `t => f(b(t))` |
| `B.pure(x)` | `t => x` |
| `B.ap(bf, bx)` | `t => bf(t)(bx(t))` |
| `B.time` | `t => t` |
| `B.warp(f, b)` | `t => b(f(t))`: `b` on another clock (Elliott's time transformation) |
| `B.delay(d, b)`, `B.faster(k, b)` | `B.warp` by `t => t - d`, by `t => k * t` |
| `B.seconds` | `t =>` the seconds of `t` as an `F32`, for arithmetic |
| `E.map(f, e)` | each occurrence's value through `f` |
| `E.filter(p, e)` | the occurrences whose value passes `p` |
| `E.merge(e1, e2)` | both, in time order (`e1` first at equal times) |
| `E.never` | no occurrences |
| `E.accum(f, x, e)` | each occurrence carries `f` folded over the values so far, from `x` |
| `B.stepper(x, e)` | `x` before `e`'s first occurrence, then its latest value |
| `B.switcher(fam, k, e)` | `fam(k)`, then `fam` of each key `e` delivers, from its occurrence on (a behavior is a closure, which an occurrence cannot carry, so `e` carries keys into a family) |
| `E.snapshot(f, e, b)` | each occurrence `(t, a)` as `(t, f(a, b(t)))` |
| `E.snapshot.stepper(f, e, x, d)` | `E.snapshot(f, e, B.stepper(x, d))`, with the behavior as data |

`Dyn.bend` adds dynamic values (Reflex's `Dynamic`, Elliott's reactive
value): a `Dyn<A>` is a first value and an event of later values, and it
means a behavior with the event of its changes:

| bend-frp | its meaning |
|---|---|
| `Dyn.current(d)` | `B.stepper(first value, changes)` |
| `Dyn.updated(d)` | its changes |
| `Dyn.hold(x, e)` (`holdDyn`) | `x`, then each value `e` delivers |
| `Dyn.fold(f, x, e)` (`foldDyn`) | at `t`, `f` folded from `x` over `e`'s values before `t`; changes at each of `e`'s occurrences |
| `Dyn.pure(x)` (`constDyn`) | `x`, never changing |
| `Dyn.map(f, d)` | current: `t => f(current(d)(t))`; changes when `d` does |
| `Dyn.zip(da, db)`, `Dyn.zip_with(f, da, db)` (`zipDyn`, `zipDynWith`) | current: the pair of currents, `f` of both; changes when either does, once when both change at one time |
| `Dyn.join(dd)` | current: `t => current(current(dd)(t))(t)` |

A `Dyn` of functions cannot be built (an event's values are data, and a
closure is not), so the applicative is `zip` and `zip_with`: Elliott's
morphism law for it is that current of a zip is the pair of currents.

`Ops.bend` adds reflex's other event combinators:

| bend-frp | its meaning |
|---|---|
| `E.merge_with(f, e1, e2)` (`mergeWith`) | both in time order; where both occur at one time, one occurrence of `f` of the two values |
| `E.leftmost(e1, e2)` | `merge_with`, keeping `e1`'s value |
| `E.difference(e1, e2)` | `e1`'s occurrences at times `e2` does not occur |
| `E.gate(b, e)` | `e`'s occurrences at times `b` is `True` |
| `E.head(e)`, `E.tail(e)` (`headE`, `tailE`) | the first occurrence; the others |
| `E.take(e, n)`, `E.drop(e, n)` | the first `n`; the others |
| `E.fan(e)`, `E.select(same, e, k)` | keyed values spread one per key; the values at key `k`, in place |
| `E.delay(d, e)` | each occurrence `d` later |
| `E.debounce(d, e)` | an occurrence, `d` later, if the next does not come before then |
| `E.throttle(d, e)` | the first occurrence, then each at least `d` after the last that passed |

`throttle` here passes the leading occurrence and drops the rest of a burst;
reflex's also fires the burst's last at the end of the window.

What bend-frp leaves out, on purpose:

- **A behavior's "changes" event.** A behavior that varies continuously has
  no discrete changes, so `updated` (Reflex) has no meaning for it. Only a
  `Dyn` has one.
- **Frames and ticks in the interface.** Sampling is the renderer's
  business: a view is sampled when an input arrives, and on display frames
  only while it depends on `B.time`.

## Time

Elliott's time is the reals, and his implementations held it as a `Double`
(`type Time = Double` in Fran; `TimeT = Double` in Reactive, whose events and
behaviors take any ordered time type). A `Double` is not continuous, yet it did
the job, for four reasons:

1. **The meaning is over the reals, and programs are written against the
   meaning.** No operation asks for "the next moment" or counts ticks: a
   program compares times, adds durations and samples. The representation
   shows only as rounding, as `Double` stands in for the reals in any
   numerical code.
2. **Sampling is chosen last.** A program says what a value is at every time;
   the runtime decides when to look. The resolution never leaks into the
   program, and composing (transforming time, integrating) does not amplify
   sampling artifacts (Elliott, *Why program with continuous time?*).
3. **Its resolution is far finer than any clock that stamps an input.** 53
   bits of mantissa are under a microsecond for a century of seconds, so two
   inputs never collapse into one time, and order is all an event needs.
4. **It is a number.** `time` goes into arithmetic (`sin time`, durations,
   scaling), and it has infinities for "never" (Reactive's `AddBounds`).

bend-frp held time as `U32` milliseconds. That kept 1 and 2, but not 3 or 4:
it wrapped after 49.7 days, two quick inputs could share a millisecond (so a
sample could miss a value set just before it), and `B.time` was a count of
milliseconds.

Bend has no 64-bit float. `F32` (24-bit mantissa) is coarser than a
millisecond once a page has been open 4.6 hours, and its operations are
primitives whose laws cannot be proved. So bend-frp holds `Time` as 64-bit
fixed-point seconds, `Time{sec, frac}`, the fraction in units of 2^-32 s.
It does what the `Double` did, all four:

1. The meaning is still the reals, and programs only compare (`Time.lt`,
   `Time.le`), do arithmetic and sample.
2. The runtime still picks the times to sample at.
3. It resolves 0.23 ns for 136 years, and the runtime never gives two inputs
   one time: `Web.bend`'s `stamp` passes the clock's reading through
   `Time.after(last, now)`, which is the reading when it is past the last
   input's time and the next time after that one otherwise, and the laws
   prove it after the last (`time_after`).
4. It is a number: `Time.add`, `Time.sub`, `Time.mul` (two times as numbers:
   `Time{2, 2^31}` is 2.5), `Time.scale` (by a whole number), and to and from
   numbers: `Time.to_f32` (for the sine of time; within a microsecond for the
   first 16 s, a millisecond for 4.6 hours), `Time.from_f32`, `Time.from_ms`
   and `Time.from_clock` (whole seconds, milliseconds and the part of one, as
   `runtime.js` reads `performance.now()`). For behaviors: `B.warp` (Elliott's
   time transformation), `B.delay`, `B.faster` and `B.seconds`. It needs no
   infinities: `never` is the event with no occurrences.

Unlike a `Double` it orders exactly, by a plain definition on Base's 32-bit
words, so the order's laws are proved: it is a strict total order, as the
reals' is. The arithmetic is checked against values worked out by hand
(`probe/Time.bend`, the flake's `time` check), not proved: a proof would go
through 32-bit multiplication and `F32` primitives, which Bend's checker does
not reduce on unknown values. It wraps past 2^32 s.

## Laws

`LAWS.bend` states the laws; `PROOF.bend` proves them (`bend PROOF.bend` prints
ALL PROOFS CHECK when every law holds; `--verdict` rechecks with BendTT's kernel):

- behaviors, Elliott's type class morphisms (each pointwise, at every `t`):
  `map` keeps identity and composes; `ap`'s four applicative laws (identity,
  composition, homomorphism, interchange); `map(f, b)` is `ap(pure(f), b)`;
  `time` at `t` is `t`;
- events: `map` keeps identity and composes; the meanings of `map` (each
  occurrence keeps its time, its value goes through `f`), `filter` (exactly the
  occurrences whose value passes, in place) and `merge` (of two first
  occurrences the earlier goes first, `e1`'s at equal times), each stated
  occurrence by occurrence, so that with `never` (`merge`'s identity on both
  sides) they pin the operation down;
- `stepper` at `t` is the value of the last occurrence strictly before `t`, or
  its first value when there is none; sampled after all of an event it is the
  event's last value;
- `switcher` at `t` is the family's behavior for the key the keys' stepper
  holds at `t`;
- `snapshot`: each occurrence keeps its time and pairs its value with the
  behavior's at that time;
- machines agree with the meaning: `E.run` of `lift` is `E.map`, of `accum` is
  `E.accum`; `then` is composition (`E.run` of `then(a, b)` is `b` over `a`'s
  outputs, the morphism of the category of machines into functions on events);
  `each` over an event is the machine over the event spread;
- `par`: each half of its output is that machine alone (`E.run` of `par`,
  mapped through `Both.fst` or `Both.snd`);
- `E.snapshot` at `B.stepper(x, d)` is `E.snapshot.stepper(f, e, x, d)`;
- `switch` agrees with the meaning: over an event of inputs (`Fire`) and keys
  (`Set`), its outputs are `E.switched`'s: the inputs before the first key
  through the machine it runs, then from each key on the inputs before the
  next through that key's machine from its start;
- `snap` agrees with the meaning: over one event of samples (`Fire`) and
  values (`Set`) whose order `snap.ok` accepts (no value set before a sample
  listed ahead of it, every sample listed after a value later than it: two
  time-ordered events merged, samples first at equal times), the samples it
  answers are the samples snapshotted against the values' stepper;
- time: `Time.lt` is a strict total order (no time is before itself, before
  is transitive, and two times neither before the other are one time);
  `Time.tick(t)` is after `t`; `Time.after(last, now)` is after `last`, and is
  `now` when `now` is past `last` (short of the end of time, 136 years on);
- time transformation (Elliott's): warping by the identity changes nothing,
  two warps are one by the composite clock, `time` warped is the warp, and
  `delay` and `faster` are warps;
- every operation keeps events in time order (`E.ordered`): `map`, `accum`,
  `snapshot` and any machine (`E.run`) keep every time, so an event is in
  order after them exactly when it was before; `filter` and `justs` keep the
  order; `merge` of two ordered events is ordered; `flat`, which spreads
  values at one time, keeps it;
- `merge` is associative;
- `Dyn`: current of `hold` is the stepper and its updated is the event; current
  of `fold` at `t` is the fold of the values before `t`, and its updated is
  `E.accum`; `pure` is constant and never changes; current of `map` is the
  map of current, its updated is the map of updated, and `map` keeps identity
  and composes; current of `zip` is the pair of currents, of `zip_with` `f`
  of both; current of `join` at `t` is current at `t` of current of the outer
  at `t`; `join` of `pure` and `join` of `map(pure)` are the `Dyn` itself;
- the combinators of `Ops.bend`, each pinned down occurrence by occurrence:
  `merge_with` against `never` on both sides and at its two first
  occurrences (the earlier first, `f` of both at one time), `leftmost` at one
  time; `difference` against `never`, keeping an occurrence `e2` has none at
  and dropping one it has; `gate` keeping where `b` is `True` and dropping
  where it is `False`; `head` then `tail`, and `take` then `drop`, are the
  event, and `head` is `take` of 1; `select` keeping the occurrences at its
  key and dropping the others; `delay` at `never` and at one occurrence;
  `debounce` keeping an occurrence the next does not follow within `d`, and
  dropping one it does; `throttle` passing the first, then passing an
  occurrence at or after the time it waits for and dropping one before it;
  and `gate`, `take`, `drop`, `select` and `fan` keep time order;
- the page's diff (`Web.bend`): applying `diff(a, b)` to `a` gives `b`, and
  applying `diff.kids` of two lists of children to the first gives the second;
  `diff(a, a)` is `EKeep`; escaped text has no `<`, `>` or `"`.

The laws are tested by breaking the library on purpose, one mistake at a time
(`probe/mutants.sh`): a `map` that drops occurrences or shifts their times, a
`merge` that ignores time, puts `e2` first at equal times, puts the later
first, or drops an occurrence when its left side is empty, a `filter` that
keeps everything or inverts its test, `time` off by one, `ap` sampling its
function at time 0, an inclusive `stepper`, a `switcher` that ignores its
keys, a `snapshot` that samples late, an `accum` that outputs its old state,
a time order that ignores the fraction, lets a time be before itself, or
means "different", an event order that wants each time strictly later, a
`warp` that ignores its clock, a `delay` that runs early, and machines whose
outputs all happen at time 0; a `Dyn.map` that forgets the changes, a `zip`
that ignores the right side's change, or keeps only the left at a tie, a
`join` that switches to a stale value or keeps the old inner's changes, an
`updated` that never fires; a `merge_with` that keeps one value at a tie, a
`difference` that keeps everything, a `gate` turned round, a `head` that keeps
the rest, a `take` that skips, a `select` that ignores the key, a `delay`
that does not wait, a `debounce` that keeps every occurrence, a
`throttle` that lets all through; a page diff that misses a text's change or an
element's new attributes, keeps old children that should go, or calls a
changed element kept, and an escape that lets `<` through. Each one makes
`PROOF.bend` fail.

`PROOF.bend` fills each law from lemmas in `proof/`: `Logic.bend` (absurdity,
clashes of constructors, the cases of a `Bool`), `Order.bend` (the order of
times, from the bits of a `U32` up), `Events.bend` (`merge` and `filter` one
occurrence at a time, time order, associativity), `Dyn.bend` (steppers of
mapped, folded, zipped and joined events), `Ops.bend` (`merge_with`, `gate`,
`throttle` at one occurrence, `take` then `drop`, `select` in time order) and
`Web.bend` (string and attribute equality is equality; diff then apply gives
the new children; a diff that keeps every child came from equal children).

## Building

`nix develop` gives `bend` (2.0.39, the one horas and ana pin), Lean 4.34.0 with
BendTT for `--verdict`, and node. `nix flake check` runs the gate: the proofs
with `--verdict`, every module checked, the machines of `probe/Snap.bend`
and `probe/Switch.bend` run against their meanings, Time's arithmetic run
against worked values (`probe/Time.bend`), `zip` and `join` against their
meanings (`probe/Dyn.bend`), `Ops.bend`'s combinators against worked values
(`probe/Ops.bend`), a view rendered to HTML and addresses split
(`probe/Page.bend`), the mutants, and the probe and todo
pages bundled (`nix build .#todo` is the todo page's web directory).

## How it runs in Bend

Bend closures can be called once, and every recursion must end, so a
behavior cannot be a stored function sampled again and again, nor an
endless stream. So bend-frp runs a network a step at a time, as Base's `App`
runs a window:

- A network's running form is a value `Run{init, step}`: its state (Data),
  and a step from an input to the next state and an output. Operations are
  ordinary defs that build one from others (`then(a, b)` runs `b` on `a`'s
  outputs; its state holds both states).
- The runner takes the network as a template (`~r`), as `App.loop` takes an
  app, so each step builds it afresh and its closures are new each time. A
  user's own functions are top-level defs, or templates (`~f`), which Bend
  inlines and lets you call freely.
- A new input occurrence costs work in the size of the network, not of the
  history. The laws above are what make that the same thing as the
  meaning.

## The web layer

- A view is data (`Web.bend`): an HTML tree with keyed nodes, attributes, and
  handlers named by data rather than closures. An effect is data too (a request,
  a timer, a call to the page's own script), and its answer comes back as an
  input.
- An app means `Event<Input> -> Behavior<View>`: `init()` and `step(state, input)`.
- The page's diff is Bend's: `Web.bend`'s `diff(a, b)` is an edit tree (keep
  a node; build a new one in its place; a text's new text; an element's new
  attributes, and its children's edits: kept in place and edited, dropped, or
  added at the end). `LAWS.bend` proves that applying `diff(a, b)` to `a`
  gives `b` (`page_diff_apply`) and that `diff(a, a)` keeps everything
  (`page_diff_self`). Children compare by place: one whose tag or key changed
  is built afresh, so removing a child from the middle rebuilds those after it.
- `runtime.js` is what must be JavaScript: it turns DOM events into timed
  `Input` occurrences (their times from `Web.bend`'s `stamp`), calls the step
  (Bend compiles it with `bend page.html -o dist`), and does each edit `diff`
  gives with a DOM call or two. It also builds new nodes, writes an element's
  changed attributes (properties for `value`, `checked`, `disabled` and
  `selected`), keeps the listeners, and does the effects.
- Effects (as reflex-dom's): `Http` requests, `After` timers, `Focus`, `Host`
  (the page's own functions); WebSockets (`WsOpen`, `WsSend`, `WsClose`: an
  input when one opens, one for each message, one when it closes); the page's
  address (`Route`: an input now and at each change, back and forward
  included; `Navigate`: go to an address in the history; `W.path` splits an
  address into the segments to route on); the browser's storage (`StoreSet`,
  `StoreGet`, `StoreDel`, on `localStorage`).
- Server-side rendering: `W.render(view)` is the view as HTML, for a server to
  send before the script runs: text and attribute values escaped (`LAWS.bend`
  proves escaped text has no `<`, `>` or `"`, `page_escape_safe`), properties
  as attributes, handlers left to the script.

## Phones

`bend page.html -o dist` writes a plain web directory: the page and one
JavaScript file (1.7 KB for `probe/page.html`), no server needed. Capacitor
takes that directory as its `webDir` and wraps it as an app: iOS from a Mac
with Xcode, Android with Gradle (Linux works).
