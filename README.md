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
| `E.map(f, e)` | each occurrence's value through `f` |
| `E.filter(p, e)` | the occurrences whose value passes `p` |
| `E.merge(e1, e2)` | both, in time order (`e1` first at equal times) |
| `E.never` | no occurrences |
| `E.accum(f, x, e)` | each occurrence carries `f` folded over the values so far, from `x` |
| `B.stepper(x, e)` | `x` before `e`'s first occurrence, then its latest value |
| `B.switcher(fam, k, e)` | `fam(k)`, then `fam` of each key `e` delivers, from its occurrence on (a behavior is a closure, which an occurrence cannot carry, so `e` carries keys into a family) |
| `E.snapshot(f, e, b)` | each occurrence `(t, a)` as `(t, f(a, b(t)))` |
| `E.snapshot.stepper(f, e, x, d)` | `E.snapshot(f, e, B.stepper(x, d))`, with the behavior as data |

What bend-frp leaves out, on purpose:

- **A behavior's "changes" event.** A behavior that varies continuously has
  no discrete changes, so `updated` (Reflex) has no meaning here. A
  piecewise-constant behavior, built by `stepper`, is a `Reactive<A>` (a value
  and an event of later values, as in Elliott's *Push-pull functional
  reactive programming*), and only it has one.
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
That meets 1 to 3: the meaning is still the reals; programs only compare
(`Time.lt`, `Time.le`), add (`Time.add`) and sample; and it resolves 0.23 ns
for 136 years. It also orders exactly, by a plain definition, so the laws
about time are proved rather than assumed. The runtime stamps each input with
the clock and never gives two inputs the same time. Of 4, it has addition so
far; scaling and a conversion to `F32` for continuous arithmetic are still to
come. It needs no infinities: `never` is the event with no occurrences.

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
  answers are the samples snapshotted against the values' stepper.

The laws are tested by breaking `Frp.bend` on purpose, one mistake at a time
(`probe/mutants.sh`): a `map` that drops occurrences or shifts their times, a
`merge` that ignores time or puts `e2` first at equal times, a `filter` that
keeps everything or inverts its test, `time` off by one, `ap` sampling its
function at time 0, an inclusive `stepper`, a `switcher` that ignores its
keys, a `snapshot` that samples late, an `accum` that outputs its old state.
Each one makes `PROOF.bend` fail.

Not stated yet: `merge`'s associativity, and that the operations keep events
in time order. Both need the order of times as lemmas over `Time` (a pair of
Base's `U32`, 32-bit words with an inductive compare, so they can be proved).

## Building

`nix develop` gives `bend` (2.0.39, the one horas and ana pin), Lean 4.34.0 with
BendTT for `--verdict`, and node. `nix flake check` runs the gate: the proofs
with `--verdict`, every module checked, the machines of `probe/Snap.bend`
and `probe/Switch.bend` run against their meanings, and the probe and todo
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
- `runtime.js` turns DOM events into timed `Input` occurrences, calls the step
  (Bend compiles it with `bend page.html -o dist`), compares the new view with
  the last and patches the DOM, writing only what the view changed.

## Phones

`bend page.html -o dist` writes a plain web directory: the page and one
JavaScript file (1.7 KB for `probe/page.html`), no server needed. Capacitor
takes that directory as its `webDir` and wraps it as an app: iOS from a Mac
with Xcode, Android with Gradle (Linux works).
