# curva

Functional reactive programming in [Bend](https://bend-lang.com), after
Conal Elliott: a precise meaning first, and an implementation proved to
agree with it. A web layer on top (as reflex-dom is to reflex) builds pages
whose state is a behavior of their input events. First user: mugen-web's
chat, ported from Reflex-DOM.

The name: a behavior is a curve, a value at every moment.

Status: design, and three probes in `probe/` showing the approach runs
(Bend 2.0.39): `Probe.bend` (an event and `stepper`), `Probe2.bend` (two
`accum`s run in sequence over inputs) and `page.html` (that run in a web
page).

## The meaning

- `Time` is dense: between any two moments there is another.
- `Behavior<A>` means a function `Time -> A`.
- `Event<A>` means a list of occurrences `(Time, A)` in time order.

Every operation is defined by what it does to meanings, and every instance
agrees with the meaning's own (Elliott's type class morphisms):

| curva | its meaning |
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
| `B.switcher(b, e)` | `b`, then each behavior `e` delivers, from its occurrence on |
| `E.snapshot(f, e, b)` | each occurrence `(t, a)` as `(t, f(a, b(t)))` |

What curva leaves out, on purpose:

- **A behavior's "changes" event.** A behavior that varies continuously has
  no discrete changes, so `updated` (Reflex) has no meaning here. A
  piecewise-constant behavior, built by `stepper`, is a `Reactive<A>` (a value
  and an event of later values, as in Elliott's *Push-pull functional
  reactive programming*), and only it has one.
- **Frames and ticks in the interface.** Sampling is the renderer's
  business: a view is sampled when an input arrives, and on display frames
  only while it depends on `B.time`.

## Laws

`LAWS.bend` states the meaning and the agreement; `PROOF.bend` proves them
(`bend PROOF.bend` prints ALL PROOFS CHECK when every law holds):

- each instance law above, as an equation between meanings;
- each operation's running form agrees with its meaning on every finite
  history of inputs.

## How it runs in Bend

Bend closures can be called once, and every recursion must end, so a
behavior cannot be a stored function sampled again and again, nor an
endless stream. So curva runs a network a step at a time, as Base's `App`
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

- A view is data: an HTML tree with keyed nodes, attributes, and handlers
  named by data rather than closures.
- An app means `Event<Input> -> Behavior<View>`.
- A small JavaScript runtime turns DOM events into timed `Input`
  occurrences, calls the app's step (Bend compiles it with
  `bend page.html -o dist`), compares the new view with the last and patches
  the DOM.

## Phones

`bend page.html -o dist` writes a plain web directory: the page and one
JavaScript file (1.7 KB for `probe/page.html`), no server needed. Capacitor
takes that directory as its `webDir` and wraps it as an app: iOS from a Mac
with Xcode, Android with Gradle (Linux works).
