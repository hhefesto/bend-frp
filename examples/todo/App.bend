import Base
import ../../Web.bend as W

# A list and a counter, to show the web layer: every state is a fold of the
# inputs so far, and the view is a function of the state.

type S is Data:
  S{+count: U32, +draft: String, +items: List<&2, String>, +note: String}

def init() -> S:
  S{0, "", [], ""}

# What an input means.
type Msg is Data:
  MInc{}
  MDraft{+s: String}
  MAdd{}
  MDrop{+s: String}
  MAsked{}
  MTold{+s: String}
  MOther{}

def msg.pick(inc: Bool, dr: Bool, ad: Bool, dp: Bool, ask: Bool, told: Bool, +tag: String, +v: String) -> Msg:
  match inc dr ad dp ask told:
    case True{} _ _ _ _ _:
      MInc{}
    case False{} True{} _ _ _ _:
      MDraft{v}
    case False{} False{} True{} _ _ _:
      MAdd{}
    case False{} False{} False{} True{} _ _:
      MDrop{String.drop(tag, 5n)}
    case False{} False{} False{} False{} True{} _:
      MAsked{}
    case False{} False{} False{} False{} False{} True{}:
      MTold{v}
    case False{} False{} False{} False{} False{} False{}:
      MOther{}

def msg.of(+tag: String, +v: String) -> Msg:
  msg.pick(String.eq(tag, "inc"), String.eq(tag, "draft"), String.eq(tag, "add"),
           String.starts_with(tag, "drop:"), String.eq(tag, "ask"),
           String.eq(tag, "told"), tag, v)

def added(+draft: String, items: List<&2, String>, empty: Bool) -> List<&2, String>:
  match empty:
    case True{}:
      items
    case False{}:
      List.append(&2, String, items, [draft])

def without.if(h: String, rest: List<&2, String>, same: Bool) -> List<&2, String>:
  match same:
    case True{}:
      rest
    case False{}:
      h <> rest

def without(xs: List<&2, String>, +x: String) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+h, t}:
      without.if(h, without(t, x), String.eq(h, x))

def apply(s: S, m: Msg) -> S & List<&2, W.Effect>:
  match s m:
    case S{c, d, xs, n} MInc{}:
      (S{(c + 1 : U32), d, xs, n}, [])
    case S{c, d, xs, n} MDraft{v}:
      (S{c, v, xs, n}, [])
    case S{c, +d, xs, n} MAdd{}:
      (S{c, "", added(d, xs, String.eq(d, "")), n}, [W.Focus{"draft"}])
    case S{c, d, xs, n} MDrop{x}:
      (S{c, d, without(xs, x), n}, [])
    case S{c, d, xs, n} MAsked{}:
      (S{c, d, xs, "asking"}, [W.Http{"told", "GET", "./hello.txt", ""}])
    case S{c, d, xs, n} MTold{v}:
      (S{c, d, xs, v}, [])
    case S{c, d, xs, n} MOther{}:
      (S{c, d, xs, n}, [])

def update(s: S, i: W.Input) -> S & List<&2, W.Effect>:
  match i:
    case W.Input{at, +tag, +v}:
      apply(s, msg.of(tag, v))

def item(+x: String) -> W.Html:
  W.keyed("li", x, [], [W.text(x), W.el("button", [W.Prop{"id", "drop-" ++ x}, W.On{"click", "drop:" ++ x}], [W.text("x")])])

def items(xs: List<&2, String>) -> List<&2, W.Html>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+x, t}:
      item(x) <> items(t)

def view(s: S) -> W.Html:
  match s:
    case S{c, d, xs, n}:
      W.el("div", [W.cls("app")],
        [W.el("button", [W.Prop{"id", "inc"}, W.On{"click", "inc"}], [W.text("count: " ++ U32.show(c))]),
         W.el("input", [W.Prop{"id", "draft"}, W.Prop{"value", d}, W.On{"input", "draft"}, W.OnKey{"Enter", "add"}], []),
         W.el("button", [W.Prop{"id", "add"}, W.On{"click", "add"}], [W.text("add")]),
         W.el("ul", [W.Prop{"id", "items"}], items(xs)),
         W.el("button", [W.Prop{"id", "ask"}, W.On{"click", "ask"}], [W.text("ask")]),
         W.el("p", [W.Prop{"id", "note"}], [W.text(n)])])

def step(s: S, i: W.Input) -> S & W.Out:
  W.app.step(~S, ~update, ~view, s, i)
