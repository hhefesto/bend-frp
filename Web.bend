import Base
import ./Frp.bend as F

# The web layer: an app means Event<Input> -> Behavior<View>, and its running
# form is a machine from an input to a view and the effects to do. A view is
# data: runtime.js compares it with the last one and patches the DOM.

# What the page tells the app: which handler fired (handlers are named by
# data, not closures), when, and what it carries (see runtime.js).
type Input is Data:
  Input{+at: U32, +tag: String, +value: String}

type Attr is Data:
  # An attribute, or the property of that name for value, checked, disabled.
  Prop{+name: String, +value: String}
  # An attribute set once, as the element is made: the page's own scripts may
  # change it afterwards.
  Once{+name: String, +value: String}
  # When `event` happens here, an Input with this tag.
  On{+event: String, +tag: String}
  # The same, and the browser's default action does not happen.
  OnStop{+event: String, +tag: String}
  # This key, as runtime.js writes keys (`Enter`, `S-Enter`, `C-s`), stopped
  # and told; other keys go on as usual.
  OnKey{+key: String, +tag: String}

type Html is Data:
  HText{+s: String}
  # Children compare by key where they have one, else by place.
  HNode{+tag: String, +key: String, +attrs: List<&2, Attr>, +kids: List<&2, Html>}
  # An element whose inside is ready-made HTML.
  HRaw{+tag: String, +key: String, +attrs: List<&2, Attr>, +html: String}

# What the app asks of the world: each answer comes back as an Input.
type Effect is Data:
  # A request. The answer is Input{tag, the body}; tag ++ ":failed" when it did
  # not arrive or its status was not 2xx.
  Http{+tag: String, +method: String, +url: String, +body: String}
  # An Input with this tag after ms milliseconds.
  After{+tag: String, +ms: U32}
  Focus{+id: String}
  # A function of the page's own (window.bendFrp[name]), with a string; its
  # answer, if it returns a string, comes back as Input{tag, it}.
  Host{+tag: String, +name: String, +arg: String}

type Out is Data:
  Out{+view: Html, +effects: List<&2, Effect>}

# An app from its fold and its view: the view is a function of the state alone,
# so what a page shows depends only on the inputs so far.
def app.out(~S: Data, ~view: S -> Html, s: S & List<&2, Effect>) -> S & Out:
  (+t, fx) = s
  (t, Out{view(t), fx})

def app.step(~S: Data, ~update: S -> Input -> S & List<&2, Effect>, ~view: S -> Html, s: S, i: Input) -> S & Out:
  app.out(~S, ~view, update(s, i))

def app(~S: Data, ~update: S -> Input -> S & List<&2, Effect>, ~view: S -> Html, +s: S) -> F.Run<S, Input, Out>:
  F.Run{s, t => i => app.step(~S, ~update, ~view, t, i)}

# Building views
# --------------

def el(tag: String, attrs: List<&2, Attr>, kids: List<&2, Html>) -> Html:
  HNode{tag, "", attrs, kids}

def keyed(tag: String, key: String, attrs: List<&2, Attr>, kids: List<&2, Html>) -> Html:
  HNode{tag, key, attrs, kids}

def text(s: String) -> Html:
  HText{s}

def cls(c: String) -> Attr:
  Prop{"class", c}
