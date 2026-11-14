import Base
import ./Frp.bend as F

# The web layer: an app means Event<Input> -> Behavior<View>, and its running
# form is a machine from an input to a view and the effects to do. A view is
# data: runtime.js compares it with the last one and patches the DOM.

# What the page tells the app: which handler fired (handlers are named by
# data, not closures), when, and what it carries (see runtime.js).
type Input is Data:
  Input{+at: F.Time, +tag: String, +value: String}

# An input's time, from the last input's and a reading of the page's clock
# (Time.from_clock): after the last, so inputs come in time order and no two
# share a time (LAWS.bend, time_after). runtime.js calls it for every input.
def stamp(+last: F.Time, s: U32, ms: U32, sub: U32) -> F.Time:
  F.Time.after(last, F.Time.from_clock(s, ms, sub))

# Routing
# -------

# The segments of an address's path, what a Route answers ready to match on:
# "/notes/7?x=1#top" is ["notes", "7"]; empty segments are left out.
def path.close(cur: String, acc: List<&2, String>) -> List<&2, String>:
  match cur:
    case SNil{}:
      acc
    case SCon{c, rest}:
      String.reverse(SCon{c, rest}) <> acc

def path.pick(slash: Bool, stop: Bool, +x: U32, cur: String, acc: List<&2, String>,
              more: String -> List<&2, String> -> List<&2, String>) -> List<&2, String>:
  match slash stop:
    case True{} _:
      more("", path.close(cur, acc))
    case False{} True{}:
      List.reverse(&2, String, path.close(cur, acc))
    case False{} False{}:
      more(SCon{Chr{x}, cur}, acc)

def path.go(s: String, cur: String, acc: List<&2, String>) -> List<&2, String>:
  match s:
    case SNil{}:
      List.reverse(&2, String, path.close(cur, acc))
    case SCon{Chr{+x}, rest}:
      path.pick(U32.is_eq(x, 47), U32.is_eq(x, 63) || U32.is_eq(x, 35), x, cur, acc, c => a => path.go(rest, c, a))

def path(s: String) -> List<&2, String>:
  path.go(s, "", [])

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
  # Children compare by place (Web.bend's diff): one whose tag or key changed
  # is built afresh.
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
  # A WebSocket to url, known by tag: Input{tag ++ ":open", ""} once it opens,
  # Input{tag, the message} for each message, Input{tag ++ ":closed", ""} once
  # it closes.
  WsOpen{+tag: String, +url: String}
  # A message on the socket known by tag.
  WsSend{+tag: String, +data: String}
  WsClose{+tag: String}
  # The page's address (path, query and fragment): Input{tag, it} now, and
  # again each time it changes (back, forward, or Navigate).
  Route{+tag: String}
  # Go to url in the page's history (pushState), and tell each Route.
  Navigate{+url: String}
  # The browser's storage for this site (localStorage): keep value under key;
  # Input{tag, the value kept under key, or ""}; forget key.
  StoreSet{+key: String, +value: String}
  StoreGet{+tag: String, +key: String}
  StoreDel{+key: String}

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

# The page's diff
# ---------------

# What diff says to do to one node of a page to make the last view the new
# one. runtime.js does each edit with a DOM call or two.
type Edit is Data:
  # Nothing changed.
  EKeep{}
  # Build this node in the old one's place.
  ESwap{+node: Html}
  # A text node's new text.
  EText{+s: String}
  # The same element: its new attributes (None: unchanged), and its children's
  # edits.
  ENode{+attrs: Maybe<&2, List<&2, Attr>>, +kids: List<&2, Kid>}
  # The same ready-made element: its new attributes and inside, where changed.
  ERaw{+attrs: Maybe<&2, List<&2, Attr>>, +html: Maybe<&2, String>}

# Children compare by place: the edits of those in both, in order, then the
# old ones left removed or the new ones left added at the end.
type Kid is Data:
  KSame{+edit: Edit}
  KDrop{}
  KAdd{+node: Html}

# Equality of strings and attributes, code by code.
def str.eq(a: String, b: String) -> Bool:
  match a b:
    case SNil{} SNil{}:
      True{}
    case SCon{Chr{x}, as} SCon{Chr{y}, bs}:
      U32.is_eq(x, y) && str.eq(as, bs)
    case x y:
      False{}

# An attribute as three parts: which kind it is, and its two strings; made
# back from them.
def attr.kind(a: Attr) -> U32:
  match a:
    case Prop{n, v}:
      0
    case Once{n, v}:
      1
    case On{n, v}:
      2
    case OnStop{n, v}:
      3
    case OnKey{n, v}:
      4

def attr.fst(a: Attr) -> String:
  match a:
    case Prop{n, v}:
      n
    case Once{n, v}:
      n
    case On{n, v}:
      n
    case OnStop{n, v}:
      n
    case OnKey{n, v}:
      n

def attr.snd(a: Attr) -> String:
  match a:
    case Prop{n, v}:
      v
    case Once{n, v}:
      v
    case On{n, v}:
      v
    case OnStop{n, v}:
      v
    case OnKey{n, v}:
      v

def attr.make.go(k0: Bool, k1: Bool, k2: Bool, k3: Bool, n: String, v: String) -> Attr:
  match k0 k1 k2 k3:
    case True{} _ _ _:
      Prop{n, v}
    case False{} True{} _ _:
      Once{n, v}
    case False{} False{} True{} _:
      On{n, v}
    case False{} False{} False{} True{}:
      OnStop{n, v}
    case False{} False{} False{} False{}:
      OnKey{n, v}

def attr.make(+k: U32, n: String, v: String) -> Attr:
  attr.make.go(U32.is_eq(k, 0), U32.is_eq(k, 1), U32.is_eq(k, 2), U32.is_eq(k, 3), n, v)

def attr.eq(+a: Attr, +b: Attr) -> Bool:
  U32.is_eq(attr.kind(a), attr.kind(b)) && (str.eq(attr.fst(a), attr.fst(b)) && str.eq(attr.snd(a), attr.snd(b)))

def attrs.eq(a: List<&2, Attr>, b: List<&2, Attr>) -> Bool:
  match a b:
    case Nil{} Nil{}:
      True{}
    case Con{x, xs} Con{y, ys}:
      attr.eq(x, y) && attrs.eq(xs, ys)
    case x y:
      False{}

def edit.text(same: Bool, s: String) -> Edit:
  match same:
    case True{}:
      EKeep{}
    case False{}:
      EText{s}

def edit.attrs(same: Bool, a: List<&2, Attr>) -> Maybe<&2, List<&2, Attr>>:
  match same:
    case True{}:
      None{}
    case False{}:
      Some{a}

def edit.html(same: Bool, h: String) -> Maybe<&2, String>:
  match same:
    case True{}:
      None{}
    case False{}:
      Some{h}

# Whether every child is kept as it is.
def kids.kept(ks: List<&2, Kid>) -> Bool:
  match ks:
    case Nil{}:
      True{}
    case Con{KSame{EKeep{}}, rest}:
      kids.kept(rest)
    case Con{k, rest}:
      False{}

def edit.node.if(kept: Bool, ae: Maybe<&2, List<&2, Attr>>, ks: List<&2, Kid>) -> Edit:
  match kept:
    case True{}:
      EKeep{}
    case False{}:
      ENode{ae, ks}

def edit.node.mk(ae: Maybe<&2, List<&2, Attr>>, +ks: List<&2, Kid>) -> Edit:
  match ae:
    case None{}:
      edit.node.if(kids.kept(ks), None{}, ks)
    case Some{a}:
      ENode{Some{a}, ks}

def edit.node(same: Bool, ae: Maybe<&2, List<&2, Attr>>, ks: Unit -> List<&2, Kid>, n: Html) -> Edit:
  match same:
    case True{}:
      edit.node.mk(ae, ks(Unit{}))
    case False{}:
      ESwap{n}

def edit.raw.mk(ae: Maybe<&2, List<&2, Attr>>, he: Maybe<&2, String>) -> Edit:
  match ae he:
    case None{} None{}:
      EKeep{}
    case x y:
      ERaw{x, y}

def edit.raw(same: Bool, ae: Maybe<&2, List<&2, Attr>>, he: Maybe<&2, String>, n: Html) -> Edit:
  match same:
    case True{}:
      edit.raw.mk(ae, he)
    case False{}:
      ESwap{n}

# The edits that make the children olds into news.
def diff.kids(olds: List<&2, Html>, news: List<&2, Html>) -> List<&2, Kid>:
  match olds news:
    case Nil{} Nil{}:
      Nil{}
    case Con{o, os} Nil{}:
      KDrop{} <> diff.kids(os, Nil{})
    case Nil{} Con{n, ns}:
      KAdd{n} <> diff.kids(Nil{}, ns)
    case Con{HText{s1}, os} Con{HText{+s2}, ns}:
      KSame{edit.text(str.eq(s1, s2), s2)} <> diff.kids(os, ns)
    case Con{HNode{t1, k1, a1, c1}, os} Con{HNode{+t2, +k2, +a2, +c2}, ns}:
      KSame{edit.node(str.eq(t1, t2) && str.eq(k1, k2), edit.attrs(attrs.eq(a1, a2), a2), w => diff.kids(c1, c2),
        HNode{t2, k2, a2, c2})} <> diff.kids(os, ns)
    case Con{HRaw{t1, k1, a1, h1}, os} Con{HRaw{+t2, +k2, +a2, +h2}, ns}:
      KSame{edit.raw(str.eq(t1, t2) && str.eq(k1, k2), edit.attrs(attrs.eq(a1, a2), a2), edit.html(str.eq(h1, h2), h2),
        HRaw{t2, k2, a2, h2})} <> diff.kids(os, ns)
    case Con{o, os} Con{n, ns}:
      KSame{ESwap{n}} <> diff.kids(os, ns)

def kid.edit(ks: List<&2, Kid>, b: Html) -> Edit:
  match ks:
    case Con{KSame{e}, rest}:
      e
    case x:
      ESwap{b}

# The edit that makes the view a into b.
def diff(a: Html, +b: Html) -> Edit:
  kid.edit(diff.kids([a], [b]), b)

# What an edit means: what it makes of the old node (and the children's
# edits, of the old children). LAWS.bend: applying diff(a, b) to a gives b,
# and diff(a, a) is EKeep.
def apply.attrs(ae: Maybe<&2, List<&2, Attr>>, a: List<&2, Attr>) -> List<&2, Attr>:
  match ae:
    case None{}:
      a
    case Some{n}:
      n

def apply.html(he: Maybe<&2, String>, h: String) -> String:
  match he:
    case None{}:
      h
    case Some{n}:
      n

def apply.kids(ks: List<&2, Kid>, olds: List<&2, Html>) -> List<&2, Html>:
  match ks olds:
    case Nil{} os:
      Nil{}
    case Con{KDrop{}, ks2} Con{o, os}:
      apply.kids(ks2, os)
    case Con{KAdd{n}, ks2} os:
      n <> apply.kids(ks2, os)
    case Con{KSame{EKeep{}}, ks2} Con{o, os}:
      o <> apply.kids(ks2, os)
    case Con{KSame{ESwap{n}}, ks2} Con{o, os}:
      n <> apply.kids(ks2, os)
    case Con{KSame{EText{s}}, ks2} Con{o, os}:
      HText{s} <> apply.kids(ks2, os)
    case Con{KSame{ENode{ae, kks}}, ks2} Con{HNode{t, k, a, c}, os}:
      HNode{t, k, apply.attrs(ae, a), apply.kids(kks, c)} <> apply.kids(ks2, os)
    case Con{KSame{ERaw{ae, he}}, ks2} Con{HRaw{t, k, a, h}, os}:
      HRaw{t, k, apply.attrs(ae, a), apply.html(he, h)} <> apply.kids(ks2, os)
    case Con{x, ks2} os:
      apply.kids(ks2, os)

def html.first(hs: List<&2, Html>, a: Html) -> Html:
  match hs:
    case Con{h, rest}:
      h
    case Nil{}:
      a

def apply(e: Edit, +a: Html) -> Html:
  html.first(apply.kids([KSame{e}], [a]), a)

# Rendering to HTML
# -----------------

# A page's HTML, for a server to send before the script runs (server-side
# rendering): text escaped, attributes and properties as attributes, handlers
# left to runtime.js.

# s with & < > " written as entities: so text and attribute values cannot open
# a tag or close an attribute (LAWS.bend, page_escape_safe).
def esc.pick(amp: Bool, lt: Bool, gt: Bool, quot: Bool, x: U32, r: String) -> String:
  match amp lt gt quot:
    case True{} _ _ _:
      "&amp;" ++ r
    case False{} True{} _ _:
      "&lt;" ++ r
    case False{} False{} True{} _:
      "&gt;" ++ r
    case False{} False{} False{} True{}:
      "&quot;" ++ r
    case False{} False{} False{} False{}:
      SCon{Chr{x}, r}

def escape(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{Chr{+x}, rest}:
      esc.pick(U32.is_eq(x, 38), U32.is_eq(x, 60), U32.is_eq(x, 62), U32.is_eq(x, 34), x, escape(rest))

# Whether s has no < > or ".
def safe(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{Chr{+x}, rest}:
      Bool.not(U32.is_eq(x, 60)) && (Bool.not(U32.is_eq(x, 62)) && (Bool.not(U32.is_eq(x, 34)) && safe(rest)))

# Elements with no closing tag.
def void(+t: String) -> Bool:
  String.eq(t, "input") || (String.eq(t, "br") || (String.eq(t, "img") || (String.eq(t, "hr") || (String.eq(t, "meta") ||
    (String.eq(t, "link") || (String.eq(t, "area") || (String.eq(t, "base") || (String.eq(t, "col") || (String.eq(t, "embed") ||
    (String.eq(t, "source") || (String.eq(t, "track") || String.eq(t, "wbr"))))))))))))

def render.flag.on(+n: String, on: Bool) -> String:
  match on:
    case True{}:
      " " ++ n
    case False{}:
      ""

# A property that is a flag (checked, disabled, selected) is there unless it
# is "" or "false", as runtime.js sets it.
def render.flag(+n: String, +v: String, flag: Bool) -> String:
  match flag:
    case True{}:
      render.flag.on(n, Bool.not(String.eq(v, "") || String.eq(v, "false")))
    case False{}:
      " " ++ n ++ "=\"" ++ escape(v) ++ "\""

def render.attr(a: Attr) -> String:
  match a:
    case Prop{+n, +v}:
      render.flag(n, v, String.eq(n, "checked") || (String.eq(n, "disabled") || String.eq(n, "selected")))
    case Once{+n, +v}:
      render.flag(n, v, String.eq(n, "checked") || (String.eq(n, "disabled") || String.eq(n, "selected")))
    case On{e, t}:
      ""
    case OnStop{e, t}:
      ""
    case OnKey{k, t}:
      ""

def render.attrs(as: List<&2, Attr>) -> String:
  match as:
    case Nil{}:
      ""
    case Con{a, rest}:
      render.attr(a) ++ render.attrs(rest)

def render.close(+t: String, inner: String, v: Bool) -> String:
  match v:
    case True{}:
      ""
    case False{}:
      inner ++ "</" ++ t ++ ">"

def render.list(hs: List<&2, Html>) -> String:
  match hs:
    case Nil{}:
      ""
    case Con{HText{s}, rest}:
      escape(s) ++ render.list(rest)
    case Con{HNode{+t, k, a, c}, rest}:
      "<" ++ t ++ render.attrs(a) ++ ">" ++ render.close(t, render.list(c), void(t)) ++ render.list(rest)
    case Con{HRaw{+t, k, a, h}, rest}:
      "<" ++ t ++ render.attrs(a) ++ ">" ++ h ++ "</" ++ t ++ ">" ++ render.list(rest)

def render(h: Html) -> String:
  render.list([h])
