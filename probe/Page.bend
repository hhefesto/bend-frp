import Base
import ../Web.bend as W

# A view rendered to HTML (server-side rendering) and addresses split into
# segments, against what was worked out by hand: text and attribute values
# escaped, a flag property present only when set, no closing tag for input,
# the ready-made inside as it is, handlers left out.

def view() -> W.Html:
  W.el("div", [W.cls("app"), W.On{"click", "x"}],
    [W.text("a < b & \"c\""),
     W.el("input", [W.Prop{"value", "q\"x"}, W.Prop{"checked", "true"}, W.Prop{"disabled", ""}], []),
     W.HRaw{"p", "", [], "<b>raw</b>"}])

def main() -> List<&2, String>:
  [W.render(view()),
   String.join(W.path("/notes/7?x=1#top"), "|"),
   String.join(W.path("a//b/"), "|")]
