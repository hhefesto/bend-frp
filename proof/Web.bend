import Base
import ../Web.bend as W
import ./Logic.bend as L
import ./Order.bend as O

# Facts about the page's diff the laws are proved from: string and attribute
# equality are equality (sound, and true of a thing and itself); diff then
# apply gives the new children; a diff that keeps every child came from equal
# children; a diff of children with themselves keeps every one.

# Strings and attributes
# ----------------------

law is_eq_true:
  for c: Cmp
  for h: {Cmp.is_eq(c) == True{} : Bool}
  {c == EQ{} : Cmp}

def is_eq_true(c, h):
  match c:
    case LT{}:
      L.clash({LT{} == EQ{} : Cmp}, h)
    case EQ{}:
      {==}
    case GT{}:
      L.clash({GT{} == EQ{} : Cmp}, h)

law u32_eq_sound:
  for +x: U32
  for +y: U32
  for h: {U32.is_eq(x, y) == True{} : Bool}
  {x == y : U32}

def u32_eq_sound(x, y, h):
  O.u32_cmp_eq(x, y, is_eq_true(U32.cmp(x, y), h))

law u32_eq_refl:
  for +x: U32
  {U32.is_eq(x, x) == True{} : Bool}

def u32_eq_refl(x):
  O.is_eq_of_eq(U32.cmp(x, x), O.u32_cmp_refl(x))

law scon_cong:
  for -x: U32
  for -y: U32
  for -as: String
  for -bs: String
  for e1: {x == y : U32}
  for e2: {as == bs : String}
  {SCon{Chr{x}, as} == SCon{Chr{y}, bs} : String}

def scon_cong(x, y, as, bs, e1, e2):
  %e1 : {SCon{Chr{x}, as} == SCon{Chr{_}, bs} : String}
  %e2 : {SCon{Chr{x}, as} == SCon{Chr{x}, _} : String}
  {==}

law str_eq_sound:
  for a: String
  for b: String
  for h: {W.str.eq(a, b) == True{} : Bool}
  {a == b : String}

def str_eq_sound(a, b, h):
  match a b:
    case SNil{} SNil{}:
      {==}
    case SNil{} SCon{c, bs}:
      L.clash({SNil{} == SCon{c, bs} : String}, h)
    case SCon{Chr{x}, as} SNil{}:
      L.clash({SCon{Chr{x}, as} == SNil{} : String}, h)
    case SCon{Chr{+x}, +as} SCon{Chr{+y}, +bs}:
      L.and.both(U32.is_eq(x, y), W.str.eq(as, bs), {SCon{Chr{x}, as} == SCon{Chr{y}, bs} : String}, h,
        e1 => e2 => scon_cong(x, y, as, bs, u32_eq_sound(x, y, e1), str_eq_sound(as, bs, e2)))

law str_eq_refl:
  for a: String
  {W.str.eq(a, a) == True{} : Bool}

def str_eq_refl(a):
  match a:
    case SNil{}:
      {==}
    case SCon{Chr{+x}, +as}:
      L.and.intro(U32.is_eq(x, x), W.str.eq(as, as), u32_eq_refl(x), str_eq_refl(as))

# Two strings equal where their parts are, for the five attributes.
law pair_sound:
  for +n1: String
  for +v1: String
  for +n2: String
  for +v2: String
  for -G: Type
  for h: {(W.str.eq(n1, n2) && W.str.eq(v1, v2)) == True{} : Bool}
  for k: {n1 == n2 : String} -> {v1 == v2 : String} -> G
  G

def pair_sound(n1, v1, n2, v2, G, h, k):
  L.and.both(W.str.eq(n1, n2), W.str.eq(v1, v2), G, h,
    e1 => e2 => k(str_eq_sound(n1, n2, e1), str_eq_sound(v1, v2, e2)))

law pair_refl:
  for +n: String
  for +v: String
  {(W.str.eq(n, n) && W.str.eq(v, v)) == True{} : Bool}

def pair_refl(n, v):
  L.and.intro(W.str.eq(n, n), W.str.eq(v, v), str_eq_refl(n), str_eq_refl(v))

law two:
  for -A: Data
  for -B: Data
  for -C: Data
  for -f: B -> C -> A
  for -n1: B
  for -v1: C
  for -n2: B
  for -v2: C
  for e1: {n1 == n2 : B}
  for e2: {v1 == v2 : C}
  {f(n1, v1) == f(n2, v2) : A}

def two(A, B, C, f, n1, v1, n2, v2, e1, e2):
  %e1 : {f(n1, v1) == f(_, v2) : A}
  %e2 : {f(n1, v1) == f(n1, _) : A}
  {==}

law attr_parts:
  for a: W.Attr
  {W.attr.make(W.attr.kind(a), W.attr.fst(a), W.attr.snd(a)) == a : W.Attr}

def attr_parts(a):
  match a:
    case W.Prop{n, v}:
      {==}
    case W.Once{n, v}:
      {==}
    case W.On{n, v}:
      {==}
    case W.OnStop{n, v}:
      {==}
    case W.OnKey{n, v}:
      {==}

law attr_eq_sound:
  for +a: W.Attr
  for +b: W.Attr
  for h: {W.attr.eq(a, b) == True{} : Bool}
  {a == b : W.Attr}

def attr_eq_sound(a, b, h):
  L.and.both(U32.is_eq(W.attr.kind(a), W.attr.kind(b)),
    W.str.eq(W.attr.fst(a), W.attr.fst(b)) && W.str.eq(W.attr.snd(a), W.attr.snd(b)), {a == b : W.Attr}, h,
    ek => h2 => pair_sound(W.attr.fst(a), W.attr.snd(a), W.attr.fst(b), W.attr.snd(b), {a == b : W.Attr}, h2,
      e1 => e2 => L.chain5(W.Attr, a,
        W.attr.make(W.attr.kind(a), W.attr.fst(a), W.attr.snd(a)),
        W.attr.make(W.attr.kind(b), W.attr.fst(a), W.attr.snd(a)),
        W.attr.make(W.attr.kind(b), W.attr.fst(b), W.attr.snd(a)),
        W.attr.make(W.attr.kind(b), W.attr.fst(b), W.attr.snd(b)),
        b,
        Equal.sym(W.Attr, W.attr.make(W.attr.kind(a), W.attr.fst(a), W.attr.snd(a)), a, attr_parts(a)),
        Equal.cong(U32, W.Attr, k => W.attr.make(k, W.attr.fst(a), W.attr.snd(a)), W.attr.kind(a), W.attr.kind(b),
          u32_eq_sound(W.attr.kind(a), W.attr.kind(b), ek)),
        Equal.cong(String, W.Attr, n => W.attr.make(W.attr.kind(b), n, W.attr.snd(a)), W.attr.fst(a), W.attr.fst(b), e1),
        Equal.cong(String, W.Attr, v => W.attr.make(W.attr.kind(b), W.attr.fst(b), v), W.attr.snd(a), W.attr.snd(b), e2),
        attr_parts(b))))

law attr_eq_refl:
  for +a: W.Attr
  {W.attr.eq(a, a) == True{} : Bool}

def attr_eq_refl(a):
  L.and.intro(U32.is_eq(W.attr.kind(a), W.attr.kind(a)),
    W.str.eq(W.attr.fst(a), W.attr.fst(a)) && W.str.eq(W.attr.snd(a), W.attr.snd(a)),
    u32_eq_refl(W.attr.kind(a)), pair_refl(W.attr.fst(a), W.attr.snd(a)))

law attrs_eq_sound:
  for a: List<&2, W.Attr>
  for b: List<&2, W.Attr>
  for h: {W.attrs.eq(a, b) == True{} : Bool}
  {a == b : List<&2, W.Attr>}

def attrs_eq_sound(a, b, h):
  match a b:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{y, ys}:
      L.clash({Nil{} == Con{y, ys} : List<&2, W.Attr>}, h)
    case Con{x, xs} Nil{}:
      L.clash({Con{x, xs} == Nil{} : List<&2, W.Attr>}, h)
    case Con{+x, +xs} Con{+y, +ys}:
      L.and.both(W.attr.eq(x, y), W.attrs.eq(xs, ys), {x <> xs == y <> ys : List<&2, W.Attr>}, h,
        e1 => e2 => two(List<&2, W.Attr>, W.Attr, List<&2, W.Attr>, p => q => p <> q, x, xs, y, ys, attr_eq_sound(x, y, e1), attrs_eq_sound(xs, ys, e2)))

law attrs_eq_refl:
  for a: List<&2, W.Attr>
  {W.attrs.eq(a, a) == True{} : Bool}

def attrs_eq_refl(a):
  match a:
    case Nil{}:
      {==}
    case Con{+x, +xs}:
      L.and.intro(W.attr.eq(x, x), W.attrs.eq(xs, xs), attr_eq_refl(x), attrs_eq_refl(xs))

# Nodes equal where their parts are
# ---------------------------------

law hnode_cong:
  for -t1: String
  for -k1: String
  for -a1: List<&2, W.Attr>
  for -c1: List<&2, W.Html>
  for -t2: String
  for -k2: String
  for -a2: List<&2, W.Attr>
  for -c2: List<&2, W.Html>
  for et: {t1 == t2 : String}
  for ek: {k1 == k2 : String}
  for ea: {a1 == a2 : List<&2, W.Attr>}
  for ec: {c1 == c2 : List<&2, W.Html>}
  {W.HNode{t1, k1, a1, c1} == W.HNode{t2, k2, a2, c2} : W.Html}

def hnode_cong(t1, k1, a1, c1, t2, k2, a2, c2, et, ek, ea, ec):
  %et : {W.HNode{t1, k1, a1, c1} == W.HNode{_, k2, a2, c2} : W.Html}
  %ek : {W.HNode{t1, k1, a1, c1} == W.HNode{t1, _, a2, c2} : W.Html}
  %ea : {W.HNode{t1, k1, a1, c1} == W.HNode{t1, k1, _, c2} : W.Html}
  %ec : {W.HNode{t1, k1, a1, c1} == W.HNode{t1, k1, a1, _} : W.Html}
  {==}

law hraw_cong:
  for -t1: String
  for -k1: String
  for -a1: List<&2, W.Attr>
  for -h1: String
  for -t2: String
  for -k2: String
  for -a2: List<&2, W.Attr>
  for -h2: String
  for et: {t1 == t2 : String}
  for ek: {k1 == k2 : String}
  for ea: {a1 == a2 : List<&2, W.Attr>}
  for eh: {h1 == h2 : String}
  {W.HRaw{t1, k1, a1, h1} == W.HRaw{t2, k2, a2, h2} : W.Html}

def hraw_cong(t1, k1, a1, h1, t2, k2, a2, h2, et, ek, ea, eh):
  %et : {W.HRaw{t1, k1, a1, h1} == W.HRaw{_, k2, a2, h2} : W.Html}
  %ek : {W.HRaw{t1, k1, a1, h1} == W.HRaw{t1, _, a2, h2} : W.Html}
  %ea : {W.HRaw{t1, k1, a1, h1} == W.HRaw{t1, k1, _, h2} : W.Html}
  %eh : {W.HRaw{t1, k1, a1, h1} == W.HRaw{t1, k1, a1, _} : W.Html}
  {==}

# The attributes an edit leaves are the new ones.
law attrs_edit:
  for c: Bool
  for +a1: List<&2, W.Attr>
  for +a2: List<&2, W.Attr>
  for e: {W.attrs.eq(a1, a2) == c : Bool}
  {W.apply.attrs(W.edit.attrs(c, a2), a1) == a2 : List<&2, W.Attr>}

def attrs_edit(c, a1, a2, e):
  match c:
    case True{}:
      attrs_eq_sound(a1, a2, e)
    case False{}:
      {==}

law html_edit:
  for c: Bool
  for +h1: String
  for +h2: String
  for e: {W.str.eq(h1, h2) == c : Bool}
  {W.apply.html(W.edit.html(c, h2), h1) == h2 : String}

def html_edit(c, h1, h2, e):
  match c:
    case True{}:
      str_eq_sound(h1, h2, e)
    case False{}:
      {==}

# A diff that keeps every child came from equal children
# ------------------------------------------------------

law kept.text:
  for c: Bool
  for +s1: String
  for +s2: String
  for -os: List<&2, W.Html>
  for -ns: List<&2, W.Html>
  for e: {W.str.eq(s1, s2) == c : Bool}
  for ih: {W.kids.kept(W.diff.kids(os, ns)) == True{} : Bool} -> {os == ns : List<&2, W.Html>}
  for h: {W.kids.kept(W.KSame{W.edit.text(c, s2)} <> W.diff.kids(os, ns)) == True{} : Bool}
  {W.HText{s1} <> os == W.HText{s2} <> ns : List<&2, W.Html>}

def kept.text(c, s1, s2, os, ns, e, ih, h):
  match c:
    case True{}:
      two(List<&2, W.Html>, W.Html, List<&2, W.Html>, p => q => p <> q, W.HText{s1}, os, W.HText{s2}, ns,
        Equal.cong(String, W.Html, s => W.HText{s}, s1, s2, str_eq_sound(s1, s2, e)), ih(h))
    case False{}:
      L.clash({W.HText{s1} <> os == W.HText{s2} <> ns : List<&2, W.Html>}, h)

law kept.node3:
  for c3: Bool
  for -t1: String
  for -k1: String
  for -a1: List<&2, W.Attr>
  for -c1: List<&2, W.Html>
  for -t2: String
  for -k2: String
  for -a2: List<&2, W.Attr>
  for -c2: List<&2, W.Html>
  for -os: List<&2, W.Html>
  for -ns: List<&2, W.Html>
  for et: {t1 == t2 : String}
  for ek: {k1 == k2 : String}
  for ea: {a1 == a2 : List<&2, W.Attr>}
  for e3: {W.kids.kept(W.diff.kids(c1, c2)) == c3 : Bool}
  for ihc: {W.kids.kept(W.diff.kids(c1, c2)) == True{} : Bool} -> {c1 == c2 : List<&2, W.Html>}
  for ih: {W.kids.kept(W.diff.kids(os, ns)) == True{} : Bool} -> {os == ns : List<&2, W.Html>}
  for h: {W.kids.kept(W.KSame{W.edit.node.if(c3, None{}, W.diff.kids(c1, c2))} <> W.diff.kids(os, ns)) == True{} : Bool}
  {W.HNode{t1, k1, a1, c1} <> os == W.HNode{t2, k2, a2, c2} <> ns : List<&2, W.Html>}

def kept.node3(c3, t1, k1, a1, c1, t2, k2, a2, c2, os, ns, et, ek, ea, e3, ihc, ih, h):
  match c3:
    case True{}:
      two(List<&2, W.Html>, W.Html, List<&2, W.Html>, p => q => p <> q, W.HNode{t1, k1, a1, c1}, os, W.HNode{t2, k2, a2, c2}, ns,
        hnode_cong(t1, k1, a1, c1, t2, k2, a2, c2, et, ek, ea, ihc(e3)), ih(h))
    case False{}:
      L.clash({W.HNode{t1, k1, a1, c1} <> os == W.HNode{t2, k2, a2, c2} <> ns : List<&2, W.Html>}, h)

law kept.node2:
  for c2b: Bool
  for -t1: String
  for -k1: String
  for +a1: List<&2, W.Attr>
  for -c1: List<&2, W.Html>
  for -t2: String
  for -k2: String
  for +a2: List<&2, W.Attr>
  for +c2: List<&2, W.Html>
  for +c1b: List<&2, W.Html>
  for -os: List<&2, W.Html>
  for -ns: List<&2, W.Html>
  for et: {t1 == t2 : String}
  for ek: {k1 == k2 : String}
  for ea: {W.attrs.eq(a1, a2) == c2b : Bool}
  for ec1: {c1 == c1b : List<&2, W.Html>}
  for ihc: {W.kids.kept(W.diff.kids(c1b, c2)) == True{} : Bool} -> {c1b == c2 : List<&2, W.Html>}
  for ih: {W.kids.kept(W.diff.kids(os, ns)) == True{} : Bool} -> {os == ns : List<&2, W.Html>}
  for h: {W.kids.kept(W.KSame{W.edit.node.mk(W.edit.attrs(c2b, a2), W.diff.kids(c1b, c2))} <> W.diff.kids(os, ns)) == True{} : Bool}
  {W.HNode{t1, k1, a1, c1b} <> os == W.HNode{t2, k2, a2, c2} <> ns : List<&2, W.Html>}

def kept.node2(c2b, t1, k1, a1, c1, t2, k2, a2, c2, c1b, os, ns, et, ek, ea, ec1, ihc, ih, h):
  match c2b:
    case True{}:
      kept.node3(W.kids.kept(W.diff.kids(c1b, c2)), t1, k1, a1, c1b, t2, k2, a2, c2, os, ns, et, ek,
        attrs_eq_sound(a1, a2, ea), {==}, ihc, ih, h)
    case False{}:
      L.clash({W.HNode{t1, k1, a1, c1b} <> os == W.HNode{t2, k2, a2, c2} <> ns : List<&2, W.Html>}, h)

law kept.node:
  for c: Bool
  for +t1: String
  for +k1: String
  for +a1: List<&2, W.Attr>
  for +c1: List<&2, W.Html>
  for +t2: String
  for +k2: String
  for +a2: List<&2, W.Attr>
  for +c2: List<&2, W.Html>
  for -os: List<&2, W.Html>
  for -ns: List<&2, W.Html>
  for e: {(W.str.eq(t1, t2) && W.str.eq(k1, k2)) == c : Bool}
  for ihc: {W.kids.kept(W.diff.kids(c1, c2)) == True{} : Bool} -> {c1 == c2 : List<&2, W.Html>}
  for ih: {W.kids.kept(W.diff.kids(os, ns)) == True{} : Bool} -> {os == ns : List<&2, W.Html>}
  for h: {W.kids.kept(W.KSame{W.edit.node(c, W.edit.attrs(W.attrs.eq(a1, a2), a2), w => W.diff.kids(c1, c2), W.HNode{t2, k2, a2, c2})}
            <> W.diff.kids(os, ns)) == True{} : Bool}
  {W.HNode{t1, k1, a1, c1} <> os == W.HNode{t2, k2, a2, c2} <> ns : List<&2, W.Html>}

def kept.node(c, t1, k1, a1, c1, t2, k2, a2, c2, os, ns, e, ihc, ih, h):
  match c:
    case True{}:
      pair_sound(t1, k1, t2, k2, {W.HNode{t1, k1, a1, c1} <> os == W.HNode{t2, k2, a2, c2} <> ns : List<&2, W.Html>}, e,
        et => ek => kept.node2(W.attrs.eq(a1, a2), t1, k1, a1, c1, t2, k2, a2, c2, c1, os, ns, et, ek, {==}, {==}, ihc, ih, h))
    case False{}:
      L.clash({W.HNode{t1, k1, a1, c1} <> os == W.HNode{t2, k2, a2, c2} <> ns : List<&2, W.Html>}, h)

law kept.raw2:
  for ca: Bool
  for ch: Bool
  for -t1: String
  for -k1: String
  for +a1: List<&2, W.Attr>
  for +h1: String
  for -t2: String
  for -k2: String
  for +a2: List<&2, W.Attr>
  for +h2: String
  for -os: List<&2, W.Html>
  for -ns: List<&2, W.Html>
  for et: {t1 == t2 : String}
  for ek: {k1 == k2 : String}
  for ea: {W.attrs.eq(a1, a2) == ca : Bool}
  for eh: {W.str.eq(h1, h2) == ch : Bool}
  for ih: {W.kids.kept(W.diff.kids(os, ns)) == True{} : Bool} -> {os == ns : List<&2, W.Html>}
  for h: {W.kids.kept(W.KSame{W.edit.raw.mk(W.edit.attrs(ca, a2), W.edit.html(ch, h2))} <> W.diff.kids(os, ns)) == True{} : Bool}
  {W.HRaw{t1, k1, a1, h1} <> os == W.HRaw{t2, k2, a2, h2} <> ns : List<&2, W.Html>}

def kept.raw2(ca, ch, t1, k1, a1, h1, t2, k2, a2, h2, os, ns, et, ek, ea, eh, ih, h):
  match ca ch:
    case True{} True{}:
      two(List<&2, W.Html>, W.Html, List<&2, W.Html>, p => q => p <> q, W.HRaw{t1, k1, a1, h1}, os, W.HRaw{t2, k2, a2, h2}, ns,
        hraw_cong(t1, k1, a1, h1, t2, k2, a2, h2, et, ek, attrs_eq_sound(a1, a2, ea), str_eq_sound(h1, h2, eh)), ih(h))
    case True{} False{}:
      L.clash({W.HRaw{t1, k1, a1, h1} <> os == W.HRaw{t2, k2, a2, h2} <> ns : List<&2, W.Html>}, h)
    case False{} True{}:
      L.clash({W.HRaw{t1, k1, a1, h1} <> os == W.HRaw{t2, k2, a2, h2} <> ns : List<&2, W.Html>}, h)
    case False{} False{}:
      L.clash({W.HRaw{t1, k1, a1, h1} <> os == W.HRaw{t2, k2, a2, h2} <> ns : List<&2, W.Html>}, h)

law kept.raw:
  for c: Bool
  for +t1: String
  for +k1: String
  for +a1: List<&2, W.Attr>
  for +h1: String
  for +t2: String
  for +k2: String
  for +a2: List<&2, W.Attr>
  for +h2: String
  for -os: List<&2, W.Html>
  for -ns: List<&2, W.Html>
  for e: {(W.str.eq(t1, t2) && W.str.eq(k1, k2)) == c : Bool}
  for ih: {W.kids.kept(W.diff.kids(os, ns)) == True{} : Bool} -> {os == ns : List<&2, W.Html>}
  for h: {W.kids.kept(W.KSame{W.edit.raw(c, W.edit.attrs(W.attrs.eq(a1, a2), a2), W.edit.html(W.str.eq(h1, h2), h2), W.HRaw{t2, k2, a2, h2})}
            <> W.diff.kids(os, ns)) == True{} : Bool}
  {W.HRaw{t1, k1, a1, h1} <> os == W.HRaw{t2, k2, a2, h2} <> ns : List<&2, W.Html>}

def kept.raw(c, t1, k1, a1, h1, t2, k2, a2, h2, os, ns, e, ih, h):
  match c:
    case True{}:
      pair_sound(t1, k1, t2, k2, {W.HRaw{t1, k1, a1, h1} <> os == W.HRaw{t2, k2, a2, h2} <> ns : List<&2, W.Html>}, e,
        et => ek => kept.raw2(W.attrs.eq(a1, a2), W.str.eq(h1, h2), t1, k1, a1, h1, t2, k2, a2, h2, os, ns, et, ek, {==}, {==}, ih, h))
    case False{}:
      L.clash({W.HRaw{t1, k1, a1, h1} <> os == W.HRaw{t2, k2, a2, h2} <> ns : List<&2, W.Html>}, h)

law kept_eq:
  for olds: List<&2, W.Html>
  for news: List<&2, W.Html>
  for h: {W.kids.kept(W.diff.kids(olds, news)) == True{} : Bool}
  {olds == news : List<&2, W.Html>}

def kept_eq(olds, news, h):
  match olds news:
    case Nil{} Nil{}:
      {==}
    case Con{o, os} Nil{}:
      L.clash({o <> os == Nil{} : List<&2, W.Html>}, h)
    case Nil{} Con{n, ns}:
      L.clash({Nil{} == n <> ns : List<&2, W.Html>}, h)
    case Con{W.HText{+s1}, +os} Con{W.HText{+s2}, +ns}:
      kept.text(W.str.eq(s1, s2), s1, s2, os, ns, {==}, h2 => kept_eq(os, ns, h2), h)
    case Con{W.HNode{+t1, +k1, +a1, +c1}, +os} Con{W.HNode{+t2, +k2, +a2, +c2}, +ns}:
      kept.node(W.str.eq(t1, t2) && W.str.eq(k1, k2), t1, k1, a1, c1, t2, k2, a2, c2, os, ns, {==},
        h2 => kept_eq(c1, c2, h2), h3 => kept_eq(os, ns, h3), h)
    case Con{W.HRaw{+t1, +k1, +a1, +h1}, +os} Con{W.HRaw{+t2, +k2, +a2, +h2}, +ns}:
      kept.raw(W.str.eq(t1, t2) && W.str.eq(k1, k2), t1, k1, a1, h1, t2, k2, a2, h2, os, ns, {==},
        h3 => kept_eq(os, ns, h3), h)
    case Con{W.HText{s1}, os} Con{W.HNode{t2, k2, a2, c2}, ns}:
      L.clash({W.HText{s1} <> os == W.HNode{t2, k2, a2, c2} <> ns : List<&2, W.Html>}, h)
    case Con{W.HText{s1}, os} Con{W.HRaw{t2, k2, a2, h2}, ns}:
      L.clash({W.HText{s1} <> os == W.HRaw{t2, k2, a2, h2} <> ns : List<&2, W.Html>}, h)
    case Con{W.HNode{t1, k1, a1, c1}, os} Con{W.HText{s2}, ns}:
      L.clash({W.HNode{t1, k1, a1, c1} <> os == W.HText{s2} <> ns : List<&2, W.Html>}, h)
    case Con{W.HNode{t1, k1, a1, c1}, os} Con{W.HRaw{t2, k2, a2, h2}, ns}:
      L.clash({W.HNode{t1, k1, a1, c1} <> os == W.HRaw{t2, k2, a2, h2} <> ns : List<&2, W.Html>}, h)
    case Con{W.HRaw{t1, k1, a1, h1}, os} Con{W.HText{s2}, ns}:
      L.clash({W.HRaw{t1, k1, a1, h1} <> os == W.HText{s2} <> ns : List<&2, W.Html>}, h)
    case Con{W.HRaw{t1, k1, a1, h1}, os} Con{W.HNode{t2, k2, a2, c2}, ns}:
      L.clash({W.HRaw{t1, k1, a1, h1} <> os == W.HNode{t2, k2, a2, c2} <> ns : List<&2, W.Html>}, h)

# Diff, then apply, gives the new children
# ----------------------------------------

law app.text:
  for c: Bool
  for +s1: String
  for +s2: String
  for -os: List<&2, W.Html>
  for -ns: List<&2, W.Html>
  for e: {W.str.eq(s1, s2) == c : Bool}
  for ih: {W.apply.kids(W.diff.kids(os, ns), os) == ns : List<&2, W.Html>}
  {W.apply.kids(W.KSame{W.edit.text(c, s2)} <> W.diff.kids(os, ns), W.HText{s1} <> os) == W.HText{s2} <> ns : List<&2, W.Html>}

def app.text(c, s1, s2, os, ns, e, ih):
  match c:
    case True{}:
      two(List<&2, W.Html>, W.Html, List<&2, W.Html>, p => q => p <> q, W.HText{s1}, W.apply.kids(W.diff.kids(os, ns), os), W.HText{s2}, ns,
        Equal.cong(String, W.Html, s => W.HText{s}, s1, s2, str_eq_sound(s1, s2, e)), ih)
    case False{}:
      L.cons_cong(W.Html, W.HText{s2}, W.apply.kids(W.diff.kids(os, ns), os), ns, ih)

law app.node3:
  for c3: Bool
  for -t1: String
  for -k1: String
  for -a1: List<&2, W.Attr>
  for -c1: List<&2, W.Html>
  for -t2: String
  for -k2: String
  for -a2: List<&2, W.Attr>
  for -c2: List<&2, W.Html>
  for -os: List<&2, W.Html>
  for -ns: List<&2, W.Html>
  for et: {t1 == t2 : String}
  for ek: {k1 == k2 : String}
  for ea: {a1 == a2 : List<&2, W.Attr>}
  for e3: {W.kids.kept(W.diff.kids(c1, c2)) == c3 : Bool}
  for ihc: {W.apply.kids(W.diff.kids(c1, c2), c1) == c2 : List<&2, W.Html>}
  for kc: {W.kids.kept(W.diff.kids(c1, c2)) == True{} : Bool} -> {c1 == c2 : List<&2, W.Html>}
  for ih: {W.apply.kids(W.diff.kids(os, ns), os) == ns : List<&2, W.Html>}
  {W.apply.kids(W.KSame{W.edit.node.if(c3, None{}, W.diff.kids(c1, c2))} <> W.diff.kids(os, ns), W.HNode{t1, k1, a1, c1} <> os)
     == W.HNode{t2, k2, a2, c2} <> ns : List<&2, W.Html>}

def app.node3(c3, t1, k1, a1, c1, t2, k2, a2, c2, os, ns, et, ek, ea, e3, ihc, kc, ih):
  match c3:
    case True{}:
      two(List<&2, W.Html>, W.Html, List<&2, W.Html>, p => q => p <> q, W.HNode{t1, k1, a1, c1}, W.apply.kids(W.diff.kids(os, ns), os),
        W.HNode{t2, k2, a2, c2}, ns, hnode_cong(t1, k1, a1, c1, t2, k2, a2, c2, et, ek, ea, kc(e3)), ih)
    case False{}:
      two(List<&2, W.Html>, W.Html, List<&2, W.Html>, p => q => p <> q,
        W.HNode{t1, k1, a1, W.apply.kids(W.diff.kids(c1, c2), c1)}, W.apply.kids(W.diff.kids(os, ns), os),
        W.HNode{t2, k2, a2, c2}, ns,
        hnode_cong(t1, k1, a1, W.apply.kids(W.diff.kids(c1, c2), c1), t2, k2, a2, c2, et, ek, ea, ihc), ih)

law app.node2:
  for c2b: Bool
  for -t1: String
  for -k1: String
  for +a1: List<&2, W.Attr>
  for +c1: List<&2, W.Html>
  for -t2: String
  for -k2: String
  for +a2: List<&2, W.Attr>
  for +c2: List<&2, W.Html>
  for -os: List<&2, W.Html>
  for -ns: List<&2, W.Html>
  for et: {t1 == t2 : String}
  for ek: {k1 == k2 : String}
  for ea: {W.attrs.eq(a1, a2) == c2b : Bool}
  for ihc: {W.apply.kids(W.diff.kids(c1, c2), c1) == c2 : List<&2, W.Html>}
  for kc: {W.kids.kept(W.diff.kids(c1, c2)) == True{} : Bool} -> {c1 == c2 : List<&2, W.Html>}
  for ih: {W.apply.kids(W.diff.kids(os, ns), os) == ns : List<&2, W.Html>}
  {W.apply.kids(W.KSame{W.edit.node.mk(W.edit.attrs(c2b, a2), W.diff.kids(c1, c2))} <> W.diff.kids(os, ns), W.HNode{t1, k1, a1, c1} <> os)
     == W.HNode{t2, k2, a2, c2} <> ns : List<&2, W.Html>}

def app.node2(c2b, t1, k1, a1, c1, t2, k2, a2, c2, os, ns, et, ek, ea, ihc, kc, ih):
  match c2b:
    case True{}:
      app.node3(W.kids.kept(W.diff.kids(c1, c2)), t1, k1, a1, c1, t2, k2, a2, c2, os, ns, et, ek,
        attrs_eq_sound(a1, a2, ea), {==}, ihc, kc, ih)
    case False{}:
      two(List<&2, W.Html>, W.Html, List<&2, W.Html>, p => q => p <> q,
        W.HNode{t1, k1, a2, W.apply.kids(W.diff.kids(c1, c2), c1)}, W.apply.kids(W.diff.kids(os, ns), os),
        W.HNode{t2, k2, a2, c2}, ns,
        hnode_cong(t1, k1, a2, W.apply.kids(W.diff.kids(c1, c2), c1), t2, k2, a2, c2, et, ek, {==}, ihc), ih)

law app.node:
  for c: Bool
  for +t1: String
  for +k1: String
  for +a1: List<&2, W.Attr>
  for +c1: List<&2, W.Html>
  for +t2: String
  for +k2: String
  for +a2: List<&2, W.Attr>
  for +c2: List<&2, W.Html>
  for -os: List<&2, W.Html>
  for -ns: List<&2, W.Html>
  for e: {(W.str.eq(t1, t2) && W.str.eq(k1, k2)) == c : Bool}
  for ihc: {W.apply.kids(W.diff.kids(c1, c2), c1) == c2 : List<&2, W.Html>}
  for kc: {W.kids.kept(W.diff.kids(c1, c2)) == True{} : Bool} -> {c1 == c2 : List<&2, W.Html>}
  for ih: {W.apply.kids(W.diff.kids(os, ns), os) == ns : List<&2, W.Html>}
  {W.apply.kids(W.KSame{W.edit.node(c, W.edit.attrs(W.attrs.eq(a1, a2), a2), w => W.diff.kids(c1, c2), W.HNode{t2, k2, a2, c2})}
       <> W.diff.kids(os, ns), W.HNode{t1, k1, a1, c1} <> os)
     == W.HNode{t2, k2, a2, c2} <> ns : List<&2, W.Html>}

def app.node(c, t1, k1, a1, c1, t2, k2, a2, c2, os, ns, e, ihc, kc, ih):
  match c:
    case True{}:
      pair_sound(t1, k1, t2, k2,
        {W.apply.kids(W.KSame{W.edit.node.mk(W.edit.attrs(W.attrs.eq(a1, a2), a2), W.diff.kids(c1, c2))} <> W.diff.kids(os, ns),
           W.HNode{t1, k1, a1, c1} <> os) == W.HNode{t2, k2, a2, c2} <> ns : List<&2, W.Html>}, e,
        et => ek => app.node2(W.attrs.eq(a1, a2), t1, k1, a1, c1, t2, k2, a2, c2, os, ns, et, ek, {==}, ihc, kc, ih))
    case False{}:
      L.cons_cong(W.Html, W.HNode{t2, k2, a2, c2}, W.apply.kids(W.diff.kids(os, ns), os), ns, ih)

law app.raw2:
  for ca: Bool
  for ch: Bool
  for -t1: String
  for -k1: String
  for +a1: List<&2, W.Attr>
  for +h1: String
  for -t2: String
  for -k2: String
  for +a2: List<&2, W.Attr>
  for +h2: String
  for -os: List<&2, W.Html>
  for -ns: List<&2, W.Html>
  for et: {t1 == t2 : String}
  for ek: {k1 == k2 : String}
  for ea: {W.attrs.eq(a1, a2) == ca : Bool}
  for eh: {W.str.eq(h1, h2) == ch : Bool}
  for ih: {W.apply.kids(W.diff.kids(os, ns), os) == ns : List<&2, W.Html>}
  {W.apply.kids(W.KSame{W.edit.raw.mk(W.edit.attrs(ca, a2), W.edit.html(ch, h2))} <> W.diff.kids(os, ns), W.HRaw{t1, k1, a1, h1} <> os)
     == W.HRaw{t2, k2, a2, h2} <> ns : List<&2, W.Html>}

def app.raw2(ca, ch, t1, k1, a1, h1, t2, k2, a2, h2, os, ns, et, ek, ea, eh, ih):
  match ca ch:
    case True{} True{}:
      two(List<&2, W.Html>, W.Html, List<&2, W.Html>, p => q => p <> q, W.HRaw{t1, k1, a1, h1}, W.apply.kids(W.diff.kids(os, ns), os),
        W.HRaw{t2, k2, a2, h2}, ns,
        hraw_cong(t1, k1, a1, h1, t2, k2, a2, h2, et, ek, attrs_edit(True{}, a1, a2, ea), html_edit(True{}, h1, h2, eh)), ih)
    case True{} False{}:
      two(List<&2, W.Html>, W.Html, List<&2, W.Html>, p => q => p <> q, W.HRaw{t1, k1, a1, h2}, W.apply.kids(W.diff.kids(os, ns), os),
        W.HRaw{t2, k2, a2, h2}, ns,
        hraw_cong(t1, k1, a1, h2, t2, k2, a2, h2, et, ek, attrs_edit(True{}, a1, a2, ea), {==}), ih)
    case False{} True{}:
      two(List<&2, W.Html>, W.Html, List<&2, W.Html>, p => q => p <> q, W.HRaw{t1, k1, a2, h1}, W.apply.kids(W.diff.kids(os, ns), os),
        W.HRaw{t2, k2, a2, h2}, ns,
        hraw_cong(t1, k1, a2, h1, t2, k2, a2, h2, et, ek, {==}, html_edit(True{}, h1, h2, eh)), ih)
    case False{} False{}:
      two(List<&2, W.Html>, W.Html, List<&2, W.Html>, p => q => p <> q, W.HRaw{t1, k1, a2, h2}, W.apply.kids(W.diff.kids(os, ns), os),
        W.HRaw{t2, k2, a2, h2}, ns,
        hraw_cong(t1, k1, a2, h2, t2, k2, a2, h2, et, ek, {==}, {==}), ih)

law app.raw:
  for c: Bool
  for +t1: String
  for +k1: String
  for +a1: List<&2, W.Attr>
  for +h1: String
  for +t2: String
  for +k2: String
  for +a2: List<&2, W.Attr>
  for +h2: String
  for -os: List<&2, W.Html>
  for -ns: List<&2, W.Html>
  for e: {(W.str.eq(t1, t2) && W.str.eq(k1, k2)) == c : Bool}
  for ih: {W.apply.kids(W.diff.kids(os, ns), os) == ns : List<&2, W.Html>}
  {W.apply.kids(W.KSame{W.edit.raw(c, W.edit.attrs(W.attrs.eq(a1, a2), a2), W.edit.html(W.str.eq(h1, h2), h2), W.HRaw{t2, k2, a2, h2})}
       <> W.diff.kids(os, ns), W.HRaw{t1, k1, a1, h1} <> os)
     == W.HRaw{t2, k2, a2, h2} <> ns : List<&2, W.Html>}

def app.raw(c, t1, k1, a1, h1, t2, k2, a2, h2, os, ns, e, ih):
  match c:
    case True{}:
      pair_sound(t1, k1, t2, k2,
        {W.apply.kids(W.KSame{W.edit.raw.mk(W.edit.attrs(W.attrs.eq(a1, a2), a2), W.edit.html(W.str.eq(h1, h2), h2))} <> W.diff.kids(os, ns),
           W.HRaw{t1, k1, a1, h1} <> os) == W.HRaw{t2, k2, a2, h2} <> ns : List<&2, W.Html>}, e,
        et => ek => app.raw2(W.attrs.eq(a1, a2), W.str.eq(h1, h2), t1, k1, a1, h1, t2, k2, a2, h2, os, ns, et, ek, {==}, {==}, ih))
    case False{}:
      L.cons_cong(W.Html, W.HRaw{t2, k2, a2, h2}, W.apply.kids(W.diff.kids(os, ns), os), ns, ih)

law diff_apply_kids:
  for olds: List<&2, W.Html>
  for news: List<&2, W.Html>
  {W.apply.kids(W.diff.kids(olds, news), olds) == news : List<&2, W.Html>}

def diff_apply_kids(olds, news):
  match olds news:
    case Nil{} Nil{}:
      {==}
    case Con{o, os} Nil{}:
      diff_apply_kids(os, Nil{})
    case Nil{} Con{+n, ns}:
      L.cons_cong(W.Html, n, W.apply.kids(W.diff.kids(Nil{}, ns), Nil{}), ns, diff_apply_kids(Nil{}, ns))
    case Con{W.HText{+s1}, +os} Con{W.HText{+s2}, +ns}:
      app.text(W.str.eq(s1, s2), s1, s2, os, ns, {==}, diff_apply_kids(os, ns))
    case Con{W.HNode{+t1, +k1, +a1, +c1}, +os} Con{W.HNode{+t2, +k2, +a2, +c2}, +ns}:
      app.node(W.str.eq(t1, t2) && W.str.eq(k1, k2), t1, k1, a1, c1, t2, k2, a2, c2, os, ns, {==},
        diff_apply_kids(c1, c2), h => kept_eq(c1, c2, h), diff_apply_kids(os, ns))
    case Con{W.HRaw{+t1, +k1, +a1, +h1}, +os} Con{W.HRaw{+t2, +k2, +a2, +h2}, +ns}:
      app.raw(W.str.eq(t1, t2) && W.str.eq(k1, k2), t1, k1, a1, h1, t2, k2, a2, h2, os, ns, {==}, diff_apply_kids(os, ns))
    case Con{W.HText{s1}, +os} Con{W.HNode{+t2, +k2, +a2, +c2}, +ns}:
      L.cons_cong(W.Html, W.HNode{t2, k2, a2, c2}, W.apply.kids(W.diff.kids(os, ns), os), ns, diff_apply_kids(os, ns))
    case Con{W.HText{s1}, +os} Con{W.HRaw{+t2, +k2, +a2, +h2}, +ns}:
      L.cons_cong(W.Html, W.HRaw{t2, k2, a2, h2}, W.apply.kids(W.diff.kids(os, ns), os), ns, diff_apply_kids(os, ns))
    case Con{W.HNode{t1, k1, a1, c1}, +os} Con{W.HText{+s2}, +ns}:
      L.cons_cong(W.Html, W.HText{s2}, W.apply.kids(W.diff.kids(os, ns), os), ns, diff_apply_kids(os, ns))
    case Con{W.HNode{t1, k1, a1, c1}, +os} Con{W.HRaw{+t2, +k2, +a2, +h2}, +ns}:
      L.cons_cong(W.Html, W.HRaw{t2, k2, a2, h2}, W.apply.kids(W.diff.kids(os, ns), os), ns, diff_apply_kids(os, ns))
    case Con{W.HRaw{t1, k1, a1, h1}, +os} Con{W.HText{+s2}, +ns}:
      L.cons_cong(W.Html, W.HText{s2}, W.apply.kids(W.diff.kids(os, ns), os), ns, diff_apply_kids(os, ns))
    case Con{W.HRaw{t1, k1, a1, h1}, +os} Con{W.HNode{+t2, +k2, +a2, +c2}, +ns}:
      L.cons_cong(W.Html, W.HNode{t2, k2, a2, c2}, W.apply.kids(W.diff.kids(os, ns), os), ns, diff_apply_kids(os, ns))

# Children diffed with themselves are all kept
# --------------------------------------------

law self_kept:
  for vs: List<&2, W.Html>
  {W.kids.kept(W.diff.kids(vs, vs)) == True{} : Bool}

def self_kept(vs):
  match vs:
    case Nil{}:
      {==}
    case Con{W.HText{+s}, +rest}:
      %Equal.sym(Bool, W.str.eq(s, s), True{}, str_eq_refl(s)) :
        {W.kids.kept(W.KSame{W.edit.text(_, s)} <> W.diff.kids(rest, rest)) == True{} : Bool}
      self_kept(rest)
    case Con{W.HNode{+t, +k, +a, +c}, +rest}:
      %Equal.sym(Bool, W.str.eq(t, t) && W.str.eq(k, k), True{}, pair_refl(t, k)) :
        {W.kids.kept(W.KSame{W.edit.node(_, W.edit.attrs(W.attrs.eq(a, a), a), w => W.diff.kids(c, c), W.HNode{t, k, a, c})}
           <> W.diff.kids(rest, rest)) == True{} : Bool}
      %Equal.sym(Bool, W.attrs.eq(a, a), True{}, attrs_eq_refl(a)) :
        {W.kids.kept(W.KSame{W.edit.node(True{}, W.edit.attrs(_, a), w => W.diff.kids(c, c), W.HNode{t, k, a, c})}
           <> W.diff.kids(rest, rest)) == True{} : Bool}
      %Equal.sym(Bool, W.kids.kept(W.diff.kids(c, c)), True{}, self_kept(c)) :
        {W.kids.kept(W.KSame{W.edit.node.if(_, None{}, W.diff.kids(c, c))} <> W.diff.kids(rest, rest)) == True{} : Bool}
      self_kept(rest)
    case Con{W.HRaw{+t, +k, +a, +h}, +rest}:
      %Equal.sym(Bool, W.str.eq(t, t) && W.str.eq(k, k), True{}, pair_refl(t, k)) :
        {W.kids.kept(W.KSame{W.edit.raw(_, W.edit.attrs(W.attrs.eq(a, a), a), W.edit.html(W.str.eq(h, h), h), W.HRaw{t, k, a, h})}
           <> W.diff.kids(rest, rest)) == True{} : Bool}
      %Equal.sym(Bool, W.attrs.eq(a, a), True{}, attrs_eq_refl(a)) :
        {W.kids.kept(W.KSame{W.edit.raw(True{}, W.edit.attrs(_, a), W.edit.html(W.str.eq(h, h), h), W.HRaw{t, k, a, h})}
           <> W.diff.kids(rest, rest)) == True{} : Bool}
      %Equal.sym(Bool, W.str.eq(h, h), True{}, str_eq_refl(h)) :
        {W.kids.kept(W.KSame{W.edit.raw(True{}, W.edit.attrs(True{}, a), W.edit.html(_, h), W.HRaw{t, k, a, h})}
           <> W.diff.kids(rest, rest)) == True{} : Bool}
      self_kept(rest)

# The page's two laws
# -------------------

law diff_self:
  for +a: W.Html
  {W.diff(a, a) == W.EKeep{} : W.Edit}

def diff_self(a):
  match a:
    case W.HText{+s}:
      %Equal.sym(Bool, W.str.eq(s, s), True{}, str_eq_refl(s)) : {W.edit.text(_, s) == W.EKeep{} : W.Edit}
      {==}
    case W.HNode{+t, +k, +as, +c}:
      %Equal.sym(Bool, W.str.eq(t, t) && W.str.eq(k, k), True{}, pair_refl(t, k)) :
        {W.edit.node(_, W.edit.attrs(W.attrs.eq(as, as), as), w => W.diff.kids(c, c), W.HNode{t, k, as, c}) == W.EKeep{} : W.Edit}
      %Equal.sym(Bool, W.attrs.eq(as, as), True{}, attrs_eq_refl(as)) :
        {W.edit.node(True{}, W.edit.attrs(_, as), w => W.diff.kids(c, c), W.HNode{t, k, as, c}) == W.EKeep{} : W.Edit}
      %Equal.sym(Bool, W.kids.kept(W.diff.kids(c, c)), True{}, self_kept(c)) :
        {W.edit.node.if(_, None{}, W.diff.kids(c, c)) == W.EKeep{} : W.Edit}
      {==}
    case W.HRaw{+t, +k, +as, +h}:
      %Equal.sym(Bool, W.str.eq(t, t) && W.str.eq(k, k), True{}, pair_refl(t, k)) :
        {W.edit.raw(_, W.edit.attrs(W.attrs.eq(as, as), as), W.edit.html(W.str.eq(h, h), h), W.HRaw{t, k, as, h}) == W.EKeep{} : W.Edit}
      %Equal.sym(Bool, W.attrs.eq(as, as), True{}, attrs_eq_refl(as)) :
        {W.edit.raw(True{}, W.edit.attrs(_, as), W.edit.html(W.str.eq(h, h), h), W.HRaw{t, k, as, h}) == W.EKeep{} : W.Edit}
      %Equal.sym(Bool, W.str.eq(h, h), True{}, str_eq_refl(h)) :
        {W.edit.raw(True{}, W.edit.attrs(True{}, as), W.edit.html(_, h), W.HRaw{t, k, as, h}) == W.EKeep{} : W.Edit}
      {==}

law diff_apply:
  for +a: W.Html
  for +b: W.Html
  {W.apply(W.diff(a, b), a) == b : W.Html}

def diff_apply(a, b):
  match a b:
    case W.HText{+s1} W.HText{+s2}:
      Equal.cong(List<&2, W.Html>, W.Html, hs => W.html.first(hs, W.HText{s1}),
        W.apply.kids(W.diff.kids([W.HText{s1}], [W.HText{s2}]), [W.HText{s1}]), [W.HText{s2}],
        diff_apply_kids([W.HText{s1}], [W.HText{s2}]))
    case W.HText{+s1} W.HNode{+t2, +k2, +a2, +c2}:
      Equal.cong(List<&2, W.Html>, W.Html, hs => W.html.first(hs, W.HText{s1}),
        W.apply.kids(W.diff.kids([W.HText{s1}], [W.HNode{t2, k2, a2, c2}]), [W.HText{s1}]), [W.HNode{t2, k2, a2, c2}],
        diff_apply_kids([W.HText{s1}], [W.HNode{t2, k2, a2, c2}]))
    case W.HText{+s1} W.HRaw{+t2, +k2, +a2, +h2}:
      Equal.cong(List<&2, W.Html>, W.Html, hs => W.html.first(hs, W.HText{s1}),
        W.apply.kids(W.diff.kids([W.HText{s1}], [W.HRaw{t2, k2, a2, h2}]), [W.HText{s1}]), [W.HRaw{t2, k2, a2, h2}],
        diff_apply_kids([W.HText{s1}], [W.HRaw{t2, k2, a2, h2}]))
    case W.HNode{+t1, +k1, +a1, +c1} W.HText{+s2}:
      Equal.cong(List<&2, W.Html>, W.Html, hs => W.html.first(hs, W.HNode{t1, k1, a1, c1}),
        W.apply.kids(W.diff.kids([W.HNode{t1, k1, a1, c1}], [W.HText{s2}]), [W.HNode{t1, k1, a1, c1}]), [W.HText{s2}],
        diff_apply_kids([W.HNode{t1, k1, a1, c1}], [W.HText{s2}]))
    case W.HNode{+t1, +k1, +a1, +c1} W.HNode{+t2, +k2, +a2, +c2}:
      Equal.cong(List<&2, W.Html>, W.Html, hs => W.html.first(hs, W.HNode{t1, k1, a1, c1}),
        W.apply.kids(W.diff.kids([W.HNode{t1, k1, a1, c1}], [W.HNode{t2, k2, a2, c2}]), [W.HNode{t1, k1, a1, c1}]), [W.HNode{t2, k2, a2, c2}],
        diff_apply_kids([W.HNode{t1, k1, a1, c1}], [W.HNode{t2, k2, a2, c2}]))
    case W.HNode{+t1, +k1, +a1, +c1} W.HRaw{+t2, +k2, +a2, +h2}:
      Equal.cong(List<&2, W.Html>, W.Html, hs => W.html.first(hs, W.HNode{t1, k1, a1, c1}),
        W.apply.kids(W.diff.kids([W.HNode{t1, k1, a1, c1}], [W.HRaw{t2, k2, a2, h2}]), [W.HNode{t1, k1, a1, c1}]), [W.HRaw{t2, k2, a2, h2}],
        diff_apply_kids([W.HNode{t1, k1, a1, c1}], [W.HRaw{t2, k2, a2, h2}]))
    case W.HRaw{+t1, +k1, +a1, +h1} W.HText{+s2}:
      Equal.cong(List<&2, W.Html>, W.Html, hs => W.html.first(hs, W.HRaw{t1, k1, a1, h1}),
        W.apply.kids(W.diff.kids([W.HRaw{t1, k1, a1, h1}], [W.HText{s2}]), [W.HRaw{t1, k1, a1, h1}]), [W.HText{s2}],
        diff_apply_kids([W.HRaw{t1, k1, a1, h1}], [W.HText{s2}]))
    case W.HRaw{+t1, +k1, +a1, +h1} W.HNode{+t2, +k2, +a2, +c2}:
      Equal.cong(List<&2, W.Html>, W.Html, hs => W.html.first(hs, W.HRaw{t1, k1, a1, h1}),
        W.apply.kids(W.diff.kids([W.HRaw{t1, k1, a1, h1}], [W.HNode{t2, k2, a2, c2}]), [W.HRaw{t1, k1, a1, h1}]), [W.HNode{t2, k2, a2, c2}],
        diff_apply_kids([W.HRaw{t1, k1, a1, h1}], [W.HNode{t2, k2, a2, c2}]))
    case W.HRaw{+t1, +k1, +a1, +h1} W.HRaw{+t2, +k2, +a2, +h2}:
      Equal.cong(List<&2, W.Html>, W.Html, hs => W.html.first(hs, W.HRaw{t1, k1, a1, h1}),
        W.apply.kids(W.diff.kids([W.HRaw{t1, k1, a1, h1}], [W.HRaw{t2, k2, a2, h2}]), [W.HRaw{t1, k1, a1, h1}]), [W.HRaw{t2, k2, a2, h2}],
        diff_apply_kids([W.HRaw{t1, k1, a1, h1}], [W.HRaw{t2, k2, a2, h2}]))
