import Base
import ../Frp.bend as F
import ./Logic.bend as L

# The order of times is a strict total order, as the reals' is. Time.cmp
# compares the seconds, then the fractions, each a U32: Base's 32-bit word,
# whose compare (Word.cmp) is defined bit by bit. So the facts are proved
# from the bits up: a compare turned round is flipped; EQ means equal; LT is
# transitive. Time.lt's laws (LAWS.bend) follow.

def cmp.flip(c: Cmp) -> Cmp:
  match c:
    case LT{}:
      GT{}
    case EQ{}:
      EQ{}
    case GT{}:
      LT{}

# Words
# -----

law bool_cmp_flip:
  for a: Bool
  for b: Bool
  {Bool.cmp(a, b) == cmp.flip(Bool.cmp(b, a)) : Cmp}

def bool_cmp_flip(a, b):
  match a b:
    case False{} False{}:
      {==}
    case False{} True{}:
      {==}
    case True{} False{}:
      {==}
    case True{} True{}:
      {==}

law fin_flip:
  for a: Bool
  for b: Bool
  for c: Cmp
  {Word.cmp.fin(a, b, cmp.flip(c)) == cmp.flip(Word.cmp.fin(b, a, c)) : Cmp}

def fin_flip(a, b, c):
  match c:
    case LT{}:
      {==}
    case EQ{}:
      bool_cmp_flip(a, b)
    case GT{}:
      {==}

law word_cmp_flip:
  for +n: Nat
  for a: Word(n)
  for b: Word(n)
  {Word.cmp(n, a, b) == cmp.flip(Word.cmp(n, b, a)) : Cmp}

def word_cmp_flip(n, a, b):
  match n:
    case 0n:
      {==}
    case 1n+p:
      match a b:
        case WCon{ab, +at} WCon{bb, +bt}:
          Equal.trans(Cmp, Word.cmp.fin(ab, bb, Word.cmp(p, at, bt)),
            Word.cmp.fin(ab, bb, cmp.flip(Word.cmp(p, bt, at))),
            cmp.flip(Word.cmp.fin(bb, ab, Word.cmp(p, bt, at))),
            Equal.cong(Cmp, Cmp, c => Word.cmp.fin(ab, bb, c), Word.cmp(p, at, bt), cmp.flip(Word.cmp(p, bt, at)),
              word_cmp_flip(p, at, bt)),
            fin_flip(ab, bb, Word.cmp(p, bt, at)))

law fin_eq:
  for c: Cmp
  for ab: Bool
  for bb: Bool
  for -G: Type
  for h: {Word.cmp.fin(ab, bb, c) == EQ{} : Cmp}
  for k: {ab == bb : Bool} -> {c == EQ{} : Cmp} -> G
  G

def fin_eq(c, ab, bb, G, h, k):
  match c:
    case LT{}:
      L.cmp.ne_eq(G, LT{}, h, Unit{})
    case EQ{}:
      match ab bb:
        case False{} False{}:
          k({==}, {==})
        case False{} True{}:
          L.cmp.ne_eq(G, LT{}, h, Unit{})
        case True{} False{}:
          L.cmp.ne_eq(G, GT{}, h, Unit{})
        case True{} True{}:
          k({==}, {==})
    case GT{}:
      L.cmp.ne_eq(G, GT{}, h, Unit{})

law wcon_cong:
  for -p: Nat
  for -ab: Bool
  for -bb: Bool
  for -at: Word(p)
  for -bt: Word(p)
  for e1: {ab == bb : Bool}
  for e2: {at == bt : Word(p)}
  {WCon{ab, at} == WCon{bb, bt} : Word(1n+p)}

def wcon_cong(p, ab, bb, at, bt, e1, e2):
  %e1 : {WCon{ab, at} == WCon{_, bt} : Word(1n+p)}
  %e2 : {WCon{ab, at} == WCon{ab, _} : Word(1n+p)}
  {==}

law word_cmp_eq:
  for +n: Nat
  for a: Word(n)
  for b: Word(n)
  for h: {Word.cmp(n, a, b) == EQ{} : Cmp}
  {a == b : Word(n)}

def word_cmp_eq(n, a, b, h):
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n+p:
      match a b:
        case WCon{ab, +at} WCon{bb, +bt}:
          fin_eq(Word.cmp(p, at, bt), ab, bb, {WCon{ab, at} == WCon{bb, bt} : Word(1n+p)}, h,
            e1 => e2 => wcon_cong(p, ab, bb, at, bt, e1, word_cmp_eq(p, at, bt, e2)))

law fin_lt:
  for c: Cmp
  for ab: Bool
  for bb: Bool
  for -G: Type
  for h: {Word.cmp.fin(ab, bb, c) == LT{} : Cmp}
  for k1: {c == LT{} : Cmp} -> G
  for k2: {c == EQ{} : Cmp} -> {ab == False{} : Bool} -> {bb == True{} : Bool} -> G
  G

def fin_lt(c, ab, bb, G, h, k1, k2):
  match c:
    case LT{}:
      k1({==})
    case EQ{}:
      match ab bb:
        case False{} False{}:
          L.cmp.ne_lt(G, EQ{}, h, Unit{})
        case False{} True{}:
          k2({==}, {==}, {==})
        case True{} False{}:
          L.cmp.ne_lt(G, GT{}, h, Unit{})
        case True{} True{}:
          L.cmp.ne_lt(G, EQ{}, h, Unit{})
    case GT{}:
      L.cmp.ne_lt(G, GT{}, h, Unit{})

law fin_of_lt:
  for -x: Bool
  for -y: Bool
  for -c: Cmp
  for h: {c == LT{} : Cmp}
  {Word.cmp.fin(x, y, c) == LT{} : Cmp}

def fin_of_lt(x, y, c, h):
  Equal.cong(Cmp, Cmp, z => Word.cmp.fin(x, y, z), c, LT{}, h)

law word_lt_eq_r:
  for -n: Nat
  for -a: Word(n)
  for -b: Word(n)
  for -c: Word(n)
  for l: {Word.cmp(n, a, b) == LT{} : Cmp}
  for e: {b == c : Word(n)}
  {Word.cmp(n, a, c) == LT{} : Cmp}

def word_lt_eq_r(n, a, b, c, l, e):
  %e : {Word.cmp(n, a, _) == LT{} : Cmp}
  l

law word_lt_eq_l:
  for -n: Nat
  for -a: Word(n)
  for -b: Word(n)
  for -c: Word(n)
  for e: {a == b : Word(n)}
  for l: {Word.cmp(n, b, c) == LT{} : Cmp}
  {Word.cmp(n, a, c) == LT{} : Cmp}

def word_lt_eq_l(n, a, b, c, e, l):
  %Equal.sym(Word(n), a, b, e) : {Word.cmp(n, _, c) == LT{} : Cmp}
  l

law word_cmp_lt_trans:
  for +n: Nat
  for a: Word(n)
  for b: Word(n)
  for c: Word(n)
  for h1: {Word.cmp(n, a, b) == LT{} : Cmp}
  for +h2: {Word.cmp(n, b, c) == LT{} : Cmp}
  {Word.cmp(n, a, c) == LT{} : Cmp}

def word_cmp_lt_trans(n, a, b, c, h1, h2):
  match n:
    case 0n:
      L.cmp.ne_lt({EQ{} == LT{} : Cmp}, EQ{}, h1, Unit{})
    case 1n+p:
      match a b c:
        case WCon{+ab, +at} WCon{+bb, +bt} WCon{+cb, +ct}:
          fin_lt(Word.cmp(p, at, bt), ab, bb, {Word.cmp.fin(ab, cb, Word.cmp(p, at, ct)) == LT{} : Cmp}, h1,
            +l1 => fin_lt(Word.cmp(p, bt, ct), bb, cb, {Word.cmp.fin(ab, cb, Word.cmp(p, at, ct)) == LT{} : Cmp}, h2,
              l2 => fin_of_lt(ab, cb, Word.cmp(p, at, ct), word_cmp_lt_trans(p, at, bt, ct, l1, l2)),
              e2 => x => y => fin_of_lt(ab, cb, Word.cmp(p, at, ct), word_lt_eq_r(p, at, bt, ct, l1, word_cmp_eq(p, bt, ct, e2)))),
            e1 => abF => bbT => fin_lt(Word.cmp(p, bt, ct), bb, cb, {Word.cmp.fin(ab, cb, Word.cmp(p, at, ct)) == LT{} : Cmp}, h2,
              l2 => fin_of_lt(ab, cb, Word.cmp(p, at, ct), word_lt_eq_l(p, at, bt, ct, word_cmp_eq(p, at, bt, e1), l2)),
              e2 => bbF => cbT => L.both({Word.cmp.fin(ab, cb, Word.cmp(p, at, ct)) == LT{} : Cmp}, bb, bbT, bbF)))

# U32
# ---

law u32_cmp_flip:
  for a: U32
  for b: U32
  {U32.cmp(a, b) == cmp.flip(U32.cmp(b, a)) : Cmp}

def u32_cmp_flip(a, b):
  match a b:
    case U32{x} U32{y}:
      word_cmp_flip(32n, x, y)

law u32_cmp_eq:
  for a: U32
  for b: U32
  for h: {U32.cmp(a, b) == EQ{} : Cmp}
  {a == b : U32}

def u32_cmp_eq(a, b, h):
  match a b:
    case U32{x} U32{y}:
      Equal.cong(Word(32n), U32, w => U32{w}, x, y, word_cmp_eq(32n, x, y, h))

law u32_cmp_lt_trans:
  for a: U32
  for b: U32
  for c: U32
  for h1: {U32.cmp(a, b) == LT{} : Cmp}
  for h2: {U32.cmp(b, c) == LT{} : Cmp}
  {U32.cmp(a, c) == LT{} : Cmp}

def u32_cmp_lt_trans(a, b, c, h1, h2):
  match a b c:
    case U32{x} U32{y} U32{z}:
      word_cmp_lt_trans(32n, x, y, z, h1, h2)

# A compare equal to its flip is EQ.
law cmp_flip_self:
  for c: Cmp
  for h: {c == cmp.flip(c) : Cmp}
  {c == EQ{} : Cmp}

def cmp_flip_self(c, h):
  match c:
    case LT{}:
      L.cmp.ne_gt({LT{} == EQ{} : Cmp}, LT{}, h, Unit{})
    case EQ{}:
      {==}
    case GT{}:
      L.cmp.ne_lt({GT{} == EQ{} : Cmp}, GT{}, h, Unit{})

law u32_cmp_refl:
  for +a: U32
  {U32.cmp(a, a) == EQ{} : Cmp}

def u32_cmp_refl(a):
  cmp_flip_self(U32.cmp(a, a), u32_cmp_flip(a, a))

law u32_cmp_eq_of:
  for +a: U32
  for -b: U32
  for e: {a == b : U32}
  {U32.cmp(a, b) == EQ{} : Cmp}

def u32_cmp_eq_of(a, b, e):
  %e : {U32.cmp(a, _) == EQ{} : Cmp}
  u32_cmp_refl(a)

law u32_lt_eq_r:
  for -a: U32
  for -b: U32
  for -c: U32
  for l: {U32.cmp(a, b) == LT{} : Cmp}
  for e: {b == c : U32}
  {U32.cmp(a, c) == LT{} : Cmp}

def u32_lt_eq_r(a, b, c, l, e):
  %e : {U32.cmp(a, _) == LT{} : Cmp}
  l

law u32_lt_eq_l:
  for -a: U32
  for -b: U32
  for -c: U32
  for e: {a == b : U32}
  for l: {U32.cmp(b, c) == LT{} : Cmp}
  {U32.cmp(a, c) == LT{} : Cmp}

def u32_lt_eq_l(a, b, c, e, l):
  %Equal.sym(U32, a, b, e) : {U32.cmp(_, c) == LT{} : Cmp}
  l

# Time.cmp
# --------

law lex_flip:
  for h: Cmp
  for -l: Cmp
  {F.Time.lex(cmp.flip(h), cmp.flip(l)) == cmp.flip(F.Time.lex(h, l)) : Cmp}

def lex_flip(h, l):
  match h:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

law time_cmp_flip:
  for a: F.Time
  for b: F.Time
  {F.Time.cmp(a, b) == cmp.flip(F.Time.cmp(b, a)) : Cmp}

def time_cmp_flip(a, b):
  match a b:
    case F.Time{+as, +af} F.Time{+bs, +bf}:
      %Equal.sym(Cmp, U32.cmp(as, bs), cmp.flip(U32.cmp(bs, as)), u32_cmp_flip(as, bs)) :
        {F.Time.lex(_, U32.cmp(af, bf)) == cmp.flip(F.Time.lex(U32.cmp(bs, as), U32.cmp(bf, af))) : Cmp}
      %Equal.sym(Cmp, U32.cmp(af, bf), cmp.flip(U32.cmp(bf, af)), u32_cmp_flip(af, bf)) :
        {F.Time.lex(cmp.flip(U32.cmp(bs, as)), _) == cmp.flip(F.Time.lex(U32.cmp(bs, as), U32.cmp(bf, af))) : Cmp}
      lex_flip(U32.cmp(bs, as), U32.cmp(bf, af))

law lex_eq:
  for h: Cmp
  for -l: Cmp
  for -G: Type
  for e: {F.Time.lex(h, l) == EQ{} : Cmp}
  for k: {h == EQ{} : Cmp} -> {l == EQ{} : Cmp} -> G
  G

def lex_eq(h, l, G, e, k):
  match h:
    case LT{}:
      L.cmp.ne_eq(G, LT{}, e, Unit{})
    case EQ{}:
      k({==}, e)
    case GT{}:
      L.cmp.ne_eq(G, GT{}, e, Unit{})

law time_cong:
  for -as: U32
  for -af: U32
  for -bs: U32
  for -bf: U32
  for e1: {as == bs : U32}
  for e2: {af == bf : U32}
  {F.Time{as, af} == F.Time{bs, bf} : F.Time}

def time_cong(as, af, bs, bf, e1, e2):
  %e1 : {F.Time{as, af} == F.Time{_, bf} : F.Time}
  %e2 : {F.Time{as, af} == F.Time{as, _} : F.Time}
  {==}

law time_cmp_eq:
  for a: F.Time
  for b: F.Time
  for h: {F.Time.cmp(a, b) == EQ{} : Cmp}
  {a == b : F.Time}

def time_cmp_eq(a, b, h):
  match a b:
    case F.Time{+as, +af} F.Time{+bs, +bf}:
      lex_eq(U32.cmp(as, bs), U32.cmp(af, bf), {F.Time{as, af} == F.Time{bs, bf} : F.Time}, h,
        e1 => e2 => time_cong(as, af, bs, bf, u32_cmp_eq(as, bs, e1), u32_cmp_eq(af, bf, e2)))

law lex_lt:
  for h: Cmp
  for -l: Cmp
  for -G: Type
  for e: {F.Time.lex(h, l) == LT{} : Cmp}
  for k1: {h == LT{} : Cmp} -> G
  for k2: {h == EQ{} : Cmp} -> {l == LT{} : Cmp} -> G
  G

def lex_lt(h, l, G, e, k1, k2):
  match h:
    case LT{}:
      k1({==})
    case EQ{}:
      k2({==}, e)
    case GT{}:
      L.cmp.ne_lt(G, GT{}, e, Unit{})

law lex_of_lt:
  for -h: Cmp
  for -l: Cmp
  for e: {h == LT{} : Cmp}
  {F.Time.lex(h, l) == LT{} : Cmp}

def lex_of_lt(h, l, e):
  Equal.cong(Cmp, Cmp, z => F.Time.lex(z, l), h, LT{}, e)

law lex_of_eq:
  for -h: Cmp
  for -l: Cmp
  for e: {h == EQ{} : Cmp}
  for e2: {l == LT{} : Cmp}
  {F.Time.lex(h, l) == LT{} : Cmp}

def lex_of_eq(h, l, e, e2):
  %Equal.sym(Cmp, h, EQ{}, e) : {F.Time.lex(_, l) == LT{} : Cmp}
  e2

law time_cmp_lt_trans:
  for a: F.Time
  for b: F.Time
  for c: F.Time
  for h1: {F.Time.cmp(a, b) == LT{} : Cmp}
  for +h2: {F.Time.cmp(b, c) == LT{} : Cmp}
  {F.Time.cmp(a, c) == LT{} : Cmp}

def time_cmp_lt_trans(a, b, c, h1, h2):
  match a b c:
    case F.Time{+as, +af} F.Time{+bs, +bf} F.Time{+cs, +cf}:
      lex_lt(U32.cmp(as, bs), U32.cmp(af, bf), {F.Time.lex(U32.cmp(as, cs), U32.cmp(af, cf)) == LT{} : Cmp}, h1,
        +l1 => lex_lt(U32.cmp(bs, cs), U32.cmp(bf, cf), {F.Time.lex(U32.cmp(as, cs), U32.cmp(af, cf)) == LT{} : Cmp}, h2,
          l2 => lex_of_lt(U32.cmp(as, cs), U32.cmp(af, cf), u32_cmp_lt_trans(as, bs, cs, l1, l2)),
          e2 => m2 => lex_of_lt(U32.cmp(as, cs), U32.cmp(af, cf), u32_lt_eq_r(as, bs, cs, l1, u32_cmp_eq(bs, cs, e2)))),
        +e1 => +m1 => lex_lt(U32.cmp(bs, cs), U32.cmp(bf, cf), {F.Time.lex(U32.cmp(as, cs), U32.cmp(af, cf)) == LT{} : Cmp}, h2,
          l2 => lex_of_lt(U32.cmp(as, cs), U32.cmp(af, cf), u32_lt_eq_l(as, bs, cs, u32_cmp_eq(as, bs, e1), l2)),
          e2 => m2 => lex_of_eq(U32.cmp(as, cs), U32.cmp(af, cf),
            u32_cmp_eq_of(as, cs, Equal.trans(U32, as, bs, cs, u32_cmp_eq(as, bs, e1), u32_cmp_eq(bs, cs, e2))),
            u32_cmp_lt_trans(af, bf, cf, m1, m2))))

law time_cmp_refl:
  for +t: F.Time
  {F.Time.cmp(t, t) == EQ{} : Cmp}

def time_cmp_refl(t):
  cmp_flip_self(F.Time.cmp(t, t), time_cmp_flip(t, t))

# Time.lt
# -------

law is_lt_true:
  for c: Cmp
  for h: {Cmp.is_lt(c) == True{} : Bool}
  {c == LT{} : Cmp}

def is_lt_true(c, h):
  match c:
    case LT{}:
      {==}
    case EQ{}:
      L.clash({EQ{} == LT{} : Cmp}, h)
    case GT{}:
      L.clash({GT{} == LT{} : Cmp}, h)

law is_lt_of:
  for -c: Cmp
  for e: {c == LT{} : Cmp}
  {Cmp.is_lt(c) == True{} : Bool}

def is_lt_of(c, e):
  Equal.cong(Cmp, Bool, z => Cmp.is_lt(z), c, LT{}, e)

law is_lt_of_eq:
  for -c: Cmp
  for e: {c == EQ{} : Cmp}
  {Cmp.is_lt(c) == False{} : Bool}

def is_lt_of_eq(c, e):
  Equal.cong(Cmp, Bool, z => Cmp.is_lt(z), c, EQ{}, e)

law is_lt_of_gt:
  for -c: Cmp
  for e: {c == GT{} : Cmp}
  {Cmp.is_lt(c) == False{} : Bool}

def is_lt_of_gt(c, e):
  Equal.cong(Cmp, Bool, z => Cmp.is_lt(z), c, GT{}, e)

law lt_irrefl:
  for +t: F.Time
  {F.Time.lt(t, t) == False{} : Bool}

def lt_irrefl(t):
  is_lt_of_eq(F.Time.cmp(t, t), time_cmp_refl(t))

law lt_asym:
  for +a: F.Time
  for +b: F.Time
  for h: {F.Time.lt(a, b) == True{} : Bool}
  {F.Time.lt(b, a) == False{} : Bool}

def lt_asym(a, b, h):
  is_lt_of_gt(F.Time.cmp(b, a),
    Equal.trans(Cmp, F.Time.cmp(b, a), cmp.flip(F.Time.cmp(a, b)), GT{}, time_cmp_flip(b, a),
      Equal.cong(Cmp, Cmp, z => cmp.flip(z), F.Time.cmp(a, b), LT{}, is_lt_true(F.Time.cmp(a, b), h))))

law lt_trans:
  for +a: F.Time
  for +b: F.Time
  for +c: F.Time
  for h1: {F.Time.lt(a, b) == True{} : Bool}
  for h2: {F.Time.lt(b, c) == True{} : Bool}
  {F.Time.lt(a, c) == True{} : Bool}

def lt_trans(a, b, c, h1, h2):
  is_lt_of(F.Time.cmp(a, c),
    time_cmp_lt_trans(a, b, c, is_lt_true(F.Time.cmp(a, b), h1), is_lt_true(F.Time.cmp(b, c), h2)))

# Neither before the other: the same time.
law tri_cmp:
  for c: Cmp
  for d: Cmp
  for e: {c == cmp.flip(d) : Cmp}
  for h1: {Cmp.is_lt(c) == False{} : Bool}
  for h2: {Cmp.is_lt(d) == False{} : Bool}
  {c == EQ{} : Cmp}

def tri_cmp(c, d, e, h1, h2):
  match c:
    case LT{}:
      L.clash.flip({LT{} == EQ{} : Cmp}, h1)
    case EQ{}:
      {==}
    case GT{}:
      match d:
        case LT{}:
          L.clash.flip({GT{} == EQ{} : Cmp}, h2)
        case EQ{}:
          L.cmp.ne_eq({GT{} == EQ{} : Cmp}, GT{}, e, Unit{})
        case GT{}:
          L.cmp.ne_lt({GT{} == EQ{} : Cmp}, GT{}, e, Unit{})

law lt_total:
  for +a: F.Time
  for +b: F.Time
  for h1: {F.Time.lt(a, b) == False{} : Bool}
  for h2: {F.Time.lt(b, a) == False{} : Bool}
  {a == b : F.Time}

def lt_total(a, b, h1, h2):
  time_cmp_eq(a, b, tri_cmp(F.Time.cmp(a, b), F.Time.cmp(b, a), time_cmp_flip(a, b), h1, h2))

# a not after b, b before c: a before c.
law nlt_lt_trans:
  for +a: F.Time
  for +b: F.Time
  for +c: F.Time
  for +h1: {F.Time.lt(b, a) == False{} : Bool}
  for +h2: {F.Time.lt(b, c) == True{} : Bool}
  {F.Time.lt(a, c) == True{} : Bool}

def nlt_lt_trans(a, b, c, h1, h2):
  L.bool.cases(F.Time.lt(a, c), {F.Time.lt(a, c) == True{} : Bool},
    t => t,
    +hac => L.bool.cases(F.Time.lt(c, a), {F.Time.lt(a, c) == True{} : Bool},
      hca => L.both({F.Time.lt(a, c) == True{} : Bool}, F.Time.lt(b, a), lt_trans(b, c, a, h2, hca), h1),
      hca2 => L.both({F.Time.lt(a, c) == True{} : Bool}, F.Time.lt(b, a),
        Equal.trans(Bool, F.Time.lt(b, a), F.Time.lt(b, c), True{},
          Equal.cong(F.Time, Bool, z => F.Time.lt(b, z), a, c, lt_total(a, c, hac, hca2)), h2),
        h1)))

# a before b, b not after c: a before c.
law lt_nlt_trans:
  for +a: F.Time
  for +b: F.Time
  for +c: F.Time
  for +h1: {F.Time.lt(a, b) == True{} : Bool}
  for +h2: {F.Time.lt(c, b) == False{} : Bool}
  {F.Time.lt(a, c) == True{} : Bool}

def lt_nlt_trans(a, b, c, h1, h2):
  L.bool.cases(F.Time.lt(a, c), {F.Time.lt(a, c) == True{} : Bool},
    t => t,
    +hac => L.bool.cases(F.Time.lt(c, a), {F.Time.lt(a, c) == True{} : Bool},
      hca => L.both({F.Time.lt(a, c) == True{} : Bool}, F.Time.lt(c, b), lt_trans(c, a, b, hca, h1), h2),
      hca2 => L.both({F.Time.lt(a, c) == True{} : Bool}, F.Time.lt(c, b),
        Equal.trans(Bool, F.Time.lt(c, b), F.Time.lt(a, b), True{},
          Equal.cong(F.Time, Bool, z => F.Time.lt(z, b), c, a, Equal.sym(F.Time, a, c, lt_total(a, c, hac, hca2))), h1),
        h2)))

# Time.le
# -------

law le_refl:
  for +t: F.Time
  {F.Time.le(t, t) == True{} : Bool}

def le_refl(t):
  L.not.of(F.Time.lt(t, t), lt_irrefl(t))

law le_of_lt:
  for +a: F.Time
  for +b: F.Time
  for h: {F.Time.lt(a, b) == True{} : Bool}
  {F.Time.le(a, b) == True{} : Bool}

def le_of_lt(a, b, h):
  L.not.of(F.Time.lt(b, a), lt_asym(a, b, h))

law le_trans:
  for +a: F.Time
  for +b: F.Time
  for +c: F.Time
  for h1: {F.Time.le(a, b) == True{} : Bool}
  for +h2: {F.Time.le(b, c) == True{} : Bool}
  {F.Time.le(a, c) == True{} : Bool}

def le_trans(a, b, c, h1, h2):
  L.not.of(F.Time.lt(c, a),
    L.bool.cases(F.Time.lt(c, a), {F.Time.lt(c, a) == False{} : Bool},
      hca => L.both({F.Time.lt(c, a) == False{} : Bool}, F.Time.lt(c, b),
        lt_nlt_trans(c, a, b, hca, L.not.true(F.Time.lt(b, a), h1)), L.not.true(F.Time.lt(c, b), h2)),
      f => f))

# The next time
# -------------

# The word with every bit set: the largest.
def ones(n: Nat) -> Word(n):
  match n:
    case 0n:
      WNil{}
    case 1n+p:
      WCon{True{}, ones(p)}

law word_cmp_refl:
  for +n: Nat
  for +w: Word(n)
  {Word.cmp(n, w, w) == EQ{} : Cmp}

def word_cmp_refl(n, w):
  cmp_flip_self(Word.cmp(n, w, w), word_cmp_flip(n, w, w))

# No word is above ones: below it, or it.
law fin_ft_eq:
  for -c: Cmp
  for e: {c == EQ{} : Cmp}
  {Word.cmp.fin(False{}, True{}, c) == LT{} : Cmp}

def fin_ft_eq(c, e):
  %Equal.sym(Cmp, c, EQ{}, e) : {Word.cmp.fin(False{}, True{}, _) == LT{} : Cmp}
  {==}

law fin_tt_eq:
  for -c: Cmp
  for e: {c == EQ{} : Cmp}
  {Word.cmp.fin(True{}, True{}, c) == EQ{} : Cmp}

def fin_tt_eq(c, e):
  %Equal.sym(Cmp, c, EQ{}, e) : {Word.cmp.fin(True{}, True{}, _) == EQ{} : Cmp}
  {==}

law word_ones_cases:
  for +n: Nat
  for w: Word(n)
  for -G: Type
  for k1: {Word.cmp(n, w, ones(n)) == LT{} : Cmp} -> G
  for k2: {Word.cmp(n, w, ones(n)) == EQ{} : Cmp} -> G
  G

def word_ones_cases(n, w, G, k1, k2):
  match n:
    case 0n:
      k2({==})
    case 1n+p:
      match w:
        case WCon{False{}, +t}:
          k1(word_ones_cases(p, t, {Word.cmp.fin(False{}, True{}, Word.cmp(p, t, ones(p))) == LT{} : Cmp},
            l => fin_of_lt(False{}, True{}, Word.cmp(p, t, ones(p)), l),
            e => fin_ft_eq(Word.cmp(p, t, ones(p)), e)))
        case WCon{True{}, +t}:
          word_ones_cases(p, t, G,
            l => k1(fin_of_lt(True{}, True{}, Word.cmp(p, t, ones(p)), l)),
            e => k2(fin_tt_eq(Word.cmp(p, t, ones(p)), e)))

# A word below ones is below the next word.
law word_inc_lt:
  for +n: Nat
  for w: Word(n)
  for h: {Word.cmp(n, w, ones(n)) == LT{} : Cmp}
  {Word.cmp(n, w, Word.inc(n, w)) == LT{} : Cmp}

def word_inc_lt(n, w, h):
  match n:
    case 0n:
      L.cmp.ne_lt({EQ{} == LT{} : Cmp}, EQ{}, h, Unit{})
    case 1n+p:
      match w:
        case WCon{False{}, +t}:
          fin_ft_eq(Word.cmp(p, t, t), word_cmp_refl(p, t))
        case WCon{True{}, +t}:
          fin_lt(Word.cmp(p, t, ones(p)), True{}, True{},
            {Word.cmp.fin(True{}, False{}, Word.cmp(p, t, Word.inc(p, t))) == LT{} : Cmp}, h,
            l => fin_of_lt(True{}, False{}, Word.cmp(p, t, Word.inc(p, t)), word_inc_lt(p, t, l)),
            e => x => y => L.clash.flip({Word.cmp.fin(True{}, False{}, Word.cmp(p, t, Word.inc(p, t))) == LT{} : Cmp}, x))

law u32_ones_cases:
  for a: U32
  for -G: Type
  for k1: {U32.cmp(a, 4294967295) == LT{} : Cmp} -> G
  for k2: {U32.cmp(a, 4294967295) == EQ{} : Cmp} -> G
  G

def u32_ones_cases(a, G, k1, k2):
  match a:
    case U32{x}:
      word_ones_cases(32n, x, G, k1, k2)

law u32_inc_lt:
  for a: U32
  for h: {U32.cmp(a, 4294967295) == LT{} : Cmp}
  {U32.cmp(a, U32.inc(a)) == LT{} : Cmp}

def u32_inc_lt(a, h):
  match a:
    case U32{x}:
      word_inc_lt(32n, x, h)

law is_eq_of_lt:
  for -c: Cmp
  for e: {c == LT{} : Cmp}
  {Cmp.is_eq(c) == False{} : Bool}

def is_eq_of_lt(c, e):
  Equal.cong(Cmp, Bool, z => Cmp.is_eq(z), c, LT{}, e)

law is_eq_of_eq:
  for -c: Cmp
  for e: {c == EQ{} : Cmp}
  {Cmp.is_eq(c) == True{} : Bool}

def is_eq_of_eq(c, e):
  Equal.cong(Cmp, Bool, z => Cmp.is_eq(z), c, EQ{}, e)

law tick_lt.if:
  for top: Bool
  for +s: U32
  for +f: U32
  for +e: {U32.is_eq(f, 4294967295) == top : Bool}
  for h: {Cmp.is_lt(F.Time.lex(U32.cmp(s, 4294967295), U32.cmp(f, 4294967295))) == True{} : Bool}
  {F.Time.lt(F.Time{s, f}, F.Time.tick.if(top, s, f)) == True{} : Bool}

def tick_lt.if(top, s, f, e, h):
  match top:
    case True{}:
      lex_lt(U32.cmp(s, 4294967295), U32.cmp(f, 4294967295),
        {F.Time.lt(F.Time{s, f}, F.Time{U32.inc(s), 0}) == True{} : Bool},
        is_lt_true(F.Time.lex(U32.cmp(s, 4294967295), U32.cmp(f, 4294967295)), h),
        l => is_lt_of(F.Time.lex(U32.cmp(s, U32.inc(s)), U32.cmp(f, 0)),
          lex_of_lt(U32.cmp(s, U32.inc(s)), U32.cmp(f, 0), u32_inc_lt(s, l))),
        q => l2 => L.both({F.Time.lt(F.Time{s, f}, F.Time{U32.inc(s), 0}) == True{} : Bool},
          U32.is_eq(f, 4294967295), e, is_eq_of_lt(U32.cmp(f, 4294967295), l2)))
    case False{}:
      u32_ones_cases(f, {F.Time.lt(F.Time{s, f}, F.Time{s, U32.inc(f)}) == True{} : Bool},
        l => is_lt_of(F.Time.lex(U32.cmp(s, s), U32.cmp(f, U32.inc(f))),
          lex_of_eq(U32.cmp(s, s), U32.cmp(f, U32.inc(f)), u32_cmp_refl(s), u32_inc_lt(f, l))),
        q => L.both({F.Time.lt(F.Time{s, f}, F.Time{s, U32.inc(f)}) == True{} : Bool},
          U32.is_eq(f, 4294967295), is_eq_of_eq(U32.cmp(f, 4294967295), q), e))

law tick_lt:
  for t: F.Time
  for h: {F.Time.lt(t, F.Time.end()) == True{} : Bool}
  {F.Time.lt(t, F.Time.tick(t)) == True{} : Bool}

def tick_lt(t, h):
  match t:
    case F.Time{+s, +f}:
      tick_lt.if(U32.is_eq(f, 4294967295), s, f, {==}, h)

law after.pick.lt:
  for later: Bool
  for +last: F.Time
  for -now: F.Time
  for e: {F.Time.lt(last, now) == later : Bool}
  for h: {F.Time.lt(last, F.Time.end()) == True{} : Bool}
  {F.Time.lt(last, F.Time.after.pick(later, last, now)) == True{} : Bool}

def after.pick.lt(later, last, now, e, h):
  match later:
    case True{}:
      e
    case False{}:
      tick_lt(last, h)

law after_lt:
  for +last: F.Time
  for +now: F.Time
  for h: {F.Time.lt(last, F.Time.end()) == True{} : Bool}
  {F.Time.lt(last, F.Time.after(last, now)) == True{} : Bool}

def after_lt(last, now, h):
  after.pick.lt(F.Time.lt(last, now), last, now, {==}, h)

law after.pick.now:
  for later: Bool
  for -last: F.Time
  for -now: F.Time
  for h: {later == True{} : Bool}
  {F.Time.after.pick(later, last, now) == now : F.Time}

def after.pick.now(later, last, now, h):
  match later:
    case True{}:
      {==}
    case False{}:
      L.clash({F.Time.after.pick(False{}, last, now) == now : F.Time}, h)

law after_now:
  for +last: F.Time
  for +now: F.Time
  for h: {F.Time.lt(last, now) == True{} : Bool}
  {F.Time.after(last, now) == now : F.Time}

def after_now(last, now, h):
  after.pick.now(F.Time.lt(last, now), last, now, h)
