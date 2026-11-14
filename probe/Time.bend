import Base
import ../Frp.bend as F

# Time's arithmetic and conversions, run (F32 needs the compiled program),
# against values worked out by hand. Prints one line, which the flake's
# `time` check compares:
#   from_ms 1500 = 1.5 s; from_ms 999 = floor(999 * 2^32 / 1000) in 2^-32 s;
#   2.5 * 3.25 = 8.125; 3 * 0.75 = 2.25; 5 s + 100 less 2 s + 200;
#   the clock at 1 s 234.5 ms; to_f32 of 2.5 s; from_f32 2.75;
#   65536 * 65536 wraps to 0; 0.5 * 0.5; (1 - 2^-32)^2 rounded down.

def show(t: F.Time) -> String:
  match t:
    case F.Time{s, f}:
      U32.show(s) ++ "+" ++ U32.show(f)

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(String.join([
      show(F.Time.from_ms(1500)),
      show(F.Time.from_ms(999)),
      show(F.Time.mul(F.Time{2, 2147483648}, F.Time{3, 1073741824})),
      show(F.Time.scale(3, F.Time{0, 3221225472})),
      show(F.Time.sub(F.Time{5, 100}, F.Time{2, 200})),
      show(F.Time.from_clock(1, 234, 2147483648)),
      F32.show(F.Time.to_f32(F.Time{2, 2147483648})),
      show(F.Time.from_f32(2.75)),
      show(F.Time.mul(F.Time{65536, 0}, F.Time{65536, 0})),
      show(F.Time.mul(F.Time{0, 2147483648}, F.Time{0, 2147483648})),
      show(F.Time.mul(F.Time{0, 4294967295}, F.Time{0, 4294967295}))], " "))
