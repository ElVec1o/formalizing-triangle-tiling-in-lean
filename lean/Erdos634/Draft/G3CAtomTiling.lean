-- G3CAtomTiling.lean — exact kernel verification of a 48-tile certificate (Erdos #634, atom A_4 at (e,f)=(1,2)).
-- UNAUDITED. G3C (room FINISH, seat HILBERT).  The tile (2,3,4) tiles the isosceles ATOM A_4 = (legs 24, base 12;
-- angles (alpha+beta, alpha+beta, alpha)) with 48 = b m^2 (b=3, m=4) congruent copies.  Found by float search
-- (private working notes, not included), snapped EXACTLY to Z[sqrt15]/8, verified by (private working notes, not included) `exactq` (independent re-implementation of (private working notes, not included)).
-- Scaled by 8 into Z[sqrt15]: (C1) squared side multiset {256,576,1024}; (C2) CCW + vertices in closed target;
-- (C3) explicit separating edge-line per pair (1128 pairs); (C4) signed 2-areas sum to the target's. No imports, no axioms.
namespace G3CAtomTiling
abbrev Z15 := Int × Int
abbrev Pt := Int × Int × Int × Int
def zmul (u v : Z15) : Z15 := (u.1*v.1 + 15*u.2*v.2, u.1*v.2 + u.2*v.1)
def zsub (u v : Z15) : Z15 := (u.1 - v.1, u.2 - v.2)
def zadd (u v : Z15) : Z15 := (u.1 + v.1, u.2 + v.2)
def znonneg (z : Z15) : Bool :=
  if 0 <= z.1 then (if 0 <= z.2 then true else 15*z.2*z.2 <= z.1*z.1)
  else (if z.2 < 0 then false else z.1*z.1 <= 15*z.2*z.2)
def znonpos (z : Z15) : Bool := znonneg (-z.1, -z.2)
def zpos (z : Z15) : Bool := !(znonpos z)
def px (p : Pt) : Z15 := (p.1, p.2.1)
def py (p : Pt) : Z15 := (p.2.2.1, p.2.2.2)
def cross (o a b : Pt) : Z15 :=
  zsub (zmul (zsub (px a) (px o)) (zsub (py b) (py o))) (zmul (zsub (py a) (py o)) (zsub (px b) (px o)))
def dist2 (p q : Pt) : Z15 :=
  zadd (zmul (zsub (px q) (px p)) (zsub (px q) (px p))) (zmul (zsub (py q) (py p)) (zsub (py q) (py p)))
abbrev Tri := Pt × Pt × Pt
def t1 (t : Tri) : Pt := t.1
def t2 (t : Tri) : Pt := t.2.1
def t3 (t : Tri) : Pt := t.2.2
def congOK (t : Tri) : Bool :=
  let d1 := dist2 (t1 t) (t2 t); let d2 := dist2 (t2 t) (t3 t); let d3 := dist2 (t3 t) (t1 t)
  let s : List Z15 := [d1, d2, d3]
  s.contains ((256:Int),(0:Int)) && s.contains ((576:Int),(0:Int)) && s.contains ((1024:Int),(0:Int))
  && d1.2 == 0 && d2.2 == 0 && d3.2 == 0 && (d1.1 + d2.1 + d3.1 == 1856)
def target : Tri := ((0,0,0,0), (96,0,0,0), (48,0,0,48))
def insideOK (t : Tri) : Bool :=
  zpos (cross (t1 t) (t2 t) (t3 t)) &&
  [t1 t, t2 t, t3 t].all (fun v =>
    znonneg (cross (t1 target) (t2 target) v) && znonneg (cross (t2 target) (t3 target) v) &&
    znonneg (cross (t3 target) (t1 target) v))
def sepBy (P Q : Pt) (A B : Tri) : Bool :=
  let sA := [t1 A, t2 A, t3 A].map (fun v => cross P Q v)
  let sB := [t1 B, t2 B, t3 B].map (fun v => cross P Q v)
  (sA.all znonneg && sB.all znonpos) || (sA.all znonpos && sB.all znonneg)
def edgeOf (t : Tri) (e : Nat) : Pt × Pt :=
  if e == 0 then (t1 t, t2 t) else if e == 1 then (t2 t, t3 t) else (t3 t, t1 t)
def area2 (t : Tri) : Z15 := cross (t1 t) (t2 t) (t3 t)
def tiles : List Tri := [
  ((0,0,0,0), (32,0,0,0), (21,0,0,3)),
  ((0,0,0,0), (14,0,0,2), (8,0,0,8)),
  ((32,0,0,0), (64,0,0,0), (53,0,0,3)),
  ((32,0,0,0), (53,0,0,3), (21,0,0,3)),
  ((64,0,0,0), (96,0,0,0), (85,0,0,3)),
  ((64,0,0,0), (85,0,0,3), (53,0,0,3)),
  ((96,0,0,0), (90,0,0,6), (74,0,0,6)),
  ((14,0,0,2), (28,0,0,4), (22,0,0,10)),
  ((14,0,0,2), (22,0,0,10), (8,0,0,8)),
  ((21,0,0,3), (53,0,0,3), (42,0,0,6)),
  ((53,0,0,3), (85,0,0,3), (74,0,0,6)),
  ((53,0,0,3), (74,0,0,6), (42,0,0,6)),
  ((28,0,0,4), (42,0,0,6), (36,0,0,12)),
  ((28,0,0,4), (36,0,0,12), (22,0,0,10)),
  ((42,0,0,6), (58,0,0,6), (36,0,0,12)),
  ((58,0,0,6), (90,0,0,6), (79,0,0,9)),
  ((58,0,0,6), (79,0,0,9), (47,0,0,9)),
  ((90,0,0,6), (84,0,0,12), (68,0,0,12)),
  ((8,0,0,8), (22,0,0,10), (16,0,0,16)),
  ((47,0,0,9), (79,0,0,9), (68,0,0,12)),
  ((47,0,0,9), (68,0,0,12), (36,0,0,12)),
  ((22,0,0,10), (36,0,0,12), (30,0,0,18)),
  ((22,0,0,10), (30,0,0,18), (16,0,0,16)),
  ((36,0,0,12), (60,0,0,12), (32,0,0,16)),
  ((60,0,0,12), (84,0,0,12), (56,0,0,16)),
  ((60,0,0,12), (56,0,0,16), (32,0,0,16)),
  ((84,0,0,12), (80,0,0,16), (56,0,0,16)),
  ((16,0,0,16), (30,0,0,18), (24,0,0,24)),
  ((32,0,0,16), (56,0,0,16), (28,0,0,20)),
  ((56,0,0,16), (80,0,0,16), (52,0,0,20)),
  ((56,0,0,16), (52,0,0,20), (28,0,0,20)),
  ((80,0,0,16), (76,0,0,20), (52,0,0,20)),
  ((28,0,0,20), (52,0,0,20), (24,0,0,24)),
  ((52,0,0,20), (76,0,0,20), (48,0,0,24)),
  ((52,0,0,20), (48,0,0,24), (24,0,0,24)),
  ((76,0,0,20), (68,0,0,28), (62,0,0,22)),
  ((62,0,0,22), (68,0,0,28), (54,0,0,30)),
  ((62,0,0,22), (54,0,0,30), (48,0,0,24)),
  ((24,0,0,24), (48,0,0,24), (52,0,0,28)),
  ((24,0,0,24), (38,0,0,26), (32,0,0,32)),
  ((38,0,0,26), (52,0,0,28), (46,0,0,34)),
  ((38,0,0,26), (46,0,0,34), (32,0,0,32)),
  ((52,0,0,28), (60,0,0,36), (46,0,0,34)),
  ((68,0,0,28), (60,0,0,36), (54,0,0,30)),
  ((32,0,0,32), (46,0,0,34), (40,0,0,40)),
  ((46,0,0,34), (60,0,0,36), (54,0,0,42)),
  ((46,0,0,34), (54,0,0,42), (40,0,0,40)),
  ((40,0,0,40), (54,0,0,42), (48,0,0,48))
]
def wit : List (Bool × Nat) := [
  (true,2), (true,1), (true,1), (true,1), (true,1), (true,1), (true,2), (true,2), (true,1), (true,1), (true,1), (true,1),
  (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1),
  (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1),
  (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,0),
  (true,0), (true,0), (true,0), (true,0), (true,1), (true,1), (true,0), (true,0), (true,0), (true,1), (true,1), (true,1),
  (true,0), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1),
  (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1),
  (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,2), (true,1), (true,1),
  (true,1), (true,2), (true,2), (true,2), (true,1), (true,1), (true,2), (true,2), (true,1), (true,1), (true,1), (true,1),
  (true,2), (true,1), (true,1), (true,2), (true,2), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1),
  (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1),
  (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,0), (true,0), (true,0), (false,0), (false,0), (true,1),
  (true,0), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1),
  (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1),
  (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1),
  (true,1), (true,1), (true,2), (true,1), (true,2), (true,2), (true,2), (true,2), (true,2), (true,2), (true,2), (true,2),
  (true,2), (true,2), (true,1), (true,2), (true,2), (true,2), (true,2), (true,2), (true,2), (true,1), (true,2), (true,1),
  (true,2), (true,2), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1),
  (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (false,2), (true,2), (true,2),
  (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1),
  (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1),
  (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1),
  (true,1), (true,1), (true,1), (true,2), (true,2), (true,2), (true,2), (true,2), (true,2), (true,2), (true,1), (true,1),
  (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1),
  (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1),
  (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,2), (true,0), (true,0), (true,0),
  (true,1), (true,1), (true,1), (true,0), (true,1), (true,1), (true,2), (true,1), (true,1), (true,1), (true,1), (true,1),
  (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1),
  (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1),
  (true,0), (true,0), (true,0), (true,0), (true,0), (true,0), (true,0), (true,0), (true,0), (true,1), (true,0), (true,0),
  (true,0), (true,1), (true,0), (true,0), (true,0), (true,0), (true,1), (true,1), (true,0), (true,1), (true,0), (true,1),
  (true,0), (true,1), (true,0), (true,0), (true,0), (true,1), (true,1), (true,0), (true,1), (true,0), (true,0), (true,1),
  (true,0), (true,1), (true,1), (true,1), (true,1), (true,2), (true,2), (true,1), (true,1), (true,1), (true,1), (true,2),
  (true,1), (true,1), (true,2), (true,2), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1),
  (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1),
  (true,1), (true,1), (true,1), (true,1), (true,1), (true,2), (true,2), (true,2), (true,2), (false,0), (true,2), (true,1),
  (true,2), (true,2), (true,2), (true,2), (true,2), (true,2), (true,1), (true,2), (true,1), (true,2), (true,2), (true,1),
  (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1),
  (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (false,0), (false,0), (true,1), (true,1), (true,1), (true,1),
  (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1),
  (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1),
  (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,2), (true,1), (true,0), (true,1), (true,1), (true,2),
  (true,1), (true,1), (true,2), (true,2), (true,1), (true,1), (true,1), (true,1), (true,2), (true,1), (true,1), (true,1),
  (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1),
  (true,1), (true,1), (true,1), (true,1), (true,1), (true,0), (true,0), (true,0), (true,0), (true,1), (true,0), (true,0),
  (true,1), (true,1), (false,0), (true,0), (false,2), (true,0), (true,1), (true,1), (true,0), (true,1), (true,0), (true,1),
  (true,0), (true,1), (true,0), (true,0), (true,0), (true,1), (true,1), (true,1), (true,1), (true,1), (true,0), (true,1),
  (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,2), (true,1), (true,1), (true,2), (true,2), (true,1),
  (true,1), (true,1), (true,1), (true,2), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1),
  (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1),
  (true,2), (true,1), (true,2), (true,2), (true,2), (true,2), (true,2), (true,2), (true,2), (true,2), (true,1), (true,2),
  (true,2), (true,1), (true,2), (true,1), (true,2), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1),
  (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (false,2), (true,2), (true,1), (true,1),
  (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1),
  (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1),
  (true,1), (true,1), (true,1), (true,2), (true,2), (true,2), (true,2), (true,2), (true,1), (true,1), (true,1), (true,1),
  (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1),
  (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,0), (true,0), (true,1),
  (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1),
  (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1),
  (true,1), (true,1), (true,2), (true,2), (true,2), (true,2), (false,0), (true,2), (true,1), (true,2), (true,2), (true,1),
  (true,2), (true,1), (true,2), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1),
  (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (false,0), (false,0), (true,1), (true,1), (true,1), (true,1),
  (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1),
  (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,2), (true,1), (true,1),
  (true,1), (true,1), (true,2), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1),
  (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,0),
  (true,0), (true,0), (true,0), (true,1), (false,2), (true,0), (false,2), (true,0), (false,0), (true,0), (false,2), (true,0),
  (true,0), (true,0), (true,1), (true,1), (true,0), (true,1), (true,0), (true,0), (true,1), (true,0), (true,1), (true,1),
  (true,1), (true,1), (true,1), (true,2), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1),
  (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1),
  (true,2), (true,1), (true,2), (true,2), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1),
  (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,0),
  (true,1), (true,1), (true,0), (true,1), (true,0), (true,1), (true,0), (true,1), (true,0), (true,0), (true,0), (true,1),
  (true,1), (true,1), (true,1), (true,0), (true,0), (true,1), (true,0), (true,0), (true,0), (true,1), (true,1), (true,1),
  (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1),
  (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,0), (true,1), (true,0), (true,1), (true,1),
  (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1),
  (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1),
  (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,2), (true,1), (true,2),
  (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1),
  (true,1), (true,1), (true,1), (true,0), (true,1), (true,0), (true,1), (true,0), (true,0), (true,0), (true,1), (true,1),
  (true,1), (true,1), (true,0), (true,0), (true,1), (true,0), (true,0), (true,0), (true,1), (true,1), (true,1), (true,1),
  (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1),
  (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1),
  (true,1), (true,1), (true,1), (true,2), (true,1), (true,1), (true,1), (false,0), (true,2), (true,1), (true,1), (true,1),
  (true,1), (true,1), (true,1), (true,1), (true,1), (true,0), (true,0), (true,0), (true,1), (true,1), (true,1), (true,1),
  (true,0), (true,0), (true,1), (true,0), (true,0), (true,0), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1),
  (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,2), (true,2), (true,2), (true,2), (true,2), (false,0),
  (true,1), (true,2), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,0), (true,1),
  (true,1), (true,1), (true,1), (true,2), (true,2), (true,2), (true,2), (true,1), (true,2), (true,2), (true,2), (true,2),
  (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,2), (true,1), (true,1), (true,2),
  (true,1), (true,1), (true,1), (true,0), (true,0), (true,1), (true,0), (true,1), (true,1), (true,0), (true,1), (true,1),
  (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,1), (true,2), (true,2), (true,1)
]
def pairSep (A B : Tri) (w : Bool × Nat) : Bool :=
  let pq := edgeOf (if w.1 then A else B) w.2
  sepBy pq.1 pq.2 A B
def checkPairs : List Tri → List (Bool × Nat) → Bool
  | [], ws => ws.isEmpty
  | t :: rest, ws =>
      let n := rest.length
      (ws.take n).length == n
      && (List.zip rest (ws.take n)).all (fun (u, w) => pairSep t u w)
      && checkPairs rest (ws.drop n)
def zsum (l : List Z15) : Z15 := l.foldl zadd ((0:Int),(0:Int))
def checkAll : Bool :=
  tiles.length == 48 && tiles.all congOK && tiles.all insideOK
  && checkPairs tiles wit && zsum (tiles.map area2) == area2 target
set_option maxRecDepth 12672 in
set_option maxHeartbeats 0 in
theorem tiling48_certificate : checkAll = true := by decide
#print axioms tiling48_certificate
end G3CAtomTiling