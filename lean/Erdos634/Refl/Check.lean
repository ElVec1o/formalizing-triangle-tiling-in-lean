/-! Reflective checker PROTOTYPE (core Lean only, Int arithmetic, no Real, no Mathlib).
    Measures kernel cost; soundness theorems are NOT proved here (see DESIGN_reflective_checker.md). -/

structure Pt where
  x : Int
  y : Int
  w : Int

structure Tri where
  a : Pt
  b : Pt
  c : Pt

structure Lin where
  α : Int
  β : Int
  γ : Int

def pt (x y w : Int) : Pt := ⟨x, y, w⟩

/-- 3x3 determinant of homogeneous points; sign = sign of the rational edge functional ef(a,b,c)
    when all weights are positive. -/
def det3 (a b c : Pt) : Int :=
  a.x * (b.y * c.w - b.w * c.y) - a.y * (b.x * c.w - b.w * c.x) + a.w * (b.x * c.y - b.y * c.x)

def Tri.vert (t : Tri) : Nat → Pt
  | 0 => t.a
  | 1 => t.b
  | _ => t.c

def Tri.ok (t : Tri) : Bool := decide (0 < t.a.w) && decide (0 < t.b.w) && decide (0 < t.c.w) &&
  decide (0 < det3 t.a t.b t.c)

def linOf (a b : Pt) : Lin :=
  ⟨a.y * b.w - a.w * b.y, a.w * b.x - a.x * b.w, a.x * b.y - a.y * b.x⟩

def Lin.neg (l : Lin) : Lin := ⟨-l.α, -l.β, -l.γ⟩

def Tri.edge (t : Tri) (i : Nat) : Lin := linOf (t.vert (i % 3)) (t.vert ((i + 1) % 3))

/-- Farkas certificate for infeasibility of `∧ (α X + β Y + γ ≥ 0 | > 0)`: the nonnegative
    combination has zero X,Y-coefficients and a negative constant (or zero with a strict member). -/
def fk : List (Lin × Bool) → List Nat → Int → Int → Int → Bool → Bool
  | (l, s) :: cs, m :: ms, a, b, g, st =>
    fk cs ms (a + (m : Int) * l.α) (b + (m : Int) * l.β) (g + (m : Int) * l.γ) (st || (s && m != 0))
  | _, _, a, b, g, st => a == 0 && b == 0 && (decide (g < 0) || (g == 0 && st))

def farkas (cs : List (Lin × Bool)) (ms : List Nat) : Bool := fk cs ms 0 0 0 false

inductive Bsp
  | inf (ms : List Nat)
  | tile (m : Nat) (f0 f1 f2 : List Nat)
  | cell (ms : List Nat)
  | split (m i : Nat) (l r : Bsp)

def Bsp.check (cfg : List Tri) (closedBase : List Lin) (extra : List (Lin × Bool))
    (allowCell : Bool) : List (Lin × Bool) → List Lin → Bsp → Bool
  | cons, _, .inf ms => farkas cons ms
  | cons, _, .tile m f0 f1 f2 =>
    match cfg[m]? with
    | none => false
    | some t =>
      farkas (cons ++ [((t.edge 0).neg, true)]) f0 &&
      farkas (cons ++ [((t.edge 1).neg, true)]) f1 &&
      farkas (cons ++ [((t.edge 2).neg, true)]) f2
  | _, path, .cell ms =>
    allowCell && farkas ((closedBase ++ path).map (fun l => (l, false)) ++ extra) ms
  | cons, path, .split m i l r =>
    match cfg[m]? with
    | none => false
    | some t =>
      let e := t.edge i
      Bsp.check cfg closedBase extra allowCell (cons ++ [(e, false)]) (path ++ [e]) l &&
      Bsp.check cfg closedBase extra allowCell (cons ++ [(e.neg, true)]) (path ++ [e.neg]) r

inductive Kill
  | esc (q : Bool) (e : Nat)
  | ovl (m : Nat) (w : Pt)
  | child

structure Place where
  l1 : Int
  pn : Int
  pd : Int
  qn : Int
  qd : Int

structure Inst where
  Dn : Int
  tgt : Tri
  sides : Int × Int × Int
  pl : List Place    -- six placements

/-- placement data are consistent: p = (l1^2+l2^2-l3^2)/(2 l1), Dn q^2 = l2^2 - p^2 -/
def placeOk (I : Inst) (l1 l2 l3 : Int) (p : Place) : Bool :=
  decide (0 < p.l1) && decide (0 < p.pd) && decide (0 < p.qd) && decide (0 < p.qn) &&
  (p.l1 == l1) &&
  (2 * l1 * p.pn == (l1 * l1 + l2 * l2 - l3 * l3) * p.pd) &&
  (I.Dn * p.qn * p.qn * p.pd * p.pd == (l2 * l2 * p.pd * p.pd - p.pn * p.pn) * (p.qd * p.qd))

def Inst.ok (I : Inst) : Bool :=
  let (a, b, c) := I.sides
  I.pl.length == 6 && I.tgt.ok && decide (0 < I.Dn) &&
  (match I.pl with
   | [p1, p2, p3, p4, p5, p6] =>
     placeOk I a c b p1 && placeOk I c a b p2 && placeOk I a b c p3 &&
     placeOk I b a c p4 && placeOk I c b a p5 && placeOk I b c a p6
   | _ => false)

/-- placed tile (v, P, Q) -/
def placeTri (I : Inst) (v d : Pt) (p : Place) : Tri :=
  let P : Pt := ⟨v.x * d.w + p.l1 * d.x * v.w, v.y * d.w + p.l1 * d.y * v.w, v.w * d.w⟩
  let Q : Pt := ⟨v.x * d.w * p.pd * p.qd + p.pn * d.x * v.w * p.qd - I.Dn * p.qn * d.y * v.w * p.pd,
                 v.y * d.w * p.pd * p.qd + p.pn * d.y * v.w * p.qd + p.qn * d.x * v.w * p.pd,
                 v.w * d.w * p.pd * p.qd⟩
  ⟨v, P, Q⟩

structure Blocked where
  base : Bool
  m : Nat
  W : Tri

structure Node where
  v : Pt
  d : Pt
  t1 : Bsp
  t2 : Bsp
  tauN : Int
  tauD : Int
  fedges : List Nat      -- per cfg tile: edge index that is negative along the curve
  hb : Blocked
  kills : List Kill
  children : List Node

def vsub (p q : Pt) : Int × Int := (p.x * q.w - q.x * p.w, p.y * q.w - q.y * p.w)
def vcross (u v : Int × Int) : Int := u.1 * v.2 - u.2 * v.1

/-- quadratic coefficients (c0, ct, cu) of the edge form along the curve, times wv*wd -/
def quad (I : Inst) (v d : Pt) (l : Lin) : Int × Int × Int :=
  ((l.α * v.x + l.β * v.y + l.γ * v.w) * d.w,
   (l.α * d.x + l.β * d.y) * v.w,
   (-(l.α * I.Dn * d.y) + l.β * d.x) * v.w)

def okPos (c : Int × Int × Int) (tn td : Int) : Bool :=
  let (c0, c1, c2) := c
  if 0 < c0 then decide (0 < c0 * td * td + min c1 0 * tn * td + min c2 0 * tn * tn)
  else if c0 == 0 then
    (if 0 < c1 then decide (0 < c1 * td + min c2 0 * tn) else
      if c1 == 0 then decide (0 ≤ c2) else false)
  else false

def okNeg (c : Int × Int × Int) (tn td : Int) : Bool :=
  let (c0, c1, c2) := c
  if c0 < 0 then decide (c0 * td * td + max c1 0 * tn * td + max c2 0 * tn * tn < 0)
  else if c0 == 0 then
    (if c1 < 0 then decide (c1 * td + max c2 0 * tn < 0) else
      if c1 == 0 then decide (c2 < 0) else false)
  else false

def eqvPt (p q : Pt) : Bool := p.x * q.w == q.x * p.w && p.y * q.w == q.y * p.w

def inClosed (t : Tri) (p : Pt) : Bool :=
  decide (0 ≤ det3 t.a t.b p) && decide (0 ≤ det3 t.b t.c p) && decide (0 ≤ det3 t.c t.a p)

def inOpen (t : Tri) (p : Pt) : Bool :=
  decide (0 < det3 t.a t.b p) && decide (0 < det3 t.b t.c p) && decide (0 < det3 t.c t.a p)

def blockedOk (I : Inst) (cfg : List Tri) (v d : Pt) (b : Blocked) : Bool :=
  if b.base then (v.y == 0 && d.y == 0 && decide (0 < d.x) && d.x == d.w)
  else
    match cfg[b.m]? with
    | none => false
    | some T =>
      let W := b.W
      let e1 := vsub W.b W.a
      let e2 := vsub W.c W.a
      let dd : Int × Int := (d.x, d.y)
      let nn : Int × Int := (-(I.Dn * d.y), d.x)
      eqvPt W.a v && decide (0 < det3 W.a W.b W.c) && W.ok &&
      inClosed T W.a && inClosed T W.b && inClosed T W.c &&
      (decide (0 < vcross dd e2) || (vcross dd e2 == 0 && decide (vcross nn e2 < 0))) &&
      (decide (0 < vcross e1 dd) || (vcross e1 dd == 0 && decide (vcross e1 nn < 0)))

def killOk (I : Inst) (cfg : List Tri) (tri : Tri) (rec : List Tri → Bool) : Kill → Bool
  | .esc q e =>
    let pt := if q then tri.c else tri.b
    decide (det3 (I.tgt.vert (e % 3)) (I.tgt.vert ((e + 1) % 3)) pt < 0)
  | .ovl m w =>
    match cfg[m]? with
    | none => false
    | some U => decide (0 < w.w) && inOpen tri w && inOpen U w
  | .child => rec (cfg ++ [tri])

def killsCheck (I : Inst) (cfg : List Tri) (v d : Pt) :
    List Kill → List Place → List Node → (Node → List Tri → Bool) → Bool
  | [], [], [], _ => true
  | k :: ks, p :: ps, ch, rec =>
    let tri := placeTri I v d p
    match k with
    | .child =>
      match ch with
      | [] => false
      | c :: cs => rec c (cfg ++ [tri]) && killsCheck I cfg v d ks ps cs rec
    | _ => killOk I cfg tri (fun _ => false) k && killsCheck I cfg v d ks ps ch rec
  | _, _, _, _ => false

def nodeLocalOk (I : Inst) (cfg : List Tri) (n : Node) : Bool :=
  let v := n.v
  let d := n.d
  let tgtLins := (List.range 3).map (fun i => I.tgt.edge i)
  -- region (i): target ∧ Y < yv covered
  let ylt : Lin := ⟨0, -v.w, v.y⟩
  let ygeL : Lin := ⟨0, v.w, -v.y⟩
  let xltL : Lin := ⟨-v.w, 0, v.x⟩
  let r1 := n.t1.check cfg [] [] false (tgtLins.map (fun l => (l, false)) ++ [(ylt, true)]) []
  let r2 := n.t2.check cfg (tgtLins ++ [ygeL]) [(ylt, false), (xltL, true)] true
      (tgtLins.map (fun l => (l, false)) ++ [(ygeL, false), (xltL, true)]) []
  -- hfree
  let tgtQ := tgtLins.all (fun l => okPos (quad I v d l) n.tauN n.tauD)
  let tileQ := (cfg.zip n.fedges).all (fun (T, e) => okNeg (quad I v d (T.edge e)) n.tauN n.tauD)
  decide (0 < v.w) && decide (0 < d.w) && (d.x * d.x + I.Dn * d.y * d.y == d.w * d.w) &&
  decide (0 < n.tauN) && decide (0 < n.tauD) && (n.fedges.length == cfg.length) &&
  r1 && r2 && tgtQ && tileQ && blockedOk I cfg v d n.hb

def checkNode (I : Inst) : Nat → List Tri → Node → Bool
  | 0, _, _ => false
  | fuel + 1, cfg, n =>
    nodeLocalOk I cfg n && killsCheck I cfg n.v n.d n.kills I.pl (n.children) (fun c cfg' => checkNode I fuel cfg' c)

def Inst.checkAll (I : Inst) (fuel : Nat) (n : Node) : Bool := I.ok && checkNode I fuel [] n
