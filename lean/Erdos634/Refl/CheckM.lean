import Erdos634.Refl.Check

/-! Refl/CheckM.lean -- reflective checker with a FREE branch point (core Lean only, Int arithmetic).

    `Check.lean` branches at the lexicographically least point of the unfilled region and pays, at
    every node, a GLOBAL sweep certificate ("everything below `v` is covered").  Here a node may
    branch at ANY convex corner `v` of the unfilled region: the node supplies two rays `d`, `g` at `v`
    (`0 < cross d g`) and a LOCAL certificate that, inside a small box around `v`, every target point
    outside the cone spanned by `d`, `g` lies in a placed tile.  The six placements, the kills and the
    recursion are those of `Check.lean`.

    Soundness: `SoundM*.lean`, through `PlacementCompleteness.placement_completeness_cone`. -/

namespace Refl

structure NodeM where
  v : Pt
  d : Pt          -- unit ray: the new tile has an edge along `d` and lies counter-clockwise of it
  g : Pt          -- second ray of the cone (any positive multiple)
  eN : Int        -- box half-width eN/eD (in the rational coordinates X, Y)
  eD : Int
  t1 : Bsp        -- box ∧ target ∧ (strictly clockwise of d)         ⊆ placed tiles
  t2 : Bsp        -- box ∧ target ∧ (on/left of d) ∧ (strictly left of g) ⊆ placed tiles
  tauN : Int
  tauD : Int
  fedges : List Nat
  kills : List Kill
  children : List NodeM

/-- the line through `v` with direction `d`: positive on the left (counter-clockwise side) of `d` -/
def rayL (v d : Pt) : Lin := ⟨-(d.y * v.w), d.x * v.w, d.y * v.x - d.x * v.y⟩

/-- the closed box `|X - vX| ≤ eN/eD`, `|Y - vY| ≤ eN/eD` -/
def boxL (v : Pt) (eN eD : Int) : List Lin :=
  [⟨v.w * eD, 0, eN * v.w - v.x * eD⟩, ⟨-(v.w * eD), 0, eN * v.w + v.x * eD⟩,
   ⟨0, v.w * eD, eN * v.w - v.y * eD⟩, ⟨0, -(v.w * eD), eN * v.w + v.y * eD⟩]

def tgtLinsM (I : Inst) : List Lin := (List.range 3).map (fun i => I.tgt.edge i)

def consM1 (I : Inst) (n : NodeM) : List (Lin × Bool) :=
  (tgtLinsM I ++ boxL n.v n.eN n.eD).map (fun l => (l, false)) ++ [((rayL n.v n.d).neg, true)]

def consM2 (I : Inst) (n : NodeM) : List (Lin × Bool) :=
  (tgtLinsM I ++ boxL n.v n.eN n.eD).map (fun l => (l, false)) ++
    [(rayL n.v n.d, false), (rayL n.v n.g, true)]

def nodeLocalOkM (I : Inst) (cfg : List Tri) (n : NodeM) : Bool :=
  let v := n.v
  let d := n.d
  let r1 := n.t1.check cfg [] [] false (consM1 I n) []
  let r2 := n.t2.check cfg [] [] false (consM2 I n) []
  let tgtQ := (tgtLinsM I).all (fun l => okPos (quad I v d l) n.tauN n.tauD)
  let tileQ := (cfg.zip n.fedges).all (fun (T, e) => okNeg (quad I v d (T.edge e)) n.tauN n.tauD)
  decide (0 < v.w) && decide (0 < d.w) && (d.x * d.x + I.Dn * d.y * d.y == d.w * d.w) &&
  decide (0 < n.tauN) && decide (0 < n.tauD) && (n.fedges.length == cfg.length) &&
  decide (0 < n.g.w) && decide (0 < n.eN) && decide (0 < n.eD) &&
  decide (0 < d.x * n.g.y - d.y * n.g.x) &&
  r1 && r2 && tgtQ && tileQ

/-- `killsCheck` of `Check.lean`, for `NodeM` children -/
def killsCheckM (I : Inst) (cfg : List Tri) (v d : Pt) :
    List Kill → List Place → List NodeM → (NodeM → List Tri → Bool) → Bool
  | [], [], [], _ => true
  | k :: ks, p :: ps, ch, rec =>
    let tri := placeTri I v d p
    match k with
    | .child =>
      match ch with
      | [] => false
      | c :: cs => rec c (cfg ++ [tri]) && killsCheckM I cfg v d ks ps cs rec
    | _ => killOk I cfg tri (fun _ => false) k && killsCheckM I cfg v d ks ps ch rec
  | _, _, _, _ => false

def ptEqM (p q : Pt) : Bool := p.x == q.x && p.y == q.y && p.w == q.w
def triEqM (s t : Tri) : Bool := ptEqM s.a t.a && ptEqM s.b t.b && ptEqM s.c t.c

/-- every tile of `c` occurs (literally) in `cfg` -/
def cfgSub (c cfg : List Tri) : Bool := c.all (fun t => cfg.any (fun u => triEqM t u))

/-- Chunked checker.  A *stub* node (`tauN = 0`; real nodes have `0 < tauN`) is accepted iff some
    `known` configuration is a SUBSET of the current one (a refuted configuration stays refuted when
    tiles are added); each known configuration is certified separately. -/
def checkNodeM (I : Inst) (known : List (List Tri)) : Nat → List Tri → NodeM → Bool
  | 0, _, _ => false
  | fuel + 1, cfg, n =>
    if n.tauN == 0 then known.any (fun c => cfgSub c cfg)
    else nodeLocalOkM I cfg n &&
      killsCheckM I cfg n.v n.d n.kills I.pl (n.children) (fun c cfg' => checkNodeM I known fuel cfg' c)

def _root_.Inst.checkAllM (I : Inst) (known : List (List Tri)) (fuel : Nat) (n : NodeM) : Bool :=
  I.ok && checkNodeM I known fuel [] n

def stubM : NodeM :=
  ⟨pt 0 0 1, pt 0 0 1, pt 0 0 1, 1, 1, Bsp.inf [], Bsp.inf [], 0, 1, [], [], []⟩

end Refl
