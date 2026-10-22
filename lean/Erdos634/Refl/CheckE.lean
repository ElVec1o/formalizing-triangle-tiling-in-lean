import Erdos634.Refl.Check

/-! Refl/CheckE.lean -- the reflective checker of `Check.lean`, with one extra `blocked` kind: the clockwise wedge at `v`
    is outside the target because `d` runs along a target edge (positively) and `v` lies on that edge.  Needed for a
    target with a non-horizontal edge whose base corner is reached by the sweep (equilateral side-15 instance, GapE120).
    Encoding: `Blocked.base = true` with `Blocked.m = e` means "target edge `e`" (the old base case stays allowed).
    `checkNodeE` is `checkNode` with `blockedOkE`; soundness in `SoundE*.lean`.  UNAUDITED. -/

namespace Refl

/-- `d` runs positively along the target edge `e` and `v` lies on that edge's line. -/
def edgeBlockedOk (I : Inst) (v d : Pt) (e : Nat) : Bool :=
  let A := I.tgt.vert (e % 3)
  let B := I.tgt.vert ((e + 1) % 3)
  let ev := vsub B A
  det3 A B v == 0 && (d.x * ev.2 - d.y * ev.1 == 0) && decide (0 < d.x * ev.1 + d.y * ev.2)

def blockedOkE (I : Inst) (cfg : List _root_.Tri) (v d : Pt) (b : Blocked) : Bool :=
  if b.base then
    ((v.y == 0 && d.y == 0 && decide (0 < d.x) && d.x == d.w) || edgeBlockedOk I v d b.m)
  else blockedOk I cfg v d b

def nodeLocalOkE (I : Inst) (cfg : List _root_.Tri) (n : Node) : Bool :=
  let v := n.v
  let d := n.d
  let tgtLins := (List.range 3).map (fun i => I.tgt.edge i)
  let ylt : Lin := ⟨0, -v.w, v.y⟩
  let ygeL : Lin := ⟨0, v.w, -v.y⟩
  let xltL : Lin := ⟨-v.w, 0, v.x⟩
  let r1 := n.t1.check cfg [] [] false (tgtLins.map (fun l => (l, false)) ++ [(ylt, true)]) []
  let r2 := n.t2.check cfg (tgtLins ++ [ygeL]) [(ylt, false), (xltL, true)] true
      (tgtLins.map (fun l => (l, false)) ++ [(ygeL, false), (xltL, true)]) []
  let tgtQ := tgtLins.all (fun l => okPos (quad I v d l) n.tauN n.tauD)
  let tileQ := (cfg.zip n.fedges).all (fun (T, e) => okNeg (quad I v d (T.edge e)) n.tauN n.tauD)
  decide (0 < v.w) && decide (0 < d.w) && (d.x * d.x + I.Dn * d.y * d.y == d.w * d.w) &&
  decide (0 < n.tauN) && decide (0 < n.tauD) && (n.fedges.length == cfg.length) &&
  r1 && r2 && tgtQ && tileQ && blockedOkE I cfg v d n.hb

def checkNodeE (I : Inst) : Nat → List _root_.Tri → Node → Bool
  | 0, _, _ => false
  | fuel + 1, cfg, n =>
    nodeLocalOkE I cfg n && killsCheck I cfg n.v n.d n.kills I.pl (n.children) (fun c cfg' => checkNodeE I fuel cfg' c)

def _root_.Inst.checkAllE (I : Inst) (fuel : Nat) (n : Node) : Bool := I.ok && checkNodeE I fuel [] n

end Refl
