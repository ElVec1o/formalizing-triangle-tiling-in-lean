import Erdos634.Refl.CheckM

/-! Refl/CheckN.lean -- `CheckM` with SEMANTIC subset stubs (nogoods).

`checkNodeM` accepts a stub when some known (separately refuted) configuration is literally contained in the current
one.  Here containment is up to equality of triangles as point sets (`triEqv`: the vertices agree projectively, in some
order), so a refuted configuration found in one branch can be reused in another branch where the same tiles were
placed from different corners.  Everything else is `CheckM`.  Soundness: `SoundN.lean`. -/

namespace Refl

/-- the same triangle up to a permutation of the vertices (projective equality of the homogeneous points) -/
def triEqv (s t : Tri) : Bool :=
  (eqvPt s.a t.a && eqvPt s.b t.b && eqvPt s.c t.c) || (eqvPt s.a t.b && eqvPt s.b t.c && eqvPt s.c t.a) ||
  (eqvPt s.a t.c && eqvPt s.b t.a && eqvPt s.c t.b) || (eqvPt s.a t.a && eqvPt s.b t.c && eqvPt s.c t.b) ||
  (eqvPt s.a t.b && eqvPt s.b t.a && eqvPt s.c t.c) || (eqvPt s.a t.c && eqvPt s.b t.b && eqvPt s.c t.a)

/-- every tile of `c` occurs in `cfg` (as a triangle) -/
def cfgSubV (c cfg : List Tri) : Bool := c.all (fun t => cfg.any (fun u => triEqv t u))

def checkNodeN (I : Inst) (known : List (List Tri)) : Nat → List Tri → NodeM → Bool
  | 0, _, _ => false
  | fuel + 1, cfg, n =>
    if n.tauN == 0 then known.any (fun c => cfgSubV c cfg)
    else nodeLocalOkM I cfg n &&
      killsCheckM I cfg n.v n.d n.kills I.pl (n.children) (fun c cfg' => checkNodeN I known fuel cfg' c)

end Refl
