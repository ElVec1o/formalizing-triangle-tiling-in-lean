-- Draft/LaczFormalIIcIsoWitD.lean -- NON-VACUITY witness for `IIcIsoCore`, step D: disjointness, congruence, `octDiss : CongruentRegionDissection 8` (regular octagon cut from the centre).
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012)), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcIsoWitC

open Erdos634.Geometry Erdos634.CertCoord Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Thm21

namespace Erdos634.Draft.LaczFormal.IsoWit

theorem cxy_ne (a : Fin 8) : (0:ℝ) ≠ cx a ∨ (0:ℝ) ≠ cy a := by
  by_contra H
  push_neg at H
  have := cxy_sq a
  rw [← H.1, ← H.2] at this
  norm_num at this

theorem tile_disjoint : Pairwise fun i j => Disjoint (interior (tile i).carrier) (interior (tile j).carrier) := by
  intro i j hij
  obtain ⟨a, h0, h1, h2, h3⟩ := sep_exists i j hij
  have hv : ∀ (t : Fin 8) (m : Fin 3), Erdos634.CertGeom.lineFun 0 0 (cx a) (cy a) ((tile t).pts m) =
      (if m = 0 then cr a t else if m = 1 then cr a (t + 1) else 0) := by
    intro t m
    fin_cases m <;> simp [tile_pts, Erdos634.CertGeom.lineFun_apply, cr] <;> ring
  refine Erdos634.CertGeom.interiors_disjoint_of_separating (Erdos634.CertGeom.lineFun 0 0 (cx a) (cy a))
    (Erdos634.CertGeom.lineFun_linear_ne_zero (cxy_ne a)) 0 ?_ ?_
  · refine Erdos634.CertGeom.le_of_forall_pts_le _ ?_
    intro m
    rw [hv]
    fin_cases m <;> simp <;> assumption
  · intro x hx
    have := Erdos634.CertGeom.le_of_forall_pts_le (t := tile j) (Erdos634.CertGeom.lineFun 0 0 (-(cx a)) (-(cy a))) (c := 0) ?_ x hx
    · simp only [Erdos634.CertGeom.lineFun_apply] at this ⊢
      nlinarith [this]
    · intro m
      have := hv j m
      simp only [Erdos634.CertGeom.lineFun_apply] at this ⊢
      fin_cases m <;> simp at this ⊢ <;> nlinarith [h2, h3]

theorem tile_cong (i : Fin 8) : (tile i).Congruent (tile 0) := by
  refine Erdos634.SssCongruent.congruent_of_sq_dist_perm (1 : Equiv.Perm (Fin 3)) ?_
  intro m n
  have := hh_sq; have := hh_pos
  simp only [Equiv.Perm.coe_one, id_eq]
  fin_cases i <;> fin_cases m <;> fin_cases n <;> simp [tile_pts, dist_sq_mkPt, cx, cy] <;> nlinarith

/-- **The regular octagon cut into eight isosceles triangles from the centre.** -/
noncomputable def octDiss : CongruentRegionDissection 8 where
  region := oct.carrier
  tile := tile
  covers := by
    ext x
    simp only [Set.mem_iUnion]
    exact ⟨fun ⟨i, hi⟩ => tile_sub i hi, fun hx => oct_sub x hx⟩
  interiors_disjoint := tile_disjoint
  model := tile 0
  tiles_congruent := tile_cong

end Erdos634.Draft.LaczFormal.IsoWit
