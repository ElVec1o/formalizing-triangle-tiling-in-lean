-- Draft/RWAssemble.lean — `Δ₁ = W₁ ⊔ East`: a dissection of the west piece `W₁` by tiles of
-- model `M` (sides `(ef, f²−e², f²)`) extends to a dissection of `Δ₁(e,f)` with `f²` more tiles.
-- Imported via AllNew8.lean → All.lean:853 (stale "NOT imported" header corrected 2026-10-04).
import Erdos634.Draft.RWEast

open scoped Classical
open Erdos634.Geometry Erdos634.BaseBetaTargetCoord Erdos634.CertCoord Erdos634.Draft.RWPieces
  Erdos634.Draft.RWGlue Erdos634.Draft.RWEast Erdos634.TilePlacement

namespace Erdos634.Draft.RWAssemble

theorem rw_tiled {N : ℕ} (eN fN : ℕ) (he : 0 < eN) (hef : eN < fN)
    (D : CongruentDissection N)
    (hD : D.target.Congruent (wTri (e := (eN : ℝ)) (f := (fN : ℝ)) (by exact_mod_cast he)
      (by exact_mod_cast hef)))
    (hM0 : sideOpp D.model 0 = (eN : ℝ) * fN) (hM1 : sideOpp D.model 1 = (fN : ℝ) ^ 2 - (eN : ℝ) ^ 2)
    (hM2 : sideOpp D.model 2 = (fN : ℝ) ^ 2) :
    ∃ (N' : ℕ) (D' : CongruentDissection N'),
      D'.target.Congruent (baseBetaTarget (eN : ℝ) fN (by exact_mod_cast he) (by exact_mod_cast hef)) ∧
      sideOpp D'.model 0 = (eN : ℝ) * fN ∧ sideOpp D'.model 1 = (fN : ℝ) ^ 2 - (eN : ℝ) ^ 2 ∧
      sideOpp D'.model 2 = (fN : ℝ) ^ 2 := by
  have he' : (0 : ℝ) < eN := by exact_mod_cast he
  have hef' : (eN : ℝ) < fN := by exact_mod_cast hef
  have hfpos : 0 < fN := lt_trans he hef
  obtain ⟨E, hE, hEm⟩ := east_dissection (eN : ℝ) (fN : ℝ) fN rfl hfpos he' hef' D.model hM0 hM1 hM2
  set Δ := baseBetaTarget (eN : ℝ) fN he' hef' with hΔ
  set T : Tri := Δ.relabel (finRotate 3).symm with hT
  have hL := baseLen_pos he' hef'
  have hxP := xP_pos he' hef'
  have hxPL := xP_lt he' hef'
  set t : ℝ := xP (eN : ℝ) fN / baseLen (eN : ℝ) fN with ht
  have ht0 : 0 < t := div_pos hxP hL
  have ht1 : t < 1 := (div_lt_one hL).mpr hxPL
  have hlm : AffineMap.lineMap (mkPt 0 0) (mkPt (baseLen (eN : ℝ) fN) 0) t
      = mkPt (xP (eN : ℝ) fN) 0 := by
    rw [AffineMap.lineMap_apply]
    ext i
    fin_cases i
    · simp [ht]; field_simp
    · simp
  have hTp0 : T.pts 0 = mkPt (baseLen (eN : ℝ) fN / 2) (height (eN : ℝ) fN) := rfl
  have hTp1 : T.pts 1 = mkPt 0 0 := rfl
  have hTp2 : T.pts 2 = mkPt (baseLen (eN : ℝ) fN) 0 := rfl
  obtain ⟨D', hDt, hDm⟩ := glue_two T (wTri he' hef') (eTri he' hef') t ht0 ht1
    (by rw [hTp0]; rfl) (by rw [hTp1]; rfl) (by rw [hTp1, hTp2, hlm]; rfl)
    (by rw [hTp0]; rfl) (by rw [hTp1, hTp2, hlm]; rfl) (by rw [hTp2]; rfl)
    D E (by rw [hEm]; exact Tri.Congruent.refl _) hD hE
  refine ⟨_, D', ?_, ?_⟩
  · rw [hDt]; exact (Δ.congruent_relabel _).symm
  · rw [hDm]; exact ⟨hM0, hM1, hM2⟩

end Erdos634.Draft.RWAssemble

#print axioms Erdos634.Draft.RWAssemble.rw_tiled
