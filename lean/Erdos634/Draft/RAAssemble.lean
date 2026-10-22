-- Draft/RAAssemble.lean — `Δ₁ = West ⊔ A₁ ⊔ East`: a dissection of the atom `A₁ = (A,Q,P)`
-- (obtained from the target `ABC` by thm:ladder at ratio σ) plus the two `f·T` pieces gives a
-- dissection of `Δ₁(e,f)`.  Imported via AllNew8.lean → All.lean:853 (stale "NOT imported" header corrected 2026-10-04).
import Erdos634.Draft.RAPieces
import Erdos634.Draft.RWAssemble

open scoped Classical
open Erdos634.Geometry Erdos634.BaseBetaTargetCoord Erdos634.CertCoord Erdos634.Draft.RWPieces
  Erdos634.Draft.RWGlue Erdos634.Draft.RWEast Erdos634.Draft.RAPieces Erdos634.TilePlacement
open Erdos634.RouteOneCrossing (selfDissection)

namespace Erdos634.Draft.RAAssemble

/-- **West piece.**  `(A, W, Q)` is dissected into `f²` copies of `M` (sides `(ef, f²−e², f²)`). -/
theorem west_dissection (e f : ℝ) (fN : ℕ) (hfN : (fN : ℝ) = f) (hfpos : 0 < fN)
    (he : 0 < e) (hef : e < f) (M : Tri)
    (hM0 : M.oppLen 0 = e * f) (hM1 : M.oppLen 1 = f ^ 2 - e ^ 2) (hM2 : M.oppLen 2 = f ^ 2) :
    ∃ E : CongruentDissection (fN * fN * 1), E.target.Congruent (westTri he hef) ∧ E.model = M := by
  obtain ⟨hind, heta⟩ := tri_eta M
  set D0 : CongruentDissection 1 :=
    { toDissection := selfDissection M
      model := M
      tiles_congruent := fun _ => Tri.Congruent.refl M } with hD0
  obtain ⟨E, hEt, hEm⟩ := Erdos634.Ladder.ladder (M.pts 0) (M.pts 1) (M.pts 2) hind D0
    (heta) fN hfpos
  refine ⟨E, ?_, hEm⟩
  rw [hEt]
  have hd := dist_bigTri (M.pts 0) (M.pts 1) (M.pts 2) hind fN hfpos
  have o0 : dist (M.pts 1) (M.pts 2) = e * f := hM0
  have o1 : dist (M.pts 2) (M.pts 0) = f ^ 2 - e ^ 2 := hM1
  have o2 : dist (M.pts 0) (M.pts 1) = f ^ 2 := hM2
  refine SssCongruent.congruent_of_dist_three ?_ ?_ ?_
  · rw [hd 0 1]
    show (fN : ℝ) * dist (M.pts 0) (M.pts 1) = dist ((westTri he hef).pts 0) ((westTri he hef).pts 1)
    rw [o2, hfN]
    show f * f ^ 2 = dist (mkPt (baseLen e f / 2) (height e f)) (mkPt 0 0)
    rw [d_AW he hef]; ring
  · rw [hd 1 2]
    show (fN : ℝ) * dist (M.pts 1) (M.pts 2) = dist ((westTri he hef).pts 1) ((westTri he hef).pts 2)
    rw [o0, hfN]
    show f * (e * f) = dist (mkPt 0 0) (mkPt (xQ e f) 0)
    rw [d_WQ he hef]; ring
  · rw [hd 2 0]
    show (fN : ℝ) * dist (M.pts 2) (M.pts 0) = dist ((westTri he hef).pts 2) ((westTri he hef).pts 0)
    rw [o1, hfN]
    show f * (f ^ 2 - e ^ 2) = dist (mkPt (xQ e f) 0) (mkPt (baseLen e f / 2) (height e f))
    rw [dist_comm, d_AQ he hef]

/-- **Atom piece.**  If `D` has target `(P₀,P₁,P₂)` with `σ·|P₀P₁| = f b`, `σ·|P₁P₂| = e b`,
`σ·|P₂P₀| = f b` (`b = f²−e²`), the ladder at ratio `σ` dissects the atom `(A,Q,P)` into `σ²N`
tiles of the same model. -/
theorem atom_dissection (e f : ℝ) (he : 0 < e) (hef : e < f) {N : ℕ} (D : CongruentDissection N)
    (σ : ℕ) (hσ : 0 < σ)
    (h01 : (σ : ℝ) * dist (D.target.pts 0) (D.target.pts 1) = f * (f ^ 2 - e ^ 2))
    (h12 : (σ : ℝ) * dist (D.target.pts 1) (D.target.pts 2) = e * (f ^ 2 - e ^ 2))
    (h20 : (σ : ℝ) * dist (D.target.pts 2) (D.target.pts 0) = f * (f ^ 2 - e ^ 2)) :
    ∃ E : CongruentDissection (σ * σ * N), E.target.Congruent (atomTri he hef) ∧ E.model = D.model := by
  obtain ⟨hind, heta⟩ := tri_eta D.target
  obtain ⟨E, hEt, hEm⟩ := Erdos634.Ladder.ladder (D.target.pts 0) (D.target.pts 1) (D.target.pts 2)
    hind D heta σ hσ
  refine ⟨E, ?_, hEm⟩
  rw [hEt]
  have hd := dist_bigTri (D.target.pts 0) (D.target.pts 1) (D.target.pts 2) hind σ hσ
  refine SssCongruent.congruent_of_dist_three ?_ ?_ ?_
  · rw [hd 0 1]
    show (σ : ℝ) * dist (D.target.pts 0) (D.target.pts 1) = dist ((atomTri he hef).pts 0) ((atomTri he hef).pts 1)
    rw [h01]
    show f * (f ^ 2 - e ^ 2) = dist (mkPt (baseLen e f / 2) (height e f)) (mkPt (xQ e f) 0)
    rw [d_AQ he hef]
  · rw [hd 1 2]
    show (σ : ℝ) * dist (D.target.pts 1) (D.target.pts 2) = dist ((atomTri he hef).pts 1) ((atomTri he hef).pts 2)
    rw [h12]
    show e * (f ^ 2 - e ^ 2) = dist (mkPt (xQ e f) 0) (mkPt (xP e f) 0)
    rw [d_QP he hef]
  · rw [hd 2 0]
    show (σ : ℝ) * dist (D.target.pts 2) (D.target.pts 0) = dist ((atomTri he hef).pts 2) ((atomTri he hef).pts 0)
    rw [h20]
    show f * (f ^ 2 - e ^ 2) = dist (mkPt (xP e f) 0) (mkPt (baseLen e f / 2) (height e f))
    rw [dist_comm, d_AP he hef]

theorem lm (a b t : ℝ) :
    AffineMap.lineMap (mkPt a 0) (mkPt b 0) t = mkPt (a + t * (b - a)) 0 := by
  rw [AffineMap.lineMap_apply]
  ext i
  fin_cases i
  · simp; ring
  · simp

theorem ra_tiled {N : ℕ} (eN fN σ : ℕ) (he : 0 < eN) (hef : eN < fN) (hσ : 0 < σ)
    (D : CongruentDissection N)
    (h01 : (σ : ℝ) * dist (D.target.pts 0) (D.target.pts 1) = (fN : ℝ) * ((fN : ℝ) ^ 2 - (eN : ℝ) ^ 2))
    (h12 : (σ : ℝ) * dist (D.target.pts 1) (D.target.pts 2) = (eN : ℝ) * ((fN : ℝ) ^ 2 - (eN : ℝ) ^ 2))
    (h20 : (σ : ℝ) * dist (D.target.pts 2) (D.target.pts 0) = (fN : ℝ) * ((fN : ℝ) ^ 2 - (eN : ℝ) ^ 2))
    (hM0 : sideOpp D.model 0 = (eN : ℝ) * fN) (hM1 : sideOpp D.model 1 = (fN : ℝ) ^ 2 - (eN : ℝ) ^ 2)
    (hM2 : sideOpp D.model 2 = (fN : ℝ) ^ 2) :
    ∃ (N' : ℕ) (D' : CongruentDissection N'),
      D'.target.Congruent (baseBetaTarget (eN : ℝ) fN (by exact_mod_cast he) (by exact_mod_cast hef)) ∧
      sideOpp D'.model 0 = (eN : ℝ) * fN ∧ sideOpp D'.model 1 = (fN : ℝ) ^ 2 - (eN : ℝ) ^ 2 ∧
      sideOpp D'.model 2 = (fN : ℝ) ^ 2 := by
  have he' : (0 : ℝ) < eN := by exact_mod_cast he
  have hef' : (eN : ℝ) < fN := by exact_mod_cast hef
  have hfpos : 0 < fN := lt_trans he hef
  obtain ⟨Dw, hDw, hDwm⟩ := west_dissection (eN : ℝ) (fN : ℝ) fN rfl hfpos he' hef' D.model hM0 hM1 hM2
  obtain ⟨De, hDe, hDem⟩ := east_dissection (eN : ℝ) (fN : ℝ) fN rfl hfpos he' hef' D.model hM0 hM1 hM2
  obtain ⟨Da, hDa, hDam⟩ := atom_dissection (eN : ℝ) (fN : ℝ) he' hef' D σ hσ h01 h12 h20
  set Δ := baseBetaTarget (eN : ℝ) fN he' hef' with hΔ
  set T : Tri := Δ.relabel (finRotate 3).symm with hT
  have hL := baseLen_pos he' hef'
  have hxQ := xQ_pos he' hef'
  have hxP := xP_pos he' hef'
  have hxQP := xQ_lt_xP he' hef'
  have hxPL := xP_lt he' hef'
  -- first cut: T = (A, W, E) at Q
  set t1 : ℝ := xQ (eN : ℝ) fN / baseLen (eN : ℝ) fN with ht1
  have ht10 : 0 < t1 := div_pos hxQ hL
  have ht11 : t1 < 1 := (div_lt_one hL).mpr (by linarith)
  have hlm1 : AffineMap.lineMap (mkPt 0 0) (mkPt (baseLen (eN : ℝ) fN) 0) t1
      = mkPt (xQ (eN : ℝ) fN) 0 := by
    rw [show (mkPt 0 0 : Plane) = mkPt (0 : ℝ) 0 from rfl, lm]
    congr 1; rw [ht1]; field_simp; ring
  have hTp0 : T.pts 0 = mkPt (baseLen (eN : ℝ) fN / 2) (height (eN : ℝ) fN) := rfl
  have hTp1 : T.pts 1 = mkPt 0 0 := rfl
  have hTp2 : T.pts 2 = mkPt (baseLen (eN : ℝ) fN) 0 := rfl
  -- second cut: midTri = (A, Q, E) at P
  set t2 : ℝ := (xP (eN : ℝ) fN - xQ (eN : ℝ) fN) / (baseLen (eN : ℝ) fN - xQ (eN : ℝ) fN) with ht2
  have hLQ : 0 < baseLen (eN : ℝ) fN - xQ (eN : ℝ) fN := by linarith
  have ht20 : 0 < t2 := div_pos (by linarith) hLQ
  have ht21 : t2 < 1 := (div_lt_one hLQ).mpr (by linarith)
  have hlm2 : AffineMap.lineMap (mkPt (xQ (eN : ℝ) fN) 0) (mkPt (baseLen (eN : ℝ) fN) 0) t2
      = mkPt (xP (eN : ℝ) fN) 0 := by
    rw [lm]
    congr 1; rw [ht2]; field_simp; ring
  have hMp0 : (midTri he' hef').pts 0 = mkPt (baseLen (eN : ℝ) fN / 2) (height (eN : ℝ) fN) := rfl
  have hMp1 : (midTri he' hef').pts 1 = mkPt (xQ (eN : ℝ) fN) 0 := rfl
  have hMp2 : (midTri he' hef').pts 2 = mkPt (baseLen (eN : ℝ) fN) 0 := rfl
  obtain ⟨Dr, hDrt, hDrm⟩ := glue_two (midTri he' hef') (atomTri he' hef') (eTri he' hef') t2 ht20 ht21
    (by rw [hMp0]; rfl) (by rw [hMp1]; rfl) (by rw [hMp1, hMp2, hlm2]; rfl)
    (by rw [hMp0]; rfl) (by rw [hMp1, hMp2, hlm2]; rfl) (by rw [hMp2]; rfl)
    Da De (by rw [hDem, hDam]; exact Tri.Congruent.refl _) hDa hDe
  obtain ⟨D', hDt, hDm⟩ := glue_two T (westTri he' hef') (midTri he' hef') t1 ht10 ht11
    (by rw [hTp0]; rfl) (by rw [hTp1]; rfl) (by rw [hTp1, hTp2, hlm1]; rfl)
    (by rw [hTp0, hMp0]) (by rw [hTp1, hTp2, hlm1, hMp1]) (by rw [hTp2, hMp2])
    Dw Dr (by rw [hDrm, hDwm, hDam]; exact Tri.Congruent.refl _) hDw (by rw [hDrt]; exact Tri.Congruent.refl _)
  refine ⟨_, D', ?_, ?_⟩
  · rw [hDt]; exact (Δ.congruent_relabel _).symm
  · rw [hDm, hDwm]; exact ⟨hM0, hM1, hM2⟩

end Erdos634.Draft.RAAssemble

#print axioms Erdos634.Draft.RAAssemble.ra_tiled
