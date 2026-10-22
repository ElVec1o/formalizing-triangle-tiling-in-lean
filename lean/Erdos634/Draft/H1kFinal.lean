/-
Draft/H1kFinal.lean — atoms H1.j + H1.k: `RightCaseD N` for ALL N, hence `H1Right N` for ALL N, no hypotheses.
Route: given `D`, `RightNormal D α`, `hlam`, `hirr`, `hrs`:
  1. `g := exists_axis_isometry` (target vertex 0 ↦ 0, vertex 1 ↦ x-axis); `D1 := normalizeC D g 1` (same model,
     tiles/target moved by `g`);  2. `D2 := scaleDissection 0 (1/b) D1` (homothety about the origin, ratio `1/b`);
  3. transfer `RightNormal`, `λ ∉ ℚ`, `a/b ∉ ℚ`, `c = r a + s b` (all similarity-invariant) to `D2`;
  4. `hb1 : D2.model.oppLen 1 = 1`; `hL1` from `H1gPos.L1` (frame `target.pts 0 = 0`, `pts 1 1 = 0` is preserved by the
     origin-centred homothety; `K ∋ a,b,c` gives `K ∋` all model distances and `|det model| = a b` by `det_abs_right`);
  5. `rightCaseD_of_pieces D2`.
*** UNAUDITED.  Formalization debt, NOT /goal progress.  No sorry, no native_decide, no hypotheses. ***
-/
import Erdos634.Draft.H1jGlue
import Erdos634.Draft.H1cCaseC

open scoped Classical

namespace Erdos634.Draft.H1k

open Erdos634.Geometry Erdos634.Geometry.Row3.RP Erdos634.Draft.TheoremPConditional Erdos634.Draft.H1a Erdos634.Realizable Erdos634.Draft.H1j Erdos634.Draft.ChainComposite

/-- **`RightCaseD N` for every `N`.** -/
theorem rightCaseD (N : ℕ) : RightCaseD N := by
  intro D α hR hlam hirr hrs
  -- step 1: the isometric copy in the paper's frame
  have hne : D.target.pts 0 ≠ D.target.pts 1 := by
    intro h
    exact absurd (D.target.indep.injective h) (by decide)
  obtain ⟨g, hg0, hg1⟩ := Erdos634.H1gPos.exists_axis_isometry _ _ hne
  let D1 := Erdos634.NormalPosition.normalizeC D g 1
  have hmod1 : D1.model = D.model := rfl
  have htgt1 : ∀ k, D1.target.pts k = g (D.target.pts k) := fun k => rfl
  have hang : ∀ k, D1.target.angleAt k = D.target.angleAt k ∧ D1.target.oppLen k = D.target.oppLen k :=
    fun k => let h := Erdos634.Geometry.Row3.angle_oppLen_of_isometry g (fun k => (htgt1 k).symm) k
             ⟨h.1.symm, h.2.symm⟩
  have hR1 : RightNormal D1 α :=
    ⟨hR.pos, hR.lt, hR.irr, by rw [hmod1]; exact hR.m0, by rw [hmod1]; exact hR.m2,
      by rw [(hang 0).1]; exact hR.t0, by rw [(hang 1).1]; exact hR.t1⟩
  have h10 : D1.target.pts 0 = 0 := by rw [htgt1]; exact hg0
  have h11 : D1.target.pts 1 1 = 0 := by rw [htgt1]; exact hg1
  -- step 2: scale by 1/b about 0
  have hb : 0 < D.model.oppLen 1 := oppLen_pos _ _
  set b := D.model.oppLen 1 with hbdef
  set r : ℝ := b⁻¹ with hrdef
  have hr0 : 0 < r := inv_pos.mpr hb
  have hrne : r ≠ 0 := hr0.ne'
  let D2 := scaleDissection (0 : Plane) r hrne D1
  have hmp : ∀ i, D2.model.pts i = r • D1.model.pts i := by
    intro i
    rw [scaleDissection_model_pts, homothetyEquiv_apply]
    simp [AffineMap.homothety_apply]
  have htp : ∀ i, D2.target.pts i = r • D1.target.pts i := by
    intro i
    rw [scaleDissection_target_pts, homothetyEquiv_apply]
    simp [AffineMap.homothety_apply]
  have hM := fun k => homothety_angle_opp' D1.model D2.model r hr0 hmp k
  have hT := fun k => homothety_angle_opp' D1.target D2.target r hr0 htp k
  have hR2 : RightNormal D2 α :=
    ⟨hR.pos, hR.lt, hR.irr, by rw [(hM 0).1]; exact hR1.m0, by rw [(hM 2).1]; exact hR1.m2,
      by rw [(hT 0).1]; exact hR1.t0, by rw [(hT 1).1]; exact hR1.t1⟩
  have hb2 : D2.model.oppLen 1 = 1 := by
    rw [(hM 1).2, hmod1, hrdef]; exact inv_mul_cancel₀ hb.ne'
  have hD1m : ∀ k, D1.model.oppLen k = D.model.oppLen k := fun k => rfl
  have hmk : ∀ k, D2.model.oppLen k = r * D.model.oppLen k := fun k => by rw [(hM k).2]; rfl
  have htk : ∀ k, D2.target.oppLen k = r * D.target.oppLen k := fun k => by
    rw [(hT k).2, (hang k).2]
  -- step 3: transfer
  have hlam2 : Irrational (D2.target.oppLen 1 / D2.model.oppLen 2) := by
    rw [htk, hmk, mul_div_mul_left _ _ hrne]; exact hlam
  have hirr2 : Irrational (D2.model.oppLen 0 / D2.model.oppLen 1) := by
    rw [hmk, hmk, mul_div_mul_left _ _ hrne]; exact hirr
  have hrs2 : ∃ r' s' : ℚ, D2.model.oppLen 2 = r' * D2.model.oppLen 0 + s' * D2.model.oppLen 1 := by
    obtain ⟨r', s', h⟩ := hrs
    exact ⟨r', s', by rw [hmk, hmk, hmk, h]; ring⟩
  -- step 4: hL1
  have hL1 : ∀ K : Subfield ℝ, D2.model.oppLen 0 ∈ K → D2.model.oppLen 1 ∈ K → D2.model.oppLen 2 ∈ K →
      (∀ i k v, (D2.tile i).pts k v ∈ K) ∧ (∀ k v, D2.target.pts k v ∈ K) := by
    intro K ha hb' hc
    have hd := dist_mem_of_oppLen D2.model K ha hb' hc
    have hdet : |D2.model.det| ∈ K := by
      rw [det_abs_right _ hR2.m2]; exact K.mul_mem ha hb'
    refine Erdos634.H1gPos.L1 D2 K hd hdet ?_ ?_
    · rw [htp, h10]; simp
    · rw [htp]; simp [h11]
  exact Erdos634.Draft.H1eCL.rightCaseD_of_pieces D2 hR2 hb2 hlam2 hirr2 hrs2 hL1

/-- **`H1Right N` for every `N`, with no hypotheses.** -/
theorem h1Right (N : ℕ) : ChainComposite.H1Right N :=
  h1Right_of_caseC_caseD N (Erdos634.Draft.H1c.rightCaseC N) (rightCaseD N)

end Erdos634.Draft.H1k

#print axioms Erdos634.Draft.H1k.rightCaseD
#print axioms Erdos634.Draft.H1k.h1Right
