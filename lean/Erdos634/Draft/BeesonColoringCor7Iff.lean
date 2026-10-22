import Erdos634.Draft.BeesonColoringCor7
import Erdos634.Draft.FluxRow11Witness

/-!
# Beeson (arXiv 1206.2229v4) Corollary 7 (iff)

NOTE, UNAUDITED.  Credit: Michael Beeson (arXiv 1206.2229 v4, Cor 7, Cor 6, Thm 15), Laczkovich (DCG 48 (2012)),
Beeson-Zhang.  Statement: the tile has angles `(alpha, beta, 2 alpha + beta)`, `3 alpha + 2 beta = pi`, side data
`(A, B, C)` (opposite those angles; some triangle realises it).  Some triangle with angles `(2 alpha, alpha, 2 beta)`
is tiled by the tile (a `CongruentDissection` whose model has that `ThreeAlphaData`) iff `s = 2 sin(alpha/2)` is
rational.  Hypothesis (H1) `alpha not in Q * pi` (named; Beeson's Lemma 1 not in Lean) is used by the only-if part.
Tile of the "if" part: `cor7_if` (tile `(uv, v^2-u^2, v^2)`, `s = u/v`) rescaled by `scaleDissection`.
-/

open scoped Classical

namespace Erdos634.BeesonColoring.Cor7

open Erdos634.Geometry Erdos634.CertCoord Erdos634.Draft.FluxGridWitness Erdos634.BeesonCor6 Erdos634.BeesonColoring.Cor6M Erdos634.Realizable

set_option maxHeartbeats 800000 in
theorem cor7_if_real {α β A B C : ℝ} (hrel : 3 * α + 2 * β = Real.pi)
    (hT : ∃ T : Tri, T.ThreeAlphaData α β A B C) (hq : ∃ q : ℚ, 2 * Real.sin (α / 2) = (q : ℝ)) :
    ∃ (N : ℕ) (D : CongruentDissection N), D.model.ThreeAlphaData α β A B C ∧
      D.target.angleAt 0 = 2 * α ∧ D.target.angleAt 1 = α ∧ D.target.angleAt 2 = 2 * β := by
  obtain ⟨q, hq⟩ := hq
  obtain ⟨T, hT'⟩ := hT
  obtain ⟨hCpos, hA⟩ := model_a_eq hrel hT'
  have hB := Rows11_13AnyLabel.threeAlpha_b_eq hrel hT'
  obtain ⟨-, -, -, hαpos, hβpos⟩ := model_abc_pos hT'
  have hαlt : α < Real.pi / 3 := by linarith
  have hs_pos : 0 < Real.sin (α / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hs_lt : Real.sin (α / 2) < 1 / 2 := by
    rw [← Real.sin_pi_div_six]
    exact Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
      (by linarith)
  have hq0 : (0 : ℝ) < q := by rw [← hq]; linarith
  have hq1 : (q : ℝ) < 1 := by rw [← hq]; linarith
  have hq0' : (0 : ℚ) < q := by exact_mod_cast hq0
  have hq1' : q < 1 := by exact_mod_cast hq1
  -- q = u / v, coprime
  obtain ⟨u, hu⟩ : ∃ u : ℕ, q.num = u := ⟨q.num.toNat, (Int.toNat_of_nonneg (Rat.num_nonneg.mpr hq0'.le)).symm⟩
  obtain ⟨v, hv⟩ : ∃ v : ℕ, v = q.den := ⟨_, rfl⟩
  have hvpos : 0 < v := by rw [hv]; exact q.den_pos
  have hupos : 0 < u := by
    have := Rat.num_pos.mpr hq0'
    rw [hu] at this; exact_mod_cast this
  have h1 : (q : ℚ) = (u : ℚ) / (v : ℚ) := by
    have := Rat.num_div_den q
    rw [hu, ← hv] at this; simpa using this.symm
  have hvQ : (0 : ℚ) < v := by exact_mod_cast hvpos
  have huv : u < v := by
    have : (u : ℚ) / v < 1 := h1 ▸ hq1'
    rw [div_lt_one hvQ] at this; exact_mod_cast this
  have hcop : Nat.Coprime u v := by
    have := q.reduced
    rw [hu, ← hv] at this; simpa using this
  have hqr : (q : ℝ) = (u : ℝ) / (v : ℝ) := by
    rw [h1]; push_cast; rfl
  obtain ⟨ha, hb, h, hg⟩ := coprime_tile u v hupos huv hcop
  obtain ⟨L, hL, T0, E, hE, m01, m02, m12, t01, t02, t12⟩ := cor7_if u v hupos huv hcop
  obtain ⟨D', hD'm, hcos, hrel0, hdata, e0, e1, e2⟩ := cor6_prepare (u * v) (v * v - u * u) (v * v) L ha hb hL h E
    (by rw [hE]; exact m01) (by rw [hE]; exact m02) (by rw [hE]; exact m12) t01 t02 t12
  -- the angle alpha0 equals alpha
  have hle : u * u ≤ v * v := Nat.mul_le_mul huv.le huv.le
  have hcosα : Real.cos α = 1 - (q : ℝ) ^ 2 / 2 := by
    have h2 : Real.cos α = 2 * Real.cos (α / 2) ^ 2 - 1 := by
      rw [← Real.cos_two_mul]; congr 1; ring
    have h3 := Real.sin_sq_add_cos_sq (α / 2)
    have h4 : Real.sin (α / 2) = (q : ℝ) / 2 := by linarith
    rw [h4] at h3
    nlinarith
  have hvR : (0 : ℝ) < v := by exact_mod_cast hvpos
  have hcos0 : Real.cos (E.model.angleAt 0) = 1 - (q : ℝ) ^ 2 / 2 := by
    rw [hcos, hqr]
    push_cast [Nat.cast_sub hle]
    field_simp
    ring
  have hα0 : E.model.angleAt 0 = α :=
    Real.injOn_cos (cornerAngle_mem _ _ _) ⟨hαpos.le, by linarith [Real.pi_pos]⟩ (hcos0.trans hcosα.symm)
  have hβ0 : E.model.angleAt 1 = β := by linarith
  -- rescale
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = C / ((v : ℝ) * v) := ⟨_, rfl⟩
  have hrpos : 0 < r := by rw [hr]; positivity
  obtain ⟨D'', hD''⟩ : ∃ D'', D'' = scaleDissection (D'.target.pts 0) r hrpos.ne' D' := ⟨_, rfl⟩
  have hA' : A = r * ((u * v : ℕ) : ℝ) := by
    rw [hA, hq, hqr, hr]; push_cast; field_simp
  have hC' : C = r * ((v * v : ℕ) : ℝ) := by rw [hr]; push_cast; field_simp
  have hB' : B = r * ((v * v - u * u : ℕ) : ℝ) := by
    have hBc : B = C - A ^ 2 / C := by field_simp; linarith
    rw [hBc, hA', hC']
    push_cast [Nat.cast_sub hle]
    have : (r * ((v : ℝ) * v)) ≠ 0 := by positivity
    field_simp
  refine ⟨_, D'',?_, ?_, ?_, ?_⟩
  · have := scale_data D' (D'.target.pts 0) r hrpos.ne' (by rw [hD'm]; exact hdata)
    rw [abs_of_pos hrpos, hα0, hβ0] at this
    rw [hD'', hA', hB', hC']; exact this
  · rw [hD'', Erdos634.Draft.FDCScaleReduce.scale_target_angleAt, e0, hα0]
  · rw [hD'', Erdos634.Draft.FDCScaleReduce.scale_target_angleAt, e1, hα0]
  · rw [hD'', Erdos634.Draft.FDCScaleReduce.scale_target_angleAt, e2, hβ0]

/-- **Beeson Corollary 7** (UNAUDITED; (H1) `alpha not in Q * pi`, named; (H2) not involved).  Tile with angles
`(alpha, beta, 2 alpha + beta)`, `3 alpha + 2 beta = pi`, sides `(A, B, C)`: some triangle with angles
`(2 alpha, alpha, 2 beta)` can be tiled by the tile iff `s = 2 sin(alpha/2)` is rational. -/
theorem cor7_iff {α β A B C : ℝ} (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hrel : 3 * α + 2 * β = Real.pi)
    (hT : ∃ T : Tri, T.ThreeAlphaData α β A B C) :
    (∃ (N : ℕ) (D : CongruentDissection N), D.model.ThreeAlphaData α β A B C ∧
      D.target.angleAt 0 = 2 * α ∧ D.target.angleAt 1 = α ∧ D.target.angleAt 2 = 2 * β) ↔
      ∃ q : ℚ, 2 * Real.sin (α / 2) = (q : ℝ) := by
  constructor
  · rintro ⟨N, D, h, e0, e1, e2⟩
    exact cor7_only_if D hα hrel h e0 e1 e2
  · exact cor7_if_real hrel hT

/-- **witness** (all hypotheses of `cor7_iff` hold): the tile `(16,24,32)` (`alpha44`, `s = 1/2`) -- both sides of the iff. -/
theorem cor7_iff_wit_44 :
    (∃ (N : ℕ) (D : CongruentDissection N), D.model.ThreeAlphaData α44 β44 16 24 32 ∧
      D.target.angleAt 0 = 2 * α44 ∧ D.target.angleAt 1 = α44 ∧ D.target.angleAt 2 = 2 * β44) ∧
      ∃ q : ℚ, 2 * Real.sin (α44 / 2) = (q : ℝ) := by
  have hT : ∃ T : Tri, T.ThreeAlphaData α44 β44 16 24 32 :=
    ⟨_, Erdos634.Draft.FluxRow11Witness.data44⟩
  have hq : ∃ q : ℚ, 2 * Real.sin (α44 / 2) = (q : ℝ) := by
    obtain ⟨hC, hA⟩ := model_a_eq three_α_two_β Erdos634.Draft.FluxRow11Witness.data44
    exact ⟨1 / 2, by push_cast; linarith⟩
  exact ⟨(cor7_iff α44_irr three_α_two_β hT).mpr hq, hq⟩

end Erdos634.BeesonColoring.Cor7

#print axioms Erdos634.BeesonColoring.Cor7.cor7_if_real
#print axioms Erdos634.BeesonColoring.Cor7.cor7_iff
#print axioms Erdos634.BeesonColoring.Cor7.cor7_iff_wit_44
