import Erdos634.Draft.BeesonColoringCor6M
import Erdos634.Draft.BeesonColoringThm1
import Erdos634.Draft.BeesonColoringThm21
import Erdos634.Draft.BeesonCor5Legs

/-!
# Joint witness for `Beeson.thm21` and the isosceles base-`alpha+beta` case of `Beeson.thm1`

NOTE, UNAUDITED.  Credit: Michael Beeson (arXiv 1206.2229 v4, Cor 5, Lemma 51/53, Cor 4, Thm 1), Laczkovich
(DCG 48 (2012)), Beeson-Zhang.  The isosceles dissection of `cor5_legs` (apex = target vertex 2, angle `alpha`, base
angles `alpha + beta` at vertices 0, 1) is turned into the data `thm21`/`thm1` need: model `ThreeAlphaData` (via
`Congruent.exists_perm` and `scaleTri`) and the three target angles (apex from the `cor5_legs` conclusion, base angles
equal by isosceles).  Hypothesis (H1) `alpha not in Q * pi` is a hypothesis for general `(a,b,c)` and is witnessed at
`(2,3,4)` (`alpha = alpha44`).
-/

open scoped Classical

namespace Erdos634.BeesonColoring.Cor5Wit

open Erdos634.Geometry Erdos634.CertCoord Erdos634.Draft.FluxGridWitness Erdos634.BeesonCor6
  Erdos634.BeesonColoring.Cor6M Erdos634.Realizable

theorem scale_angleAt (T : Tri) (r : ℝ) (hr : 0 < r) (k : Fin 3) :
    (scaleTri r hr.ne' T).angleAt k = T.angleAt k := by
  unfold Tri.angleAt
  exact Erdos634.BeesonCor5.angle_scale T r hr (k + 1) k (k + 2) (by fin_cases k <;> decide)
    (by fin_cases k <;> decide)

theorem scale_oppLen (T : Tri) (r : ℝ) (hr : 0 < r) (k : Fin 3) :
    (scaleTri r hr.ne' T).oppLen k = r * T.oppLen k := by
  unfold Tri.oppLen
  simp only [scaleTri_pts]
  rw [Erdos634.Realizable.dist_homothety, abs_of_pos hr]

/-- **Cor 5 isosceles dissection with the data of `thm21`/`thm1`.** -/
theorem cor5_iso_data (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (h : a * a + c * b = c * c)
    (hg : Nat.gcd (Nat.gcd a b) c = 1) :
    ∃ (N : ℕ) (D : CongruentDissection N) (α β : ℝ) (k : ℝ), 0 < k ∧
      α = Real.arccos (((b : ℝ) + c) / (2 * c)) ∧ 3 * α + 2 * β = Real.pi ∧
      D.model.ThreeAlphaData α β (k * a) (k * b) (k * c) ∧
      D.target.angleAt 0 = α + β ∧ D.target.angleAt 1 = α + β ∧ D.target.angleAt 2 = α := by
  obtain ⟨R, hRa, hRb, hRc⟩ := exists_RTri_of_nat a b c ha hb h
  obtain ⟨s, hs, N, D, hiso, hang, hcong, -⟩ := Erdos634.BeesonCor5Legs.cor5_legs a b c ha hb h hg R hRa hRb hRc
  have d01 : dist (R.Δ.pts 0) (R.Δ.pts 1) = c := by rw [R.hc, hRc]; simp
  have d02 : dist (R.Δ.pts 0) (R.Δ.pts 2) = b := by rw [dist_comm, R.hb, hRb]; simp
  have d12 : dist (R.Δ.pts 1) (R.Δ.pts 2) = a := by rw [R.ha, hRa]; simp
  obtain ⟨hcos, hrel, hdata⟩ := model_angles R.Δ a b c ha hb h d01 d02 d12
  obtain ⟨σ, hσ⟩ := hcong.exists_perm
  obtain ⟨τ, h0, o0, h1, o1, h2, o2⟩ := hdata
  have key : ∀ j, D.model.angleAt (σ.symm j) = R.Δ.angleAt j ∧
      D.model.oppLen (σ.symm j) = s * R.Δ.oppLen j := by
    intro j
    obtain ⟨e1, e2⟩ := hσ (σ.symm j)
    rw [Equiv.apply_symm_apply] at e1 e2
    rw [e1, e2, scale_angleAt R.Δ s hs, scale_oppLen R.Δ s hs]
    exact ⟨rfl, rfl⟩
  have hdat : D.model.ThreeAlphaData (R.Δ.angleAt 0) (R.Δ.angleAt 1) (s * a) (s * b) (s * c) := by
    refine ⟨τ.trans σ.symm, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact ((key (τ 0)).1.trans h0)
    · exact ((key (τ 0)).2.trans (by rw [o0]))
    · exact ((key (τ 1)).1.trans h1)
    · exact ((key (τ 1)).2.trans (by rw [o1]))
    · exact ((key (τ 2)).1.trans h2)
    · exact ((key (τ 2)).2.trans (by rw [o2]))
  have hα0eq : R.Δ.angleAt 0 = Real.arccos (((b : ℝ) + c) / (2 * c)) := by
    rw [← hcos]
    exact (Real.arccos_cos (cornerAngle_mem _ _ _).1 (cornerAngle_mem _ _ _).2).symm
  -- target angles
  have hapex : D.target.angleAt 2 = R.Δ.angleAt 0 := by
    have : D.target.angleAt 2 = cornerAngle (D.target.pts 0) (D.target.pts 2) (D.target.pts 1) := rfl
    rw [this, hang]; rfl
  have hbase : D.target.angleAt 0 = D.target.angleAt 1 := by
    have := EuclideanGeometry.angle_eq_angle_of_dist_eq hiso
    have e0 : D.target.angleAt 0 = EuclideanGeometry.angle (D.target.pts 2) (D.target.pts 0) (D.target.pts 1) := by
      show EuclideanGeometry.angle (D.target.pts 1) (D.target.pts 0) (D.target.pts 2) = _
      exact EuclideanGeometry.angle_comm _ _ _
    have e1 : D.target.angleAt 1 = EuclideanGeometry.angle (D.target.pts 2) (D.target.pts 1) (D.target.pts 0) := rfl
    rw [e0, e1]; exact this
  have hsum := D.target.angleAt_sum
  refine ⟨N, D, R.Δ.angleAt 0, R.Δ.angleAt 1, s, hs, hα0eq, hrel, hdat, ?_, ?_, hapex⟩
  · linarith
  · linarith

/-- **Joint witness, tile `(2,3,4)`** (`alpha = alpha44 not in Q pi`): a genuine isosceles `CongruentDissection` with
all hypotheses of `thm21` and of the base-`alpha+beta` case of `thm1`; the conclusions are derived. -/
theorem thm21_thm1_witness_234 :
    ∃ (N : ℕ) (D : CongruentDissection N) (α β k : ℝ), 0 < k ∧ α = α44 ∧ 3 * α + 2 * β = Real.pi ∧
      D.model.ThreeAlphaData α β (k * 2) (k * 3) (k * 4) ∧
      D.target.angleAt 0 = α + β ∧ D.target.angleAt 1 = α + β ∧ D.target.angleAt 2 = α ∧
      (∃ (M : ℤ) (s : ℚ), 0 < M ∧ s = 1 / 2 ∧ (N : ℚ) * (1 - s) = (M : ℚ) ^ 2 * (1 + s) ∧
        (N : ℚ) = 3 * (M : ℚ) ^ 2) ∧
      (∃ M : ℤ, 0 < M ∧ (M : ℝ) * (k * 2 + k * 3 + k * 4) =
        D.target.oppLen 0 + D.target.oppLen 1 - D.target.oppLen 2) := by
  obtain ⟨N, D, α, β, k, hk, hαeq, hrel, hdat, e0, e1, e2⟩ :=
    cor5_iso_data 2 3 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hα44 : α = α44 := by
    rw [hαeq]
    have h78 : (((3 : ℕ) : ℝ) + ((4 : ℕ) : ℝ)) / (2 * ((4 : ℕ) : ℝ)) = Real.cos α44 := by
      rw [cos_α44]; norm_num
    rw [h78]
    have h0 : 0 ≤ α44 := (cornerAngle_mem _ _ _).1
    exact Real.arccos_cos h0 (by linarith [α44_le, Real.pi_pos])
  have hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi := by rw [hα44]; exact α44_irr
  refine ⟨N, D, α, β, k, hk, hα44, hrel, hdat, e0, e1, e2, ?_, ?_⟩
  · obtain ⟨M, s, hM, hsac, -, -, -, -, hN, -⟩ :=
      Erdos634.BeesonColoring.thm21 D hα hrel hdat e0 e1 e2
    have hs : s = 1 / 2 := by
      have : (s : ℝ) = ((1 / 2 : ℚ) : ℝ) := by
        rw [hsac]; push_cast; field_simp; norm_num
      exact_mod_cast this
    subst hs
    refine ⟨M, 1 / 2, hM, rfl, hN, ?_⟩
    norm_num at hN ⊢; linarith
  · exact (Erdos634.BeesonColoring.thm1 D hα hrel hdat).2.2.1 ⟨e0, e1, e2⟩

end Erdos634.BeesonColoring.Cor5Wit

#print axioms Erdos634.BeesonColoring.Cor5Wit.cor5_iso_data
#print axioms Erdos634.BeesonColoring.Cor5Wit.thm21_thm1_witness_234
