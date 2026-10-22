import Erdos634.Draft.LaczFormalL22Iso

/-!
# Laczkovich Theorem 2.4, first triple `(α, α, π - 2α)`: the chart geometry of Fig. 4

NOTE, UNAUDITED.  Credit: Laczkovich (Discrete Math. 140 (1995) 79-94, Theorem 2.4, Fig. 4), Beeson,
Beeson-Zhang, Zhang.

With `sin(α/2) = a/2` (`0 < a < 1`) and `Δ = (a, 1 - a², 1)` (sides opposite `α, β, γ`), Fig. 4 is, in the chart
`(G; w = GB, d = GF)`, the following rational picture (`b = 1 - a²`, `N = a² + b²`):
`G = (0,0)`, `B = (1,0)`, `F = (0,1)`, `C = (τ,1)`, `D = (0,δ)`, `E = (0,e)`, `A = (τ, 2 - a²)`, with
`τ = b²/N`, `δ = 1 + b³/a²`, `e = δ + b/a²`.  The target is the triangle `GBE`; it is the union of the
trapezoid `trapSet τ = GBCF`, and the four tiles `BCA, ACD, ADE, CDF` (`t1_cover`), pairwise interior-disjoint.
This file: covering and disjointness, in real arithmetic only.
-/

namespace Erdos634.LaczL24

open Erdos634.Geometry Erdos634.CertCoord Erdos634.LaczL22

/-! ## Topological helper -/

theorem disjoint_interior_union {S₁ S₂ S₃ : Set Plane} (h₁ : IsClosed S₁)
    (d₁ : Disjoint (interior S₁) (interior S₃)) (d₂ : Disjoint (interior S₂) (interior S₃)) :
    Disjoint (interior (S₁ ∪ S₂)) (interior S₃) := by
  rw [Set.disjoint_left]
  intro x hx hx3
  set U : Set Plane := interior (S₁ ∪ S₂) ∩ interior S₃ with hU
  have hUo : IsOpen U := isOpen_interior.inter isOpen_interior
  have hV : IsOpen (U ∩ S₁ᶜ) := hUo.inter h₁.isOpen_compl
  have hVS₂ : U ∩ S₁ᶜ ⊆ S₂ := by
    intro y hy
    have : y ∈ S₁ ∪ S₂ := interior_subset hy.1.1
    rcases this with h | h
    · exact absurd h hy.2
    · exact h
  have hVi : U ∩ S₁ᶜ ⊆ interior S₂ := interior_maximal hVS₂ hV
  have hUS₁ : U ⊆ S₁ := by
    intro y hy
    by_contra hyS
    exact (Set.disjoint_left.mp d₂) (hVi ⟨hy, hyS⟩) hy.2
  have hUi : U ⊆ interior S₁ := interior_maximal hUS₁ hUo
  exact (Set.disjoint_left.mp d₁) (hUi ⟨hx, hx3⟩) hx3

theorem isClosed_trapSet (τ : ℝ) : IsClosed (trapSet τ) := by
  have h0 : IsClosed {z : Plane | 0 ≤ z 1} := isClosed_le continuous_const (by fun_prop)
  have h1 : IsClosed {z : Plane | z 1 ≤ 1} := isClosed_le (by fun_prop) continuous_const
  have h2 : IsClosed {z : Plane | 0 ≤ z 0} := isClosed_le continuous_const (by fun_prop)
  have h3 : IsClosed {z : Plane | z 0 ≤ 1 + (τ - 1) * z 1} :=
    isClosed_le (by fun_prop) (by fun_prop)
  have : trapSet τ = {z : Plane | 0 ≤ z 1} ∩ {z | z 1 ≤ 1} ∩ {z | 0 ≤ z 0} ∩ {z | z 0 ≤ 1 + (τ - 1) * z 1} := by
    ext z; simp [trapSet, and_assoc]
  rw [this]
  exact ((h0.inter h1).inter h2).inter h3

theorem mem_mkTri_of_dets {x0 y0 x1 y1 x2 y2 a b : ℝ} (hD : det3 x0 y0 x1 y1 x2 y2 ≠ 0)
    (h₀ : 0 ≤ det3 a b x1 y1 x2 y2 / det3 x0 y0 x1 y1 x2 y2)
    (h₁ : 0 ≤ det3 x0 y0 a b x2 y2 / det3 x0 y0 x1 y1 x2 y2)
    (h₂ : 0 ≤ det3 x0 y0 x1 y1 a b / det3 x0 y0 x1 y1 x2 y2) :
    mkPt a b ∈ (mkTri x0 y0 x1 y1 x2 y2 hD).carrier := by
  set D := det3 x0 y0 x1 y1 x2 y2 with hDdef
  refine Erdos634.CertGeom.mem_carrier_of_combo _ _
    ![det3 a b x1 y1 x2 y2 / D, det3 x0 y0 a b x2 y2 / D, det3 x0 y0 x1 y1 a b / D] ?_ ?_ ?_
  · show _ / D + _ / D + _ / D = 1
    rw [← add_div, ← add_div, det3_split, hDdef]
    exact div_self hD
  · intro k
    have htri : ∀ y : Fin 3, y = 0 ∨ y = 1 ∨ y = 2 := by decide
    rcases htri k with rfl | rfl | rfl
    · exact h₀
    · exact h₁
    · exact h₂
  · show mkPt a b = _ • (mkTri x0 y0 x1 y1 x2 y2 hD).pts 0
        + _ • (mkTri x0 y0 x1 y1 x2 y2 hD).pts 1
        + _ • (mkTri x0 y0 x1 y1 x2 y2 hD).pts 2
    have hpts : ∀ (i : Fin 3), (mkTri x0 y0 x1 y1 x2 y2 hD).pts i
        = ![mkPt x0 y0, mkPt x1 y1, mkPt x2 y2] i := fun _ => rfl
    rw [hpts 0, hpts 1, hpts 2]
    refine PiLp.ext ?_
    intro i
    have hi : i = 0 ∨ i = 1 := by omega
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
    rcases hi with rfl | rfl
    · simp only [mkPt_zero]
      field_simp
      simp only [hDdef, det3]
      ring
    · simp only [mkPt_one]
      field_simp
      simp only [hDdef, det3]
      ring


/-! ## Parameters of Fig. 4 -/

noncomputable def gN (a : ℝ) : ℝ := a ^ 2 + (1 - a ^ 2) ^ 2
noncomputable def gTau (a : ℝ) : ℝ := (1 - a ^ 2) ^ 2 / gN a
noncomputable def gDel (a : ℝ) : ℝ := 1 + (1 - a ^ 2) ^ 3 / a ^ 2
noncomputable def gE (a : ℝ) : ℝ := gDel a + (1 - a ^ 2) / a ^ 2

section facts
variable {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
include ha0 ha1

theorem gb_pos : 0 < 1 - a ^ 2 := by nlinarith
theorem gN_pos : 0 < gN a := by unfold gN; have := gb_pos ha0 ha1; positivity
theorem gTau_pos : 0 < gTau a := by
  unfold gTau; have := gb_pos ha0 ha1; have := gN_pos ha0 ha1; positivity
theorem gTau_lt_one : gTau a < 1 := by
  unfold gTau
  have hN := gN_pos ha0 ha1
  rw [div_lt_one hN]
  unfold gN; nlinarith
theorem gDel_gt : 1 < gDel a := by
  unfold gDel; have := gb_pos ha0 ha1
  have : 0 < (1 - a ^ 2) ^ 3 / a ^ 2 := by positivity
  linarith
theorem gE_gt : gDel a < gE a := by
  unfold gE; have := gb_pos ha0 ha1
  have : 0 < (1 - a ^ 2) / a ^ 2 := by positivity
  linarith
theorem gAe : gE a * (1 - gTau a) = 2 - a ^ 2 := by
  have hN := (gN_pos ha0 ha1).ne'
  have ha := ha0.ne'
  unfold gE gDel gTau gN
  unfold gN at hN
  field_simp
  ring
end facts

section tris
variable (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1)

/-- The target triangle `G B E`. -/
noncomputable def triT1 : Tri :=
  mkTri 0 0 1 0 0 (gE a) (by
    have := gE_gt ha0 ha1; have := gDel_gt ha0 ha1
    intro h; simp only [det3] at h; nlinarith)

noncomputable def triBCA : Tri :=
  mkTri 1 0 (gTau a) 1 (gTau a) (2 - a ^ 2) (by
    have := gTau_lt_one ha0 ha1; have := gb_pos ha0 ha1
    intro h; simp only [det3] at h; nlinarith [mul_pos (sub_pos.2 this) (gb_pos ha0 ha1)])

noncomputable def triACD : Tri :=
  mkTri (gTau a) (2 - a ^ 2) (gTau a) 1 0 (gDel a) (by
    have := gTau_pos ha0 ha1; have := gb_pos ha0 ha1
    intro h; simp only [det3] at h; nlinarith [mul_pos (gTau_pos ha0 ha1) (gb_pos ha0 ha1)])

noncomputable def triADE : Tri :=
  mkTri (gTau a) (2 - a ^ 2) 0 (gDel a) 0 (gE a) (by
    have := gE_gt ha0 ha1
    intro h; simp only [det3] at h
    nlinarith [mul_pos (gTau_pos ha0 ha1) (sub_pos.2 (gE_gt ha0 ha1))])

noncomputable def triCDF : Tri :=
  mkTri (gTau a) 1 0 (gDel a) 0 1 (by
    intro h; simp only [det3] at h
    nlinarith [mul_pos (gTau_pos ha0 ha1) (sub_pos.2 (gDel_gt ha0 ha1))])

end tris

end Erdos634.LaczL24
