-- Draft/LaczFormalIIcL8s.lean -- Laczkovich (DCG 48 (2012)), Sect. 6.3, L8 `gexc_disjoint`, step 12: polygon facts (vertices are not interior points, convexity of the carrier) and the collinear ordering lemma `col_E_in`.
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcL8f
import Erdos634.Draft.LaczFormalRG12GExcEndT

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.Draft.LaczFormal.Thm21

namespace Erdos634.Draft.LaczFormal.RG

variable {M : ℕ} [NeZero M]

theorem region_convex (P : ConvPoly M) : Convex ℝ P.carrier :=
  convex_iff_segment_subset.mpr (fun _ hx _ hy => carrier_segment P hx hy)

theorem vertex_not_interior (P : ConvPoly M) (j : Fin M) : P.v j ∉ interior P.carrier := by
  intro h
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior _ h
  have hM := P.three_le
  obtain ⟨f1, f2, f3, f4, f5, f6⟩ := ConvPoly.fin_facts hM j
  set w := P.v (j + 2) - P.v j with hw
  have hpos : 0 < P.c j (P.v (j + 2)) := P.c_vertex_pos f2 f3
  have hwne : 0 < ‖w‖ := by
    rw [norm_pos_iff]
    intro h0
    have : P.v (j + 2) = P.v j := sub_eq_zero.mp h0
    rw [this, P.c_self] at hpos
    exact lt_irrefl _ hpos
  set t : ℝ := ε / (2 * (‖w‖ + 1)) with ht
  have ht0 : 0 < t := by positivity
  set x : Plane := P.v j - t • w with hx
  have hxb : x ∈ Metric.ball (P.v j) ε := by
    rw [Metric.mem_ball, hx, dist_eq_norm]
    simp only [sub_sub_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos ht0]
    rw [ht]
    have : ε / (2 * (‖w‖ + 1)) * ‖w‖ < ε := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]; nlinarith
    exact this
  have hxc : x ∈ P.carrier := interior_subset (hball hxb)
  have h1 := hxc j
  have hcx : P.c j x = - t * P.c j (P.v (j + 2)) := by
    have : x = (1 - (-t)) • P.v j + (-t) • P.v (j + 2) := by
      rw [hx, hw]; module
    rw [this, P.c_comb, P.c_self]; ring
  have : 0 ≤ P.c j x := h1
  rw [hcx] at this
  nlinarith

theorem openSegment_interior_of (P : ConvPoly M) {E A : Plane} (hE : E ∈ interior P.carrier) (hA : A ∈ P.carrier) : openSegment ℝ E A ⊆ interior P.carrier :=
  (region_convex P).openSegment_interior_closure_subset_interior hE (subset_closure hA)

/-- **Collinear ordering**: `E, F` distinct points of the open chord `AB`, and the segments `AE`, `BF` have a common inner point: then `E` is an inner point of `BF`. -/
theorem col_E_in {A B E F X : Plane} (hAB : A ≠ B) (hE : E ∈ openSegment ℝ A B) (hF : F ∈ openSegment ℝ A B) (hEF : E ≠ F)
    (hX1 : X ∈ openSegment ℝ A E) (hX2 : X ∈ openSegment ℝ B F) : E ∈ openSegment ℝ B F := by
  obtain ⟨e, he0, he1, hEe⟩ := openSegment_param hE
  obtain ⟨f, hf0, hf1, hFf⟩ := openSegment_param hF
  obtain ⟨σ, hσ0, hσ1, hXσ⟩ := openSegment_param hX1
  obtain ⟨τ, hτ0, hτ1, hXτ⟩ := openSegment_param hX2
  have hw : B - A ≠ 0 := sub_ne_zero.mpr hAB.symm
  have key : (σ * e - 1 - τ * (f - 1)) • (B - A) = 0 := by
    have h1 : X = A + (σ * e) • (B - A) := by rw [hXσ, hEe]; module
    have h2 : X = A + (1 + τ * (f - 1)) • (B - A) := by rw [hXτ, hFf]; module
    have := h1.symm.trans h2
    have h3 : (σ * e) • (B - A) = (1 + τ * (f - 1)) • (B - A) := add_left_cancel this
    rw [sub_smul, sub_smul, h3]; module
  have hs : σ * e - 1 - τ * (f - 1) = 0 := (smul_eq_zero.mp key).resolve_right hw
  have hef : e ≠ f := by
    intro h; apply hEF; rw [hEe, hFf, h]
  rcases lt_or_gt_of_ne hef with hlt | hgt
  · exfalso; nlinarith
  · -- f < e
    have hfe : 0 < 1 - f := by linarith
    refine ⟨1 - (1 - e) / (1 - f), (1 - e) / (1 - f), ?_, div_pos (by linarith) hfe, by ring, ?_⟩
    · rw [sub_pos, div_lt_one hfe]; linarith
    · rw [hEe, hFf]
      have : (1 - e) / (1 - f) * (1 - f) = 1 - e := by field_simp
      ext i
      simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
      field_simp
      ring

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.col_E_in
#print axioms Erdos634.Draft.LaczFormal.RG.vertex_not_interior
