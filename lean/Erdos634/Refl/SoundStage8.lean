import Erdos634.Refl.SoundStage7

/-! Stage 8: `hblocked_sound`. -/

set_option linter.unusedSimpArgs false
open Erdos634.CertNode Erdos634.PlacementCompleteness
open Erdos634.Geometry (Plane)

namespace Refl

/-- `hblocked_of_wedge` without the hypothesis `1 < √Dn` (rescale the wedge instead). -/
theorem hblocked_of_wedge' {Dn : ℝ} (hD : 0 < Dn) {N : ℕ} (D : Erdos634.Geometry.Dissection N)
    (S : Finset (Fin N)) {i : Fin N} (hi : i ∈ S) (v d : Plane) (T : Erdos634.Geometry.Tri)
    (hT : T.carrier ⊆ (D.tile i).carrier) (hT0 : T.pts 0 = v)
    (hw : ∃ δ : ℝ, 0 < δ ∧ ∀ t s : ℝ, 0 < t → t < δ → 0 < s → s < δ →
      T.pts 0 + t • (d - s • (sr Dn • perp d)) ∈ interior T.carrier) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t s : ℝ, 0 < t → t < δ → 0 < s → s < δ →
      v + t • (d - s • perp d) ∉ unfilled D S := by
  obtain ⟨δ, hδ, h⟩ := hw
  have hs := sr_pos hD
  refine ⟨min δ (δ * sr Dn), lt_min hδ (mul_pos hδ hs), fun t s ht htδ hs0 hsδ hU => ?_⟩
  have htδ' : t < δ := lt_of_lt_of_le htδ (min_le_left _ _)
  have hsδ' : s < δ * sr Dn := lt_of_lt_of_le hsδ (min_le_right _ _)
  have hs' : 0 < s / sr Dn := div_pos hs0 hs
  have hsδ'' : s / sr Dn < δ := by rwa [div_lt_iff₀ hs]
  have hmem := h t (s / sr Dn) ht htδ' hs' hsδ''
  rw [hT0, ← cw_eq hD] at hmem
  obtain ⟨-, hn⟩ := hU
  apply hn
  exact Set.mem_iUnion₂.mpr ⟨i, hi, hT (interior_subset hmem)⟩

/-- if the target lies in `y ≥ 0`, the clockwise wedge at a base vertex with `d = (1,0)` is empty -/
theorem hblocked_base_sound (Dn : ℝ) (hD : 0 < Dn) (n : Node) (hvw : 0 < n.v.w) (hdw : 0 < n.d.w)
    (hb : (n.v.y == 0 && n.d.y == 0 && decide (0 < n.d.x) && n.d.x == n.d.w) = true)
    {N : ℕ} (D : Erdos634.Geometry.CongruentDissection N) (S : Finset (Fin N))
    (hy : ∀ p ∈ D.target.carrier, 0 ≤ p 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t s : ℝ, 0 < t → t < δ → 0 < s → s < δ →
      (n.v.re Dn) + t • ((n.d.re Dn) - s • perp (n.d.re Dn)) ∉ unfilled D.toDissection S := by
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hb
  obtain ⟨⟨⟨hvy, hdy⟩, hdx⟩, hdxw⟩ := hb
  have e1 : n.v.Y = 0 := by simp [Pt.Y, hvy]
  have e2 : n.d.Y = 0 := by simp [Pt.Y, hdy]
  have e3 : n.d.X = 1 := by
    have := Pt.w_ne n.d hdw
    simp only [Pt.X, hdxw]; exact div_self this
  have : (n.v.re Dn) = rp Dn n.v.X 0 := by simp [Pt.re, e1]
  rw [this]
  have h2 : (n.d.re Dn) = rp Dn 1 0 := by simp [Pt.re, e2, e3]
  rw [h2]
  exact hblocked_base hD D.toDissection S hy n.v.X


#print axioms Refl.hblocked_base_sound

theorem wedge_real (Dn : ℝ) (hD : 0 < Dn) (Ax Ay Bx By Cx Cy dX dY : ℝ)
    (hpos : 0 < ef Ax Ay Bx By Cx Cy)
    (c1 : 0 < dX * (Cy - Ay) - dY * (Cx - Ax) ∨
      (dX * (Cy - Ay) - dY * (Cx - Ax) = 0 ∧ (-(Dn * dY)) * (Cy - Ay) - dX * (Cx - Ax) < 0))
    (c2 : 0 < (Bx - Ax) * dY - (By - Ay) * dX ∨
      ((Bx - Ax) * dY - (By - Ay) * dX = 0 ∧ (Bx - Ax) * dX - (By - Ay) * (-(Dn * dY)) < 0)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t s : ℝ, 0 < t → t < δ → 0 < s → s < δ →
      (rtri Dn hD Ax Ay Bx By Cx Cy hpos).pts 0 + t • (rp Dn dX dY - s • (sr Dn • perp (rp Dn dX dY)))
        ∈ interior (rtri Dn hD Ax Ay Bx By Cx Cy hpos).carrier := by
  have hdet : 0 < (Bx - Ax) * (Cy - Ay) - (Cx - Ax) * (By - Ay) := hpos
  obtain ⟨p0, p1, p2⟩ := rtri_pts Dn hD Ax Ay Bx By Cx Cy hpos
  set T := rtri Dn hD Ax Ay Bx By Cx Cy hpos
  set det := (Bx - Ax) * (Cy - Ay) - (Cx - Ax) * (By - Ay) with hdetdef
  simp only [sr_smul_perp_rp hD]
  refine wedge_interior T (rp Dn dX dY) (rp Dn (-(Dn * dY)) dX)
    ((dX * (Cy - Ay) - dY * (Cx - Ax)) / det) (((Bx - Ax) * dY - (By - Ay) * dX) / det)
    (((-(Dn * dY)) * (Cy - Ay) - dX * (Cx - Ax)) / det)
    (((Bx - Ax) * dX - (By - Ay) * (-(Dn * dY))) / det) ?_ ?_ ?_ ?_
  · rw [p0, p1, p2]
    refine plane_ext ?_ ?_
    · simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, rp_zero, rp_one]
      field_simp; ring
    · simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, rp_zero, rp_one]
      field_simp; ring
  · rw [p0, p1, p2]
    refine plane_ext ?_ ?_
    · simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, rp_zero, rp_one]
      field_simp; ring
    · simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, rp_zero, rp_one]
      field_simp; ring
  · rcases c1 with h | ⟨h, h'⟩
    · exact Or.inl (div_pos h hdet)
    · exact Or.inr ⟨by rw [h]; simp, div_neg_of_neg_of_pos h' hdet⟩
  · rcases c2 with h | ⟨h, h'⟩
    · exact Or.inl (div_pos h hdet)
    · exact Or.inr ⟨by rw [h]; simp, div_neg_of_neg_of_pos h' hdet⟩

#print axioms Refl.wedge_real
end Refl
