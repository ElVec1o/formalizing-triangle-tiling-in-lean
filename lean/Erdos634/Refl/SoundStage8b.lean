import Erdos634.Refl.SoundStage8

/-! Stage 8b: `hblocked_sound` (wedge case from the checked cone signs). -/

set_option linter.unusedSimpArgs false
open Erdos634.CertNode Erdos634.PlacementCompleteness
open Erdos634.Geometry (Plane)

namespace Refl

theorem cone_transfer (K : ℝ) (hK : 0 < K) (Xi Yi : Int) (x y : ℝ)
    (hx : (Xi : ℝ) = K * x) (hy : (Yi : ℝ) = K * y) :
    (0 < Xi ∨ (Xi = 0 ∧ Yi < 0)) → (0 < x ∨ (x = 0 ∧ y < 0)) := by
  rintro (h | ⟨h, h'⟩)
  · left
    have : (0:ℝ) < Xi := by exact_mod_cast h
    rw [hx] at this; exact (mul_pos_iff_of_pos_left hK).mp this
  · right
    have h1 : (Xi : ℝ) = 0 := by exact_mod_cast h
    have h2 : (Yi : ℝ) < 0 := by exact_mod_cast h'
    rw [hx] at h1; rw [hy] at h2
    exact ⟨(mul_eq_zero.mp h1).resolve_left hK.ne', by by_contra hh; push_neg at hh; nlinarith [mul_nonneg hK.le hh]⟩

theorem eqvPt_sound (p q : Pt) (hp : 0 < p.w) (hq : 0 < q.w) (h : eqvPt p q = true) :
    p.X = q.X ∧ p.Y = q.Y := by
  simp only [eqvPt, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨h1, h2⟩ := h
  have a := Pt.w_ne p hp
  have b := Pt.w_ne q hq
  unfold Pt.X Pt.Y
  constructor
  · rw [div_eq_div_iff a b]; exact_mod_cast h1
  · rw [div_eq_div_iff a b]; exact_mod_cast h2

/-- the wedge data of `blockedOk` gives a sub-triangle of the placed tile with the clockwise wedge inside -/
theorem wedge_data_sound (Dn : ℝ) (hD : 0 < Dn) (I : Inst) (hDn : (I.Dn : ℝ) = Dn)
    (T : _root_.Tri) (hT : T.ok = true) (v d : Pt) (hvw : 0 < v.w) (hdw : 0 < d.w) (W : _root_.Tri)
    (h : ((((((eqvPt W.a v = true ∧ 0 < det3 W.a W.b W.c) ∧ W.ok = true) ∧ inClosed T W.a = true) ∧
          inClosed T W.b = true) ∧
        inClosed T W.c = true) ∧
      (0 < vcross (d.x, d.y) (vsub W.c W.a) ∨
        vcross (d.x, d.y) (vsub W.c W.a) = 0 ∧ vcross (-(I.Dn * d.y), d.x) (vsub W.c W.a) < 0)) ∧
    (0 < vcross (vsub W.b W.a) (d.x, d.y) ∨
      vcross (vsub W.b W.a) (d.x, d.y) = 0 ∧ vcross (vsub W.b W.a) (-(I.Dn * d.y), d.x) < 0)) :
    ∃ T' : Erdos634.Geometry.Tri, T'.carrier ⊆ T.carr Dn ∧ T'.pts 0 = v.re Dn ∧
      ∃ δ : ℝ, 0 < δ ∧ ∀ t s : ℝ, 0 < t → t < δ → 0 < s → s < δ →
        T'.pts 0 + t • ((d.re Dn) - s • (sr Dn • perp (d.re Dn))) ∈ interior T'.carrier := by
  obtain ⟨⟨⟨⟨⟨⟨⟨heq, -⟩, hWok⟩, hA⟩, hB⟩, hC⟩, hc1⟩, hc2⟩ := h
  obtain ⟨hpos, hcar⟩ := Tri.ok_sem Dn hD W hWok
  obtain ⟨wa, wb, wc⟩ := Tri.ok_w W hWok
  have wa' := Pt.w_pos _ wa
  have wb' := Pt.w_pos _ wb
  have wc' := Pt.w_pos _ wc
  have dw' := Pt.w_pos _ hdw
  obtain ⟨eX, eY⟩ := eqvPt_sound W.a v wa hvw heq
  obtain ⟨hposT, hcarT⟩ := Tri.ok_sem Dn hD T hT
  have hA' := inClosed_sound Dn hD T W.a wa hT hA
  have hB' := inClosed_sound Dn hD T W.b wb hT hB
  have hC' := inClosed_sound Dn hD T W.c wc hT hC
  refine ⟨rtri Dn hD W.a.X W.a.Y W.b.X W.b.Y W.c.X W.c.Y hpos, ?_, ?_, ?_⟩
  · rw [hcarT]
    rw [hcarT] at hA' hB' hC'
    exact rtri_subset hD hpos _ hA' hB' hC'
  · show rp Dn W.a.X W.a.Y = rp Dn v.X v.Y
    rw [eX, eY]
  · have hcone1 : 0 < d.X * (W.c.Y - W.a.Y) - d.Y * (W.c.X - W.a.X) ∨
        (d.X * (W.c.Y - W.a.Y) - d.Y * (W.c.X - W.a.X) = 0 ∧
          (-(Dn * d.Y)) * (W.c.Y - W.a.Y) - d.X * (W.c.X - W.a.X) < 0) := by
      refine cone_transfer ((d.w : ℝ) * W.a.w * W.c.w) (by positivity) _ _ _ _ ?_ ?_ hc1
      · simp only [vcross, vsub, Pt.X, Pt.Y]; push_cast
        field_simp
      · simp only [vcross, vsub, Pt.X, Pt.Y]; push_cast; rw [hDn]
        field_simp
    have hcone2 : 0 < (W.b.X - W.a.X) * d.Y - (W.b.Y - W.a.Y) * d.X ∨
        ((W.b.X - W.a.X) * d.Y - (W.b.Y - W.a.Y) * d.X = 0 ∧
          (W.b.X - W.a.X) * d.X - (W.b.Y - W.a.Y) * (-(Dn * d.Y)) < 0) := by
      refine cone_transfer ((d.w : ℝ) * W.a.w * W.b.w) (by positivity) _ _ _ _ ?_ ?_ hc2
      · simp only [vcross, vsub, Pt.X, Pt.Y]; push_cast
        field_simp
      · simp only [vcross, vsub, Pt.X, Pt.Y]; push_cast; rw [hDn]
        field_simp
    exact wedge_real Dn hD _ _ _ _ _ _ d.X d.Y hpos hcone1 hcone2

#print axioms Refl.wedge_data_sound
end Refl
