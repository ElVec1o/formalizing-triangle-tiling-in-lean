import Erdos634.Refl.SoundStage9

/-! Stage 10: `place_sound` — a placement of `six_placements` realises `placeTri`. -/

set_option linter.unusedSimpArgs false
open Erdos634.CertNode Erdos634.PlacementCompleteness Erdos634.SixPlacements
open Erdos634.Geometry (Plane)

namespace Refl

theorem placeOk_facts (I : Inst) (l1 l2 l3 : Int) (p : Place) (h : placeOk I l1 l2 l3 p = true) :
    0 < p.l1 ∧ 0 < p.pd ∧ 0 < p.qd ∧ 0 < p.qn ∧ p.l1 = l1 ∧
    2 * l1 * p.pn = (l1 * l1 + l2 * l2 - l3 * l3) * p.pd ∧
    I.Dn * p.qn * p.qn * p.pd * p.pd = (l2 * l2 * p.pd * p.pd - p.pn * p.pn) * (p.qd * p.qd) := by
  simp only [placeOk, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨a, b⟩, c⟩, d⟩, e⟩, f⟩, g⟩ := h
  exact ⟨a, b, c, d, e, f, g⟩

/-- **A `six_placements` outcome realises the checker's `placeTri`.** -/
theorem place_sound (Dn : ℝ) (hD : 0 < Dn) (I : Inst) (hDn : (I.Dn : ℝ) = Dn)
    (v d : Pt) (hvw : 0 < v.w) (hdw : 0 < d.w) (hdu : d.x * d.x + I.Dn * d.y * d.y = d.w * d.w)
    (l1 l2 l3 : Int) (p : Place) (hp : placeOk I l1 l2 l3 p = true)
    (T : Erdos634.Geometry.Tri) {k₀ k₁ k₂ : Fin 3} (h01 : k₀ ≠ k₁) (h02 : k₀ ≠ k₂) (h12 : k₁ ≠ k₂)
    (h0 : T.pts k₀ = v.re Dn) (h1 : T.pts k₁ = v.re Dn + (l1 : ℝ) • d.re Dn)
    (h2 : T.pts k₂ = placeThird (v.re Dn) (d.re Dn) l1 l2 l3) :
    T.carrier = (placeTri I v d p).carr Dn := by
  obtain ⟨pl1, ppd, pqd, pqn, pl, hpn, hq⟩ := placeOk_facts I l1 l2 l3 p hp
  have htok := placeTri_ok I v d p hvw hdw hdu (by exact_mod_cast (hDn ▸ hD : (0:ℝ) < I.Dn)) pl1 ppd pqd pqn
  obtain ⟨hpos, hcar⟩ := Tri.ok_sem Dn hD _ htok
  rw [hcar]
  have hvw' := Pt.w_pos _ hvw
  have hdw' := Pt.w_pos _ hdw
  have ppd' : (0:ℝ) < p.pd := by exact_mod_cast ppd
  have pqd' : (0:ℝ) < p.qd := by exact_mod_cast pqd
  have pqn' : (0:ℝ) < p.qn := by exact_mod_cast pqn
  have hl1 : (l1 : ℝ) = p.l1 := by rw [pl]
  have hl1pos : (0:ℝ) < l1 := by rw [hl1]; exact_mod_cast pl1
  -- the real numbers p, q
  have hpR : ((l1:ℝ) ^ 2 + (l2:ℝ) ^ 2 - (l3:ℝ) ^ 2) / (2 * l1) = (p.pn : ℝ) / p.pd := by
    rw [div_eq_div_iff (by positivity) ppd'.ne']
    have : (2 * l1 * p.pn : Int) = (l1 * l1 + l2 * l2 - l3 * l3) * p.pd := hpn
    have := congrArg (fun z : Int => (z : ℝ)) this
    push_cast at this; nlinarith
  have hqR : (l2:ℝ) ^ 2 - ((p.pn:ℝ) / p.pd) ^ 2 = Dn * ((p.qn : ℝ) / p.qd) ^ 2 := by
    have := congrArg (fun z : Int => (z : ℝ)) hq
    push_cast at this
    rw [hDn] at this
    field_simp
    nlinarith [this]
  have hplace := placeThird_rp hD (v.X) (v.Y) (d.X) (d.Y) l1 l2 l3 ((p.pn:ℝ)/p.pd) ((p.qn:ℝ)/p.qd)
    hpR (by positivity) hqR
  have hvre : v.re Dn = rp Dn v.X v.Y := rfl
  have hdre : d.re Dn = rp Dn d.X d.Y := rfl
  rw [hvre] at h0 h1 h2
  rw [hdre] at h1 h2
  rw [hplace] at h2
  rw [rp_add_smul] at h1
  refine carrier_eq_rtri_of_pts hD T h01 h02 h12 (x₀ := v.X) (y₀ := v.Y)
    (x₁ := (placeTri I v d p).b.X) (y₁ := (placeTri I v d p).b.Y)
    (x₂ := (placeTri I v d p).c.X) (y₂ := (placeTri I v d p).c.Y) h0 ?_ ?_ ?_
  · rw [h1]
    have e1 : v.X + (l1:ℝ) * d.X = (placeTri I v d p).b.X := by
      simp only [placeTri, Pt.X, Pt.Y]; rw [hl1]; push_cast; field_simp
    have e2 : v.Y + (l1:ℝ) * d.Y = (placeTri I v d p).b.Y := by
      simp only [placeTri, Pt.X, Pt.Y]; rw [hl1]; push_cast; field_simp
    rw [e1, e2]
  · rw [h2]
    have e1 : v.X + (p.pn:ℝ) / p.pd * d.X - Dn * ((p.qn:ℝ) / p.qd) * d.Y = (placeTri I v d p).c.X := by
      simp only [placeTri, Pt.X, Pt.Y]; push_cast; rw [hDn]; field_simp
    have e2 : v.Y + (p.pn:ℝ) / p.pd * d.Y + (p.qn:ℝ) / p.qd * d.X = (placeTri I v d p).c.Y := by
      simp only [placeTri, Pt.X, Pt.Y]; push_cast; field_simp
    rw [e1, e2]

#print axioms Refl.place_sound
end Refl
