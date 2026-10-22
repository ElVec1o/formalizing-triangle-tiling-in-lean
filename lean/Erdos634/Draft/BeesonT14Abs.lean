import Erdos634.Draft.BeesonT14Chart

/-!
# Beeson Theorem 14, general parameters: the abstract Fig. 17 assembly

Everything here is about abstract chart coordinates: the layout of Fig. 17 is given by points
`A = (0,0)`, `C = (K,0)`, `B`, `P`, and `Q = θ1 B`, `T = θ2 B` (on `AB`), `R = C + τ (B - C)` (on `CB`),
`S = P + ρ (R - P)` (on `PR`) and the determinant sign hypotheses of the layout.  The conclusion is the
`Dis` of the big triangle from the `Dis` of the six pieces.  Credit Beeson (arXiv 1206.2229), Beeson-Zhang,
Zhang (arXiv 2512.22696), Laczkovich.  UNAUDITED.
-/

namespace Erdos634.BeesonT14Abs

open Erdos634.Geometry Erdos634.CertCoord Erdos634.CertGeom Erdos634.RegionDissection
  Erdos634.GlueCut Erdos634.SssCongruent Erdos634.ZhangL1 Erdos634.ZhangPara
  Erdos634.ZhangSporadic Erdos634.ZhangThm4 Erdos634.BeesonT14Chart

def TriR (x0 w0 x1 w1 x2 w2 : ℝ) : ℝ → ℝ → Prop := fun X W =>
  0 ≤ detR X W x1 w1 x2 w2 ∧ 0 ≤ detR x0 w0 X W x2 w2 ∧ 0 ≤ detR x0 w0 x1 w1 X W

/-- barycentric interpolation: an affine functional `detR u v .` nonnegative at the vertices of a
positively oriented triangle is nonnegative on the triangle -/
theorem bary_nonneg {x0 w0 x1 w1 x2 w2 X W ux uw vx vw : ℝ}
    (hD : 0 < detR x0 w0 x1 w1 x2 w2) (h : TriR x0 w0 x1 w1 x2 w2 X W)
    (g0 : 0 ≤ detR ux uw vx vw x0 w0) (g1 : 0 ≤ detR ux uw vx vw x1 w1)
    (g2 : 0 ≤ detR ux uw vx vw x2 w2) : 0 ≤ detR ux uw vx vw X W := by
  obtain ⟨f0, f1, f2⟩ := h
  have key : detR ux uw vx vw X W * detR x0 w0 x1 w1 x2 w2 =
      detR ux uw vx vw x0 w0 * detR X W x1 w1 x2 w2 + detR ux uw vx vw x1 w1 * detR x0 w0 X W x2 w2
      + detR ux uw vx vw x2 w2 * detR x0 w0 x1 w1 X W := by
    simp only [detR]; ring
  have : 0 ≤ detR ux uw vx vw X W * detR x0 w0 x1 w1 x2 w2 := by
    rw [key]; positivity
  exact nonneg_of_mul_nonneg_left this hD

theorem detR_swap (ux uw vx vw X W : ℝ) : detR vx vw ux uw X W = - detR ux uw vx vw X W := by
  simp only [detR]; ring

theorem bary_nonpos {x0 w0 x1 w1 x2 w2 X W ux uw vx vw : ℝ}
    (hD : 0 < detR x0 w0 x1 w1 x2 w2) (h : TriR x0 w0 x1 w1 x2 w2 X W)
    (g0 : detR ux uw vx vw x0 w0 ≤ 0) (g1 : detR ux uw vx vw x1 w1 ≤ 0)
    (g2 : detR ux uw vx vw x2 w2 ≤ 0) : detR ux uw vx vw X W ≤ 0 := by
  have := bary_nonneg (ux := vx) (uw := vw) (vx := ux) (vw := uw) hD h
    (by rw [detR_swap]; linarith) (by rw [detR_swap]; linarith) (by rw [detR_swap]; linarith)
  rw [detR_swap] at this; linarith

theorem detR_cyc1 (x0 w0 x1 w1 x2 w2 : ℝ) : detR x0 w0 x1 w1 x2 w2 = detR x1 w1 x2 w2 x0 w0 := by
  simp only [detR]; ring

theorem detR_cyc2 (x0 w0 x1 w1 x2 w2 : ℝ) : detR x0 w0 x1 w1 x2 w2 = detR x2 w2 x0 w0 x1 w1 := by
  simp only [detR]; ring

/-- a convex quadrilateral `V0 V1 V2 V3` (ccw): affine functional nonneg at the vertices is nonneg on it -/
theorem quad_nonneg {x0 w0 x1 w1 x2 w2 x3 w3 X W ux uw vx vw : ℝ}
    (hD1 : 0 < detR x0 w0 x1 w1 x2 w2) (hD2 : 0 < detR x0 w0 x2 w2 x3 w3)
    (h : 0 ≤ detR x0 w0 x1 w1 X W ∧ 0 ≤ detR x1 w1 x2 w2 X W ∧ 0 ≤ detR x2 w2 x3 w3 X W ∧
      0 ≤ detR x3 w3 x0 w0 X W)
    (g0 : 0 ≤ detR ux uw vx vw x0 w0) (g1 : 0 ≤ detR ux uw vx vw x1 w1)
    (g2 : 0 ≤ detR ux uw vx vw x2 w2) (g3 : 0 ≤ detR ux uw vx vw x3 w3) :
    0 ≤ detR ux uw vx vw X W := by
  obtain ⟨e0, e1, e2, e3⟩ := h
  rcases le_total (detR x0 w0 x2 w2 X W) 0 with hd | hd
  · refine bary_nonneg hD1 ?_ g0 g1 g2
    refine ⟨?_, ?_, e0⟩
    · rw [detR_cyc1 X W]; exact e1
    · have : detR x0 w0 X W x2 w2 = - detR x0 w0 x2 w2 X W := by simp only [detR]; ring
      rw [this]; linarith
  · refine bary_nonneg (x1 := x2) (w1 := w2) (x2 := x3) (w2 := w3) hD2 ?_ g0 g2 g3
    refine ⟨?_, ?_, hd⟩
    · rw [detR_cyc1 X W]; exact e2
    · rw [detR_cyc2 x0 w0 X W]; exact e3

/-- a triangle with vertices in the big triangle lies in it -/
theorem tri_sub_big {K Bx Bw x0 w0 x1 w1 x2 w2 X W : ℝ} (hD : 0 < detR x0 w0 x1 w1 x2 w2)
    (hX : TriR x0 w0 x1 w1 x2 w2 X W) (h0 : TriR 0 0 K 0 Bx Bw x0 w0) (h1 : TriR 0 0 K 0 Bx Bw x1 w1)
    (h2 : TriR 0 0 K 0 Bx Bw x2 w2) : TriR 0 0 K 0 Bx Bw X W := by
  refine ⟨?_, ?_, ?_⟩
  · rw [detR_cyc1 X W]
    exact bary_nonneg hD hX (by rw [← detR_cyc1]; exact h0.1) (by rw [← detR_cyc1]; exact h1.1)
      (by rw [← detR_cyc1]; exact h2.1)
  · rw [detR_cyc2 0 0 X W Bx Bw]
    exact bary_nonneg hD hX (by rw [← detR_cyc2]; exact h0.2.1) (by rw [← detR_cyc2]; exact h1.2.1)
      (by rw [← detR_cyc2]; exact h2.2.1)
  · exact bary_nonneg hD hX h0.2.2 h1.2.2 h2.2.2

theorem fan_cover {sC sR sQ sA lC lR lQ lA : ℝ} (hC : 0 < lC) (hR : 0 < lR) (hQ : 0 < lQ) (hA : 0 < lA)
    (h : lC * sC + lR * sR + lQ * sQ + lA * sA = 0) :
    (0 ≤ sC ∧ sR ≤ 0) ∨ (0 < sR ∧ sQ ≤ 0) ∨ (0 ≤ sQ ∧ sA ≤ 0) ∨ (0 ≤ sA ∧ sC ≤ 0) := by
  rcases lt_or_ge 0 sR with h1 | h1
  · rcases le_or_gt sQ 0 with h2 | h2
    · exact Or.inr (Or.inl ⟨h1, h2⟩)
    · rcases le_or_gt sA 0 with h3 | h3
      · exact Or.inr (Or.inr (Or.inl ⟨h2.le, h3⟩))
      · rcases le_or_gt sC 0 with h4 | h4
        · exact Or.inr (Or.inr (Or.inr ⟨h3.le, h4⟩))
        · exfalso
          have := mul_pos hC h4; have := mul_pos hR h1; have := mul_pos hQ h2; have := mul_pos hA h3
          linarith
  · rcases le_or_gt 0 sC with h2 | h2
    · exact Or.inl ⟨h2, h1⟩
    · rcases le_or_gt 0 sA with h3 | h3
      · exact Or.inr (Or.inr (Or.inr ⟨h3, h2.le⟩))
      · rcases le_or_gt 0 sQ with h4 | h4
        · exact Or.inr (Or.inr (Or.inl ⟨h4, h3.le⟩))
        · exfalso
          have := mul_neg_of_pos_of_neg hC h2; have := mul_nonpos_of_nonneg_of_nonpos hR.le h1
          have := mul_neg_of_pos_of_neg hQ h4; have := mul_neg_of_pos_of_neg hA h3
          linarith

theorem ne01 {x0 w0 x1 w1 x2 w2 : ℝ} (h : 0 < detR x0 w0 x1 w1 x2 w2) : x0 ≠ x1 ∨ w0 ≠ w1 := by
  by_contra hc
  push_neg at hc
  obtain ⟨e1, e2⟩ := hc
  rw [e1, e2] at h
  simp [detR] at h

theorem ne12 {x0 w0 x1 w1 x2 w2 : ℝ} (h : 0 < detR x0 w0 x1 w1 x2 w2) : x1 ≠ x2 ∨ w1 ≠ w2 := by
  by_contra hc
  push_neg at hc
  obtain ⟨e1, e2⟩ := hc
  rw [e1, e2] at h
  simp [detR] at h

theorem ne02 {x0 w0 x1 w1 x2 w2 : ℝ} (h : 0 < detR x0 w0 x1 w1 x2 w2) : x0 ≠ x2 ∨ w0 ≠ w2 := by
  by_contra hc
  push_neg at hc
  obtain ⟨e1, e2⟩ := hc
  rw [e1, e2] at h
  simp [detR] at h

set_option hygiene false in
macro "ids" : tactic => `(tactic| (simp only [detR, hQx, hQw, hTx, hTw, hRx, hRw, hSx, hSw]; ring))

set_option maxHeartbeats 4000000 in
theorem assemble {Rt : Tri} {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) {n1 n2 n3 n4 n5 n6 : ℕ}
    (K Bx Bw Px Pw θ1 θ2 τ ρ Qx Qw Tx Tw Rx Rw Sx Sw : ℝ)
    (hQx : Qx = θ1 * Bx) (hQw : Qw = θ1 * Bw) (hTx : Tx = θ2 * Bx) (hTw : Tw = θ2 * Bw)
    (hRx : Rx = K + τ * (Bx - K)) (hRw : Rw = τ * Bw)
    (hSx : Sx = Px + ρ * (Rx - Px)) (hSw : Sw = Pw + ρ * (Rw - Pw))
    (hK : 0 < K) (hθ1 : 0 < θ1) (hθ12 : θ1 < θ2) (hθ2 : θ2 < 1) (hτ0 : 0 < τ) (hτ1 : τ < 1)
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hBlue : Dis Rt (CS α β (TriR 0 0 K 0 Px Pw)) n1)
    (hPink : Dis Rt (CS α β (TriR K 0 Rx Rw Px Pw)) n2)
    (hGreen : Dis Rt (CS α β (TriR 0 0 Px Pw Qx Qw)) n3)
    (hYellow : Dis Rt (CS α β (TriR Px Pw Sx Sw Qx Qw)) n4)
    (hTop : Dis Rt (CS α β (TriR Tx Tw Rx Rw Bx Bw)) n5)
    (hOr : Dis Rt (CS α β (fun X W => 0 ≤ detR Qx Qw Sx Sw X W ∧ 0 ≤ detR Sx Sw Rx Rw X W ∧
      0 ≤ detR Rx Rw Tx Tw X W ∧ 0 ≤ detR Tx Tw Qx Qw X W)) n6)
    (dBig : 0 < detR 0 0 K 0 Bx Bw)
    (dBlue : 0 < detR 0 0 K 0 Px Pw) (dPink : 0 < detR K 0 Rx Rw Px Pw)
    (dGreen : 0 < detR 0 0 Px Pw Qx Qw) (dYellow : 0 < detR Px Pw Sx Sw Qx Qw)
    (dTop : 0 < detR Tx Tw Rx Rw Bx Bw) (dO1 : 0 < detR Qx Qw Sx Sw Rx Rw)
    (dO2 : 0 < detR Qx Qw Rx Rw Tx Tw)
    (hP : TriR 0 0 K 0 Bx Bw Px Pw)
    (hF6A : detR Tx Tw Rx Rw 0 0 ≤ 0) (hF6C : detR Tx Tw Rx Rw K 0 ≤ 0)
    (hF6P : detR Tx Tw Rx Rw Px Pw ≤ 0) (hF6Q : detR Tx Tw Rx Rw Qx Qw ≤ 0)
    (hF5A : detR Qx Qw Sx Sw 0 0 ≤ 0) (hF5C : detR Qx Qw Sx Sw K 0 ≤ 0)
    (hF5P : detR Qx Qw Sx Sw Px Pw ≤ 0)
    (hF4C : detR Px Pw Rx Rw K 0 ≤ 0)
    (hPQS : detR Px Pw Qx Qw Sx Sw ≤ 0) (hPQA : 0 ≤ detR Px Pw Qx Qw 0 0)
    (hF4Q : 0 ≤ detR Px Pw Rx Rw Qx Qw) (hF4A : 0 ≤ detR Px Pw Rx Rw 0 0)
    (hAPS : 0 ≤ detR 0 0 Px Pw Sx Sw)
    (lC lR lQ lA : ℝ) (hlC : 0 < lC) (hlR : 0 < lR) (hlQ : 0 < lQ) (hlA : 0 < lA)
    (hspx : lC * (K - Px) + lR * (Rx - Px) + lQ * (Qx - Px) + lA * (0 - Px) = 0)
    (hspw : lC * (0 - Pw) + lR * (Rw - Pw) + lQ * (Qw - Pw) + lA * (0 - Pw) = 0) :
    Dis Rt (CS α β (TriR 0 0 K 0 Bx Bw)) (n1 + n2 + n3 + n4 + n5 + n6) := by
  have hBg := dBig
  -- vertex memberships in the big triangle
  have bigA : TriR 0 0 K 0 Bx Bw 0 0 := by
    refine ⟨?_, ?_, ?_⟩ <;> simp only [detR] at dBig ⊢ <;> nlinarith [dBig]
  have bigC : TriR 0 0 K 0 Bx Bw K 0 := by
    refine ⟨?_, ?_, ?_⟩ <;> simp only [detR] at dBig ⊢ <;> nlinarith [dBig]
  have bigB : TriR 0 0 K 0 Bx Bw Bx Bw := by
    refine ⟨?_, ?_, ?_⟩ <;> simp only [detR] at dBig ⊢ <;> nlinarith [dBig]
  have bigQ : TriR 0 0 K 0 Bx Bw Qx Qw := by
    refine ⟨?_, ?_, ?_⟩
    · have e : detR Qx Qw K 0 Bx Bw = (1 - θ1) * detR 0 0 K 0 Bx Bw := by ids
      rw [e]; exact mul_nonneg (by linarith) dBig.le
    · have e : detR 0 0 Qx Qw Bx Bw = 0 := by ids
      rw [e]
    · have e : detR 0 0 K 0 Qx Qw = θ1 * detR 0 0 K 0 Bx Bw := by ids
      rw [e]; exact mul_nonneg hθ1.le dBig.le
  have bigT : TriR 0 0 K 0 Bx Bw Tx Tw := by
    refine ⟨?_, ?_, ?_⟩
    · have e : detR Tx Tw K 0 Bx Bw = (1 - θ2) * detR 0 0 K 0 Bx Bw := by ids
      rw [e]; exact mul_nonneg (by linarith) dBig.le
    · have e : detR 0 0 Tx Tw Bx Bw = 0 := by ids
      rw [e]
    · have e : detR 0 0 K 0 Tx Tw = θ2 * detR 0 0 K 0 Bx Bw := by ids
      rw [e]; exact mul_nonneg (by linarith) dBig.le
  have bigR : TriR 0 0 K 0 Bx Bw Rx Rw := by
    refine ⟨?_, ?_, ?_⟩
    · have e : detR Rx Rw K 0 Bx Bw = 0 := by ids
      rw [e]
    · have e : detR 0 0 Rx Rw Bx Bw = (1 - τ) * detR 0 0 K 0 Bx Bw := by ids
      rw [e]; exact mul_nonneg (by linarith) dBig.le
    · have e : detR 0 0 K 0 Rx Rw = τ * detR 0 0 K 0 Bx Bw := by ids
      rw [e]; exact mul_nonneg hτ0.le dBig.le
  have bigS : TriR 0 0 K 0 Bx Bw Sx Sw := by
    obtain ⟨p1, p2, p3⟩ := hP
    obtain ⟨r1, r2, r3⟩ := bigR
    refine ⟨?_, ?_, ?_⟩
    · have e : detR Sx Sw K 0 Bx Bw = (1 - ρ) * detR Px Pw K 0 Bx Bw + ρ * detR Rx Rw K 0 Bx Bw := by ids
      rw [e]; nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 - ρ) p1, mul_nonneg hρ0.le r1]
    · have e : detR 0 0 Sx Sw Bx Bw = (1 - ρ) * detR 0 0 Px Pw Bx Bw + ρ * detR 0 0 Rx Rw Bx Bw := by ids
      rw [e]; nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 - ρ) p2, mul_nonneg hρ0.le r2]
    · have e : detR 0 0 K 0 Sx Sw = (1 - ρ) * detR 0 0 K 0 Px Pw + ρ * detR 0 0 K 0 Rx Rw := by ids
      rw [e]; nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 - ρ) p3, mul_nonneg hρ0.le r3]
  have lnR_eq : ∀ px pw qx qw X W : ℝ, lnR px pw qx qw X W = detR px pw qx qw X W := fun _ _ _ _ _ _ => rfl
  have cs_congr : ∀ {p q : ℝ → ℝ → Prop}, (∀ X W, p X W ↔ q X W) → CS α β p = CS α β q := by
    intro p q h
    ext z
    exact h _ _
  -- the fan around P
  have hFan : ∀ X W, ((TriR 0 0 K 0 Bx Bw X W ∧ detR Tx Tw Rx Rw X W ≤ 0) ∧
      (detR Qx Qw Sx Sw X W ≤ 0 ∨ detR Px Pw Rx Rw X W ≤ 0)) →
      (TriR 0 0 K 0 Px Pw X W ∨ (TriR K 0 Rx Rw Px Pw X W ∨
        (TriR Px Pw Sx Sw Qx Qw X W ∨ TriR 0 0 Px Pw Qx Qw X W))) := by
    rintro X W ⟨⟨⟨b1, b2, b3⟩, hF6⟩, hdis⟩
    have hsp : lC * detR Px Pw K 0 X W + lR * detR Px Pw Rx Rw X W + lQ * detR Px Pw Qx Qw X W
        + lA * detR Px Pw 0 0 X W = 0 := by
      simp only [detR]
      linear_combination (W - Pw) * hspx - (X - Px) * hspw
    rcases fan_cover hlC hlR hlQ hlA hsp with ⟨hc, hr⟩ | ⟨hr, hq⟩ | ⟨hq, ha⟩ | ⟨ha, hc⟩
    · -- pink
      right; left
      have e1 : detR X W Rx Rw Px Pw = - detR Px Pw Rx Rw X W := by simp only [detR]; ring
      have e2 : detR K 0 X W Px Pw = detR Px Pw K 0 X W := by simp only [detR]; ring
      have e3 : detR K 0 Rx Rw X W = τ * detR K 0 Bx Bw X W := by ids
      have e4 : detR X W K 0 Bx Bw = detR K 0 Bx Bw X W := by simp only [detR]; ring
      refine ⟨by linarith, by linarith, ?_⟩
      rw [e3]; exact mul_nonneg hτ0.le (by linarith)
    · -- yellow
      right; right; left
      have h5 : detR Qx Qw Sx Sw X W ≤ 0 := by
        rcases hdis with h | h
        · exact h
        · linarith
      have e1 : detR X W Sx Sw Qx Qw = - detR Qx Qw Sx Sw X W := by simp only [detR]; ring
      have e2 : detR Px Pw X W Qx Qw = - detR Px Pw Qx Qw X W := by simp only [detR]; ring
      have e3 : detR Px Pw Sx Sw X W = ρ * detR Px Pw Rx Rw X W := by ids
      refine ⟨by linarith, by linarith, ?_⟩
      rw [e3]; exact mul_nonneg hρ0.le hr.le
    · -- green
      right; right; right
      have e1 : detR X W Px Pw Qx Qw = detR Px Pw Qx Qw X W := by simp only [detR]; ring
      have e2 : detR 0 0 X W Qx Qw = θ1 * detR 0 0 X W Bx Bw := by ids
      have e3 : detR 0 0 Px Pw X W = - detR Px Pw 0 0 X W := by simp only [detR]; ring
      refine ⟨by linarith, ?_, by linarith⟩
      rw [e2]; exact mul_nonneg hθ1.le b2
    · -- blue
      left
      have e1 : detR X W K 0 Px Pw = - detR Px Pw K 0 X W := by simp only [detR]; ring
      have e2 : detR 0 0 X W Px Pw = detR Px Pw 0 0 X W := by simp only [detR]; ring
      exact ⟨by linarith, by linarith, b3⟩
  -- the pieces lie in the pentagon
  have hPieces : ∀ X W, (TriR 0 0 K 0 Px Pw X W ∨ (TriR K 0 Rx Rw Px Pw X W ∨
        (TriR Px Pw Sx Sw Qx Qw X W ∨ TriR 0 0 Px Pw Qx Qw X W))) →
      ((TriR 0 0 K 0 Bx Bw X W ∧ detR Tx Tw Rx Rw X W ≤ 0) ∧
      (detR Qx Qw Sx Sw X W ≤ 0 ∨ detR Px Pw Rx Rw X W ≤ 0)) := by
    have z1 : ∀ a b c d : ℝ, detR a b c d c d = 0 := fun a b c d => by simp only [detR]; ring
    have z2 : ∀ a b c d : ℝ, detR a b c d a b = 0 := fun a b c d => by simp only [detR]; ring
    have hF6S : detR Tx Tw Rx Rw Sx Sw ≤ 0 := by
      have e : detR Tx Tw Rx Rw Sx Sw = (1 - ρ) * detR Tx Tw Rx Rw Px Pw := by ids
      rw [e]; exact mul_nonpos_of_nonneg_of_nonpos (by linarith) hF6P
    rintro X W (h | h | h | h)
    · exact ⟨⟨tri_sub_big dBlue h bigA bigC hP, bary_nonpos dBlue h hF6A hF6C hF6P⟩,
        Or.inl (bary_nonpos dBlue h hF5A hF5C hF5P)⟩
    · exact ⟨⟨tri_sub_big dPink h bigC bigR hP, bary_nonpos dPink h hF6C (z1 _ _ _ _).le hF6P⟩,
        Or.inr (bary_nonpos dPink h hF4C (z1 _ _ _ _).le (z2 _ _ _ _).le)⟩
    · exact ⟨⟨tri_sub_big dYellow h hP bigS bigQ, bary_nonpos dYellow h hF6P hF6S hF6Q⟩,
        Or.inl (bary_nonpos dYellow h hF5P (z1 _ _ _ _).le (z2 _ _ _ _).le)⟩
    · exact ⟨⟨tri_sub_big dGreen h bigA hP bigQ, bary_nonpos dGreen h hF6A hF6P hF6Q⟩,
        Or.inl (bary_nonpos dGreen h hF5A hF5P (z2 _ _ _ _).le)⟩
  have zz1 : ∀ a b c d : ℝ, detR a b c d c d = 0 := fun a b c d => by simp only [detR]; ring
  have zz2 : ∀ a b c d : ℝ, detR a b c d a b = 0 := fun a b c d => by simp only [detR]; ring
  -- the quadrilateral
  have hQuadIff : ∀ X W, ((TriR 0 0 K 0 Bx Bw X W ∧ detR Tx Tw Rx Rw X W ≤ 0)) ↔
      ((0 ≤ detR Qx Qw Sx Sw X W ∧ 0 ≤ detR Sx Sw Rx Rw X W ∧ 0 ≤ detR Rx Rw Tx Tw X W ∧
        0 ≤ detR Tx Tw Qx Qw X W) ∨
      ((TriR 0 0 K 0 Bx Bw X W ∧ detR Tx Tw Rx Rw X W ≤ 0) ∧
      (detR Qx Qw Sx Sw X W ≤ 0 ∨ detR Px Pw Rx Rw X W ≤ 0))) := by
    intro X W
    constructor
    · rintro ⟨hBg, hF6⟩
      by_cases h : 0 ≤ detR Qx Qw Sx Sw X W ∧ 0 ≤ detR Px Pw Rx Rw X W
      · left
        have e2 : detR Sx Sw Rx Rw X W = (1 - ρ) * detR Px Pw Rx Rw X W := by ids
        have e3 : detR Rx Rw Tx Tw X W = - detR Tx Tw Rx Rw X W := by simp only [detR]; ring
        have e4 : detR Tx Tw Qx Qw X W = (θ2 - θ1) * detR 0 0 X W Bx Bw := by ids
        refine ⟨h.1, ?_, by linarith, ?_⟩
        · rw [e2]; exact mul_nonneg (by linarith) h.2
        · rw [e4]; exact mul_nonneg (by linarith) hBg.2.1
      · right
        refine ⟨⟨hBg, hF6⟩, ?_⟩
        rcases not_and_or.mp h with h | h
        · exact Or.inl (not_le.mp h).le
        · exact Or.inr (not_le.mp h).le
    · rintro (⟨o1, o2, o3, o4⟩ | ⟨hq, _⟩)
      · refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
        · rw [detR_cyc1 X W K 0 Bx Bw]
          exact quad_nonneg dO1 dO2 ⟨o1, o2, o3, o4⟩ (by rw [← detR_cyc1]; exact bigQ.1)
            (by rw [← detR_cyc1]; exact bigS.1) (by rw [← detR_cyc1]; exact bigR.1)
            (by rw [← detR_cyc1]; exact bigT.1)
        · rw [detR_cyc2 0 0 X W Bx Bw]
          exact quad_nonneg dO1 dO2 ⟨o1, o2, o3, o4⟩ (by rw [← detR_cyc2]; exact bigQ.2.1)
            (by rw [← detR_cyc2]; exact bigS.2.1) (by rw [← detR_cyc2]; exact bigR.2.1)
            (by rw [← detR_cyc2]; exact bigT.2.1)
        · exact quad_nonneg dO1 dO2 ⟨o1, o2, o3, o4⟩ bigQ.2.2 bigS.2.2 bigR.2.2 bigT.2.2
        · have e3 : detR Tx Tw Rx Rw X W = - detR Rx Rw Tx Tw X W := by simp only [detR]; ring
          rw [e3]; linarith
      · exact hq
  have hBigIff : ∀ X W, TriR 0 0 K 0 Bx Bw X W ↔
      (((TriR 0 0 K 0 Bx Bw X W ∧ detR Tx Tw Rx Rw X W ≤ 0)) ∨ TriR Tx Tw Rx Rw Bx Bw X W) := by
    intro X W
    constructor
    · intro hBg
      rcases le_total (detR Tx Tw Rx Rw X W) 0 with h | h
      · exact Or.inl ⟨hBg, h⟩
      · right
        obtain ⟨b1, b2, b3⟩ := hBg
        have e1 : detR X W Rx Rw Bx Bw = (1 - τ) * detR X W K 0 Bx Bw := by ids
        have e2 : detR Tx Tw X W Bx Bw = (1 - θ2) * detR 0 0 X W Bx Bw := by ids
        refine ⟨?_, ?_, h⟩
        · rw [e1]; exact mul_nonneg (by linarith) b1
        · rw [e2]; exact mul_nonneg (by linarith) b2
    · rintro (⟨h, _⟩ | h)
      · exact h
      · exact tri_sub_big dTop h bigT bigR bigB
  -- gluing
  have step1 := glueR hα hβ hYellow hGreen Px Pw Qx Qw (ne12 dGreen)
    (fun X W h => by
      rw [lnR_eq]; exact bary_nonpos dYellow h (zz2 _ _ _ _).le hPQS (zz1 _ _ _ _).le)
    (fun X W h => by
      rw [lnR_eq]; exact bary_nonneg dGreen h hPQA (zz2 _ _ _ _).ge (zz1 _ _ _ _).ge)
  have step2 := glueR hα hβ hPink step1 Px Pw Rx Rw ((ne12 dPink).imp Ne.symm Ne.symm)
    (fun X W h => by
      rw [lnR_eq]; exact bary_nonpos dPink h hF4C (zz1 _ _ _ _).le (zz2 _ _ _ _).le)
    (fun X W h => by
      rw [lnR_eq]
      rcases h with h | h
      · refine bary_nonneg dYellow h (zz2 _ _ _ _).ge ?_ hF4Q
        have e : detR Px Pw Rx Rw Sx Sw = 0 := by ids
        rw [e]
      · exact bary_nonneg dGreen h hF4A (zz2 _ _ _ _).ge hF4Q)
  have step3 := glueQ hα hβ hBlue step2 0 0 Px Pw Px Pw K 0 (ne02 dBlue)
    ((ne12 dBlue).imp Ne.symm Ne.symm)
    (fun X W h => by
      rw [lnR_eq]
      have e : detR 0 0 Px Pw K 0 = - detR 0 0 K 0 Px Pw := by simp only [detR]; ring
      exact bary_nonpos dBlue h (zz2 _ _ _ _).le (by rw [e]; linarith) (zz1 _ _ _ _).le)
    (fun X W h => by
      rw [lnR_eq]
      have e : detR Px Pw K 0 0 0 = - detR 0 0 K 0 Px Pw := by simp only [detR]; ring
      exact bary_nonpos dBlue h (by rw [e]; linarith) (zz1 _ _ _ _).le (zz2 _ _ _ _).le)
    (fun X W h => by
      rw [lnR_eq, lnR_eq]
      rcases h with h | h | h
      · right
        have e : detR Px Pw K 0 Rx Rw = detR K 0 Rx Rw Px Pw := by simp only [detR]; ring
        exact bary_nonneg dPink h (zz1 _ _ _ _).ge (by rw [e]; exact dPink.le) (zz2 _ _ _ _).ge
      · left
        exact bary_nonneg dYellow h (zz1 _ _ _ _).ge hAPS dGreen.le
      · left
        have e : detR 0 0 Px Pw 0 0 = 0 := by simp only [detR]; ring
        exact bary_nonneg dGreen h (by rw [e]) (zz1 _ _ _ _).ge dGreen.le)
  have hPentDis := step3.congr (cs_congr (fun X W => ⟨hPieces X W, hFan X W⟩)) rfl
  have step5 := glueQ hα hβ hOr hPentDis Sx Sw Qx Qw Rx Rw Px Pw (ne12 dYellow)
    (ne12 dPink)
    (fun X W h => by
      rw [lnR_eq]
      have e : detR Sx Sw Qx Qw X W = - detR Qx Qw Sx Sw X W := by simp only [detR]; ring
      rw [e]; linarith [h.1])
    (fun X W h => by
      rw [lnR_eq]
      have e : detR Rx Rw Px Pw X W = - detR Px Pw Rx Rw X W := by simp only [detR]; ring
      have e2 : detR Sx Sw Rx Rw X W = (1 - ρ) * detR Px Pw Rx Rw X W := by ids
      have h2 := h.2.1
      rw [e2] at h2
      rw [e]
      by_contra hc
      push_neg at hc
      have := mul_pos (by linarith : (0:ℝ) < 1 - ρ) hc
      nlinarith)
    (fun X W h => by
      rw [lnR_eq, lnR_eq]
      have e : detR Sx Sw Qx Qw X W = - detR Qx Qw Sx Sw X W := by simp only [detR]; ring
      have e' : detR Rx Rw Px Pw X W = - detR Px Pw Rx Rw X W := by simp only [detR]; ring
      rcases h.2 with h5 | h4
      · left; rw [e]; linarith
      · right; rw [e']; linarith)
  have hQuadDis := step5.congr (cs_congr (fun X W => (hQuadIff X W).symm)) rfl
  have step6 := glueR hα hβ hQuadDis hTop Tx Tw Rx Rw (ne01 dTop)
    (fun X W h => by rw [lnR_eq]; exact h.2)
    (fun X W h => by rw [lnR_eq]; exact h.2.2)
  exact step6.congr (cs_congr (fun X W => (hBigIff X W).symm)) (by omega)

end Erdos634.BeesonT14Abs
