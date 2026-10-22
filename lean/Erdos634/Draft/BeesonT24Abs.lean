import Erdos634.Draft.BeesonT14Abs

/-!
# Beeson Theorem 24, general parameters: the abstract assembly

Isosceles triangle `A = (0,0)`, `C = (Y,0)`, `B` assembled from the seven pieces of the proof of Theorem 24:
green `APG`, blue `AGK`, yellow `KLB`, red `PQG`, pink `KVL`, parallelograms `PCRQ` and `GRLV`.  Abstract chart
coordinates, hypotheses = the determinant signs of the layout; conclusion = the `Dis` of the big triangle.
Credit Beeson (arXiv 1206.2229), Beeson-Zhang, Zhang (arXiv 2512.22696), Laczkovich.  UNAUDITED.
-/

namespace Erdos634.BeesonT24Abs

open Erdos634.Geometry Erdos634.CertCoord Erdos634.CertGeom Erdos634.RegionDissection
  Erdos634.GlueCut Erdos634.SssCongruent Erdos634.ZhangL1 Erdos634.ZhangPara
  Erdos634.ZhangSporadic Erdos634.ZhangThm4 Erdos634.BeesonT14Chart Erdos634.BeesonT14Abs

def PcrqP (Px Y Rx Rw Qx Qw : ℝ) (X W : ℝ) : Prop :=
  0 ≤ detR Px 0 Y 0 X W ∧ 0 ≤ detR Y 0 Rx Rw X W ∧ 0 ≤ detR Rx Rw Qx Qw X W ∧
    0 ≤ detR Qx Qw Px 0 X W

def GrlvP (Gx Gw Rx Rw Lx Lw Vx Vw : ℝ) (X W : ℝ) : Prop :=
  0 ≤ detR Gx Gw Rx Rw X W ∧ 0 ≤ detR Rx Rw Lx Lw X W ∧ 0 ≤ detR Lx Lw Vx Vw X W ∧
    0 ≤ detR Vx Vw Gx Gw X W

set_option hygiene false in
macro "ids24" : tactic => `(tactic| (simp only [detR, hKx, hKw, hRx, hRw, hLx, hLw, hQx, hQw, hVx, hVw]; ring))

set_option maxHeartbeats 8000000 in
theorem assemble24 {Rt : Tri} {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) {n1 n2 n3 n4 n5 n6 n7 : ℕ}
    (Y Bx Bw Px Gx Gw κ τ σ ν ζ Kx Kw Lx Lw Rx Rw Qx Qw Vx Vw : ℝ)
    (hKx : Kx = κ * Bx) (hKw : Kw = κ * Bw)
    (hRx : Rx = Y + τ * (Bx - Y)) (hRw : Rw = τ * Bw)
    (hLx : Lx = Y + σ * (Bx - Y)) (hLw : Lw = σ * Bw)
    (hQx : Qx = Gx + ν * (Rx - Gx)) (hQw : Qw = Gw + ν * (Rw - Gw))
    (hVx : Vx = Gx + ζ * (Kx - Gx)) (hVw : Vw = Gw + ζ * (Kw - Gw))
    (hY : 0 < Y) (hPx0 : 0 < Px) (hPxY : Px < Y) (hκ0 : 0 < κ) (hκ1 : κ < 1) (hτ0 : 0 < τ)
    (hτσ : τ < σ) (hσ1 : σ < 1) (hν0 : 0 < ν) (hν1 : ν < 1) (hζ0 : 0 < ζ) (hζ1 : ζ < 1)
    (hGreen : Dis Rt (CS α β (TriR 0 0 Px 0 Gx Gw)) n1)
    (hBlue : Dis Rt (CS α β (TriR 0 0 Gx Gw Kx Kw)) n2)
    (hYellow : Dis Rt (CS α β (TriR Kx Kw Lx Lw Bx Bw)) n3)
    (hRed : Dis Rt (CS α β (TriR Px 0 Qx Qw Gx Gw)) n4)
    (hPink : Dis Rt (CS α β (TriR Kx Kw Vx Vw Lx Lw)) n5)
    (hPcrq : Dis Rt (CS α β (PcrqP Px Y Rx Rw Qx Qw)) n6)
    (hGrlv : Dis Rt (CS α β (GrlvP Gx Gw Rx Rw Lx Lw Vx Vw)) n7)
    (dBig : 0 < detR 0 0 Y 0 Bx Bw)
    (dGreen : 0 < detR 0 0 Px 0 Gx Gw) (dBlue : 0 < detR 0 0 Gx Gw Kx Kw)
    (dYellow : 0 < detR Kx Kw Lx Lw Bx Bw) (dRed : 0 < detR Px 0 Qx Qw Gx Gw)
    (dPink : 0 < detR Kx Kw Vx Vw Lx Lw) (dP1 : 0 < detR Px 0 Y 0 Rx Rw)
    (dP2 : 0 < detR Px 0 Rx Rw Qx Qw) (dG1 : 0 < detR Gx Gw Rx Rw Lx Lw)
    (dG2 : 0 < detR Gx Gw Lx Lw Vx Vw)
    (hGbig : TriR 0 0 Y 0 Bx Bw Gx Gw)
    (lP lR lK lA : ℝ) (hlP : 0 < lP) (hlR : 0 < lR) (hlK : 0 < lK) (hlA : 0 < lA)
    (hspx : lP * (Px - Gx) + lR * (Rx - Gx) + lK * (Kx - Gx) + lA * (0 - Gx) = 0)
    (hspw : lP * (0 - Gw) + lR * (Rw - Gw) + lK * (Kw - Gw) + lA * (0 - Gw) = 0)
    (fRP : detR Gx Gw Rx Rw Px 0 ≤ 0) (fRC : detR Gx Gw Rx Rw Y 0 ≤ 0)
    (fRK : 0 ≤ detR Gx Gw Rx Rw Kx Kw) (fRL : 0 ≤ detR Gx Gw Rx Rw Lx Lw)
    (fKP : detR Gx Gw Kx Kw Px 0 ≤ 0) (fKC : detR Gx Gw Kx Kw Y 0 ≤ 0)
    (fKR : detR Gx Gw Kx Kw Rx Rw ≤ 0) (fKL : detR Gx Gw Kx Kw Lx Lw ≤ 0)
    (fPC : 0 ≤ detR Gx Gw Px 0 Y 0) (fPR : 0 ≤ detR Gx Gw Px 0 Rx Rw)
    (fPK : 0 ≤ detR Gx Gw Px 0 Kx Kw) (fPL : 0 ≤ detR Gx Gw Px 0 Lx Lw)
    (fLA : detR Kx Kw Lx Lw 0 0 ≤ 0) (fLP : detR Kx Kw Lx Lw Px 0 ≤ 0)
    (fLC : detR Kx Kw Lx Lw Y 0 ≤ 0) (fLG : detR Kx Kw Lx Lw Gx Gw ≤ 0)
    (fLQ : detR Kx Kw Lx Lw Qx Qw ≤ 0) (fLR : detR Kx Kw Lx Lw Rx Rw ≤ 0)
    (fLV : detR Kx Kw Lx Lw Vx Vw ≤ 0) :
    Dis Rt (CS α β (TriR 0 0 Y 0 Bx Bw)) (n1 + n2 + n3 + n4 + n5 + n6 + n7) := by
  have eBig : detR 0 0 Y 0 Bx Bw = Y * Bw := by simp only [detR]; ring
  have hBwp : 0 < Bw := by
    by_contra hc
    push_neg at hc
    have := mul_nonpos_of_nonneg_of_nonpos hY.le hc
    rw [eBig] at dBig
    linarith
  have zz1 : ∀ a b c d : ℝ, detR a b c d c d = 0 := fun a b c d => by simp only [detR]; ring
  have zz2 : ∀ a b c d : ℝ, detR a b c d a b = 0 := fun a b c d => by simp only [detR]; ring
  have lnR_eq : ∀ px pw qx qw X W : ℝ, lnR px pw qx qw X W = detR px pw qx qw X W :=
    fun _ _ _ _ _ _ => rfl
  have cs_congr : ∀ {p q : ℝ → ℝ → Prop}, (∀ X W, p X W ↔ q X W) → CS α β p = CS α β q := by
    intro p q h
    ext z
    exact h _ _
  -- vertex memberships in the big triangle
  have bigA : TriR 0 0 Y 0 Bx Bw 0 0 :=
    ⟨dBig.le, (by simp only [detR]; ring : detR 0 0 0 0 Bx Bw = 0).ge,
      (by simp only [detR]; ring : detR 0 0 Y 0 0 0 = 0).ge⟩
  have bigC : TriR 0 0 Y 0 Bx Bw Y 0 :=
    ⟨(by simp only [detR]; ring : detR Y 0 Y 0 Bx Bw = 0).ge, dBig.le,
      (by simp only [detR]; ring : detR 0 0 Y 0 Y 0 = 0).ge⟩
  have bigB : TriR 0 0 Y 0 Bx Bw Bx Bw :=
    ⟨(by simp only [detR]; ring : detR Bx Bw Y 0 Bx Bw = 0).ge,
      (by simp only [detR]; ring : detR 0 0 Bx Bw Bx Bw = 0).ge, dBig.le⟩
  have bigP : TriR 0 0 Y 0 Bx Bw Px 0 := by
    refine ⟨?_, ?_, ?_⟩
    · have e : detR Px 0 Y 0 Bx Bw = (Y - Px) * Bw := by simp only [detR]; ring
      rw [e]; exact mul_nonneg (by linarith) hBwp.le
    · have e : detR 0 0 Px 0 Bx Bw = Px * Bw := by simp only [detR]; ring
      rw [e]; exact mul_nonneg hPx0.le hBwp.le
    · exact (by simp only [detR]; ring : detR 0 0 Y 0 Px 0 = 0).ge
  have bigK : TriR 0 0 Y 0 Bx Bw Kx Kw := by
    refine ⟨?_, ?_, ?_⟩
    · have e : detR Kx Kw Y 0 Bx Bw = (1 - κ) * detR 0 0 Y 0 Bx Bw := by ids24
      rw [e]; exact mul_nonneg (by linarith) dBig.le
    · have e : detR 0 0 Kx Kw Bx Bw = 0 := by ids24
      rw [e]
    · have e : detR 0 0 Y 0 Kx Kw = κ * detR 0 0 Y 0 Bx Bw := by ids24
      rw [e]; exact mul_nonneg hκ0.le dBig.le
  have bigR : TriR 0 0 Y 0 Bx Bw Rx Rw := by
    refine ⟨?_, ?_, ?_⟩
    · have e : detR Rx Rw Y 0 Bx Bw = 0 := by ids24
      rw [e]
    · have e : detR 0 0 Rx Rw Bx Bw = (1 - τ) * detR 0 0 Y 0 Bx Bw := by ids24
      rw [e]; exact mul_nonneg (by linarith) dBig.le
    · have e : detR 0 0 Y 0 Rx Rw = τ * detR 0 0 Y 0 Bx Bw := by ids24
      rw [e]; exact mul_nonneg hτ0.le dBig.le
  have bigL : TriR 0 0 Y 0 Bx Bw Lx Lw := by
    refine ⟨?_, ?_, ?_⟩
    · have e : detR Lx Lw Y 0 Bx Bw = 0 := by ids24
      rw [e]
    · have e : detR 0 0 Lx Lw Bx Bw = (1 - σ) * detR 0 0 Y 0 Bx Bw := by ids24
      rw [e]; exact mul_nonneg (by linarith) dBig.le
    · have e : detR 0 0 Y 0 Lx Lw = σ * detR 0 0 Y 0 Bx Bw := by ids24
      rw [e]; exact mul_nonneg (by linarith) dBig.le
  have bigQ : TriR 0 0 Y 0 Bx Bw Qx Qw := by
    obtain ⟨p1, p2, p3⟩ := hGbig
    obtain ⟨r1, r2, r3⟩ := bigR
    refine ⟨?_, ?_, ?_⟩
    · have e : detR Qx Qw Y 0 Bx Bw = (1 - ν) * detR Gx Gw Y 0 Bx Bw + ν * detR Rx Rw Y 0 Bx Bw := by ids24
      rw [e]; exact add_nonneg (mul_nonneg (by linarith) p1) (mul_nonneg hν0.le r1)
    · have e : detR 0 0 Qx Qw Bx Bw = (1 - ν) * detR 0 0 Gx Gw Bx Bw + ν * detR 0 0 Rx Rw Bx Bw := by ids24
      rw [e]; exact add_nonneg (mul_nonneg (by linarith) p2) (mul_nonneg hν0.le r2)
    · have e : detR 0 0 Y 0 Qx Qw = (1 - ν) * detR 0 0 Y 0 Gx Gw + ν * detR 0 0 Y 0 Rx Rw := by ids24
      rw [e]; exact add_nonneg (mul_nonneg (by linarith) p3) (mul_nonneg hν0.le r3)
  have bigV : TriR 0 0 Y 0 Bx Bw Vx Vw := by
    obtain ⟨p1, p2, p3⟩ := hGbig
    obtain ⟨r1, r2, r3⟩ := bigK
    refine ⟨?_, ?_, ?_⟩
    · have e : detR Vx Vw Y 0 Bx Bw = (1 - ζ) * detR Gx Gw Y 0 Bx Bw + ζ * detR Kx Kw Y 0 Bx Bw := by ids24
      rw [e]; exact add_nonneg (mul_nonneg (by linarith) p1) (mul_nonneg hζ0.le r1)
    · have e : detR 0 0 Vx Vw Bx Bw = (1 - ζ) * detR 0 0 Gx Gw Bx Bw + ζ * detR 0 0 Kx Kw Bx Bw := by ids24
      rw [e]; exact add_nonneg (mul_nonneg (by linarith) p2) (mul_nonneg hζ0.le r2)
    · have e : detR 0 0 Y 0 Vx Vw = (1 - ζ) * detR 0 0 Y 0 Gx Gw + ζ * detR 0 0 Y 0 Kx Kw := by ids24
      rw [e]; exact add_nonneg (mul_nonneg (by linarith) p3) (mul_nonneg hζ0.le r3)
  -- the fan around G
  have hFan : ∀ X W, (TriR 0 0 Y 0 Bx Bw X W ∧ detR Kx Kw Lx Lw X W ≤ 0) →
      (TriR 0 0 Px 0 Gx Gw X W ∨ (((PcrqP Px Y Rx Rw Qx Qw X W ∨ TriR Px 0 Qx Qw Gx Gw X W) ∨
        (GrlvP Gx Gw Rx Rw Lx Lw Vx Vw X W ∨ TriR Kx Kw Vx Vw Lx Lw X W)) ∨
        TriR 0 0 Gx Gw Kx Kw X W)) := by
    rintro X W ⟨⟨b1, b2, b3⟩, hKL⟩
    have hW : 0 ≤ W := by
      have e : detR 0 0 Y 0 X W = Y * W := by simp only [detR]; ring
      rw [e] at b3
      by_contra hc
      push_neg at hc
      have := mul_neg_of_pos_of_neg hY hc
      linarith
    have b1' : 0 ≤ detR Y 0 Bx Bw X W := by
      have e : detR X W Y 0 Bx Bw = detR Y 0 Bx Bw X W := by simp only [detR]; ring
      rw [e] at b1; exact b1
    have hsp : lP * detR Gx Gw Px 0 X W + lR * detR Gx Gw Rx Rw X W +
        lK * detR Gx Gw Kx Kw X W + lA * detR Gx Gw 0 0 X W = 0 := by
      simp only [detR]
      linear_combination (W - Gw) * hspx - (X - Gx) * hspw
    rcases fan_cover hlP hlR hlK hlA hsp with ⟨hc, hr⟩ | ⟨hr, hq⟩ | ⟨hq, ha⟩ | ⟨ha, hc⟩
    · rcases le_total (detR Px 0 Qx Qw X W) 0 with hpq | hpq
      · right; left; left; left
        have e1 : detR Px 0 Y 0 X W = (Y - Px) * W := by simp only [detR]; ring
        have e2 : detR Y 0 Rx Rw X W = τ * detR Y 0 Bx Bw X W := by ids24
        have e3 : detR Rx Rw Qx Qw X W = -((1 - ν) * detR Gx Gw Rx Rw X W) := by ids24
        have e4 : detR Qx Qw Px 0 X W = - detR Px 0 Qx Qw X W := by simp only [detR]; ring
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [e1]; exact mul_nonneg (by linarith) hW
        · rw [e2]; exact mul_nonneg hτ0.le b1'
        · rw [e3]
          have := mul_nonneg (by linarith : (0:ℝ) ≤ 1 - ν) (neg_nonneg.mpr hr)
          linarith
        · rw [e4]; linarith
      · right; left; left; right
        have e1 : detR X W Qx Qw Gx Gw = -(ν * detR Gx Gw Rx Rw X W) := by ids24
        have e2 : detR Px 0 X W Gx Gw = detR Gx Gw Px 0 X W := by simp only [detR]; ring
        refine ⟨?_, ?_, hpq⟩
        · rw [e1]
          have := mul_nonneg hν0.le (neg_nonneg.mpr hr)
          linarith
        · rw [e2]; exact hc
    · rcases le_total (detR Vx Vw Lx Lw X W) 0 with hvl | hvl
      · right; left; right; left
        have e1 : detR Rx Rw Lx Lw X W = (σ - τ) * detR Y 0 Bx Bw X W := by ids24
        have e2 : detR Lx Lw Vx Vw X W = - detR Vx Vw Lx Lw X W := by simp only [detR]; ring
        have e3 : detR Vx Vw Gx Gw X W = -(ζ * detR Gx Gw Kx Kw X W) := by ids24
        refine ⟨hr.le, ?_, ?_, ?_⟩
        · rw [e1]; exact mul_nonneg (by linarith) b1'
        · rw [e2]; linarith
        · rw [e3]
          have := mul_nonneg hζ0.le (neg_nonneg.mpr hq)
          linarith
      · right; left; right; right
        have e1 : detR X W Vx Vw Lx Lw = detR Vx Vw Lx Lw X W := by simp only [detR]; ring
        have e2 : detR Kx Kw X W Lx Lw = - detR Kx Kw Lx Lw X W := by simp only [detR]; ring
        have e3 : detR Kx Kw Vx Vw X W = -((1 - ζ) * detR Gx Gw Kx Kw X W) := by ids24
        refine ⟨?_, ?_, ?_⟩
        · rw [e1]; exact hvl
        · rw [e2]; linarith
        · rw [e3]
          have := mul_nonneg (by linarith : (0:ℝ) ≤ 1 - ζ) (neg_nonneg.mpr hq)
          linarith
    · right; right
      have e1 : detR X W Gx Gw Kx Kw = detR Gx Gw Kx Kw X W := by simp only [detR]; ring
      have e2 : detR 0 0 X W Kx Kw = κ * detR 0 0 X W Bx Bw := by ids24
      have e3 : detR 0 0 Gx Gw X W = - detR Gx Gw 0 0 X W := by simp only [detR]; ring
      refine ⟨?_, ?_, ?_⟩
      · rw [e1]; exact hq
      · rw [e2]; exact mul_nonneg hκ0.le b2
      · rw [e3]; linarith
    · left
      have e1 : detR X W Px 0 Gx Gw = - detR Gx Gw Px 0 X W := by simp only [detR]; ring
      have e2 : detR 0 0 X W Gx Gw = detR Gx Gw 0 0 X W := by simp only [detR]; ring
      have e3 : detR 0 0 Px 0 X W = Px * W := by simp only [detR]; ring
      refine ⟨?_, ?_, ?_⟩
      · rw [e1]; linarith
      · rw [e2]; exact ha
      · rw [e3]; exact mul_nonneg hPx0.le hW
  -- quadrilaterals lie in the big triangle and below KL
  have pcrq_big : ∀ X W, PcrqP Px Y Rx Rw Qx Qw X W → TriR 0 0 Y 0 Bx Bw X W := by
    intro X W h
    refine ⟨?_, ?_, ?_⟩
    · rw [detR_cyc1 X W Y 0 Bx Bw]
      exact quad_nonneg dP1 dP2 h (by rw [← detR_cyc1]; exact bigP.1)
        (by rw [← detR_cyc1]; exact bigC.1) (by rw [← detR_cyc1]; exact bigR.1)
        (by rw [← detR_cyc1]; exact bigQ.1)
    · rw [detR_cyc2 0 0 X W Bx Bw]
      exact quad_nonneg dP1 dP2 h (by rw [← detR_cyc2]; exact bigP.2.1)
        (by rw [← detR_cyc2]; exact bigC.2.1) (by rw [← detR_cyc2]; exact bigR.2.1)
        (by rw [← detR_cyc2]; exact bigQ.2.1)
    · exact quad_nonneg dP1 dP2 h bigP.2.2 bigC.2.2 bigR.2.2 bigQ.2.2
  have grlv_big : ∀ X W, GrlvP Gx Gw Rx Rw Lx Lw Vx Vw X W → TriR 0 0 Y 0 Bx Bw X W := by
    intro X W h
    obtain ⟨g1, g2, g3⟩ := hGbig
    refine ⟨?_, ?_, ?_⟩
    · rw [detR_cyc1 X W Y 0 Bx Bw]
      exact quad_nonneg dG1 dG2 h (by rw [← detR_cyc1]; exact g1)
        (by rw [← detR_cyc1]; exact bigR.1) (by rw [← detR_cyc1]; exact bigL.1)
        (by rw [← detR_cyc1]; exact bigV.1)
    · rw [detR_cyc2 0 0 X W Bx Bw]
      exact quad_nonneg dG1 dG2 h (by rw [← detR_cyc2]; exact g2)
        (by rw [← detR_cyc2]; exact bigR.2.1) (by rw [← detR_cyc2]; exact bigL.2.1)
        (by rw [← detR_cyc2]; exact bigV.2.1)
    · exact quad_nonneg dG1 dG2 h g3 bigR.2.2 bigL.2.2 bigV.2.2
  have pcrq_kl : ∀ X W, PcrqP Px Y Rx Rw Qx Qw X W → detR Kx Kw Lx Lw X W ≤ 0 := by
    intro X W h
    have := quad_nonneg (ux := Lx) (uw := Lw) (vx := Kx) (vw := Kw) dP1 dP2 h
      (by rw [detR_swap]; linarith) (by rw [detR_swap]; linarith) (by rw [detR_swap]; linarith)
      (by rw [detR_swap]; linarith)
    rw [detR_swap] at this
    linarith
  have grlv_kl : ∀ X W, GrlvP Gx Gw Rx Rw Lx Lw Vx Vw X W → detR Kx Kw Lx Lw X W ≤ 0 := by
    intro X W h
    have := quad_nonneg (ux := Lx) (uw := Lw) (vx := Kx) (vw := Kw) dG1 dG2 h
      (by rw [detR_swap]; linarith) (by rw [detR_swap]; linarith) (by rw [detR_swap, zz1]; simp)
      (by rw [detR_swap]; linarith)
    rw [detR_swap] at this
    linarith
  -- the pieces lie in the quadrilateral
  have hPieces : ∀ X W, (TriR 0 0 Px 0 Gx Gw X W ∨ (((PcrqP Px Y Rx Rw Qx Qw X W ∨
        TriR Px 0 Qx Qw Gx Gw X W) ∨ (GrlvP Gx Gw Rx Rw Lx Lw Vx Vw X W ∨
        TriR Kx Kw Vx Vw Lx Lw X W)) ∨ TriR 0 0 Gx Gw Kx Kw X W)) →
      (TriR 0 0 Y 0 Bx Bw X W ∧ detR Kx Kw Lx Lw X W ≤ 0) := by
    rintro X W (h | ((h | h) | (h | h)) | h)
    · exact ⟨tri_sub_big dGreen h bigA bigP hGbig, bary_nonpos dGreen h fLA fLP fLG⟩
    · exact ⟨pcrq_big X W h, pcrq_kl X W h⟩
    · exact ⟨tri_sub_big dRed h bigP bigQ hGbig, bary_nonpos dRed h fLP fLQ fLG⟩
    · exact ⟨grlv_big X W h, grlv_kl X W h⟩
    · exact ⟨tri_sub_big dPink h bigK bigV bigL,
        bary_nonpos dPink h (zz2 _ _ _ _).le fLV (zz1 _ _ _ _).le⟩
    · exact ⟨tri_sub_big dBlue h bigA hGbig bigK, bary_nonpos dBlue h fLA fLG (zz2 _ _ _ _).le⟩
  have hBigIff : ∀ X W, TriR 0 0 Y 0 Bx Bw X W ↔
      ((TriR 0 0 Px 0 Gx Gw X W ∨ (((PcrqP Px Y Rx Rw Qx Qw X W ∨ TriR Px 0 Qx Qw Gx Gw X W) ∨
        (GrlvP Gx Gw Rx Rw Lx Lw Vx Vw X W ∨ TriR Kx Kw Vx Vw Lx Lw X W)) ∨
        TriR 0 0 Gx Gw Kx Kw X W)) ∨ TriR Kx Kw Lx Lw Bx Bw X W) := by
    intro X W
    constructor
    · intro hBg
      rcases le_total (detR Kx Kw Lx Lw X W) 0 with h | h
      · left; exact hFan X W ⟨hBg, h⟩
      · right
        obtain ⟨b1, b2, b3⟩ := hBg
        have b1' : 0 ≤ detR Y 0 Bx Bw X W := by
          have e : detR X W Y 0 Bx Bw = detR Y 0 Bx Bw X W := by simp only [detR]; ring
          rw [e] at b1; exact b1
        have e1 : detR X W Lx Lw Bx Bw = (1 - σ) * detR Y 0 Bx Bw X W := by ids24
        have e2 : detR Kx Kw X W Bx Bw = (1 - κ) * detR 0 0 X W Bx Bw := by ids24
        refine ⟨?_, ?_, h⟩
        · rw [e1]; exact mul_nonneg (by linarith) b1'
        · rw [e2]; exact mul_nonneg (by linarith) b2
    · rintro (h | h)
      · exact (hPieces X W h).1
      · exact tri_sub_big dYellow h bigK bigL bigB
  -- gluing
  have J1 := glueR hα hβ hPcrq hRed Px 0 Qx Qw (ne01 dRed)
    (fun X W h => by
      have e : detR Px 0 Qx Qw X W = - detR Qx Qw Px 0 X W := by simp only [detR]; ring
      rw [lnR_eq, e]; linarith [h.2.2.2])
    (fun X W h => by rw [lnR_eq]; exact h.2.2)
  have J2 := glueR hα hβ hGrlv hPink Vx Vw Lx Lw (ne12 dPink)
    (fun X W h => by
      have e : detR Vx Vw Lx Lw X W = - detR Lx Lw Vx Vw X W := by simp only [detR]; ring
      rw [lnR_eq, e]; linarith [h.2.2.1])
    (fun X W h => by
      have e : detR Vx Vw Lx Lw X W = detR X W Vx Vw Lx Lw := by simp only [detR]; ring
      rw [lnR_eq, e]; exact h.1)
  have hGRne : Gx ≠ Rx ∨ Gw ≠ Rw := ne01 dG1
  have J3 := glueR hα hβ J1 J2 Gx Gw Rx Rw hGRne
    (fun X W h => by
      rw [lnR_eq]
      rcases h with h | h
      · have := quad_nonneg (ux := Rx) (uw := Rw) (vx := Gx) (vw := Gw) dP1 dP2 h
          (by rw [detR_swap]; linarith) (by rw [detR_swap]; linarith)
          (by rw [detR_swap, zz1]; simp)
          (by
            have e : detR Gx Gw Rx Rw Qx Qw = 0 := by ids24
            rw [detR_swap, e]; simp)
        rw [detR_swap] at this; linarith
      · refine bary_nonpos dRed h fRP ?_ (zz2 _ _ _ _).le
        have e : detR Gx Gw Rx Rw Qx Qw = 0 := by ids24
        rw [e])
    (fun X W h => by
      rw [lnR_eq]
      have eV : detR Gx Gw Rx Rw Vx Vw = ζ * detR Gx Gw Rx Rw Kx Kw := by ids24
      rcases h with h | h
      · exact quad_nonneg dG1 dG2 h (zz2 _ _ _ _).ge (zz1 _ _ _ _).ge fRL
          (by rw [eV]; exact mul_nonneg hζ0.le fRK)
      · exact bary_nonneg dPink h fRK (by rw [eV]; exact mul_nonneg hζ0.le fRK) fRL)
  have J4 := glueR hα hβ J3 hBlue Gx Gw Kx Kw (ne12 dBlue)
    (fun X W h => by
      rw [lnR_eq]
      have eQ : detR Gx Gw Kx Kw Qx Qw = ν * detR Gx Gw Kx Kw Rx Rw := by ids24
      have eV : detR Gx Gw Kx Kw Vx Vw = 0 := by ids24
      rcases h with (h | h) | (h | h)
      · have := quad_nonneg (ux := Kx) (uw := Kw) (vx := Gx) (vw := Gw) dP1 dP2 h
          (by rw [detR_swap]; linarith) (by rw [detR_swap]; linarith)
          (by rw [detR_swap]; linarith)
          (by rw [detR_swap, eQ]; nlinarith [mul_nonneg hν0.le (neg_nonneg.mpr fKR)])
        rw [detR_swap] at this; linarith
      · refine bary_nonpos dRed h fKP ?_ (zz2 _ _ _ _).le
        rw [eQ]; exact mul_nonpos_of_nonneg_of_nonpos hν0.le fKR
      · have := quad_nonneg (ux := Kx) (uw := Kw) (vx := Gx) (vw := Gw) dG1 dG2 h
          (by rw [detR_swap, zz2]; simp) (by rw [detR_swap]; linarith)
          (by rw [detR_swap]; linarith) (by rw [detR_swap, eV]; simp)
        rw [detR_swap] at this; linarith
      · exact bary_nonpos dPink h (zz1 _ _ _ _).le (by rw [eV]) fKL)
    (fun X W h => by
      rw [lnR_eq]
      have e : detR Gx Gw Kx Kw 0 0 = detR 0 0 Gx Gw Kx Kw := by simp only [detR]; ring
      exact bary_nonneg dBlue h (by rw [e]; exact dBlue.le) (zz2 _ _ _ _).ge (zz1 _ _ _ _).ge)
  have J5 := glueQ hα hβ hGreen J4 Gx Gw Px 0 0 0 Gx Gw ((ne12 dGreen).imp Ne.symm Ne.symm)
    (ne02 dGreen)
    (fun X W h => by
      rw [lnR_eq]
      have e : detR Gx Gw Px 0 0 0 = - detR 0 0 Px 0 Gx Gw := by simp only [detR]; ring
      exact bary_nonpos dGreen h (by rw [e]; linarith) (zz1 _ _ _ _).le (zz2 _ _ _ _).le)
    (fun X W h => by
      rw [lnR_eq]
      have e : detR 0 0 Gx Gw Px 0 = - detR 0 0 Px 0 Gx Gw := by simp only [detR]; ring
      exact bary_nonpos dGreen h (zz2 _ _ _ _).le (by rw [e]; linarith) (zz1 _ _ _ _).le)
    (fun X W h => by
      rw [lnR_eq, lnR_eq]
      have eQ : detR Gx Gw Px 0 Qx Qw = ν * detR Gx Gw Px 0 Rx Rw := by ids24
      have eV : detR Gx Gw Px 0 Vx Vw = ζ * detR Gx Gw Px 0 Kx Kw := by ids24
      rcases h with ((h | h) | (h | h)) | h
      · left
        exact quad_nonneg dP1 dP2 h (zz1 _ _ _ _).ge fPC fPR
          (by rw [eQ]; exact mul_nonneg hν0.le fPR)
      · left
        exact bary_nonneg dRed h (zz1 _ _ _ _).ge (by rw [eQ]; exact mul_nonneg hν0.le fPR)
          (zz2 _ _ _ _).ge
      · left
        exact quad_nonneg dG1 dG2 h (zz2 _ _ _ _).ge fPR fPL (by rw [eV]; exact mul_nonneg hζ0.le fPK)
      · left
        exact bary_nonneg dPink h fPK (by rw [eV]; exact mul_nonneg hζ0.le fPK) fPL
      · right
        have e : detR 0 0 Gx Gw Kx Kw = detR 0 0 Gx Gw Kx Kw := rfl
        exact bary_nonneg dBlue h (zz2 _ _ _ _).ge (zz1 _ _ _ _).ge dBlue.le)
  have J6 := glueR hα hβ J5 hYellow Kx Kw Lx Lw (ne01 dYellow)
    (fun X W h => by
      rw [lnR_eq]
      rcases h with h | (((h | h) | (h | h)) | h)
      · exact bary_nonpos dGreen h fLA fLP fLG
      · exact pcrq_kl X W h
      · exact bary_nonpos dRed h fLP fLQ fLG
      · exact grlv_kl X W h
      · exact bary_nonpos dPink h (zz2 _ _ _ _).le fLV (zz1 _ _ _ _).le
      · exact bary_nonpos dBlue h fLA fLG (zz2 _ _ _ _).le)
    (fun X W h => by rw [lnR_eq]; exact h.2.2)
  exact J6.congr (cs_congr (fun X W => (hBigIff X W).symm)) (by omega)

end Erdos634.BeesonT24Abs
