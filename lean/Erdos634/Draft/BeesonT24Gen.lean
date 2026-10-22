import Erdos634.Draft.BeesonT14Gen
import Erdos634.Draft.BeesonT24Strips

/-!
# Beeson Theorem 24 (arXiv 1206.2229v4) in GENERAL parameters

Tile `(a,b,c) = (g s t, g (s^2-t^2), g s^2)`, `mu = lam a b (a+c)`, `p = a c rho`, ...  Chart
`(X, W) -> (X / (2 s), rt0 W / (2 s))`, `rt0^2 = 4 s^2 - t^2`; all vertices are polynomial in `(g,s,t,lam,rho)`.
Hypotheses: `r > 0`, `h > 0` (the polynomials `F3`, `F4` below).
Credit Beeson (arXiv 1206.2229), Beeson-Zhang, Zhang (arXiv 2512.22696), Laczkovich.  UNAUDITED.
-/

namespace Erdos634.BeesonT24Gen

open Erdos634.Geometry Erdos634.CertCoord Erdos634.CertGeom Erdos634.RegionDissection
  Erdos634.GlueCut Erdos634.SssCongruent Erdos634.ZhangL1 Erdos634.ZhangPara
  Erdos634.ZhangSporadic Erdos634.ZhangThm4 Erdos634.BeesonT14Chart Erdos634.BeesonT14Abs
  Erdos634.BeesonT14Piece Erdos634.BeesonT14Grid Erdos634.BeesonT14Gen Erdos634.BeesonT24Abs
  Erdos634.BeesonT24Strips

section defs
noncomputable def TYx (g s t lam rho : ℝ) : ℝ := 2*g^4*lam*s^4*t^2*(s - t)*(s + t)^2
noncomputable def TBx (g s t lam rho : ℝ) : ℝ := g^4*lam*s^4*t^2*(s - t)*(s + t)^2
noncomputable def TBw (g s t lam rho : ℝ) : ℝ := g^4*lam*s^4*t*(s - t)*(s + t)^2
noncomputable def TPx (g s t lam rho : ℝ) : ℝ := 2*g^3*rho*s^6*t
noncomputable def TGx (g s t lam rho : ℝ) : ℝ := g^3*rho*s^2*t*(s - t)*(s + t)*(2*s^2 - t^2)
noncomputable def TGw (g s t lam rho : ℝ) : ℝ := g^3*rho*s^2*t^2*(s - t)*(s + t)
noncomputable def TKx (g s t lam rho : ℝ) : ℝ := g^3*rho*s^4*t*(s - t)*(s + t)
noncomputable def TKw (g s t lam rho : ℝ) : ℝ := g^3*rho*s^4*(s - t)*(s + t)
noncomputable def TLx (g s t lam rho : ℝ) : ℝ := g^3*s^4*t*(2*g*lam*s^3*t + 2*g*lam*s^2*t^2 - g*lam*s*t^3 - g*lam*t^4 - rho*s^2)
noncomputable def TLw (g s t lam rho : ℝ) : ℝ := g^3*s^4*(-g*lam*s*t^3 - g*lam*t^4 + rho*s^2)
noncomputable def TQx (g s t lam rho : ℝ) : ℝ := g^3*rho*s^2*t*(2*s^4 - s^2*t^2 + t^4)
noncomputable def TQw (g s t lam rho : ℝ) : ℝ := g^3*rho*s^2*t^2*(s - t)*(s + t)
noncomputable def TRx (g s t lam rho : ℝ) : ℝ := g^3*s^2*t^2*(s - t)*(s + t)*(2*g*lam*s^3 + 2*g*lam*s^2*t - rho*t)
noncomputable def TRw (g s t lam rho : ℝ) : ℝ := g^3*rho*s^2*t^2*(s - t)*(s + t)
noncomputable def TVx (g s t lam rho : ℝ) : ℝ := g^3*s^4*t*(g*lam*s*t^3 + g*lam*t^4 + rho*s^2 - 2*rho*t^2)
noncomputable def TVw (g s t lam rho : ℝ) : ℝ := g^3*s^4*(-g*lam*s*t^3 - g*lam*t^4 + rho*s^2)
noncomputable def Tkap (g s t lam rho : ℝ) : ℝ := rho / (g * lam * t * (s + t))
noncomputable def Ttau (g s t lam rho : ℝ) : ℝ := rho * t / (g * lam * s ^ 2 * (s + t))
noncomputable def Tsig (g s t lam rho : ℝ) : ℝ :=
  (-g * lam * s * t ^ 3 - g * lam * t ^ 4 + rho * s ^ 2) / (g * lam * t * (s - t) * (s + t) ^ 2)
noncomputable def Tnu (g s t lam rho : ℝ) : ℝ :=
  rho * t ^ 2 / ((s - t) * (s + t) * (g * lam * s * t + g * lam * t ^ 2 - rho))
noncomputable def Tzet (g s t lam rho : ℝ) : ℝ :=
  (-g * lam * s ^ 3 * t ^ 3 - g * lam * s ^ 2 * t ^ 4 + rho * s ^ 4 - rho * s ^ 2 * t ^ 2 + rho * t ^ 4) /
    (rho * (s - t) ^ 2 * (s + t) ^ 2)
end defs

structure Par24 (g s t lam rho rt0 : ℝ) : Prop where
  hg : 0 < g
  hs : 0 < s
  ht : 0 < t
  hlam : 0 < lam
  hrho : 0 < rho
  hts : t < s
  hrt : 0 < rt0
  hD : rt0 * rt0 = 4 * s ^ 2 - t ^ 2
  hF3 : 0 < g*lam*s^3*t + g*lam*s^2*t^2 - g*lam*s*t^3 - g*lam*t^4 - rho*s^2
  hF4 : 0 < -g*lam*s^3*t^3 - g*lam*s^2*t^4 + rho*s^4 - rho*s^2*t^2 + rho*t^4

theorem atoms24 {g s t lam rho rt0 : ℝ} (P : Par24 g s t lam rho rt0) :
    0 < g*lam*s*t + g*lam*t^2 - rho ∧ 0 < -g*lam*s*t^3 - g*lam*t^4 + rho*s^2 ∧ 0 < g*lam*s^3*t + g*lam*s^2*t^2 - g*lam*s*t^3 - g*lam*t^4 - rho*s^2 ∧ 0 < -g*lam*s^3*t^3 - g*lam*s^2*t^4 + rho*s^4 - rho*s^2*t^2 + rho*t^4 ∧
      0 < g*lam*s^5 + g*lam*s^4*t - 3*g*lam*s^3*t^2 - 3*g*lam*s^2*t^3 + g*lam*s*t^4 + g*lam*t^5 + rho*s^2*t ∧ 0 < s^2 - 2*t^2 ∧ 0 < s^6 - 3*s^4*t^2 + 2*s^2*t^4 - t^6 := by
  obtain ⟨hg, hs, ht, hlam, hrho, hts, hrt, hD, hF3, hF4⟩ := P
  have hst : 0 < s - t := by linarith
  have hX : 0 < g * lam * t * (s + t) := by positivity
  have hN : 0 < s ^ 4 - s ^ 2 * t ^ 2 + t ^ 4 := by
    nlinarith [sq_nonneg (s ^ 2 - t ^ 2), mul_pos (pow_pos hs 2) (pow_pos ht 2)]
  have hH0 : 0 < s^6 - 3*s^4*t^2 + 2*s^2*t^4 - t^6 := by
    have e : g * lam * t * (s + t) * (s^6 - 3*s^4*t^2 + 2*s^2*t^4 - t^6) =
        (g*lam*s^3*t + g*lam*s^2*t^2 - g*lam*s*t^3 - g*lam*t^4 - rho*s^2) * (s ^ 4 - s ^ 2 * t ^ 2 + t ^ 4) + s ^ 2 * (-g*lam*s^3*t^3 - g*lam*s^2*t^4 + rho*s^4 - rho*s^2*t^2 + rho*t^4) := by ring
    have : 0 < (g*lam*s^3*t + g*lam*s^2*t^2 - g*lam*s*t^3 - g*lam*t^4 - rho*s^2) * (s ^ 4 - s ^ 2 * t ^ 2 + t ^ 4) + s ^ 2 * (-g*lam*s^3*t^3 - g*lam*s^2*t^4 + rho*s^4 - rho*s^2*t^2 + rho*t^4) := by positivity
    rw [← e] at this
    exact (mul_pos_iff_of_pos_left hX).mp this
  have hq : 0 < s^2 - 2*t^2 := by
    by_contra hq
    push_neg at hq
    have hw1 : 0 < s ^ 2 - t ^ 2 := by nlinarith
    have hw : s ^ 2 - t ^ 2 ≤ t ^ 2 := by linarith
    have key : s^6 - 3*s^4*t^2 + 2*s^2*t^4 - t^6 = -(t ^ 2) ^ 3 - (t ^ 2) ^ 2 * (s ^ 2 - t ^ 2) + (s ^ 2 - t ^ 2) ^ 3 := by ring
    have hv : 0 < t ^ 2 := by positivity
    nlinarith [mul_nonneg (sub_nonneg.mpr hw) (sq_nonneg (s ^ 2 - t ^ 2)),
      mul_nonneg (mul_nonneg hv.le hw1.le) (sub_nonneg.mpr hw), pow_pos hv 3]
  have hF1 : 0 < g*lam*s*t + g*lam*t^2 - rho := by
    have e : s ^ 2 * (g*lam*s*t + g*lam*t^2 - rho) = (g*lam*s^3*t + g*lam*s^2*t^2 - g*lam*s*t^3 - g*lam*t^4 - rho*s^2) + g * lam * t * (s + t) * t ^ 2 := by ring
    have : 0 < (g*lam*s^3*t + g*lam*s^2*t^2 - g*lam*s*t^3 - g*lam*t^4 - rho*s^2) + g * lam * t * (s + t) * t ^ 2 := by positivity
    rw [← e] at this
    exact (mul_pos_iff_of_pos_left (by positivity)).mp this
  have hF2 : 0 < -g*lam*s*t^3 - g*lam*t^4 + rho*s^2 := by
    have e : s ^ 2 * (-g*lam*s*t^3 - g*lam*t^4 + rho*s^2) = (-g*lam*s^3*t^3 - g*lam*s^2*t^4 + rho*s^4 - rho*s^2*t^2 + rho*t^4) + rho * t ^ 2 * (s ^ 2 - t ^ 2) := by ring
    have : 0 < (-g*lam*s^3*t^3 - g*lam*s^2*t^4 + rho*s^4 - rho*s^2*t^2 + rho*t^4) + rho * t ^ 2 * (s ^ 2 - t ^ 2) := by
      have : 0 < s ^ 2 - t ^ 2 := by nlinarith
      positivity
    rw [← e] at this
    exact (mul_pos_iff_of_pos_left (by positivity)).mp this
  have hF6 : 0 < g*lam*s^5 + g*lam*s^4*t - 3*g*lam*s^3*t^2 - 3*g*lam*s^2*t^3 + g*lam*s*t^4 + g*lam*t^5 + rho*s^2*t := by
    have e : t * (s ^ 4 - s ^ 2 * t ^ 2 + t ^ 4) * (g*lam*s^5 + g*lam*s^4*t - 3*g*lam*s^3*t^2 - 3*g*lam*s^2*t^3 + g*lam*s*t^4 + g*lam*t^5 + rho*s^2*t) =
        g * lam * t * (s + t) * (s ^ 2 - t ^ 2) ^ 4 + s ^ 2 * t ^ 2 * (-g*lam*s^3*t^3 - g*lam*s^2*t^4 + rho*s^4 - rho*s^2*t^2 + rho*t^4) := by ring
    have : 0 < g * lam * t * (s + t) * (s ^ 2 - t ^ 2) ^ 4 + s ^ 2 * t ^ 2 * (-g*lam*s^3*t^3 - g*lam*s^2*t^4 + rho*s^4 - rho*s^2*t^2 + rho*t^4) := by
      have : 0 < s ^ 2 - t ^ 2 := by nlinarith
      positivity
    rw [← e] at this
    exact (mul_pos_iff_of_pos_left (by positivity)).mp this
  exact ⟨hF1, hF2, hF3, hF4, hF6, hq, hH0⟩

theorem fact24_dBig {g s t lam rho rt0 : ℝ} (P : Par24 g s t lam rho rt0) :
    0 < detR 0 0 (TYx g s t lam rho) 0 (TBx g s t lam rho) (TBw g s t lam rho) := by
  obtain ⟨hF1, hF2, hF3, hF4, hF6, hq, hH0⟩ := atoms24 P
  obtain ⟨hg, hs, ht, hlam, hrho, hts, hrt, hD, _, _⟩ := P
  have h1 : 0 < s - t := by linarith
  have h2 : 0 < s + t := by linarith
  have e : detR 0 0 (TYx g s t lam rho) 0 (TBx g s t lam rho) (TBw g s t lam rho) = 2*lam^2*t^3*g^8*s^8*(s - t)^2*(s + t)^4 := by simp only [detR, TYx, TBx, TBw, TPx, TGx, TGw, TKx, TKw, TLx, TLw, TQx, TQw, TRx, TRw, TVx, TVw]; ring
  rw [e]; positivity

theorem fact24_dGreen {g s t lam rho rt0 : ℝ} (P : Par24 g s t lam rho rt0) :
    0 < detR 0 0 (TPx g s t lam rho) 0 (TGx g s t lam rho) (TGw g s t lam rho) := by
  obtain ⟨hF1, hF2, hF3, hF4, hF6, hq, hH0⟩ := atoms24 P
  obtain ⟨hg, hs, ht, hlam, hrho, hts, hrt, hD, _, _⟩ := P
  have h1 : 0 < s - t := by linarith
  have h2 : 0 < s + t := by linarith
  have e : detR 0 0 (TPx g s t lam rho) 0 (TGx g s t lam rho) (TGw g s t lam rho) = 2*rho^2*t^3*g^6*s^8*(s - t)*(s + t) := by simp only [detR, TYx, TBx, TBw, TPx, TGx, TGw, TKx, TKw, TLx, TLw, TQx, TQw, TRx, TRw, TVx, TVw]; ring
  rw [e]; positivity

theorem fact24_dBlue {g s t lam rho rt0 : ℝ} (P : Par24 g s t lam rho rt0) :
    0 < detR 0 0 (TGx g s t lam rho) (TGw g s t lam rho) (TKx g s t lam rho) (TKw g s t lam rho) := by
  obtain ⟨hF1, hF2, hF3, hF4, hF6, hq, hH0⟩ := atoms24 P
  obtain ⟨hg, hs, ht, hlam, hrho, hts, hrt, hD, _, _⟩ := P
  have h1 : 0 < s - t := by linarith
  have h2 : 0 < s + t := by linarith
  have e : detR 0 0 (TGx g s t lam rho) (TGw g s t lam rho) (TKx g s t lam rho) (TKw g s t lam rho) = 2*t*rho^2*g^6*s^6*(s - t)^3*(s + t)^3 := by simp only [detR, TYx, TBx, TBw, TPx, TGx, TGw, TKx, TKw, TLx, TLw, TQx, TQw, TRx, TRw, TVx, TVw]; ring
  rw [e]; positivity

theorem fact24_dYellow {g s t lam rho rt0 : ℝ} (P : Par24 g s t lam rho rt0) :
    0 < detR (TKx g s t lam rho) (TKw g s t lam rho) (TLx g s t lam rho) (TLw g s t lam rho) (TBx g s t lam rho) (TBw g s t lam rho) := by
  obtain ⟨hF1, hF2, hF3, hF4, hF6, hq, hH0⟩ := atoms24 P
  obtain ⟨hg, hs, ht, hlam, hrho, hts, hrt, hD, _, _⟩ := P
  have h1 : 0 < s - t := by linarith
  have h2 : 0 < s + t := by linarith
  have e : detR (TKx g s t lam rho) (TKw g s t lam rho) (TLx g s t lam rho) (TLw g s t lam rho) (TBx g s t lam rho) (TBw g s t lam rho) = 2*t*g^6*s^10*(s - t)*(s + t)*(g*lam*s*t + g*lam*t^2 - rho)^2 := by simp only [detR, TYx, TBx, TBw, TPx, TGx, TGw, TKx, TKw, TLx, TLw, TQx, TQw, TRx, TRw, TVx, TVw]; ring
  rw [e]; positivity

theorem fact24_dRed {g s t lam rho rt0 : ℝ} (P : Par24 g s t lam rho rt0) :
    0 < detR (TPx g s t lam rho) 0 (TQx g s t lam rho) (TQw g s t lam rho) (TGx g s t lam rho) (TGw g s t lam rho) := by
  obtain ⟨hF1, hF2, hF3, hF4, hF6, hq, hH0⟩ := atoms24 P
  obtain ⟨hg, hs, ht, hlam, hrho, hts, hrt, hD, _, _⟩ := P
  have h1 : 0 < s - t := by linarith
  have h2 : 0 < s + t := by linarith
  have e : detR (TPx g s t lam rho) 0 (TQx g s t lam rho) (TQw g s t lam rho) (TGx g s t lam rho) (TGw g s t lam rho) = 2*rho^2*t^5*g^6*s^6*(s - t)*(s + t) := by simp only [detR, TYx, TBx, TBw, TPx, TGx, TGw, TKx, TKw, TLx, TLw, TQx, TQw, TRx, TRw, TVx, TVw]; ring
  rw [e]; positivity

theorem fact24_dPink {g s t lam rho rt0 : ℝ} (P : Par24 g s t lam rho rt0) :
    0 < detR (TKx g s t lam rho) (TKw g s t lam rho) (TVx g s t lam rho) (TVw g s t lam rho) (TLx g s t lam rho) (TLw g s t lam rho) := by
  obtain ⟨hF1, hF2, hF3, hF4, hF6, hq, hH0⟩ := atoms24 P
  obtain ⟨hg, hs, ht, hlam, hrho, hts, hrt, hD, _, _⟩ := P
  have h1 : 0 < s - t := by linarith
  have h2 : 0 < s + t := by linarith
  have e : detR (TKx g s t lam rho) (TKw g s t lam rho) (TVx g s t lam rho) (TVw g s t lam rho) (TLx g s t lam rho) (TLw g s t lam rho) = 2*t^3*g^6*s^8*(s - t)*(s + t)*(g*lam*s*t + g*lam*t^2 - rho)^2 := by simp only [detR, TYx, TBx, TBw, TPx, TGx, TGw, TKx, TKw, TLx, TLw, TQx, TQw, TRx, TRw, TVx, TVw]; ring
  rw [e]; positivity

theorem fact24_dP1 {g s t lam rho rt0 : ℝ} (P : Par24 g s t lam rho rt0) :
    0 < detR (TPx g s t lam rho) 0 (TYx g s t lam rho) 0 (TRx g s t lam rho) (TRw g s t lam rho) := by
  obtain ⟨hF1, hF2, hF3, hF4, hF6, hq, hH0⟩ := atoms24 P
  obtain ⟨hg, hs, ht, hlam, hrho, hts, hrt, hD, _, _⟩ := P
  have h1 : 0 < s - t := by linarith
  have h2 : 0 < s + t := by linarith
  have e : detR (TPx g s t lam rho) 0 (TYx g s t lam rho) 0 (TRx g s t lam rho) (TRw g s t lam rho) = 2*rho*t^3*g^6*s^6*(s - t)*(s + t)*(g*lam*s^3*t + g*lam*s^2*t^2 - g*lam*s*t^3 - g*lam*t^4 - rho*s^2) := by simp only [detR, TYx, TBx, TBw, TPx, TGx, TGw, TKx, TKw, TLx, TLw, TQx, TQw, TRx, TRw, TVx, TVw]; ring
  rw [e]; positivity

theorem fact24_dP2 {g s t lam rho rt0 : ℝ} (P : Par24 g s t lam rho rt0) :
    0 < detR (TPx g s t lam rho) 0 (TRx g s t lam rho) (TRw g s t lam rho) (TQx g s t lam rho) (TQw g s t lam rho) := by
  obtain ⟨hF1, hF2, hF3, hF4, hF6, hq, hH0⟩ := atoms24 P
  obtain ⟨hg, hs, ht, hlam, hrho, hts, hrt, hD, _, _⟩ := P
  have h1 : 0 < s - t := by linarith
  have h2 : 0 < s + t := by linarith
  have e : detR (TPx g s t lam rho) 0 (TRx g s t lam rho) (TRw g s t lam rho) (TQx g s t lam rho) (TQw g s t lam rho) = 2*rho*t^3*g^6*s^6*(s - t)*(s + t)*(g*lam*s^3*t + g*lam*s^2*t^2 - g*lam*s*t^3 - g*lam*t^4 - rho*s^2) := by simp only [detR, TYx, TBx, TBw, TPx, TGx, TGw, TKx, TKw, TLx, TLw, TQx, TQw, TRx, TRw, TVx, TVw]; ring
  rw [e]; positivity

theorem fact24_dG1 {g s t lam rho rt0 : ℝ} (P : Par24 g s t lam rho rt0) :
    0 < detR (TGx g s t lam rho) (TGw g s t lam rho) (TRx g s t lam rho) (TRw g s t lam rho) (TLx g s t lam rho) (TLw g s t lam rho) := by
  obtain ⟨hF1, hF2, hF3, hF4, hF6, hq, hH0⟩ := atoms24 P
  obtain ⟨hg, hs, ht, hlam, hrho, hts, hrt, hD, _, _⟩ := P
  have h1 : 0 < s - t := by linarith
  have h2 : 0 < s + t := by linarith
  have e : detR (TGx g s t lam rho) (TGw g s t lam rho) (TRx g s t lam rho) (TRw g s t lam rho) (TLx g s t lam rho) (TLw g s t lam rho) = 2*t*g^6*s^6*(s - t)*(s + t)*(g*lam*s*t + g*lam*t^2 - rho)*(-g*lam*s^3*t^3 - g*lam*s^2*t^4 + rho*s^4 - rho*s^2*t^2 + rho*t^4) := by simp only [detR, TYx, TBx, TBw, TPx, TGx, TGw, TKx, TKw, TLx, TLw, TQx, TQw, TRx, TRw, TVx, TVw]; ring
  rw [e]; positivity

theorem fact24_dG2 {g s t lam rho rt0 : ℝ} (P : Par24 g s t lam rho rt0) :
    0 < detR (TGx g s t lam rho) (TGw g s t lam rho) (TLx g s t lam rho) (TLw g s t lam rho) (TVx g s t lam rho) (TVw g s t lam rho) := by
  obtain ⟨hF1, hF2, hF3, hF4, hF6, hq, hH0⟩ := atoms24 P
  obtain ⟨hg, hs, ht, hlam, hrho, hts, hrt, hD, _, _⟩ := P
  have h1 : 0 < s - t := by linarith
  have h2 : 0 < s + t := by linarith
  have e : detR (TGx g s t lam rho) (TGw g s t lam rho) (TLx g s t lam rho) (TLw g s t lam rho) (TVx g s t lam rho) (TVw g s t lam rho) = 2*t*g^6*s^6*(s - t)*(s + t)*(g*lam*s*t + g*lam*t^2 - rho)*(-g*lam*s^3*t^3 - g*lam*s^2*t^4 + rho*s^4 - rho*s^2*t^2 + rho*t^4) := by simp only [detR, TYx, TBx, TBw, TPx, TGx, TGw, TKx, TKw, TLx, TLw, TQx, TQw, TRx, TRw, TVx, TVw]; ring
  rw [e]; positivity

theorem fact24_hG1 {g s t lam rho rt0 : ℝ} (P : Par24 g s t lam rho rt0) :
    0 ≤ detR (TGx g s t lam rho) (TGw g s t lam rho) (TYx g s t lam rho) 0 (TBx g s t lam rho) (TBw g s t lam rho) := by
  obtain ⟨hF1, hF2, hF3, hF4, hF6, hq, hH0⟩ := atoms24 P
  obtain ⟨hg, hs, ht, hlam, hrho, hts, hrt, hD, _, _⟩ := P
  have h1 : 0 < s - t := by linarith
  have h2 : 0 < s + t := by linarith
  have e : detR (TGx g s t lam rho) (TGw g s t lam rho) (TYx g s t lam rho) 0 (TBx g s t lam rho) (TBw g s t lam rho) = 2*lam*t^2*g^7*s^8*(s - t)^2*(s + t)^3*(g*lam*s*t + g*lam*t^2 - rho) := by simp only [detR, TYx, TBx, TBw, TPx, TGx, TGw, TKx, TKw, TLx, TLw, TQx, TQw, TRx, TRw, TVx, TVw]; ring
  rw [e]; positivity

theorem fact24_hG2 {g s t lam rho rt0 : ℝ} (P : Par24 g s t lam rho rt0) :
    0 ≤ detR 0 0 (TGx g s t lam rho) (TGw g s t lam rho) (TBx g s t lam rho) (TBw g s t lam rho) := by
  obtain ⟨hF1, hF2, hF3, hF4, hF6, hq, hH0⟩ := atoms24 P
  obtain ⟨hg, hs, ht, hlam, hrho, hts, hrt, hD, _, _⟩ := P
  have h1 : 0 < s - t := by linarith
  have h2 : 0 < s + t := by linarith
  have e : detR 0 0 (TGx g s t lam rho) (TGw g s t lam rho) (TBx g s t lam rho) (TBw g s t lam rho) = 2*lam*rho*t^2*s^6*g^7*(s - t)^3*(s + t)^4 := by simp only [detR, TYx, TBx, TBw, TPx, TGx, TGw, TKx, TKw, TLx, TLw, TQx, TQw, TRx, TRw, TVx, TVw]; ring
  rw [e]; positivity

theorem fact24_hG3 {g s t lam rho rt0 : ℝ} (P : Par24 g s t lam rho rt0) :
    0 ≤ detR 0 0 (TYx g s t lam rho) 0 (TGx g s t lam rho) (TGw g s t lam rho) := by
  obtain ⟨hF1, hF2, hF3, hF4, hF6, hq, hH0⟩ := atoms24 P
  obtain ⟨hg, hs, ht, hlam, hrho, hts, hrt, hD, _, _⟩ := P
  have h1 : 0 < s - t := by linarith
  have h2 : 0 < s + t := by linarith
  have e : detR 0 0 (TYx g s t lam rho) 0 (TGx g s t lam rho) (TGw g s t lam rho) = 2*lam*rho*t^4*s^6*g^7*(s - t)^2*(s + t)^3 := by simp only [detR, TYx, TBx, TBw, TPx, TGx, TGw, TKx, TKw, TLx, TLw, TQx, TQw, TRx, TRw, TVx, TVw]; ring
  rw [e]; positivity

theorem fact24_fRP {g s t lam rho rt0 : ℝ} (P : Par24 g s t lam rho rt0) :
    detR (TGx g s t lam rho) (TGw g s t lam rho) (TRx g s t lam rho) (TRw g s t lam rho) (TPx g s t lam rho) 0 ≤ 0 := by
  obtain ⟨hF1, hF2, hF3, hF4, hF6, hq, hH0⟩ := atoms24 P
  obtain ⟨hg, hs, ht, hlam, hrho, hts, hrt, hD, _, _⟩ := P
  have h1 : 0 < s - t := by linarith
  have h2 : 0 < s + t := by linarith
  have e : detR (TGx g s t lam rho) (TGw g s t lam rho) (TRx g s t lam rho) (TRw g s t lam rho) (TPx g s t lam rho) 0 = -(2*rho*t^3*g^6*s^6*(s - t)^2*(s + t)^2*(g*lam*s*t + g*lam*t^2 - rho)) := by simp only [detR, TYx, TBx, TBw, TPx, TGx, TGw, TKx, TKw, TLx, TLw, TQx, TQw, TRx, TRw, TVx, TVw]; ring
  rw [e]
  have : 0 < 2*rho*t^3*g^6*s^6*(s - t)^2*(s + t)^2*(g*lam*s*t + g*lam*t^2 - rho) := by positivity
  linarith

theorem fact24_fRC {g s t lam rho rt0 : ℝ} (P : Par24 g s t lam rho rt0) :
    detR (TGx g s t lam rho) (TGw g s t lam rho) (TRx g s t lam rho) (TRw g s t lam rho) (TYx g s t lam rho) 0 ≤ 0 := by
  obtain ⟨hF1, hF2, hF3, hF4, hF6, hq, hH0⟩ := atoms24 P
  obtain ⟨hg, hs, ht, hlam, hrho, hts, hrt, hD, _, _⟩ := P
  have h1 : 0 < s - t := by linarith
  have h2 : 0 < s + t := by linarith
  have e : detR (TGx g s t lam rho) (TGw g s t lam rho) (TRx g s t lam rho) (TRw g s t lam rho) (TYx g s t lam rho) 0 = -(2*rho*t^3*g^6*s^6*(s - t)^2*(s + t)^2*(g*lam*s*t + g*lam*t^2 - rho)) := by simp only [detR, TYx, TBx, TBw, TPx, TGx, TGw, TKx, TKw, TLx, TLw, TQx, TQw, TRx, TRw, TVx, TVw]; ring
  rw [e]
  have : 0 < 2*rho*t^3*g^6*s^6*(s - t)^2*(s + t)^2*(g*lam*s*t + g*lam*t^2 - rho) := by positivity
  linarith

theorem fact24_fRK {g s t lam rho rt0 : ℝ} (P : Par24 g s t lam rho rt0) :
    0 ≤ detR (TGx g s t lam rho) (TGw g s t lam rho) (TRx g s t lam rho) (TRw g s t lam rho) (TKx g s t lam rho) (TKw g s t lam rho) := by
  obtain ⟨hF1, hF2, hF3, hF4, hF6, hq, hH0⟩ := atoms24 P
  obtain ⟨hg, hs, ht, hlam, hrho, hts, hrt, hD, _, _⟩ := P
  have h1 : 0 < s - t := by linarith
  have h2 : 0 < s + t := by linarith
  have e : detR (TGx g s t lam rho) (TGw g s t lam rho) (TRx g s t lam rho) (TRw g s t lam rho) (TKx g s t lam rho) (TKw g s t lam rho) = 2*rho*t*g^6*s^6*(s - t)^3*(s + t)^3*(g*lam*s*t + g*lam*t^2 - rho) := by simp only [detR, TYx, TBx, TBw, TPx, TGx, TGw, TKx, TKw, TLx, TLw, TQx, TQw, TRx, TRw, TVx, TVw]; ring
  rw [e]; positivity

theorem fact24_fRL {g s t lam rho rt0 : ℝ} (P : Par24 g s t lam rho rt0) :
    0 ≤ detR (TGx g s t lam rho) (TGw g s t lam rho) (TRx g s t lam rho) (TRw g s t lam rho) (TLx g s t lam rho) (TLw g s t lam rho) := by
  obtain ⟨hF1, hF2, hF3, hF4, hF6, hq, hH0⟩ := atoms24 P
  obtain ⟨hg, hs, ht, hlam, hrho, hts, hrt, hD, _, _⟩ := P
  have h1 : 0 < s - t := by linarith
  have h2 : 0 < s + t := by linarith
  have e : detR (TGx g s t lam rho) (TGw g s t lam rho) (TRx g s t lam rho) (TRw g s t lam rho) (TLx g s t lam rho) (TLw g s t lam rho) = 2*t*g^6*s^6*(s - t)*(s + t)*(g*lam*s*t + g*lam*t^2 - rho)*(-g*lam*s^3*t^3 - g*lam*s^2*t^4 + rho*s^4 - rho*s^2*t^2 + rho*t^4) := by simp only [detR, TYx, TBx, TBw, TPx, TGx, TGw, TKx, TKw, TLx, TLw, TQx, TQw, TRx, TRw, TVx, TVw]; ring
  rw [e]; positivity

theorem fact24_fKP {g s t lam rho rt0 : ℝ} (P : Par24 g s t lam rho rt0) :
    detR (TGx g s t lam rho) (TGw g s t lam rho) (TKx g s t lam rho) (TKw g s t lam rho) (TPx g s t lam rho) 0 ≤ 0 := by
  obtain ⟨hF1, hF2, hF3, hF4, hF6, hq, hH0⟩ := atoms24 P
  obtain ⟨hg, hs, ht, hlam, hrho, hts, hrt, hD, _, _⟩ := P
  have h1 : 0 < s - t := by linarith
  have h2 : 0 < s + t := by linarith
  have e : detR (TGx g s t lam rho) (TGw g s t lam rho) (TKx g s t lam rho) (TKw g s t lam rho) (TPx g s t lam rho) 0 = -(2*rho^2*t^3*g^6*s^6*(s - t)^2*(s + t)^2) := by simp only [detR, TYx, TBx, TBw, TPx, TGx, TGw, TKx, TKw, TLx, TLw, TQx, TQw, TRx, TRw, TVx, TVw]; ring
  rw [e]
  have : 0 < 2*rho^2*t^3*g^6*s^6*(s - t)^2*(s + t)^2 := by positivity
  linarith

theorem fact24_fKC {g s t lam rho rt0 : ℝ} (P : Par24 g s t lam rho rt0) :
    detR (TGx g s t lam rho) (TGw g s t lam rho) (TKx g s t lam rho) (TKw g s t lam rho) (TYx g s t lam rho) 0 ≤ 0 := by
  obtain ⟨hF1, hF2, hF3, hF4, hF6, hq, hH0⟩ := atoms24 P
  obtain ⟨hg, hs, ht, hlam, hrho, hts, hrt, hD, _, _⟩ := P
  have h1 : 0 < s - t := by linarith
  have h2 : 0 < s + t := by linarith
  have e : detR (TGx g s t lam rho) (TGw g s t lam rho) (TKx g s t lam rho) (TKw g s t lam rho) (TYx g s t lam rho) 0 = -(2*rho*t*g^6*s^6*(s - t)^3*(s + t)^3*(g*lam*s*t + g*lam*t^2 - rho)) := by simp only [detR, TYx, TBx, TBw, TPx, TGx, TGw, TKx, TKw, TLx, TLw, TQx, TQw, TRx, TRw, TVx, TVw]; ring
  rw [e]
  have : 0 < 2*rho*t*g^6*s^6*(s - t)^3*(s + t)^3*(g*lam*s*t + g*lam*t^2 - rho) := by positivity
  linarith

theorem fact24_fKR {g s t lam rho rt0 : ℝ} (P : Par24 g s t lam rho rt0) :
    detR (TGx g s t lam rho) (TGw g s t lam rho) (TKx g s t lam rho) (TKw g s t lam rho) (TRx g s t lam rho) (TRw g s t lam rho) ≤ 0 := by
  obtain ⟨hF1, hF2, hF3, hF4, hF6, hq, hH0⟩ := atoms24 P
  obtain ⟨hg, hs, ht, hlam, hrho, hts, hrt, hD, _, _⟩ := P
  have h1 : 0 < s - t := by linarith
  have h2 : 0 < s + t := by linarith
  have e : detR (TGx g s t lam rho) (TGw g s t lam rho) (TKx g s t lam rho) (TKw g s t lam rho) (TRx g s t lam rho) (TRw g s t lam rho) = -(2*rho*t*g^6*s^6*(s - t)^3*(s + t)^3*(g*lam*s*t + g*lam*t^2 - rho)) := by simp only [detR, TYx, TBx, TBw, TPx, TGx, TGw, TKx, TKw, TLx, TLw, TQx, TQw, TRx, TRw, TVx, TVw]; ring
  rw [e]
  have : 0 < 2*rho*t*g^6*s^6*(s - t)^3*(s + t)^3*(g*lam*s*t + g*lam*t^2 - rho) := by positivity
  linarith

theorem fact24_fKL {g s t lam rho rt0 : ℝ} (P : Par24 g s t lam rho rt0) :
    detR (TGx g s t lam rho) (TGw g s t lam rho) (TKx g s t lam rho) (TKw g s t lam rho) (TLx g s t lam rho) (TLw g s t lam rho) ≤ 0 := by
  obtain ⟨hF1, hF2, hF3, hF4, hF6, hq, hH0⟩ := atoms24 P
  obtain ⟨hg, hs, ht, hlam, hrho, hts, hrt, hD, _, _⟩ := P
  have h1 : 0 < s - t := by linarith
  have h2 : 0 < s + t := by linarith
  have e : detR (TGx g s t lam rho) (TGw g s t lam rho) (TKx g s t lam rho) (TKw g s t lam rho) (TLx g s t lam rho) (TLw g s t lam rho) = -(2*rho*t*g^6*s^6*(s - t)^3*(s + t)^3*(g*lam*s*t + g*lam*t^2 - rho)) := by simp only [detR, TYx, TBx, TBw, TPx, TGx, TGw, TKx, TKw, TLx, TLw, TQx, TQw, TRx, TRw, TVx, TVw]; ring
  rw [e]
  have : 0 < 2*rho*t*g^6*s^6*(s - t)^3*(s + t)^3*(g*lam*s*t + g*lam*t^2 - rho) := by positivity
  linarith

theorem fact24_fPC {g s t lam rho rt0 : ℝ} (P : Par24 g s t lam rho rt0) :
    0 ≤ detR (TGx g s t lam rho) (TGw g s t lam rho) (TPx g s t lam rho) 0 (TYx g s t lam rho) 0 := by
  obtain ⟨hF1, hF2, hF3, hF4, hF6, hq, hH0⟩ := atoms24 P
  obtain ⟨hg, hs, ht, hlam, hrho, hts, hrt, hD, _, _⟩ := P
  have h1 : 0 < s - t := by linarith
  have h2 : 0 < s + t := by linarith
  have e : detR (TGx g s t lam rho) (TGw g s t lam rho) (TPx g s t lam rho) 0 (TYx g s t lam rho) 0 = 2*rho*t^3*g^6*s^6*(s - t)*(s + t)*(g*lam*s^3*t + g*lam*s^2*t^2 - g*lam*s*t^3 - g*lam*t^4 - rho*s^2) := by simp only [detR, TYx, TBx, TBw, TPx, TGx, TGw, TKx, TKw, TLx, TLw, TQx, TQw, TRx, TRw, TVx, TVw]; ring
  rw [e]; positivity

theorem fact24_fPR {g s t lam rho rt0 : ℝ} (P : Par24 g s t lam rho rt0) :
    0 ≤ detR (TGx g s t lam rho) (TGw g s t lam rho) (TPx g s t lam rho) 0 (TRx g s t lam rho) (TRw g s t lam rho) := by
  obtain ⟨hF1, hF2, hF3, hF4, hF6, hq, hH0⟩ := atoms24 P
  obtain ⟨hg, hs, ht, hlam, hrho, hts, hrt, hD, _, _⟩ := P
  have h1 : 0 < s - t := by linarith
  have h2 : 0 < s + t := by linarith
  have e : detR (TGx g s t lam rho) (TGw g s t lam rho) (TPx g s t lam rho) 0 (TRx g s t lam rho) (TRw g s t lam rho) = 2*rho*t^3*g^6*s^6*(s - t)^2*(s + t)^2*(g*lam*s*t + g*lam*t^2 - rho) := by simp only [detR, TYx, TBx, TBw, TPx, TGx, TGw, TKx, TKw, TLx, TLw, TQx, TQw, TRx, TRw, TVx, TVw]; ring
  rw [e]; positivity

theorem fact24_fPK {g s t lam rho rt0 : ℝ} (P : Par24 g s t lam rho rt0) :
    0 ≤ detR (TGx g s t lam rho) (TGw g s t lam rho) (TPx g s t lam rho) 0 (TKx g s t lam rho) (TKw g s t lam rho) := by
  obtain ⟨hF1, hF2, hF3, hF4, hF6, hq, hH0⟩ := atoms24 P
  obtain ⟨hg, hs, ht, hlam, hrho, hts, hrt, hD, _, _⟩ := P
  have h1 : 0 < s - t := by linarith
  have h2 : 0 < s + t := by linarith
  have e : detR (TGx g s t lam rho) (TGw g s t lam rho) (TPx g s t lam rho) 0 (TKx g s t lam rho) (TKw g s t lam rho) = 2*rho^2*t^3*g^6*s^6*(s - t)^2*(s + t)^2 := by simp only [detR, TYx, TBx, TBw, TPx, TGx, TGw, TKx, TKw, TLx, TLw, TQx, TQw, TRx, TRw, TVx, TVw]; ring
  rw [e]; positivity

theorem fact24_fPL {g s t lam rho rt0 : ℝ} (P : Par24 g s t lam rho rt0) :
    0 ≤ detR (TGx g s t lam rho) (TGw g s t lam rho) (TPx g s t lam rho) 0 (TLx g s t lam rho) (TLw g s t lam rho) := by
  obtain ⟨hF1, hF2, hF3, hF4, hF6, hq, hH0⟩ := atoms24 P
  obtain ⟨hg, hs, ht, hlam, hrho, hts, hrt, hD, _, _⟩ := P
  have h1 : 0 < s - t := by linarith
  have h2 : 0 < s + t := by linarith
  have e : detR (TGx g s t lam rho) (TGw g s t lam rho) (TPx g s t lam rho) 0 (TLx g s t lam rho) (TLw g s t lam rho) = 2*rho*t^4*g^6*s^6*(g*lam*s^5 + g*lam*s^4*t - 3*g*lam*s^3*t^2 - 3*g*lam*s^2*t^3 + g*lam*s*t^4 + g*lam*t^5 + rho*s^2*t) := by simp only [detR, TYx, TBx, TBw, TPx, TGx, TGw, TKx, TKw, TLx, TLw, TQx, TQw, TRx, TRw, TVx, TVw]; ring
  rw [e]; positivity

theorem fact24_fLA {g s t lam rho rt0 : ℝ} (P : Par24 g s t lam rho rt0) :
    detR (TKx g s t lam rho) (TKw g s t lam rho) (TLx g s t lam rho) (TLw g s t lam rho) 0 0 ≤ 0 := by
  obtain ⟨hF1, hF2, hF3, hF4, hF6, hq, hH0⟩ := atoms24 P
  obtain ⟨hg, hs, ht, hlam, hrho, hts, hrt, hD, _, _⟩ := P
  have h1 : 0 < s - t := by linarith
  have h2 : 0 < s + t := by linarith
  have e : detR (TKx g s t lam rho) (TKw g s t lam rho) (TLx g s t lam rho) (TLw g s t lam rho) 0 0 = -(2*rho*t*g^6*s^10*(s - t)*(s + t)*(g*lam*s*t + g*lam*t^2 - rho)) := by simp only [detR, TYx, TBx, TBw, TPx, TGx, TGw, TKx, TKw, TLx, TLw, TQx, TQw, TRx, TRw, TVx, TVw]; ring
  rw [e]
  have : 0 < 2*rho*t*g^6*s^10*(s - t)*(s + t)*(g*lam*s*t + g*lam*t^2 - rho) := by positivity
  linarith

theorem fact24_fLP {g s t lam rho rt0 : ℝ} (P : Par24 g s t lam rho rt0) :
    detR (TKx g s t lam rho) (TKw g s t lam rho) (TLx g s t lam rho) (TLw g s t lam rho) (TPx g s t lam rho) 0 ≤ 0 := by
  obtain ⟨hF1, hF2, hF3, hF4, hF6, hq, hH0⟩ := atoms24 P
  obtain ⟨hg, hs, ht, hlam, hrho, hts, hrt, hD, _, _⟩ := P
  have h1 : 0 < s - t := by linarith
  have h2 : 0 < s + t := by linarith
  have e : detR (TKx g s t lam rho) (TKw g s t lam rho) (TLx g s t lam rho) (TLw g s t lam rho) (TPx g s t lam rho) 0 = -(2*rho*t*g^6*s^10*(g*lam*s*t + g*lam*t^2 - rho)*(s^2 - 2*t^2)) := by simp only [detR, TYx, TBx, TBw, TPx, TGx, TGw, TKx, TKw, TLx, TLw, TQx, TQw, TRx, TRw, TVx, TVw]; ring
  rw [e]
  have : 0 < 2*rho*t*g^6*s^10*(g*lam*s*t + g*lam*t^2 - rho)*(s^2 - 2*t^2) := by positivity
  linarith

theorem fact24_fLC {g s t lam rho rt0 : ℝ} (P : Par24 g s t lam rho rt0) :
    detR (TKx g s t lam rho) (TKw g s t lam rho) (TLx g s t lam rho) (TLw g s t lam rho) (TYx g s t lam rho) 0 ≤ 0 := by
  obtain ⟨hF1, hF2, hF3, hF4, hF6, hq, hH0⟩ := atoms24 P
  obtain ⟨hg, hs, ht, hlam, hrho, hts, hrt, hD, _, _⟩ := P
  have h1 : 0 < s - t := by linarith
  have h2 : 0 < s + t := by linarith
  have e : detR (TKx g s t lam rho) (TKw g s t lam rho) (TLx g s t lam rho) (TLw g s t lam rho) (TYx g s t lam rho) 0 = -(2*t*g^6*s^8*(s - t)*(s + t)*(g*lam*s*t + g*lam*t^2 - rho)*(-g*lam*s*t^3 - g*lam*t^4 + rho*s^2)) := by simp only [detR, TYx, TBx, TBw, TPx, TGx, TGw, TKx, TKw, TLx, TLw, TQx, TQw, TRx, TRw, TVx, TVw]; ring
  rw [e]
  have : 0 < 2*t*g^6*s^8*(s - t)*(s + t)*(g*lam*s*t + g*lam*t^2 - rho)*(-g*lam*s*t^3 - g*lam*t^4 + rho*s^2) := by positivity
  linarith

theorem fact24_fLG {g s t lam rho rt0 : ℝ} (P : Par24 g s t lam rho rt0) :
    detR (TKx g s t lam rho) (TKw g s t lam rho) (TLx g s t lam rho) (TLw g s t lam rho) (TGx g s t lam rho) (TGw g s t lam rho) ≤ 0 := by
  obtain ⟨hF1, hF2, hF3, hF4, hF6, hq, hH0⟩ := atoms24 P
  obtain ⟨hg, hs, ht, hlam, hrho, hts, hrt, hD, _, _⟩ := P
  have h1 : 0 < s - t := by linarith
  have h2 : 0 < s + t := by linarith
  have e : detR (TKx g s t lam rho) (TKw g s t lam rho) (TLx g s t lam rho) (TLw g s t lam rho) (TGx g s t lam rho) (TGw g s t lam rho) = -(2*rho*t*g^6*s^6*(s - t)^3*(s + t)^3*(g*lam*s*t + g*lam*t^2 - rho)) := by simp only [detR, TYx, TBx, TBw, TPx, TGx, TGw, TKx, TKw, TLx, TLw, TQx, TQw, TRx, TRw, TVx, TVw]; ring
  rw [e]
  have : 0 < 2*rho*t*g^6*s^6*(s - t)^3*(s + t)^3*(g*lam*s*t + g*lam*t^2 - rho) := by positivity
  linarith

theorem fact24_fLQ {g s t lam rho rt0 : ℝ} (P : Par24 g s t lam rho rt0) :
    detR (TKx g s t lam rho) (TKw g s t lam rho) (TLx g s t lam rho) (TLw g s t lam rho) (TQx g s t lam rho) (TQw g s t lam rho) ≤ 0 := by
  obtain ⟨hF1, hF2, hF3, hF4, hF6, hq, hH0⟩ := atoms24 P
  obtain ⟨hg, hs, ht, hlam, hrho, hts, hrt, hD, _, _⟩ := P
  have h1 : 0 < s - t := by linarith
  have h2 : 0 < s + t := by linarith
  have e : detR (TKx g s t lam rho) (TKw g s t lam rho) (TLx g s t lam rho) (TLw g s t lam rho) (TQx g s t lam rho) (TQw g s t lam rho) = -(2*rho*t*g^6*s^6*(g*lam*s*t + g*lam*t^2 - rho)*(s^6 - 3*s^4*t^2 + 2*s^2*t^4 - t^6)) := by simp only [detR, TYx, TBx, TBw, TPx, TGx, TGw, TKx, TKw, TLx, TLw, TQx, TQw, TRx, TRw, TVx, TVw]; ring
  rw [e]
  have : 0 < 2*rho*t*g^6*s^6*(g*lam*s*t + g*lam*t^2 - rho)*(s^6 - 3*s^4*t^2 + 2*s^2*t^4 - t^6) := by positivity
  linarith

theorem fact24_fLR {g s t lam rho rt0 : ℝ} (P : Par24 g s t lam rho rt0) :
    detR (TKx g s t lam rho) (TKw g s t lam rho) (TLx g s t lam rho) (TLw g s t lam rho) (TRx g s t lam rho) (TRw g s t lam rho) ≤ 0 := by
  obtain ⟨hF1, hF2, hF3, hF4, hF6, hq, hH0⟩ := atoms24 P
  obtain ⟨hg, hs, ht, hlam, hrho, hts, hrt, hD, _, _⟩ := P
  have h1 : 0 < s - t := by linarith
  have h2 : 0 < s + t := by linarith
  have e : detR (TKx g s t lam rho) (TKw g s t lam rho) (TLx g s t lam rho) (TLw g s t lam rho) (TRx g s t lam rho) (TRw g s t lam rho) = -(2*t*g^6*s^6*(s - t)*(s + t)*(g*lam*s*t + g*lam*t^2 - rho)*(-g*lam*s^3*t^3 - g*lam*s^2*t^4 + rho*s^4 - rho*s^2*t^2 + rho*t^4)) := by simp only [detR, TYx, TBx, TBw, TPx, TGx, TGw, TKx, TKw, TLx, TLw, TQx, TQw, TRx, TRw, TVx, TVw]; ring
  rw [e]
  have : 0 < 2*t*g^6*s^6*(s - t)*(s + t)*(g*lam*s*t + g*lam*t^2 - rho)*(-g*lam*s^3*t^3 - g*lam*s^2*t^4 + rho*s^4 - rho*s^2*t^2 + rho*t^4) := by positivity
  linarith

theorem fact24_fLV {g s t lam rho rt0 : ℝ} (P : Par24 g s t lam rho rt0) :
    detR (TKx g s t lam rho) (TKw g s t lam rho) (TLx g s t lam rho) (TLw g s t lam rho) (TVx g s t lam rho) (TVw g s t lam rho) ≤ 0 := by
  obtain ⟨hF1, hF2, hF3, hF4, hF6, hq, hH0⟩ := atoms24 P
  obtain ⟨hg, hs, ht, hlam, hrho, hts, hrt, hD, _, _⟩ := P
  have h1 : 0 < s - t := by linarith
  have h2 : 0 < s + t := by linarith
  have e : detR (TKx g s t lam rho) (TKw g s t lam rho) (TLx g s t lam rho) (TLw g s t lam rho) (TVx g s t lam rho) (TVw g s t lam rho) = -(2*t^3*g^6*s^8*(s - t)*(s + t)*(g*lam*s*t + g*lam*t^2 - rho)^2) := by simp only [detR, TYx, TBx, TBw, TPx, TGx, TGw, TKx, TKw, TLx, TLw, TQx, TQw, TRx, TRw, TVx, TVw]; ring
  rw [e]
  have : 0 < 2*t^3*g^6*s^8*(s - t)*(s + t)*(g*lam*s*t + g*lam*t^2 - rho)^2 := by positivity
  linarith


/-! ### Cell vectors and pieces -/

section vecs
noncomputable def TUAx (g s t lam rho : ℝ) : ℝ := 2 * g * s * (s ^ 2 - t ^ 2)
noncomputable def TUAw (g s t lam rho : ℝ) : ℝ := 0
noncomputable def TVAx (g s t lam rho : ℝ) : ℝ := -(g * s * t ^ 2)
noncomputable def TVAw (g s t lam rho : ℝ) : ℝ := g * s * t
noncomputable def TUBx (g s t lam rho : ℝ) : ℝ := 2 * g * s ^ 2 * t
noncomputable def TUBw (g s t lam rho : ℝ) : ℝ := 0
noncomputable def TVBx (g s t lam rho : ℝ) : ℝ := -(g * t * (s ^ 2 - t ^ 2))
noncomputable def TVBw (g s t lam rho : ℝ) : ℝ := g * (s ^ 2 - t ^ 2)
end vecs

theorem toPar {g s t lam rho rt0 : ℝ} (P : Par24 g s t lam rho rt0) : Par g s t 1 rt0 :=
  ⟨P.hg, one_pos, P.hs, P.ht, P.hts, by have := (atoms24 P).2.2.2.2.2.1; linarith, P.hrt, P.hD⟩

theorem piece24 {g s t lam rho rt0 : ℝ} (P : Par24 g s t lam rho rt0) (m : ℕ) (hm : 0 < m)
    (σ : Equiv.Perm (Fin 3)) (X0 W0 X1 W1 X2 W2 : ℝ) (hdet : 0 < detR X0 W0 X1 W1 X2 W2)
    (h01 : (X1 - X0) ^ 2 + (4 * s ^ 2 - t ^ 2) * (W1 - W0) ^ 2 =
      (2 * s) ^ 2 * (m * m * Dt (g * s ^ 2 * (g * s ^ 2)) (bbc g s t) (aac g s t) (σ 0) (σ 1)))
    (h02 : (X2 - X0) ^ 2 + (4 * s ^ 2 - t ^ 2) * (W2 - W0) ^ 2 =
      (2 * s) ^ 2 * (m * m * Dt (g * s ^ 2 * (g * s ^ 2)) (bbc g s t) (aac g s t) (σ 0) (σ 2)))
    (h12 : (X2 - X1) ^ 2 + (4 * s ^ 2 - t ^ 2) * (W2 - W1) ^ 2 =
      (2 * s) ^ 2 * (m * m * Dt (g * s ^ 2 * (g * s ^ 2)) (bbc g s t) (aac g s t) (σ 1) (σ 2))) :
    Dis (tile (g * s ^ 2) (xb g s t) (yb g s t rt0) (tile_facts (toPar P)).1)
      (CS (1 / (2 * s)) (rt0 / (2 * s)) (TriR X0 W0 X1 W1 X2 W2)) (m * m) :=
  Dis_piece_gen (tile_facts (toPar P)).1 (tile_facts (toPar P)).2.1 (tile_facts (toPar P)).2.2
    (by have := P.hs; positivity) P.hrt P.hD m hm σ X0 W0 X1 W1 X2 W2 hdet h01 h02 h12
theorem green_dis24 {g s t lam rho rt0 : ℝ} (P : Par24 g s t lam rho rt0) (m : ℕ) (hm0 : 0 < m)
    (hm : (m : ℝ) = g ^ 2 * s ^ 3 * t * rho) :
    Dis (tile (g * s ^ 2) (xb g s t) (yb g s t rt0) (tile_facts (toPar P)).1)
      (CS (1 / (2 * s)) (rt0 / (2 * s)) (TriR 0 0 (TPx g s t lam rho) 0 (TGx g s t lam rho) (TGw g s t lam rho))) (m * m) :=
  piece24 P m hm0 sg0 _ _ _ _ _ _ (fact24_dGreen P)
    (by simp [sg0, Dt]; rw [hm]; simp only [TYx, TBx, TBw, TPx, TGx, TGw, TKx, TKw, TLx, TLw, TQx, TQw, TRx, TRw, TVx, TVw, TUAx, TUAw, TVAx, TVAw, TUBx, TUBw, TVBx, TVBw, bbc, aac]; ring)
    (by simp [sg0, Dt]; rw [hm]; simp only [TYx, TBx, TBw, TPx, TGx, TGw, TKx, TKw, TLx, TLw, TQx, TQw, TRx, TRw, TVx, TVw, TUAx, TUAw, TVAx, TVAw, TUBx, TUBw, TVBx, TVBw, bbc, aac]; ring)
    (by simp [sg0, Dt]; rw [hm]; simp only [TYx, TBx, TBw, TPx, TGx, TGw, TKx, TKw, TLx, TLw, TQx, TQw, TRx, TRw, TVx, TVw, TUAx, TUAw, TVAx, TVAw, TUBx, TUBw, TVBx, TVBw, bbc, aac]; ring)

theorem blue_dis24 {g s t lam rho rt0 : ℝ} (P : Par24 g s t lam rho rt0) (m : ℕ) (hm0 : 0 < m)
    (hm : (m : ℝ) = g ^ 2 * s ^ 2 * (s ^ 2 - t ^ 2) * rho) :
    Dis (tile (g * s ^ 2) (xb g s t) (yb g s t rt0) (tile_facts (toPar P)).1)
      (CS (1 / (2 * s)) (rt0 / (2 * s)) (TriR 0 0 (TGx g s t lam rho) (TGw g s t lam rho) (TKx g s t lam rho) (TKw g s t lam rho))) (m * m) :=
  piece24 P m hm0 sg2 _ _ _ _ _ _ (fact24_dBlue P)
    (by simp [sg2, Dt]; rw [hm]; simp only [TYx, TBx, TBw, TPx, TGx, TGw, TKx, TKw, TLx, TLw, TQx, TQw, TRx, TRw, TVx, TVw, TUAx, TUAw, TVAx, TVAw, TUBx, TUBw, TVBx, TVBw, bbc, aac]; ring)
    (by simp [sg2, Dt]; rw [hm]; simp only [TYx, TBx, TBw, TPx, TGx, TGw, TKx, TKw, TLx, TLw, TQx, TQw, TRx, TRw, TVx, TVw, TUAx, TUAw, TVAx, TVAw, TUBx, TUBw, TVBx, TVBw, bbc, aac]; ring)
    (by simp [sg2, Dt]; rw [hm]; simp only [TYx, TBx, TBw, TPx, TGx, TGw, TKx, TKw, TLx, TLw, TQx, TQw, TRx, TRw, TVx, TVw, TUAx, TUAw, TVAx, TVAw, TUBx, TUBw, TVBx, TVBw, bbc, aac]; ring)

theorem yellow_dis24 {g s t lam rho rt0 : ℝ} (P : Par24 g s t lam rho rt0) (m : ℕ) (hm0 : 0 < m)
    (hm : (m : ℝ) = g ^ 2 * s ^ 4 * (g * lam * t * (s + t) - rho)) :
    Dis (tile (g * s ^ 2) (xb g s t) (yb g s t rt0) (tile_facts (toPar P)).1)
      (CS (1 / (2 * s)) (rt0 / (2 * s)) (TriR (TKx g s t lam rho) (TKw g s t lam rho) (TLx g s t lam rho) (TLw g s t lam rho) (TBx g s t lam rho) (TBw g s t lam rho))) (m * m) :=
  piece24 P m hm0 sg5 _ _ _ _ _ _ (fact24_dYellow P)
    (by simp [sg5, Dt]; rw [hm]; simp only [TYx, TBx, TBw, TPx, TGx, TGw, TKx, TKw, TLx, TLw, TQx, TQw, TRx, TRw, TVx, TVw, TUAx, TUAw, TVAx, TVAw, TUBx, TUBw, TVBx, TVBw, bbc, aac]; ring)
    (by simp [sg5, Dt]; rw [hm]; simp only [TYx, TBx, TBw, TPx, TGx, TGw, TKx, TKw, TLx, TLw, TQx, TQw, TRx, TRw, TVx, TVw, TUAx, TUAw, TVAx, TVAw, TUBx, TUBw, TVBx, TVBw, bbc, aac]; ring)
    (by simp [sg5, Dt]; rw [hm]; simp only [TYx, TBx, TBw, TPx, TGx, TGw, TKx, TKw, TLx, TLw, TQx, TQw, TRx, TRw, TVx, TVw, TUAx, TUAw, TVAx, TVAw, TUBx, TUBw, TVBx, TVBw, bbc, aac]; ring)

theorem red_dis24 {g s t lam rho rt0 : ℝ} (P : Par24 g s t lam rho rt0) (m : ℕ) (hm0 : 0 < m)
    (hm : (m : ℝ) = g ^ 2 * s ^ 2 * t ^ 2 * rho) :
    Dis (tile (g * s ^ 2) (xb g s t) (yb g s t rt0) (tile_facts (toPar P)).1)
      (CS (1 / (2 * s)) (rt0 / (2 * s)) (TriR (TPx g s t lam rho) 0 (TQx g s t lam rho) (TQw g s t lam rho) (TGx g s t lam rho) (TGw g s t lam rho))) (m * m) :=
  piece24 P m hm0 sg4 _ _ _ _ _ _ (fact24_dRed P)
    (by simp [sg4, Dt]; rw [hm]; simp only [TYx, TBx, TBw, TPx, TGx, TGw, TKx, TKw, TLx, TLw, TQx, TQw, TRx, TRw, TVx, TVw, TUAx, TUAw, TVAx, TVAw, TUBx, TUBw, TVBx, TVBw, bbc, aac]; ring)
    (by simp [sg4, Dt]; rw [hm]; simp only [TYx, TBx, TBw, TPx, TGx, TGw, TKx, TKw, TLx, TLw, TQx, TQw, TRx, TRw, TVx, TVw, TUAx, TUAw, TVAx, TVAw, TUBx, TUBw, TVBx, TVBw, bbc, aac]; ring)
    (by simp [sg4, Dt]; rw [hm]; simp only [TYx, TBx, TBw, TPx, TGx, TGw, TKx, TKw, TLx, TLw, TQx, TQw, TRx, TRw, TVx, TVw, TUAx, TUAw, TVAx, TVAw, TUBx, TUBw, TVBx, TVBw, bbc, aac]; ring)

theorem pink_dis24 {g s t lam rho rt0 : ℝ} (P : Par24 g s t lam rho rt0) (m : ℕ) (hm0 : 0 < m)
    (hm : (m : ℝ) = g ^ 2 * s ^ 3 * t * (g * lam * t * (s + t) - rho)) :
    Dis (tile (g * s ^ 2) (xb g s t) (yb g s t rt0) (tile_facts (toPar P)).1)
      (CS (1 / (2 * s)) (rt0 / (2 * s)) (TriR (TKx g s t lam rho) (TKw g s t lam rho) (TVx g s t lam rho) (TVw g s t lam rho) (TLx g s t lam rho) (TLw g s t lam rho))) (m * m) :=
  piece24 P m hm0 sg2 _ _ _ _ _ _ (fact24_dPink P)
    (by simp [sg2, Dt]; rw [hm]; simp only [TYx, TBx, TBw, TPx, TGx, TGw, TKx, TKw, TLx, TLw, TQx, TQw, TRx, TRw, TVx, TVw, TUAx, TUAw, TVAx, TVAw, TUBx, TUBw, TVBx, TVBw, bbc, aac]; ring)
    (by simp [sg2, Dt]; rw [hm]; simp only [TYx, TBx, TBw, TPx, TGx, TGw, TKx, TKw, TLx, TLw, TQx, TQw, TRx, TRw, TVx, TVw, TUAx, TUAw, TVAx, TVAw, TUBx, TUBw, TVBx, TVBw, bbc, aac]; ring)
    (by simp [sg2, Dt]; rw [hm]; simp only [TYx, TBx, TBw, TPx, TGx, TGw, TKx, TKw, TLx, TLw, TQx, TQw, TRx, TRw, TVx, TVw, TUAx, TUAw, TVAx, TVAw, TUBx, TUBw, TVBx, TVBw, bbc, aac]; ring)

theorem deltaA {g s t lam rho rt0 : ℝ} (P : Par24 g s t lam rho rt0) :
    0 < (TUAx g s t lam rho) * (TVAw g s t lam rho) - (TUAw g s t lam rho) * (TVAx g s t lam rho) := by
  obtain ⟨hg, hs, ht, hlam, hrho, hts, hrt, hD, _, _⟩ := P
  have h1 : 0 < s - t := by linarith
  have h2 : 0 < s + t := by linarith
  have e : (TUAx g s t lam rho) * (TVAw g s t lam rho) - (TUAw g s t lam rho) * (TVAx g s t lam rho) = 2 * g ^ 2 * s ^ 2 * t * ((s - t) * (s + t)) := by
    simp only [TYx, TBx, TBw, TPx, TGx, TGw, TKx, TKw, TLx, TLw, TQx, TQw, TRx, TRw, TVx, TVw, TUAx, TUAw, TVAx, TVAw, TUBx, TUBw, TVBx, TVBw, bbc, aac]; ring
  rw [e]; positivity

theorem cellA_t1 {g s t lam rho rt0 : ℝ} (P : Par24 g s t lam rho rt0) (Ox Ow : ℝ) :
    Dis (tile (g * s ^ 2) (xb g s t) (yb g s t rt0) (tile_facts (toPar P)).1)
      (CS (1 / (2 * s)) (rt0 / (2 * s))
        (TriR Ox Ow (Ox + (TUAx g s t lam rho)) (Ow + (TUAw g s t lam rho)) (Ox + (TVAx g s t lam rho)) (Ow + (TVAw g s t lam rho)))) 1 := by
  have hd : 0 < detR Ox Ow (Ox + (TUAx g s t lam rho)) (Ow + (TUAw g s t lam rho)) (Ox + (TVAx g s t lam rho)) (Ow + (TVAw g s t lam rho)) := by
    have := deltaA P
    simp only [detR]; nlinarith
  refine (piece24 P 1 one_pos sg1 _ _ _ _ _ _ hd ?_ ?_ ?_).congr rfl (by norm_num)
  all_goals (simp [sg1, Dt]; simp only [TYx, TBx, TBw, TPx, TGx, TGw, TKx, TKw, TLx, TLw, TQx, TQw, TRx, TRw, TVx, TVw, TUAx, TUAw, TVAx, TVAw, TUBx, TUBw, TVBx, TVBw, bbc, aac]; ring)

theorem cellA_t2 {g s t lam rho rt0 : ℝ} (P : Par24 g s t lam rho rt0) (Ox Ow : ℝ) :
    Dis (tile (g * s ^ 2) (xb g s t) (yb g s t rt0) (tile_facts (toPar P)).1)
      (CS (1 / (2 * s)) (rt0 / (2 * s))
        (TriR (Ox + (TUAx g s t lam rho)) (Ow + (TUAw g s t lam rho)) (Ox + (TUAx g s t lam rho) + (TVAx g s t lam rho)) (Ow + (TUAw g s t lam rho) + (TVAw g s t lam rho))
          (Ox + (TVAx g s t lam rho)) (Ow + (TVAw g s t lam rho)))) 1 := by
  have hd : 0 < detR (Ox + (TUAx g s t lam rho)) (Ow + (TUAw g s t lam rho)) (Ox + (TUAx g s t lam rho) + (TVAx g s t lam rho)) (Ow + (TUAw g s t lam rho) + (TVAw g s t lam rho))
      (Ox + (TVAx g s t lam rho)) (Ow + (TVAw g s t lam rho)) := by
    have := deltaA P
    simp only [detR]; nlinarith
  refine (piece24 P 1 one_pos sg2 _ _ _ _ _ _ hd ?_ ?_ ?_).congr rfl (by norm_num)
  all_goals (simp [sg2, Dt]; simp only [TYx, TBx, TBw, TPx, TGx, TGw, TKx, TKw, TLx, TLw, TQx, TQw, TRx, TRw, TVx, TVw, TUAx, TUAw, TVAx, TVAw, TUBx, TUBw, TVBx, TVBw, bbc, aac]; ring)

theorem cellA_dis {g s t lam rho rt0 : ℝ} (P : Par24 g s t lam rho rt0) :
    ∀ Ox Ow, Dis (tile (g * s ^ 2) (xb g s t) (yb g s t rt0) (tile_facts (toPar P)).1)
      (CS (1 / (2 * s)) (rt0 / (2 * s)) (PgP (TUAx g s t lam rho) (TUAw g s t lam rho) (TVAx g s t lam rho) (TVAw g s t lam rho) Ox Ow 1 1)) 2 :=
  cell_of_tris (by have := P.hs; positivity) (by have := P.hs; have := P.hrt; positivity)
    (deltaA P) (cellA_t1 P) (cellA_t2 P)

theorem deltaB {g s t lam rho rt0 : ℝ} (P : Par24 g s t lam rho rt0) :
    0 < (TUBx g s t lam rho) * (TVBw g s t lam rho) - (TUBw g s t lam rho) * (TVBx g s t lam rho) := by
  obtain ⟨hg, hs, ht, hlam, hrho, hts, hrt, hD, _, _⟩ := P
  have h1 : 0 < s - t := by linarith
  have h2 : 0 < s + t := by linarith
  have e : (TUBx g s t lam rho) * (TVBw g s t lam rho) - (TUBw g s t lam rho) * (TVBx g s t lam rho) = 2 * g ^ 2 * s ^ 2 * t * ((s - t) * (s + t)) := by
    simp only [TYx, TBx, TBw, TPx, TGx, TGw, TKx, TKw, TLx, TLw, TQx, TQw, TRx, TRw, TVx, TVw, TUAx, TUAw, TVAx, TVAw, TUBx, TUBw, TVBx, TVBw, bbc, aac]; ring
  rw [e]; positivity

theorem cellB_t1 {g s t lam rho rt0 : ℝ} (P : Par24 g s t lam rho rt0) (Ox Ow : ℝ) :
    Dis (tile (g * s ^ 2) (xb g s t) (yb g s t rt0) (tile_facts (toPar P)).1)
      (CS (1 / (2 * s)) (rt0 / (2 * s))
        (TriR Ox Ow (Ox + (TUBx g s t lam rho)) (Ow + (TUBw g s t lam rho)) (Ox + (TVBx g s t lam rho)) (Ow + (TVBw g s t lam rho)))) 1 := by
  have hd : 0 < detR Ox Ow (Ox + (TUBx g s t lam rho)) (Ow + (TUBw g s t lam rho)) (Ox + (TVBx g s t lam rho)) (Ow + (TVBw g s t lam rho)) := by
    have := deltaB P
    simp only [detR]; nlinarith
  refine (piece24 P 1 one_pos sg5 _ _ _ _ _ _ hd ?_ ?_ ?_).congr rfl (by norm_num)
  all_goals (simp [sg5, Dt]; simp only [TYx, TBx, TBw, TPx, TGx, TGw, TKx, TKw, TLx, TLw, TQx, TQw, TRx, TRw, TVx, TVw, TUAx, TUAw, TVAx, TVAw, TUBx, TUBw, TVBx, TVBw, bbc, aac]; ring)

theorem cellB_t2 {g s t lam rho rt0 : ℝ} (P : Par24 g s t lam rho rt0) (Ox Ow : ℝ) :
    Dis (tile (g * s ^ 2) (xb g s t) (yb g s t rt0) (tile_facts (toPar P)).1)
      (CS (1 / (2 * s)) (rt0 / (2 * s))
        (TriR (Ox + (TUBx g s t lam rho)) (Ow + (TUBw g s t lam rho)) (Ox + (TUBx g s t lam rho) + (TVBx g s t lam rho)) (Ow + (TUBw g s t lam rho) + (TVBw g s t lam rho))
          (Ox + (TVBx g s t lam rho)) (Ow + (TVBw g s t lam rho)))) 1 := by
  have hd : 0 < detR (Ox + (TUBx g s t lam rho)) (Ow + (TUBw g s t lam rho)) (Ox + (TUBx g s t lam rho) + (TVBx g s t lam rho)) (Ow + (TUBw g s t lam rho) + (TVBw g s t lam rho))
      (Ox + (TVBx g s t lam rho)) (Ow + (TVBw g s t lam rho)) := by
    have := deltaB P
    simp only [detR]; nlinarith
  refine (piece24 P 1 one_pos sg4 _ _ _ _ _ _ hd ?_ ?_ ?_).congr rfl (by norm_num)
  all_goals (simp [sg4, Dt]; simp only [TYx, TBx, TBw, TPx, TGx, TGw, TKx, TKw, TLx, TLw, TQx, TQw, TRx, TRw, TVx, TVw, TUAx, TUAw, TVAx, TVAw, TUBx, TUBw, TVBx, TVBw, bbc, aac]; ring)

theorem cellB_dis {g s t lam rho rt0 : ℝ} (P : Par24 g s t lam rho rt0) :
    ∀ Ox Ow, Dis (tile (g * s ^ 2) (xb g s t) (yb g s t rt0) (tile_facts (toPar P)).1)
      (CS (1 / (2 * s)) (rt0 / (2 * s)) (PgP (TUBx g s t lam rho) (TUBw g s t lam rho) (TVBx g s t lam rho) (TVBw g s t lam rho) Ox Ow 1 1)) 2 :=
  cell_of_tris (by have := P.hs; positivity) (by have := P.hs; have := P.hrt; positivity)
    (deltaB P) (cellB_t1 P) (cellB_t2 P)

set_option maxHeartbeats 8000000 in
theorem core24 {g s t lam rho rt0 : ℝ} (P : Par24 g s t lam rho rt0) (p q u v m n : ℕ) {n7 : ℕ}
    (hp : (p : ℝ) = g ^ 2 * s ^ 3 * t * rho) (hq : (q : ℝ) = g ^ 2 * s ^ 2 * (s ^ 2 - t ^ 2) * rho)
    (hu : (u : ℝ) = g ^ 2 * s ^ 4 * (g * lam * t * (s + t) - rho))
    (htt : ((n + 1 : ℕ) : ℝ) = g ^ 2 * s ^ 2 * t ^ 2 * rho)
    (hv : (v : ℝ) = g ^ 2 * s ^ 3 * t * (g * lam * t * (s + t) - rho))
    (hr : ((m + 1 : ℕ) : ℝ) = g ^ 2 * s ^ 2 * (g * lam * t * (s ^ 2 - t ^ 2) * (s + t) - s ^ 2 * rho))
    (hGrlv : Dis (tile (g * s ^ 2) (xb g s t) (yb g s t rt0) (tile_facts (toPar P)).1)
      (CS (1 / (2 * s)) (rt0 / (2 * s))
        (GrlvP (TGx g s t lam rho) (TGw g s t lam rho) (TRx g s t lam rho) (TRw g s t lam rho)
          (TLx g s t lam rho) (TLw g s t lam rho) (TVx g s t lam rho) (TVw g s t lam rho))) n7) :
    Dis (tile (g * s ^ 2) (xb g s t) (yb g s t rt0) (tile_facts (toPar P)).1)
      (CS (1 / (2 * s)) (rt0 / (2 * s)) (TriR 0 0 (TYx g s t lam rho) 0 (TBx g s t lam rho) (TBw g s t lam rho)))
      (p * p + q * q + u * u + (n + 1) * (n + 1) + v * v + 2 * (m + 1) * (n + 1) + n7) := by
  obtain ⟨hF1, hF2, hF3, hF4, hF6, hq2, hH0⟩ := atoms24 P
  have hg := P.hg
  have hs := P.hs
  have ht := P.ht
  have hlam := P.hlam
  have hrho := P.hrho
  have hts := P.hts
  have h1 : 0 < s - t := by linarith
  have h2 : 0 < s + t := by linarith
  have hF1' : 0 < g * lam * t * (s + t) - rho := by nlinarith [hF1]
  have hα : 0 < 1 / (2 * s) := by positivity
  have hβ : 0 < rt0 / (2 * s) := by have := P.hrt; positivity
  have hp0 : 0 < p := by
    have : (0 : ℝ) < p := by rw [hp]; positivity
    exact_mod_cast this
  have hq0 : 0 < q := by
    have hh : 0 < s ^ 2 - t ^ 2 := by nlinarith
    have : (0 : ℝ) < q := by rw [hq]; positivity
    exact_mod_cast this
  have hu0 : 0 < u := by
    have : (0 : ℝ) < u := by rw [hu]; positivity
    exact_mod_cast this
  have hv0 : 0 < v := by
    have : (0 : ℝ) < v := by rw [hv]; positivity
    exact_mod_cast this
  have cs_congr : ∀ {p q : ℝ → ℝ → Prop}, (∀ X W, p X W ↔ q X W) →
      CS (1 / (2 * s)) (rt0 / (2 * s)) p = CS (1 / (2 * s)) (rt0 / (2 * s)) q := by
    intro p q h
    ext z
    exact h _ _
  -- the parallelogram PCRQ
  have huB : TUBx g s t lam rho ≠ 0 ∨ TUBw g s t lam rho ≠ 0 :=
    Or.inl (by have : 0 < TUBx g s t lam rho := by simp only [TUBx]; positivity
               exact this.ne')
  have hvB : TVBx g s t lam rho ≠ 0 ∨ TVBw g s t lam rho ≠ 0 :=
    Or.inr (by have : 0 < TVBw g s t lam rho := by
                 simp only [TVBw]
                 have : 0 < s ^ 2 - t ^ 2 := by nlinarith
                 positivity
               exact this.ne')
  have hm0 : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
  have hn0 : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hSx : TYx g s t lam rho = TPx g s t lam rho + ((m + 1 : ℕ) : ℝ) * TUBx g s t lam rho := by
    rw [hr]; simp only [TYx, TPx, TUBx]; ring
  have hSw : (0 : ℝ) = 0 + ((m + 1 : ℕ) : ℝ) * TUBw g s t lam rho := by simp [TUBw]
  have hRx' : TRx g s t lam rho = TYx g s t lam rho + ((n + 1 : ℕ) : ℝ) * TVBx g s t lam rho := by
    rw [htt]; simp only [TYx, TRx, TVBx]; ring
  have hRw' : TRw g s t lam rho = 0 + ((n + 1 : ℕ) : ℝ) * TVBw g s t lam rho := by
    rw [htt]; simp only [TRw, TVBw]; ring
  have hTx' : TQx g s t lam rho = TPx g s t lam rho + ((n + 1 : ℕ) : ℝ) * TVBx g s t lam rho := by
    rw [htt]; simp only [TQx, TPx, TVBx]; ring
  have hTw' : TQw g s t lam rho = 0 + ((n + 1 : ℕ) : ℝ) * TVBw g s t lam rho := by
    rw [htt]; simp only [TQw, TVBw]; ring
  have hPcrq := (grid_dis hα hβ huB hvB (cellB_dis P) n m (TPx g s t lam rho) 0).congr
    (cs_congr (fun X W => pgp_iff hm0 hn0 hSx hSw hRx' hRw' hTx' hTw' X W)) rfl
  -- the five triangles
  have hGreen := green_dis24 P p hp0 hp
  have hBlue := blue_dis24 P q hq0 hq
  have hYellow := yellow_dis24 P u hu0 hu
  have hRed := red_dis24 P (n + 1) (by omega) htt
  have hPink := pink_dis24 P v hv0 hv
  -- the affine parameters
  have hF1n : (g * lam * s * t + g * lam * t ^ 2 - rho) ≠ 0 := hF1.ne'
  have hne1 : g * lam * t * (s + t) ≠ 0 := by positivity
  have hne2 : g * lam * s ^ 2 * (s + t) ≠ 0 := by positivity
  have hne3 : g * lam * t * (s - t) * (s + t) ^ 2 ≠ 0 := by positivity
  have hne4 : (s - t) * (s + t) * (g * lam * s * t + g * lam * t ^ 2 - rho) ≠ 0 := by positivity
  have hne5 : rho * (s - t) ^ 2 * (s + t) ^ 2 ≠ 0 := by positivity
  have hKx : TKx g s t lam rho = Tkap g s t lam rho * TBx g s t lam rho := by
    simp only [TKx, Tkap, TBx]; rw [div_mul_eq_mul_div, eq_div_iff hne1]; ring
  have hKw : TKw g s t lam rho = Tkap g s t lam rho * TBw g s t lam rho := by
    simp only [TKw, Tkap, TBw]; rw [div_mul_eq_mul_div, eq_div_iff hne1]; ring
  have hRx : TRx g s t lam rho = TYx g s t lam rho + Ttau g s t lam rho * (TBx g s t lam rho - TYx g s t lam rho) := by
    simp only [TRx, TYx, Ttau, TBx]
    rw [div_mul_eq_mul_div, ← sub_eq_iff_eq_add', eq_div_iff hne2]; ring
  have hRw : TRw g s t lam rho = Ttau g s t lam rho * TBw g s t lam rho := by
    simp only [TRw, Ttau, TBw]; rw [div_mul_eq_mul_div, eq_div_iff hne2]; ring
  have hLx : TLx g s t lam rho = TYx g s t lam rho + Tsig g s t lam rho * (TBx g s t lam rho - TYx g s t lam rho) := by
    simp only [TLx, TYx, Tsig, TBx]
    rw [div_mul_eq_mul_div, ← sub_eq_iff_eq_add', eq_div_iff hne3]; ring
  have hLw : TLw g s t lam rho = Tsig g s t lam rho * TBw g s t lam rho := by
    simp only [TLw, Tsig, TBw]; rw [div_mul_eq_mul_div, eq_div_iff hne3]; ring
  have hQx : TQx g s t lam rho = TGx g s t lam rho + Tnu g s t lam rho * (TRx g s t lam rho - TGx g s t lam rho) := by
    simp only [TQx, TGx, Tnu, TRx]
    rw [div_mul_eq_mul_div, ← sub_eq_iff_eq_add', eq_div_iff hne4]; ring
  have hQw : TQw g s t lam rho = TGw g s t lam rho + Tnu g s t lam rho * (TRw g s t lam rho - TGw g s t lam rho) := by
    simp only [TQw, TGw, Tnu, TRw]
    rw [div_mul_eq_mul_div, ← sub_eq_iff_eq_add', eq_div_iff hne4]; ring
  have hVx : TVx g s t lam rho = TGx g s t lam rho + Tzet g s t lam rho * (TKx g s t lam rho - TGx g s t lam rho) := by
    simp only [TVx, TGx, Tzet, TKx]
    rw [div_mul_eq_mul_div, ← sub_eq_iff_eq_add', eq_div_iff hne5]; ring
  have hVw : TVw g s t lam rho = TGw g s t lam rho + Tzet g s t lam rho * (TKw g s t lam rho - TGw g s t lam rho) := by
    simp only [TVw, TGw, Tzet, TKw]
    rw [div_mul_eq_mul_div, ← sub_eq_iff_eq_add', eq_div_iff hne5]; ring
  have hY : 0 < TYx g s t lam rho := by simp only [TYx]; positivity
  have hPx0 : 0 < TPx g s t lam rho := by simp only [TPx]; positivity
  have hPxY : TPx g s t lam rho < TYx g s t lam rho := by
    have e : TYx g s t lam rho - TPx g s t lam rho =
        2 * g ^ 3 * s ^ 4 * t * (g * lam * s ^ 3 * t + g * lam * s ^ 2 * t ^ 2 - g * lam * s * t ^ 3 - g * lam * t ^ 4 - rho * s ^ 2) := by
      simp only [TYx, TPx]; ring
    have : 0 < TYx g s t lam rho - TPx g s t lam rho := by rw [e]; positivity
    linarith
  have hκ0 : 0 < Tkap g s t lam rho := by simp only [Tkap]; positivity
  have hκ1 : Tkap g s t lam rho < 1 := by
    simp only [Tkap]; rw [div_lt_one (by positivity)]; nlinarith [hF1]
  have hτ0 : 0 < Ttau g s t lam rho := by simp only [Ttau]; positivity
  have hτσ : Ttau g s t lam rho < Tsig g s t lam rho := by
    simp only [Ttau, Tsig]
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    have e : (-g * lam * s * t ^ 3 - g * lam * t ^ 4 + rho * s ^ 2) * (g * lam * s ^ 2 * (s + t)) -
        rho * t * (g * lam * t * (s - t) * (s + t) ^ 2) =
        g * lam * (s + t) * (-g * lam * s ^ 3 * t ^ 3 - g * lam * s ^ 2 * t ^ 4 + rho * s ^ 4 - rho * s ^ 2 * t ^ 2 + rho * t ^ 4) := by ring
    have : 0 < g * lam * (s + t) * (-g * lam * s ^ 3 * t ^ 3 - g * lam * s ^ 2 * t ^ 4 + rho * s ^ 4 - rho * s ^ 2 * t ^ 2 + rho * t ^ 4) := by positivity
    linarith
  have hσ1 : Tsig g s t lam rho < 1 := by
    simp only [Tsig]; rw [div_lt_one (by positivity)]
    have e : g * lam * t * (s - t) * (s + t) ^ 2 - (-g * lam * s * t ^ 3 - g * lam * t ^ 4 + rho * s ^ 2) =
        s ^ 2 * (g * lam * s * t + g * lam * t ^ 2 - rho) := by ring
    have : 0 < s ^ 2 * (g * lam * s * t + g * lam * t ^ 2 - rho) := by positivity
    linarith
  have hν0 : 0 < Tnu g s t lam rho := by simp only [Tnu]; positivity
  have hν1 : Tnu g s t lam rho < 1 := by
    simp only [Tnu]; rw [div_lt_one (by positivity)]
    have e : (s - t) * (s + t) * (g * lam * s * t + g * lam * t ^ 2 - rho) - rho * t ^ 2 =
        g * lam * s ^ 3 * t + g * lam * s ^ 2 * t ^ 2 - g * lam * s * t ^ 3 - g * lam * t ^ 4 - rho * s ^ 2 := by ring
    linarith
  have hζ0 : 0 < Tzet g s t lam rho := by simp only [Tzet]; positivity
  have hζ1 : Tzet g s t lam rho < 1 := by
    simp only [Tzet]; rw [div_lt_one (by positivity)]
    have e : rho * (s - t) ^ 2 * (s + t) ^ 2 - (-g * lam * s ^ 3 * t ^ 3 - g * lam * s ^ 2 * t ^ 4 + rho * s ^ 4 - rho * s ^ 2 * t ^ 2 + rho * t ^ 4) =
        s ^ 2 * t ^ 2 * (g * lam * s * t + g * lam * t ^ 2 - rho) := by ring
    have : 0 < s ^ 2 * t ^ 2 * (g * lam * s * t + g * lam * t ^ 2 - rho) := by positivity
    linarith
  have hlP : 0 < (s ^ 2 - 2 * t ^ 2) * (s ^ 2 - t ^ 2) * (g * lam * s * t + g * lam * t ^ 2 - rho) := by
    have : 0 < s ^ 2 - t ^ 2 := by nlinarith
    positivity
  have hlR : 0 < rho * t ^ 4 := by positivity
  have hlK : 0 < t ^ 2 * (s ^ 2 - t ^ 2) * (g * lam * s * t + g * lam * t ^ 2 - rho) := by
    have : 0 < s ^ 2 - t ^ 2 := by nlinarith
    positivity
  have hspx : (s ^ 2 - 2 * t ^ 2) * (s ^ 2 - t ^ 2) * (g * lam * s * t + g * lam * t ^ 2 - rho) *
        (TPx g s t lam rho - TGx g s t lam rho) + rho * t ^ 4 * (TRx g s t lam rho - TGx g s t lam rho) +
      t ^ 2 * (s ^ 2 - t ^ 2) * (g * lam * s * t + g * lam * t ^ 2 - rho) * (TKx g s t lam rho - TGx g s t lam rho) +
      t ^ 2 * (s ^ 2 - t ^ 2) * (g * lam * s * t + g * lam * t ^ 2 - rho) * (0 - TGx g s t lam rho) = 0 := by
    simp only [TPx, TGx, TRx, TKx]; ring
  have hspw : (s ^ 2 - 2 * t ^ 2) * (s ^ 2 - t ^ 2) * (g * lam * s * t + g * lam * t ^ 2 - rho) *
        (0 - TGw g s t lam rho) + rho * t ^ 4 * (TRw g s t lam rho - TGw g s t lam rho) +
      t ^ 2 * (s ^ 2 - t ^ 2) * (g * lam * s * t + g * lam * t ^ 2 - rho) * (TKw g s t lam rho - TGw g s t lam rho) +
      t ^ 2 * (s ^ 2 - t ^ 2) * (g * lam * s * t + g * lam * t ^ 2 - rho) * (0 - TGw g s t lam rho) = 0 := by
    simp only [TGw, TRw, TKw]; ring
  exact assemble24 hα hβ (TYx g s t lam rho) (TBx g s t lam rho) (TBw g s t lam rho) (TPx g s t lam rho)
    (TGx g s t lam rho) (TGw g s t lam rho) (Tkap g s t lam rho) (Ttau g s t lam rho)
    (Tsig g s t lam rho) (Tnu g s t lam rho) (Tzet g s t lam rho) (TKx g s t lam rho) (TKw g s t lam rho)
    (TLx g s t lam rho) (TLw g s t lam rho) (TRx g s t lam rho) (TRw g s t lam rho) (TQx g s t lam rho)
    (TQw g s t lam rho) (TVx g s t lam rho) (TVw g s t lam rho)
    hKx hKw hRx hRw hLx hLw hQx hQw hVx hVw hY hPx0 hPxY hκ0 hκ1 hτ0 hτσ hσ1 hν0 hν1 hζ0 hζ1
    hGreen hBlue hYellow hRed hPink hPcrq hGrlv
    (fact24_dBig P) (fact24_dGreen P) (fact24_dBlue P) (fact24_dYellow P) (fact24_dRed P)
    (fact24_dPink P) (fact24_dP1 P) (fact24_dP2 P) (fact24_dG1 P) (fact24_dG2 P)
    ⟨fact24_hG1 P, fact24_hG2 P, fact24_hG3 P⟩ _ _ _ _ hlP hlR hlK hlK hspx hspw
    (fact24_fRP P) (fact24_fRC P) (fact24_fRK P) (fact24_fRL P) (fact24_fKP P) (fact24_fKC P)
    (fact24_fKR P) (fact24_fKL P) (fact24_fPC P) (fact24_fPR P) (fact24_fPK P) (fact24_fPL P)
    (fact24_fLA P) (fact24_fLP P) (fact24_fLC P) (fact24_fLG P) (fact24_fLQ P) (fact24_fLR P)
    (fact24_fLV P)


theorem grlv24_one {g s t lam rho rt0 : ℝ} (P : Par24 g s t lam rho rt0) (m x : ℕ)
    (hv : ((m + 1 : ℕ) : ℝ) = g ^ 2 * s ^ 3 * t * (g * lam * t * (s + t) - rho))
    (hxA : ((x + 1 : ℕ) : ℝ) * (g * s * t) = g ^ 3 * s ^ 2 * (-g * lam * s ^ 3 * t ^ 3 - g * lam * s ^ 2 * t ^ 4 + rho * s ^ 4 - rho * s ^ 2 * t ^ 2 + rho * t ^ 4)) :
    Dis (tile (g * s ^ 2) (xb g s t) (yb g s t rt0) (tile_facts (toPar P)).1)
      (CS (1 / (2 * s)) (rt0 / (2 * s))
        (GrlvP (TGx g s t lam rho) (TGw g s t lam rho) (TRx g s t lam rho) (TRw g s t lam rho)
          (TLx g s t lam rho) (TLw g s t lam rho) (TVx g s t lam rho) (TVw g s t lam rho)))
      (2 * (m + 1) * (x + 1)) := by
  have hg := P.hg
  have hs := P.hs
  have ht := P.ht
  have hα : 0 < 1 / (2 * s) := by positivity
  have hβ : 0 < rt0 / (2 * s) := by have := P.hrt; positivity
  have hts := P.hts
  have h1 : 0 < s - t := by linarith
  have hh : 0 < s ^ 2 - t ^ 2 := by nlinarith
  have huA : TUAx g s t lam rho ≠ 0 ∨ TUAw g s t lam rho ≠ 0 := by
    left
    have : 0 < TUAx g s t lam rho := by simp only [TUAx]; positivity
    exact this.ne'
  have hvA : TVAx g s t lam rho ≠ 0 ∨ TVAw g s t lam rho ≠ 0 := by
    right
    have : 0 < TVAw g s t lam rho := by simp only [TVAw]; positivity
    exact this.ne'
  refine grlv_one hα hβ huA hvA (cellA_dis P) m x _ _ _ _ _ _ _ _ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [hv]; simp only [TRx, TGx, TUAx]; ring
  · rw [hv]; simp only [TRw, TGw, TUAw]; ring
  · simp only [TLx, TRx, TVAx]; linear_combination t * hxA
  · simp only [TLw, TRw, TVAw]; linear_combination (-1) * hxA
  · simp only [TVx, TGx, TVAx]; linear_combination t * hxA
  · simp only [TVw, TGw, TVAw]; linear_combination (-1) * hxA

theorem grlv24_two {g s t lam rho rt0 : ℝ} (P : Par24 g s t lam rho rt0) (m1 m2 x y : ℕ)
    (hv : ((m1 + 1 : ℕ) : ℝ) = g ^ 2 * s ^ 3 * t * (g * lam * t * (s + t) - rho))
    (hm2 : ((m2 + 1 : ℕ) : ℝ) = g ^ 2 * s ^ 2 * (s ^ 2 - t ^ 2) * (g * lam * t * (s + t) - rho))
    (hxy : ((x + 1 : ℕ) : ℝ) * (g * s * t) + ((y + 1 : ℕ) : ℝ) * (g * (s ^ 2 - t ^ 2)) =
      g ^ 3 * s ^ 2 * (-g * lam * s ^ 3 * t ^ 3 - g * lam * s ^ 2 * t ^ 4 + rho * s ^ 4 - rho * s ^ 2 * t ^ 2 + rho * t ^ 4)) :
    Dis (tile (g * s ^ 2) (xb g s t) (yb g s t rt0) (tile_facts (toPar P)).1)
      (CS (1 / (2 * s)) (rt0 / (2 * s))
        (GrlvP (TGx g s t lam rho) (TGw g s t lam rho) (TRx g s t lam rho) (TRw g s t lam rho)
          (TLx g s t lam rho) (TLw g s t lam rho) (TVx g s t lam rho) (TVw g s t lam rho)))
      (2 * (m1 + 1) * (x + 1) + 2 * (m2 + 1) * (y + 1)) := by
  have hg := P.hg
  have hs := P.hs
  have ht := P.ht
  have hα : 0 < 1 / (2 * s) := by positivity
  have hβ : 0 < rt0 / (2 * s) := by have := P.hrt; positivity
  have hts := P.hts
  have h1 : 0 < s - t := by linarith
  have hh : 0 < s ^ 2 - t ^ 2 := by nlinarith
  have hne : s ^ 2 - t ^ 2 ≠ 0 := hh.ne'
  have hne' : s * t ≠ 0 := by positivity
  have hc1 : 0 < s * t / (s ^ 2 - t ^ 2) := by positivity
  have hc2 : 0 < (s ^ 2 - t ^ 2) / (s * t) := by positivity
  have huA : TUAx g s t lam rho ≠ 0 ∨ TUAw g s t lam rho ≠ 0 := by
    left
    have : 0 < TUAx g s t lam rho := by simp only [TUAx]; positivity
    exact this.ne'
  have hvA : TVAx g s t lam rho ≠ 0 ∨ TVAw g s t lam rho ≠ 0 := by
    right
    have : 0 < TVAw g s t lam rho := by simp only [TVAw]; positivity
    exact this.ne'
  refine grlv_two hα hβ huA hvA (deltaA P) (s * t / (s ^ 2 - t ^ 2)) ((s ^ 2 - t ^ 2) / (s * t)) hc1 hc2
    (TUBx g s t lam rho) (TUBw g s t lam rho) (TVBx g s t lam rho) (TVBw g s t lam rho) ?_ ?_ ?_ ?_
    (cellA_dis P) (cellB_dis P) m1 m2 x y ?_ _ _ _ _ _ _ _ _ ?_ ?_ ?_ ?_ ?_ ?_
  · simp only [TUBx, TUAx]; rw [div_mul_eq_mul_div, eq_div_iff hne]; ring
  · simp [TUBw, TUAw]
  · simp only [TVBx, TVAx]; rw [div_mul_eq_mul_div, eq_div_iff hne']; ring
  · simp only [TVBw, TVAw]; rw [div_mul_eq_mul_div, eq_div_iff hne']; ring
  · rw [hv, hm2]; field_simp
  · rw [hv]; simp only [TRx, TGx, TUAx]; ring
  · rw [hv]; simp only [TRw, TGw, TUAw]; ring
  · simp only [TLx, TRx, TVAx, TVBx]; linear_combination t * hxy
  · simp only [TLw, TRw, TVAw, TVBw]; linear_combination (-1) * hxy
  · simp only [TVx, TGx, TVAx, TVBx]; linear_combination t * hxy
  · simp only [TVw, TGw, TVAw, TVBw]; linear_combination (-1) * hxy

end Erdos634.BeesonT24Gen
