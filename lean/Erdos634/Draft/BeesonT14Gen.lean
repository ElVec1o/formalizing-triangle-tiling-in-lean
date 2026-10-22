import Erdos634.Draft.BeesonT14Grid

/-!
# Beeson Theorem 14 (arXiv 1206.2229v4, Fig. 17) in GENERAL parameters

Tile `(a,b,c) = (g s t, g (s^2-t^2), g s^2)` (`3 alpha + 2 beta = pi`, `c < 2 b` iff `2 t^2 < s^2`),
scale `j` (`l = j c`).  All vertices of Fig. 17 are polynomial in `(g,s,t,j)` in the chart
`(X, W) -> (X / (2 s^4), rt0 W / (2 s^4))`, `rt0^2 = 4 s^2 - t^2`.
Credit Beeson (arXiv 1206.2229), Beeson-Zhang, Zhang (arXiv 2512.22696), Laczkovich.  UNAUDITED.
-/

namespace Erdos634.BeesonT14Gen

open Erdos634.Geometry Erdos634.CertCoord Erdos634.CertGeom Erdos634.RegionDissection
  Erdos634.GlueCut Erdos634.SssCongruent Erdos634.ZhangL1 Erdos634.ZhangPara
  Erdos634.ZhangSporadic Erdos634.ZhangThm4 Erdos634.BeesonT14Chart Erdos634.BeesonT14Abs
  Erdos634.BeesonT14Piece Erdos634.BeesonT14Grid

section defs
noncomputable def Kc (g s t j : ℝ) : ℝ := 2*g^2*j*s^8
noncomputable def Bx (g s t j : ℝ) : ℝ := g^2*j*(s-t)*(s+t)*(3*s^2-t^2)*(2*s^4-4*s^2*t^2+t^4)
noncomputable def Bw (g s t j : ℝ) : ℝ := g^2*j*t*(s-t)*(s+t)*(2*s^2-t^2)*(3*s^2-t^2)
noncomputable def Px (g s t j : ℝ) : ℝ := g^2*j*s^4*(s-t)*(s+t)*(2*s^2-t^2)
noncomputable def Pw (g s t j : ℝ) : ℝ := g^2*j*s^4*t*(s-t)*(s+t)
noncomputable def Qx (g s t j : ℝ) : ℝ := g^2*j*s^4*(2*s^4-4*s^2*t^2+t^4)
noncomputable def Qw (g s t j : ℝ) : ℝ := g^2*j*s^4*t*(2*s^2-t^2)
noncomputable def Rx (g s t j : ℝ) : ℝ := g^2*j*s^2*(s-t)^2*(s+t)^2*(2*s-t)*(2*s+t)
noncomputable def Rw (g s t j : ℝ) : ℝ := g^2*j*s^2*t*(s-t)*(s+t)*(3*s^2-t^2)
noncomputable def Sx (g s t j : ℝ) : ℝ := g^2*j*s^2*(2*s^6-s^4*t^2-3*s^2*t^4+t^6)
noncomputable def Sw (g s t j : ℝ) : ℝ := g^2*j*s^2*t*(s^4+s^2*t^2-t^4)
noncomputable def Tx (g s t j : ℝ) : ℝ := 2*g^2*j*s^2*(s-t)*(s+t)*(2*s^4-4*s^2*t^2+t^4)
noncomputable def Tw (g s t j : ℝ) : ℝ := 2*g^2*j*s^2*t*(s-t)*(s+t)*(2*s^2-t^2)
noncomputable def Ux (g s t j : ℝ) : ℝ := g*s*t*(s-t)*(s+t)*(3*s^2-t^2)
noncomputable def Uw (g s t j : ℝ) : ℝ := -(g*s*(s-t)^2*(s+t)^2)
noncomputable def Vx (g s t j : ℝ) : ℝ := g*s*t*(2*s^4-4*s^2*t^2+t^4)
noncomputable def Vw (g s t j : ℝ) : ℝ := g*s*t^2*(2*s^2-t^2)
noncomputable def th1 (g s t j : ℝ) : ℝ := s^4/((s-t)*(s+t)*(3*s^2-t^2))
noncomputable def th2 (g s t j : ℝ) : ℝ := 2*s^2/(3*s^2-t^2)
noncomputable def ta (g s t j : ℝ) : ℝ := s^2/(2*s^2-t^2)
noncomputable def rh (g s t j : ℝ) : ℝ := t^2/((s-t)*(s+t))
noncomputable def xb (g s t : ℝ) : ℝ := g * (s ^ 2 - t ^ 2) * (2 * s ^ 2 - t ^ 2) / (2 * s ^ 2)
noncomputable def yb (g s t rt0 : ℝ) : ℝ := rt0 * g * t * (s ^ 2 - t ^ 2) / (2 * s ^ 2)
noncomputable def bbc (g s t : ℝ) : ℝ := g ^ 2 * (s ^ 2 - t ^ 2) ^ 2
noncomputable def aac (g s t : ℝ) : ℝ := g ^ 2 * s ^ 2 * t ^ 2
end defs

structure Par (g s t j rt0 : ℝ) : Prop where
  hg : 0 < g
  hj : 0 < j
  hs : 0 < s
  ht : 0 < t
  hts : t < s
  hq : 2 * t ^ 2 < s ^ 2
  hrt : 0 < rt0
  hD : rt0 * rt0 = 4 * s ^ 2 - t ^ 2

def sg0 : Equiv.Perm (Fin 3) := ⟨![0, 1, 2], ![0, 1, 2], by decide, by decide⟩
def sg1 : Equiv.Perm (Fin 3) := ⟨![2, 0, 1], ![1, 2, 0], by decide, by decide⟩
def sg2 : Equiv.Perm (Fin 3) := ⟨![1, 2, 0], ![2, 0, 1], by decide, by decide⟩
def sg3 : Equiv.Perm (Fin 3) := ⟨![1, 0, 2], ![1, 0, 2], by decide, by decide⟩
def sg4 : Equiv.Perm (Fin 3) := ⟨![0, 2, 1], ![0, 2, 1], by decide, by decide⟩
def sg5 : Equiv.Perm (Fin 3) := ⟨![2, 1, 0], ![2, 1, 0], by decide, by decide⟩

theorem tile_facts {g s t j rt0 : ℝ} (P : Par g s t j rt0) :
    0 < det3 0 0 (g * s ^ 2) 0 (xb g s t) (yb g s t rt0) ∧ xb g s t ^ 2 + yb g s t rt0 ^ 2 = bbc g s t ∧
    (g * s ^ 2 - xb g s t) ^ 2 + yb g s t rt0 ^ 2 = aac g s t := by
  obtain ⟨hg, hj, hs, ht, hts, hq, hrt, hD⟩ := P
  have hp : 0 < s ^ 2 - t ^ 2 := by nlinarith
  have hy2 : yb g s t rt0 ^ 2 = (4 * s ^ 2 - t ^ 2) * (g * t * (s ^ 2 - t ^ 2) / (2 * s ^ 2)) ^ 2 := by
    unfold yb
    have : (rt0 * g * t * (s ^ 2 - t ^ 2) / (2 * s ^ 2)) ^ 2 = rt0 * rt0 * (g * t * (s ^ 2 - t ^ 2) / (2 * s ^ 2)) ^ 2 := by ring
    rw [this, hD]
  refine ⟨?_, ?_, ?_⟩
  · simp only [det3, xb, yb]
    have : 0 < g * s ^ 2 * (rt0 * g * t * (s ^ 2 - t ^ 2) / (2 * s ^ 2)) := by positivity
    nlinarith
  · rw [hy2]; unfold xb bbc; field_simp; ring
  · rw [hy2]; unfold xb aac; field_simp; ring

theorem fact_dBig {g s t j rt0 : ℝ} (P : Par g s t j rt0) :
    0 < detR 0 0 (Kc g s t j) 0 (Bx g s t j) (Bw g s t j) := by
  obtain ⟨hg, hj, hs, ht, hts, hq, hrt, hD⟩ := P
  have h1 : 0 < s - t := by linarith
  have h2 : 0 < s + t := by linarith
  have h3 : 0 < s ^ 2 - 2 * t ^ 2 := by linarith
  have h4 : 0 < 2 * s ^ 2 - t ^ 2 := by nlinarith
  have h5 : 0 < 3 * s ^ 2 - t ^ 2 := by nlinarith
  have e : detR 0 0 (Kc g s t j) 0 (Bx g s t j) (Bw g s t j) = 2*g^4*j^2*s^8*t*(s - t)*(s + t)*(2*s^2 - t^2)*(3*s^2 - t^2) := by simp only [detR, Kc, Bx, Bw, Px, Pw, Qx, Qw, Rx, Rw, Sx, Sw, Tx, Tw]; ring
  rw [e]; positivity

theorem fact_dBlue {g s t j rt0 : ℝ} (P : Par g s t j rt0) :
    0 < detR 0 0 (Kc g s t j) 0 (Px g s t j) (Pw g s t j) := by
  obtain ⟨hg, hj, hs, ht, hts, hq, hrt, hD⟩ := P
  have h1 : 0 < s - t := by linarith
  have h2 : 0 < s + t := by linarith
  have h3 : 0 < s ^ 2 - 2 * t ^ 2 := by linarith
  have h4 : 0 < 2 * s ^ 2 - t ^ 2 := by nlinarith
  have h5 : 0 < 3 * s ^ 2 - t ^ 2 := by nlinarith
  have e : detR 0 0 (Kc g s t j) 0 (Px g s t j) (Pw g s t j) = 2*g^4*j^2*s^12*t*(s - t)*(s + t) := by simp only [detR, Kc, Bx, Bw, Px, Pw, Qx, Qw, Rx, Rw, Sx, Sw, Tx, Tw]; ring
  rw [e]; positivity

theorem fact_dPink {g s t j rt0 : ℝ} (P : Par g s t j rt0) :
    0 < detR (Kc g s t j) 0 (Rx g s t j) (Rw g s t j) (Px g s t j) (Pw g s t j) := by
  obtain ⟨hg, hj, hs, ht, hts, hq, hrt, hD⟩ := P
  have h1 : 0 < s - t := by linarith
  have h2 : 0 < s + t := by linarith
  have h3 : 0 < s ^ 2 - 2 * t ^ 2 := by linarith
  have h4 : 0 < 2 * s ^ 2 - t ^ 2 := by nlinarith
  have h5 : 0 < 3 * s ^ 2 - t ^ 2 := by nlinarith
  have e : detR (Kc g s t j) 0 (Rx g s t j) (Rw g s t j) (Px g s t j) (Pw g s t j) = 2*g^4*j^2*s^12*t*(s - t)*(s + t) := by simp only [detR, Kc, Bx, Bw, Px, Pw, Qx, Qw, Rx, Rw, Sx, Sw, Tx, Tw]; ring
  rw [e]; positivity

theorem fact_dGreen {g s t j rt0 : ℝ} (P : Par g s t j rt0) :
    0 < detR 0 0 (Px g s t j) (Pw g s t j) (Qx g s t j) (Qw g s t j) := by
  obtain ⟨hg, hj, hs, ht, hts, hq, hrt, hD⟩ := P
  have h1 : 0 < s - t := by linarith
  have h2 : 0 < s + t := by linarith
  have h3 : 0 < s ^ 2 - 2 * t ^ 2 := by linarith
  have h4 : 0 < 2 * s ^ 2 - t ^ 2 := by nlinarith
  have h5 : 0 < 3 * s ^ 2 - t ^ 2 := by nlinarith
  have e : detR 0 0 (Px g s t j) (Pw g s t j) (Qx g s t j) (Qw g s t j) = 2*g^4*j^2*s^12*t*(s - t)*(s + t) := by simp only [detR, Kc, Bx, Bw, Px, Pw, Qx, Qw, Rx, Rw, Sx, Sw, Tx, Tw]; ring
  rw [e]; positivity

theorem fact_dYellow {g s t j rt0 : ℝ} (P : Par g s t j rt0) :
    0 < detR (Px g s t j) (Pw g s t j) (Sx g s t j) (Sw g s t j) (Qx g s t j) (Qw g s t j) := by
  obtain ⟨hg, hj, hs, ht, hts, hq, hrt, hD⟩ := P
  have h1 : 0 < s - t := by linarith
  have h2 : 0 < s + t := by linarith
  have h3 : 0 < s ^ 2 - 2 * t ^ 2 := by linarith
  have h4 : 0 < 2 * s ^ 2 - t ^ 2 := by nlinarith
  have h5 : 0 < 3 * s ^ 2 - t ^ 2 := by nlinarith
  have e : detR (Px g s t j) (Pw g s t j) (Sx g s t j) (Sw g s t j) (Qx g s t j) (Qw g s t j) = 2*g^4*j^2*s^10*t^3*(s - t)*(s + t) := by simp only [detR, Kc, Bx, Bw, Px, Pw, Qx, Qw, Rx, Rw, Sx, Sw, Tx, Tw]; ring
  rw [e]; positivity

theorem fact_dTop {g s t j rt0 : ℝ} (P : Par g s t j rt0) :
    0 < detR (Tx g s t j) (Tw g s t j) (Rx g s t j) (Rw g s t j) (Bx g s t j) (Bw g s t j) := by
  obtain ⟨hg, hj, hs, ht, hts, hq, hrt, hD⟩ := P
  have h1 : 0 < s - t := by linarith
  have h2 : 0 < s + t := by linarith
  have h3 : 0 < s ^ 2 - 2 * t ^ 2 := by linarith
  have h4 : 0 < 2 * s ^ 2 - t ^ 2 := by nlinarith
  have h5 : 0 < 3 * s ^ 2 - t ^ 2 := by nlinarith
  have e : detR (Tx g s t j) (Tw g s t j) (Rx g s t j) (Rw g s t j) (Bx g s t j) (Bw g s t j) = 2*g^4*j^2*s^8*t*(s - t)^3*(s + t)^3 := by simp only [detR, Kc, Bx, Bw, Px, Pw, Qx, Qw, Rx, Rw, Sx, Sw, Tx, Tw]; ring
  rw [e]; positivity

theorem fact_dO1 {g s t j rt0 : ℝ} (P : Par g s t j rt0) :
    0 < detR (Qx g s t j) (Qw g s t j) (Sx g s t j) (Sw g s t j) (Rx g s t j) (Rw g s t j) := by
  obtain ⟨hg, hj, hs, ht, hts, hq, hrt, hD⟩ := P
  have h1 : 0 < s - t := by linarith
  have h2 : 0 < s + t := by linarith
  have h3 : 0 < s ^ 2 - 2 * t ^ 2 := by linarith
  have h4 : 0 < 2 * s ^ 2 - t ^ 2 := by nlinarith
  have h5 : 0 < 3 * s ^ 2 - t ^ 2 := by nlinarith
  have e : detR (Qx g s t j) (Qw g s t j) (Sx g s t j) (Sw g s t j) (Rx g s t j) (Rw g s t j) = 2*g^4*j^2*s^10*t*(s - t)*(s + t)*(s^2 - 2*t^2) := by simp only [detR, Kc, Bx, Bw, Px, Pw, Qx, Qw, Rx, Rw, Sx, Sw, Tx, Tw]; ring
  rw [e]; positivity

theorem fact_dO2 {g s t j rt0 : ℝ} (P : Par g s t j rt0) :
    0 < detR (Qx g s t j) (Qw g s t j) (Rx g s t j) (Rw g s t j) (Tx g s t j) (Tw g s t j) := by
  obtain ⟨hg, hj, hs, ht, hts, hq, hrt, hD⟩ := P
  have h1 : 0 < s - t := by linarith
  have h2 : 0 < s + t := by linarith
  have h3 : 0 < s ^ 2 - 2 * t ^ 2 := by linarith
  have h4 : 0 < 2 * s ^ 2 - t ^ 2 := by nlinarith
  have h5 : 0 < 3 * s ^ 2 - t ^ 2 := by nlinarith
  have e : detR (Qx g s t j) (Qw g s t j) (Rx g s t j) (Rw g s t j) (Tx g s t j) (Tw g s t j) = 2*g^4*j^2*s^10*t*(s - t)*(s + t)*(s^2 - 2*t^2) := by simp only [detR, Kc, Bx, Bw, Px, Pw, Qx, Qw, Rx, Rw, Sx, Sw, Tx, Tw]; ring
  rw [e]; positivity

theorem fact_hP1 {g s t j rt0 : ℝ} (P : Par g s t j rt0) :
    0 ≤ detR (Px g s t j) (Pw g s t j) (Kc g s t j) 0 (Bx g s t j) (Bw g s t j) := by
  obtain ⟨hg, hj, hs, ht, hts, hq, hrt, hD⟩ := P
  have h1 : 0 < s - t := by linarith
  have h2 : 0 < s + t := by linarith
  have h3 : 0 < s ^ 2 - 2 * t ^ 2 := by linarith
  have h4 : 0 < 2 * s ^ 2 - t ^ 2 := by nlinarith
  have h5 : 0 < 3 * s ^ 2 - t ^ 2 := by nlinarith
  have e : detR (Px g s t j) (Pw g s t j) (Kc g s t j) 0 (Bx g s t j) (Bw g s t j) = 2*g^4*j^2*s^10*t*(s - t)*(s + t)*(2*s^2 - t^2) := by simp only [detR, Kc, Bx, Bw, Px, Pw, Qx, Qw, Rx, Rw, Sx, Sw, Tx, Tw]; ring
  rw [e]; positivity

theorem fact_hP2 {g s t j rt0 : ℝ} (P : Par g s t j rt0) :
    0 ≤ detR 0 0 (Px g s t j) (Pw g s t j) (Bx g s t j) (Bw g s t j) := by
  obtain ⟨hg, hj, hs, ht, hts, hq, hrt, hD⟩ := P
  have h1 : 0 < s - t := by linarith
  have h2 : 0 < s + t := by linarith
  have h3 : 0 < s ^ 2 - 2 * t ^ 2 := by linarith
  have h4 : 0 < 2 * s ^ 2 - t ^ 2 := by nlinarith
  have h5 : 0 < 3 * s ^ 2 - t ^ 2 := by nlinarith
  have e : detR 0 0 (Px g s t j) (Pw g s t j) (Bx g s t j) (Bw g s t j) = 2*g^4*j^2*s^8*t*(s - t)^2*(s + t)^2*(3*s^2 - t^2) := by simp only [detR, Kc, Bx, Bw, Px, Pw, Qx, Qw, Rx, Rw, Sx, Sw, Tx, Tw]; ring
  rw [e]; positivity

theorem fact_hP3 {g s t j rt0 : ℝ} (P : Par g s t j rt0) :
    0 ≤ detR 0 0 (Kc g s t j) 0 (Px g s t j) (Pw g s t j) := by
  obtain ⟨hg, hj, hs, ht, hts, hq, hrt, hD⟩ := P
  have h1 : 0 < s - t := by linarith
  have h2 : 0 < s + t := by linarith
  have h3 : 0 < s ^ 2 - 2 * t ^ 2 := by linarith
  have h4 : 0 < 2 * s ^ 2 - t ^ 2 := by nlinarith
  have h5 : 0 < 3 * s ^ 2 - t ^ 2 := by nlinarith
  have e : detR 0 0 (Kc g s t j) 0 (Px g s t j) (Pw g s t j) = 2*g^4*j^2*s^12*t*(s - t)*(s + t) := by simp only [detR, Kc, Bx, Bw, Px, Pw, Qx, Qw, Rx, Rw, Sx, Sw, Tx, Tw]; ring
  rw [e]; positivity

theorem fact_hF6A {g s t j rt0 : ℝ} (P : Par g s t j rt0) :
    detR (Tx g s t j) (Tw g s t j) (Rx g s t j) (Rw g s t j) 0 0 ≤ 0 := by
  obtain ⟨hg, hj, hs, ht, hts, hq, hrt, hD⟩ := P
  have h1 : 0 < s - t := by linarith
  have h2 : 0 < s + t := by linarith
  have h3 : 0 < s ^ 2 - 2 * t ^ 2 := by linarith
  have h4 : 0 < 2 * s ^ 2 - t ^ 2 := by nlinarith
  have h5 : 0 < 3 * s ^ 2 - t ^ 2 := by nlinarith
  have e : detR (Tx g s t j) (Tw g s t j) (Rx g s t j) (Rw g s t j) 0 0 = -(4*g^4*j^2*s^10*t*(s - t)^2*(s + t)^2) := by simp only [detR, Kc, Bx, Bw, Px, Pw, Qx, Qw, Rx, Rw, Sx, Sw, Tx, Tw]; ring
  rw [e]; have : 0 < 4*g^4*j^2*s^10*t*(s - t)^2*(s + t)^2 := by positivity
  linarith

theorem fact_hF6C {g s t j rt0 : ℝ} (P : Par g s t j rt0) :
    detR (Tx g s t j) (Tw g s t j) (Rx g s t j) (Rw g s t j) (Kc g s t j) 0 ≤ 0 := by
  obtain ⟨hg, hj, hs, ht, hts, hq, hrt, hD⟩ := P
  have h1 : 0 < s - t := by linarith
  have h2 : 0 < s + t := by linarith
  have h3 : 0 < s ^ 2 - 2 * t ^ 2 := by linarith
  have h4 : 0 < 2 * s ^ 2 - t ^ 2 := by nlinarith
  have h5 : 0 < 3 * s ^ 2 - t ^ 2 := by nlinarith
  have e : detR (Tx g s t j) (Tw g s t j) (Rx g s t j) (Rw g s t j) (Kc g s t j) 0 = -(2*g^4*j^2*s^10*t*(s - t)^2*(s + t)^2) := by simp only [detR, Kc, Bx, Bw, Px, Pw, Qx, Qw, Rx, Rw, Sx, Sw, Tx, Tw]; ring
  rw [e]; have : 0 < 2*g^4*j^2*s^10*t*(s - t)^2*(s + t)^2 := by positivity
  linarith

theorem fact_hF6P {g s t j rt0 : ℝ} (P : Par g s t j rt0) :
    detR (Tx g s t j) (Tw g s t j) (Rx g s t j) (Rw g s t j) (Px g s t j) (Pw g s t j) ≤ 0 := by
  obtain ⟨hg, hj, hs, ht, hts, hq, hrt, hD⟩ := P
  have h1 : 0 < s - t := by linarith
  have h2 : 0 < s + t := by linarith
  have h3 : 0 < s ^ 2 - 2 * t ^ 2 := by linarith
  have h4 : 0 < 2 * s ^ 2 - t ^ 2 := by nlinarith
  have h5 : 0 < 3 * s ^ 2 - t ^ 2 := by nlinarith
  have e : detR (Tx g s t j) (Tw g s t j) (Rx g s t j) (Rw g s t j) (Px g s t j) (Pw g s t j) = -(2*g^4*j^2*s^10*t*(s - t)^2*(s + t)^2) := by simp only [detR, Kc, Bx, Bw, Px, Pw, Qx, Qw, Rx, Rw, Sx, Sw, Tx, Tw]; ring
  rw [e]; have : 0 < 2*g^4*j^2*s^10*t*(s - t)^2*(s + t)^2 := by positivity
  linarith

theorem fact_hF6Q {g s t j rt0 : ℝ} (P : Par g s t j rt0) :
    detR (Tx g s t j) (Tw g s t j) (Rx g s t j) (Rw g s t j) (Qx g s t j) (Qw g s t j) ≤ 0 := by
  obtain ⟨hg, hj, hs, ht, hts, hq, hrt, hD⟩ := P
  have h1 : 0 < s - t := by linarith
  have h2 : 0 < s + t := by linarith
  have h3 : 0 < s ^ 2 - 2 * t ^ 2 := by linarith
  have h4 : 0 < 2 * s ^ 2 - t ^ 2 := by nlinarith
  have h5 : 0 < 3 * s ^ 2 - t ^ 2 := by nlinarith
  have e : detR (Tx g s t j) (Tw g s t j) (Rx g s t j) (Rw g s t j) (Qx g s t j) (Qw g s t j) = -(2*g^4*j^2*s^10*t*(s - t)*(s + t)*(s^2 - 2*t^2)) := by simp only [detR, Kc, Bx, Bw, Px, Pw, Qx, Qw, Rx, Rw, Sx, Sw, Tx, Tw]; ring
  rw [e]; have : 0 < 2*g^4*j^2*s^10*t*(s - t)*(s + t)*(s^2 - 2*t^2) := by positivity
  linarith

theorem fact_hF5A {g s t j rt0 : ℝ} (P : Par g s t j rt0) :
    detR (Qx g s t j) (Qw g s t j) (Sx g s t j) (Sw g s t j) 0 0 ≤ 0 := by
  obtain ⟨hg, hj, hs, ht, hts, hq, hrt, hD⟩ := P
  have h1 : 0 < s - t := by linarith
  have h2 : 0 < s + t := by linarith
  have h3 : 0 < s ^ 2 - 2 * t ^ 2 := by linarith
  have h4 : 0 < 2 * s ^ 2 - t ^ 2 := by nlinarith
  have h5 : 0 < 3 * s ^ 2 - t ^ 2 := by nlinarith
  have e : detR (Qx g s t j) (Qw g s t j) (Sx g s t j) (Sw g s t j) 0 0 = -(2*g^4*j^2*s^12*t*(s - t)*(s + t)) := by simp only [detR, Kc, Bx, Bw, Px, Pw, Qx, Qw, Rx, Rw, Sx, Sw, Tx, Tw]; ring
  rw [e]; have : 0 < 2*g^4*j^2*s^12*t*(s - t)*(s + t) := by positivity
  linarith

theorem fact_hF5C {g s t j rt0 : ℝ} (P : Par g s t j rt0) :
    detR (Qx g s t j) (Qw g s t j) (Sx g s t j) (Sw g s t j) (Kc g s t j) 0 ≤ 0 := by
  obtain ⟨hg, hj, hs, ht, hts, hq, hrt, hD⟩ := P
  have h1 : 0 < s - t := by linarith
  have h2 : 0 < s + t := by linarith
  have h3 : 0 < s ^ 2 - 2 * t ^ 2 := by linarith
  have h4 : 0 < 2 * s ^ 2 - t ^ 2 := by nlinarith
  have h5 : 0 < 3 * s ^ 2 - t ^ 2 := by nlinarith
  have e : detR (Qx g s t j) (Qw g s t j) (Sx g s t j) (Sw g s t j) (Kc g s t j) 0 = -(2*g^4*j^2*s^10*t^3*(s - t)*(s + t)) := by simp only [detR, Kc, Bx, Bw, Px, Pw, Qx, Qw, Rx, Rw, Sx, Sw, Tx, Tw]; ring
  rw [e]; have : 0 < 2*g^4*j^2*s^10*t^3*(s - t)*(s + t) := by positivity
  linarith

theorem fact_hF5P {g s t j rt0 : ℝ} (P : Par g s t j rt0) :
    detR (Qx g s t j) (Qw g s t j) (Sx g s t j) (Sw g s t j) (Px g s t j) (Pw g s t j) ≤ 0 := by
  obtain ⟨hg, hj, hs, ht, hts, hq, hrt, hD⟩ := P
  have h1 : 0 < s - t := by linarith
  have h2 : 0 < s + t := by linarith
  have h3 : 0 < s ^ 2 - 2 * t ^ 2 := by linarith
  have h4 : 0 < 2 * s ^ 2 - t ^ 2 := by nlinarith
  have h5 : 0 < 3 * s ^ 2 - t ^ 2 := by nlinarith
  have e : detR (Qx g s t j) (Qw g s t j) (Sx g s t j) (Sw g s t j) (Px g s t j) (Pw g s t j) = -(2*g^4*j^2*s^10*t^3*(s - t)*(s + t)) := by simp only [detR, Kc, Bx, Bw, Px, Pw, Qx, Qw, Rx, Rw, Sx, Sw, Tx, Tw]; ring
  rw [e]; have : 0 < 2*g^4*j^2*s^10*t^3*(s - t)*(s + t) := by positivity
  linarith

theorem fact_hF4C {g s t j rt0 : ℝ} (P : Par g s t j rt0) :
    detR (Px g s t j) (Pw g s t j) (Rx g s t j) (Rw g s t j) (Kc g s t j) 0 ≤ 0 := by
  obtain ⟨hg, hj, hs, ht, hts, hq, hrt, hD⟩ := P
  have h1 : 0 < s - t := by linarith
  have h2 : 0 < s + t := by linarith
  have h3 : 0 < s ^ 2 - 2 * t ^ 2 := by linarith
  have h4 : 0 < 2 * s ^ 2 - t ^ 2 := by nlinarith
  have h5 : 0 < 3 * s ^ 2 - t ^ 2 := by nlinarith
  have e : detR (Px g s t j) (Pw g s t j) (Rx g s t j) (Rw g s t j) (Kc g s t j) 0 = -(2*g^4*j^2*s^12*t*(s - t)*(s + t)) := by simp only [detR, Kc, Bx, Bw, Px, Pw, Qx, Qw, Rx, Rw, Sx, Sw, Tx, Tw]; ring
  rw [e]; have : 0 < 2*g^4*j^2*s^12*t*(s - t)*(s + t) := by positivity
  linarith

theorem fact_hPQS {g s t j rt0 : ℝ} (P : Par g s t j rt0) :
    detR (Px g s t j) (Pw g s t j) (Qx g s t j) (Qw g s t j) (Sx g s t j) (Sw g s t j) ≤ 0 := by
  obtain ⟨hg, hj, hs, ht, hts, hq, hrt, hD⟩ := P
  have h1 : 0 < s - t := by linarith
  have h2 : 0 < s + t := by linarith
  have h3 : 0 < s ^ 2 - 2 * t ^ 2 := by linarith
  have h4 : 0 < 2 * s ^ 2 - t ^ 2 := by nlinarith
  have h5 : 0 < 3 * s ^ 2 - t ^ 2 := by nlinarith
  have e : detR (Px g s t j) (Pw g s t j) (Qx g s t j) (Qw g s t j) (Sx g s t j) (Sw g s t j) = -(2*g^4*j^2*s^10*t^3*(s - t)*(s + t)) := by simp only [detR, Kc, Bx, Bw, Px, Pw, Qx, Qw, Rx, Rw, Sx, Sw, Tx, Tw]; ring
  rw [e]; have : 0 < 2*g^4*j^2*s^10*t^3*(s - t)*(s + t) := by positivity
  linarith

theorem fact_hPQA {g s t j rt0 : ℝ} (P : Par g s t j rt0) :
    0 ≤ detR (Px g s t j) (Pw g s t j) (Qx g s t j) (Qw g s t j) 0 0 := by
  obtain ⟨hg, hj, hs, ht, hts, hq, hrt, hD⟩ := P
  have h1 : 0 < s - t := by linarith
  have h2 : 0 < s + t := by linarith
  have h3 : 0 < s ^ 2 - 2 * t ^ 2 := by linarith
  have h4 : 0 < 2 * s ^ 2 - t ^ 2 := by nlinarith
  have h5 : 0 < 3 * s ^ 2 - t ^ 2 := by nlinarith
  have e : detR (Px g s t j) (Pw g s t j) (Qx g s t j) (Qw g s t j) 0 0 = 2*g^4*j^2*s^12*t*(s - t)*(s + t) := by simp only [detR, Kc, Bx, Bw, Px, Pw, Qx, Qw, Rx, Rw, Sx, Sw, Tx, Tw]; ring
  rw [e]; positivity

theorem fact_hF4Q {g s t j rt0 : ℝ} (P : Par g s t j rt0) :
    0 ≤ detR (Px g s t j) (Pw g s t j) (Rx g s t j) (Rw g s t j) (Qx g s t j) (Qw g s t j) := by
  obtain ⟨hg, hj, hs, ht, hts, hq, hrt, hD⟩ := P
  have h1 : 0 < s - t := by linarith
  have h2 : 0 < s + t := by linarith
  have h3 : 0 < s ^ 2 - 2 * t ^ 2 := by linarith
  have h4 : 0 < 2 * s ^ 2 - t ^ 2 := by nlinarith
  have h5 : 0 < 3 * s ^ 2 - t ^ 2 := by nlinarith
  have e : detR (Px g s t j) (Pw g s t j) (Rx g s t j) (Rw g s t j) (Qx g s t j) (Qw g s t j) = 2*g^4*j^2*s^10*t*(s - t)^2*(s + t)^2 := by simp only [detR, Kc, Bx, Bw, Px, Pw, Qx, Qw, Rx, Rw, Sx, Sw, Tx, Tw]; ring
  rw [e]; positivity

theorem fact_hF4A {g s t j rt0 : ℝ} (P : Par g s t j rt0) :
    0 ≤ detR (Px g s t j) (Pw g s t j) (Rx g s t j) (Rw g s t j) 0 0 := by
  obtain ⟨hg, hj, hs, ht, hts, hq, hrt, hD⟩ := P
  have h1 : 0 < s - t := by linarith
  have h2 : 0 < s + t := by linarith
  have h3 : 0 < s ^ 2 - 2 * t ^ 2 := by linarith
  have h4 : 0 < 2 * s ^ 2 - t ^ 2 := by nlinarith
  have h5 : 0 < 3 * s ^ 2 - t ^ 2 := by nlinarith
  have e : detR (Px g s t j) (Pw g s t j) (Rx g s t j) (Rw g s t j) 0 0 = 2*g^4*j^2*s^10*t*(s - t)^2*(s + t)^2 := by simp only [detR, Kc, Bx, Bw, Px, Pw, Qx, Qw, Rx, Rw, Sx, Sw, Tx, Tw]; ring
  rw [e]; positivity

theorem fact_hAPS {g s t j rt0 : ℝ} (P : Par g s t j rt0) :
    0 ≤ detR 0 0 (Px g s t j) (Pw g s t j) (Sx g s t j) (Sw g s t j) := by
  obtain ⟨hg, hj, hs, ht, hts, hq, hrt, hD⟩ := P
  have h1 : 0 < s - t := by linarith
  have h2 : 0 < s + t := by linarith
  have h3 : 0 < s ^ 2 - 2 * t ^ 2 := by linarith
  have h4 : 0 < 2 * s ^ 2 - t ^ 2 := by nlinarith
  have h5 : 0 < 3 * s ^ 2 - t ^ 2 := by nlinarith
  have e : detR 0 0 (Px g s t j) (Pw g s t j) (Sx g s t j) (Sw g s t j) = 2*g^4*j^2*s^10*t^3*(s - t)*(s + t) := by simp only [detR, Kc, Bx, Bw, Px, Pw, Qx, Qw, Rx, Rw, Sx, Sw, Tx, Tw]; ring
  rw [e]; positivity

theorem piece {g s t j rt0 : ℝ} (P : Par g s t j rt0) (m : ℕ) (hm : 0 < m) (σ : Equiv.Perm (Fin 3))
    (X0 W0 X1 W1 X2 W2 : ℝ) (hdet : 0 < detR X0 W0 X1 W1 X2 W2)
    (h01 : (X1 - X0) ^ 2 + (4 * s ^ 2 - t ^ 2) * (W1 - W0) ^ 2 =
      (2 * s ^ 4) ^ 2 * (m * m * Dt (g * s ^ 2 * (g * s ^ 2)) (bbc g s t) (aac g s t) (σ 0) (σ 1)))
    (h02 : (X2 - X0) ^ 2 + (4 * s ^ 2 - t ^ 2) * (W2 - W0) ^ 2 =
      (2 * s ^ 4) ^ 2 * (m * m * Dt (g * s ^ 2 * (g * s ^ 2)) (bbc g s t) (aac g s t) (σ 0) (σ 2)))
    (h12 : (X2 - X1) ^ 2 + (4 * s ^ 2 - t ^ 2) * (W2 - W1) ^ 2 =
      (2 * s ^ 4) ^ 2 * (m * m * Dt (g * s ^ 2 * (g * s ^ 2)) (bbc g s t) (aac g s t) (σ 1) (σ 2))) :
    Dis (tile (g * s ^ 2) (xb g s t) (yb g s t rt0) (tile_facts P).1)
      (CS (1 / (2 * s ^ 4)) (rt0 / (2 * s ^ 4)) (TriR X0 W0 X1 W1 X2 W2)) (m * m) :=
  Dis_piece_gen (tile_facts P).1 (tile_facts P).2.1 (tile_facts P).2.2
    (by have := P.hs; positivity) P.hrt P.hD m hm σ X0 W0 X1 W1 X2 W2 hdet h01 h02 h12

theorem blue_dis {g s t j rt0 : ℝ} (P : Par g s t j rt0) (L : ℕ) (hL0 : 0 < L)
    (hL : (L : ℝ) = j * g * s ^ 2) :
    Dis (tile (g * s ^ 2) (xb g s t) (yb g s t rt0) (tile_facts P).1)
      (CS (1 / (2 * s ^ 4)) (rt0 / (2 * s ^ 4))
        (TriR 0 0 (Kc g s t j) 0 (Px g s t j) (Pw g s t j))) (L * L) :=
  piece P L hL0 sg0 _ _ _ _ _ _ (fact_dBlue P)
    (by simp [sg0, Dt]; rw [hL]; simp only [Kc, bbc, aac]; ring)
    (by simp [sg0, Dt]; rw [hL]; simp only [Px, Pw, bbc, aac]; ring)
    (by simp [sg0, Dt]; rw [hL]; simp only [Px, Pw, Kc, bbc, aac]; ring)

theorem pink_dis {g s t j rt0 : ℝ} (P : Par g s t j rt0) (m : ℕ) (hm0 : 0 < m)
    (hm : (m : ℝ) = j * g * s ^ 2) :
    Dis (tile (g * s ^ 2) (xb g s t) (yb g s t rt0) (tile_facts P).1)
      (CS (1 / (2 * s ^ 4)) (rt0 / (2 * s ^ 4))
        (TriR (Kc g s t j) 0 (Rx g s t j) (Rw g s t j) (Px g s t j) (Pw g s t j))) (m * m) :=
  piece P m hm0 sg3 _ _ _ _ _ _ (fact_dPink P)
    (by simp [sg3, Dt]; rw [hm]; simp only [Kc, Bx, Bw, Px, Pw, Qx, Qw, Rx, Rw, Sx, Sw, Tx, Tw, Ux, Uw, Vx, Vw, bbc, aac]; ring)
    (by simp [sg3, Dt]; rw [hm]; simp only [Kc, Bx, Bw, Px, Pw, Qx, Qw, Rx, Rw, Sx, Sw, Tx, Tw, Ux, Uw, Vx, Vw, bbc, aac]; ring)
    (by simp [sg3, Dt]; rw [hm]; simp only [Kc, Bx, Bw, Px, Pw, Qx, Qw, Rx, Rw, Sx, Sw, Tx, Tw, Ux, Uw, Vx, Vw, bbc, aac]; ring)

theorem green_dis {g s t j rt0 : ℝ} (P : Par g s t j rt0) (m : ℕ) (hm0 : 0 < m)
    (hm : (m : ℝ) = j * g * s ^ 2) :
    Dis (tile (g * s ^ 2) (xb g s t) (yb g s t rt0) (tile_facts P).1)
      (CS (1 / (2 * s ^ 4)) (rt0 / (2 * s ^ 4))
        (TriR 0 0 (Px g s t j) (Pw g s t j) (Qx g s t j) (Qw g s t j))) (m * m) :=
  piece P m hm0 sg4 _ _ _ _ _ _ (fact_dGreen P)
    (by simp [sg4, Dt]; rw [hm]; simp only [Kc, Bx, Bw, Px, Pw, Qx, Qw, Rx, Rw, Sx, Sw, Tx, Tw, Ux, Uw, Vx, Vw, bbc, aac]; ring)
    (by simp [sg4, Dt]; rw [hm]; simp only [Kc, Bx, Bw, Px, Pw, Qx, Qw, Rx, Rw, Sx, Sw, Tx, Tw, Ux, Uw, Vx, Vw, bbc, aac]; ring)
    (by simp [sg4, Dt]; rw [hm]; simp only [Kc, Bx, Bw, Px, Pw, Qx, Qw, Rx, Rw, Sx, Sw, Tx, Tw, Ux, Uw, Vx, Vw, bbc, aac]; ring)

theorem yellow_dis {g s t j rt0 : ℝ} (P : Par g s t j rt0) (m : ℕ) (hm0 : 0 < m)
    (hm : (m : ℝ) = j * g * s * t) :
    Dis (tile (g * s ^ 2) (xb g s t) (yb g s t rt0) (tile_facts P).1)
      (CS (1 / (2 * s ^ 4)) (rt0 / (2 * s ^ 4))
        (TriR (Px g s t j) (Pw g s t j) (Sx g s t j) (Sw g s t j) (Qx g s t j) (Qw g s t j))) (m * m) :=
  piece P m hm0 sg2 _ _ _ _ _ _ (fact_dYellow P)
    (by simp [sg2, Dt]; rw [hm]; simp only [Kc, Bx, Bw, Px, Pw, Qx, Qw, Rx, Rw, Sx, Sw, Tx, Tw, Ux, Uw, Vx, Vw, bbc, aac]; ring)
    (by simp [sg2, Dt]; rw [hm]; simp only [Kc, Bx, Bw, Px, Pw, Qx, Qw, Rx, Rw, Sx, Sw, Tx, Tw, Ux, Uw, Vx, Vw, bbc, aac]; ring)
    (by simp [sg2, Dt]; rw [hm]; simp only [Kc, Bx, Bw, Px, Pw, Qx, Qw, Rx, Rw, Sx, Sw, Tx, Tw, Ux, Uw, Vx, Vw, bbc, aac]; ring)

theorem top_dis {g s t j rt0 : ℝ} (P : Par g s t j rt0) (m : ℕ) (hm0 : 0 < m)
    (hm : (m : ℝ) = j * g * (s ^ 2 - t ^ 2)) :
    Dis (tile (g * s ^ 2) (xb g s t) (yb g s t rt0) (tile_facts P).1)
      (CS (1 / (2 * s ^ 4)) (rt0 / (2 * s ^ 4))
        (TriR (Tx g s t j) (Tw g s t j) (Rx g s t j) (Rw g s t j) (Bx g s t j) (Bw g s t j))) (m * m) :=
  piece P m hm0 sg5 _ _ _ _ _ _ (fact_dTop P)
    (by simp [sg5, Dt]; rw [hm]; simp only [Kc, Bx, Bw, Px, Pw, Qx, Qw, Rx, Rw, Sx, Sw, Tx, Tw, Ux, Uw, Vx, Vw, bbc, aac]; ring)
    (by simp [sg5, Dt]; rw [hm]; simp only [Kc, Bx, Bw, Px, Pw, Qx, Qw, Rx, Rw, Sx, Sw, Tx, Tw, Ux, Uw, Vx, Vw, bbc, aac]; ring)
    (by simp [sg5, Dt]; rw [hm]; simp only [Kc, Bx, Bw, Px, Pw, Qx, Qw, Rx, Rw, Sx, Sw, Tx, Tw, Ux, Uw, Vx, Vw, bbc, aac]; ring)

theorem fact_delta {g s t j rt0 : ℝ} (P : Par g s t j rt0) :
    0 < Ux g s t j * Vw g s t j - Uw g s t j * Vx g s t j := by
  obtain ⟨hg, hj, hs, ht, hts, hq, hrt, hD⟩ := P
  have h1 : 0 < s - t := by linarith
  have h2 : 0 < s + t := by linarith
  have e : Ux g s t j * Vw g s t j - Uw g s t j * Vx g s t j = 2*g^2*s^8*t*(s - t)*(s + t) := by
    simp only [Ux, Uw, Vx, Vw]; ring
  rw [e]; positivity

theorem cell_t1 {g s t j rt0 : ℝ} (P : Par g s t j rt0) (Ox Ow : ℝ) :
    Dis (tile (g * s ^ 2) (xb g s t) (yb g s t rt0) (tile_facts P).1)
      (CS (1 / (2 * s ^ 4)) (rt0 / (2 * s ^ 4))
        (TriR Ox Ow (Ox + Ux g s t j) (Ow + Uw g s t j) (Ox + Vx g s t j) (Ow + Vw g s t j))) 1 := by
  have hd : 0 < detR Ox Ow (Ox + Ux g s t j) (Ow + Uw g s t j) (Ox + Vx g s t j) (Ow + Vw g s t j) := by
    have := fact_delta P
    simp only [detR]; nlinarith
  refine (piece P 1 one_pos sg1 _ _ _ _ _ _ hd ?_ ?_ ?_).congr rfl (by norm_num)
  all_goals (simp [sg1, Dt]; simp only [Ux, Uw, Vx, Vw, bbc, aac]; ring)

theorem cell_t2 {g s t j rt0 : ℝ} (P : Par g s t j rt0) (Ox Ow : ℝ) :
    Dis (tile (g * s ^ 2) (xb g s t) (yb g s t rt0) (tile_facts P).1)
      (CS (1 / (2 * s ^ 4)) (rt0 / (2 * s ^ 4))
        (TriR (Ox + Ux g s t j) (Ow + Uw g s t j) (Ox + Ux g s t j + Vx g s t j)
          (Ow + Uw g s t j + Vw g s t j) (Ox + Vx g s t j) (Ow + Vw g s t j))) 1 := by
  have hd : 0 < detR (Ox + Ux g s t j) (Ow + Uw g s t j) (Ox + Ux g s t j + Vx g s t j)
      (Ow + Uw g s t j + Vw g s t j) (Ox + Vx g s t j) (Ow + Vw g s t j) := by
    have := fact_delta P
    simp only [detR]; nlinarith
  refine (piece P 1 one_pos sg2 _ _ _ _ _ _ hd ?_ ?_ ?_).congr rfl (by norm_num)
  all_goals (simp [sg2, Dt]; simp only [Ux, Uw, Vx, Vw, bbc, aac, Kc]; ring)

set_option maxHeartbeats 4000000 in
theorem core {g s t j rt0 : ℝ} (P : Par g s t j rt0) (L JB m n : ℕ) (hL0 : 0 < L) (hJB0 : 0 < JB)
    (hL : (L : ℝ) = j * g * s ^ 2) (hJA : ((m + 1 : ℕ) : ℝ) = j * g * s * t)
    (hJB : (JB : ℝ) = j * g * (s ^ 2 - t ^ 2))
    (hr : ((n + 1 : ℕ) : ℝ) * t = j * g * s * (s ^ 2 - 2 * t ^ 2)) :
    Dis (tile (g * s ^ 2) (xb g s t) (yb g s t rt0) (tile_facts P).1)
      (CS (1 / (2 * s ^ 4)) (rt0 / (2 * s ^ 4))
        (TriR 0 0 (Kc g s t j) 0 (Bx g s t j) (Bw g s t j)))
      (L * L + L * L + L * L + (m + 1) * (m + 1) + JB * JB + 2 * (m + 1) * (n + 1)) := by
  have hg := P.hg
  have hj := P.hj
  have hs := P.hs
  have ht := P.ht
  have hts := P.hts
  have hq := P.hq
  have h1 : 0 < s - t := by linarith
  have h2 : 0 < s + t := by linarith
  have h3 : 0 < s ^ 2 - 2 * t ^ 2 := by linarith
  have h4 : 0 < 2 * s ^ 2 - t ^ 2 := by nlinarith
  have h5 : 0 < 3 * s ^ 2 - t ^ 2 := by nlinarith
  have h6 : 0 < 2 * s ^ 4 - 4 * s ^ 2 * t ^ 2 + t ^ 4 := by
    nlinarith [mul_pos h3 h3, mul_pos h3 (pow_pos ht 2), pow_pos ht 4]
  have hp : 0 < s ^ 2 - t ^ 2 := by nlinarith
  have hα : 0 < 1 / (2 * s ^ 4) := by positivity
  have hβ : 0 < rt0 / (2 * s ^ 4) := by have := P.hrt; positivity
  have cs_congr : ∀ {p q : ℝ → ℝ → Prop}, (∀ X W, p X W ↔ q X W) →
      CS (1 / (2 * s ^ 4)) (rt0 / (2 * s ^ 4)) p = CS (1 / (2 * s ^ 4)) (rt0 / (2 * s ^ 4)) q := by
    intro p q h
    ext z
    exact h _ _
  have hcell := cell_of_tris hα hβ (fact_delta P) (cell_t1 P) (cell_t2 P)
  have hu : Ux g s t j ≠ 0 ∨ Uw g s t j ≠ 0 :=
    Or.inl (by have : 0 < Ux g s t j := by simp only [Ux]; positivity
               exact this.ne')
  have hv : Vx g s t j ≠ 0 ∨ Vw g s t j ≠ 0 :=
    Or.inl (by have : 0 < Vx g s t j := by simp only [Vx]; positivity
               exact this.ne')
  have hm0 : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
  have hn0 : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hSx : Sx g s t j = Qx g s t j + ((m + 1 : ℕ) : ℝ) * Ux g s t j := by
    rw [hJA]; simp only [Sx, Qx, Ux]; ring
  have hSw : Sw g s t j = Qw g s t j + ((m + 1 : ℕ) : ℝ) * Uw g s t j := by
    rw [hJA]; simp only [Sw, Qw, Uw]; ring
  have hRx' : Rx g s t j = Sx g s t j + ((n + 1 : ℕ) : ℝ) * Vx g s t j := by
    simp only [Rx, Sx, Vx]
    linear_combination (-(g * s * (2 * s ^ 4 - 4 * s ^ 2 * t ^ 2 + t ^ 4))) * hr
  have hRw' : Rw g s t j = Sw g s t j + ((n + 1 : ℕ) : ℝ) * Vw g s t j := by
    simp only [Rw, Sw, Vw]
    linear_combination (-(g * s * t * (2 * s ^ 2 - t ^ 2))) * hr
  have hTx' : Tx g s t j = Qx g s t j + ((n + 1 : ℕ) : ℝ) * Vx g s t j := by
    simp only [Tx, Qx, Vx]
    linear_combination (-(g * s * (2 * s ^ 4 - 4 * s ^ 2 * t ^ 2 + t ^ 4))) * hr
  have hTw' : Tw g s t j = Qw g s t j + ((n + 1 : ℕ) : ℝ) * Vw g s t j := by
    simp only [Tw, Qw, Vw]
    linear_combination (-(g * s * t * (2 * s ^ 2 - t ^ 2))) * hr
  have hOr := (grid_dis hα hβ hu hv hcell n m (Qx g s t j) (Qw g s t j)).congr
    (cs_congr (fun X W => pgp_iff hm0 hn0 hSx hSw hRx' hRw' hTx' hTw' X W)) rfl
  have hBlue := blue_dis P L hL0 hL
  have hPink := pink_dis P L hL0 hL
  have hGreen := green_dis P L hL0 hL
  have hYellow := yellow_dis P (m + 1) (by omega) hJA
  have hTop := top_dis P JB hJB0 hJB
  have hne1 : (s - t) * (s + t) * (3 * s ^ 2 - t ^ 2) ≠ 0 := by positivity
  have hne2 : 3 * s ^ 2 - t ^ 2 ≠ 0 := h5.ne'
  have hne3 : 2 * s ^ 2 - t ^ 2 ≠ 0 := h4.ne'
  have hne4 : (s - t) * (s + t) ≠ 0 := by positivity
  have hn2' : 3 * s ^ 2 ≠ t ^ 2 := fun h => hne2 (by linarith)
  have hn3' : 2 * s ^ 2 ≠ t ^ 2 := fun h => hne3 (by linarith)
  have hn5' : s - t ≠ 0 := h1.ne'
  have hn6' : s + t ≠ 0 := h2.ne'
  have hQx : Qx g s t j = th1 g s t j * Bx g s t j := by
    simp only [Qx, th1, Bx]; rw [div_mul_eq_mul_div, eq_div_iff hne1]; ring
  have hQw : Qw g s t j = th1 g s t j * Bw g s t j := by
    simp only [Qw, th1, Bw]; rw [div_mul_eq_mul_div, eq_div_iff hne1]; ring
  have hTx : Tx g s t j = th2 g s t j * Bx g s t j := by
    simp only [Tx, th2, Bx]; rw [div_mul_eq_mul_div, eq_div_iff hne2]; ring
  have hTw : Tw g s t j = th2 g s t j * Bw g s t j := by
    simp only [Tw, th2, Bw]; rw [div_mul_eq_mul_div, eq_div_iff hne2]; ring
  have hRx : Rx g s t j = Kc g s t j + ta g s t j * (Bx g s t j - Kc g s t j) := by
    simp only [Rx, Kc, ta, Bx]; rw [div_mul_eq_mul_div, ← sub_eq_iff_eq_add', eq_div_iff hne3]; ring
  have hRw : Rw g s t j = ta g s t j * Bw g s t j := by
    simp only [Rw, ta, Bw]; rw [div_mul_eq_mul_div, eq_div_iff hne3]; ring
  have hSx2 : Sx g s t j = Px g s t j + rh g s t j * (Rx g s t j - Px g s t j) := by
    simp only [Sx, Px, rh, Rx]; rw [div_mul_eq_mul_div, ← sub_eq_iff_eq_add', eq_div_iff hne4]; ring
  have hSw2 : Sw g s t j = Pw g s t j + rh g s t j * (Rw g s t j - Pw g s t j) := by
    simp only [Sw, Pw, rh, Rw]; rw [div_mul_eq_mul_div, ← sub_eq_iff_eq_add', eq_div_iff hne4]; ring
  have hK : 0 < Kc g s t j := by simp only [Kc]; positivity
  have hθ1 : 0 < th1 g s t j := by simp only [th1]; positivity
  have hθ12 : th1 g s t j < th2 g s t j := by
    simp only [th1, th2]
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_pos hs hs, pow_pos hs 4, mul_pos (mul_pos hs hs) h3, mul_pos (mul_pos h1 h2) h5]
  have hθ2 : th2 g s t j < 1 := by
    simp only [th2]
    rw [div_lt_one h5]
    nlinarith
  have hτ0 : 0 < ta g s t j := by simp only [ta]; positivity
  have hτ1 : ta g s t j < 1 := by
    simp only [ta]
    rw [div_lt_one h4]
    nlinarith
  have hρ0 : 0 < rh g s t j := by simp only [rh]; positivity
  have hρ1 : rh g s t j < 1 := by
    simp only [rh]
    rw [div_lt_one (by positivity)]
    nlinarith
  have hlC : 0 < 2 * (s ^ 2 - t ^ 2) ^ 2 := by positivity
  have hlR : 0 < (s ^ 2 - 2 * t ^ 2) * s ^ 2 := by positivity
  have hlQ : 0 < s ^ 2 * (s ^ 2 - t ^ 2) := by positivity
  have hspx : 2 * (s ^ 2 - t ^ 2) ^ 2 * (Kc g s t j - Px g s t j) +
      (s ^ 2 - 2 * t ^ 2) * s ^ 2 * (Rx g s t j - Px g s t j) +
      s ^ 2 * (s ^ 2 - t ^ 2) * (Qx g s t j - Px g s t j) +
      s ^ 2 * (s ^ 2 - t ^ 2) * (0 - Px g s t j) = 0 := by
    simp only [Kc, Px, Rx, Qx]; ring
  have hspw : 2 * (s ^ 2 - t ^ 2) ^ 2 * (0 - Pw g s t j) +
      (s ^ 2 - 2 * t ^ 2) * s ^ 2 * (Rw g s t j - Pw g s t j) +
      s ^ 2 * (s ^ 2 - t ^ 2) * (Qw g s t j - Pw g s t j) +
      s ^ 2 * (s ^ 2 - t ^ 2) * (0 - Pw g s t j) = 0 := by
    simp only [Pw, Rw, Qw]; ring
  have fin := assemble hα hβ (Kc g s t j) (Bx g s t j) (Bw g s t j) (Px g s t j) (Pw g s t j)
    (th1 g s t j) (th2 g s t j) (ta g s t j) (rh g s t j) (Qx g s t j) (Qw g s t j)
    (Tx g s t j) (Tw g s t j) (Rx g s t j) (Rw g s t j) (Sx g s t j) (Sw g s t j)
    hQx hQw hTx hTw hRx hRw hSx2 hSw2 hK hθ1 hθ12 hθ2 hτ0 hτ1 hρ0 hρ1
    hBlue hPink hGreen hYellow hTop hOr
    (fact_dBig P) (fact_dBlue P) (fact_dPink P) (fact_dGreen P) (fact_dYellow P) (fact_dTop P)
    (fact_dO1 P) (fact_dO2 P) ⟨fact_hP1 P, fact_hP2 P, fact_hP3 P⟩
    (fact_hF6A P) (fact_hF6C P) (fact_hF6P P) (fact_hF6Q P) (fact_hF5A P) (fact_hF5C P)
    (fact_hF5P P) (fact_hF4C P) (fact_hPQS P) (fact_hPQA P) (fact_hF4Q P) (fact_hF4A P)
    (fact_hAPS P) _ _ _ _ hlC hlR hlQ hlQ hspx hspw
  exact fin

end Erdos634.BeesonT14Gen


