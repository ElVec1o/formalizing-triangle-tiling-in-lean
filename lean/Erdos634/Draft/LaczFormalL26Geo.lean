import Erdos634.Draft.LaczFormalL24Main
import Erdos634.CoversGeneral
import Erdos634.AreaDet

/-!
# Laczkovich Theorem 2.4, FOURTH triple `(α, α+β, α+β)`: chart geometry of the first picture of Fig. 5

NOTE, UNAUDITED.  Credit: Laczkovich (Discrete Math. 140 (1995) 79-94, Theorem 2.4, Fig. 5), Beeson (arXiv 1206.2229,
Sect. 13.3, Theorem 23, Lemma 52), Beeson-Zhang, Zhang.

`a = a₀ = a/c = 2 sin(α/2)`, `b = 1 - a²` (so `b/c = 1 - a²`), `K = a² + b²`, `N = a⁴ - b³`.  The condition `N > 0` is exactly
`64 t⁶ - 32 t⁴ + 12 t² - 1 > 0` (`t = a/2`), i.e. `x³ < (1-x)²` with `x = b/c`, i.e. `b/c < 0.5698...` (Beeson).
Chart (scaled so that every coordinate is a polynomial in `a`): `L = (0,0)`, `R = (a²K, 0)`, `P = (-bK, K)`,
`X = (-a²b, a²)`, `V = (a²b², a⁴)`, `Z = (0, a⁴)`, `S = (0, N)`, `Q = (b², N)`; target `T = L R P` (apex `P`);
tiles `PVX, VXZ, XLZ, QZV, SQZ` and the trapezoid `L R Q S` (two triangles `LRQ`, `LQS`).
Cover from `covers_of_volume_tri` (containment, pairwise disjoint interiors by 7 separating lines, exact area identity).
-/

namespace Erdos634.LaczL26

open Erdos634.Geometry Erdos634.CertCoord Erdos634.LaczL22 Erdos634.LaczL24 MeasureTheory

def gb (a : ℝ) : ℝ := 1 - a ^ 2
def gK (a : ℝ) : ℝ := a ^ 2 + (1 - a ^ 2) ^ 2
def gN (a : ℝ) : ℝ := a ^ 4 - (1 - a ^ 2) ^ 3
def gM (a : ℝ) : ℝ := a ^ 4 - 2 * a ^ 2 + 2
def sP (a : ℝ) : ℝ := -(gb a * gK a)
def tP (a : ℝ) : ℝ := gK a
def sR (a : ℝ) : ℝ := a ^ 2 * gK a
def sX (a : ℝ) : ℝ := -(a ^ 2 * gb a)
def tX (a : ℝ) : ℝ := a ^ 2
def sV (a : ℝ) : ℝ := a ^ 2 * gb a ^ 2
def tV (a : ℝ) : ℝ := a ^ 4
def tZ (a : ℝ) : ℝ := a ^ 4
def tS (a : ℝ) : ℝ := gN a
def sQ (a : ℝ) : ℝ := gb a ^ 2
def tQ (a : ℝ) : ℝ := gN a

/-- The chart functional of the line through `(ps, pt)`, `(qs, qt)`. -/
noncomputable def lineF (ps pt qs qt : ℝ) : Plane →ᵃ[ℝ] ℝ :=
  coordFun (-(qt - pt)) (qs - ps) ((qt - pt) * ps - (qs - ps) * pt)

theorem lineF_apply (ps pt qs qt x y : ℝ) :
    lineF ps pt qs qt (mkPt x y) = (qs - ps) * (y - pt) - (qt - pt) * (x - ps) := by
  simp only [lineF, coordFun_apply, mkPt_zero, mkPt_one]; ring

macro "unf" : tactic =>
  `(tactic| simp only [lineF_apply, gb, gK, gN, gM, sP, tP, sR, sX, tX, sV, tV, tZ, tS, sQ, tQ, det3])

structure Hyp (a : ℝ) : Prop where
  ha : 0 < a
  hb : 0 < gb a
  hK : 0 < gK a
  hN : 0 < gN a
  hM : 0 < gM a

theorem Hyp.of_lt {a : ℝ} (ha : 0 < a) (hb : 0 < 1 - a ^ 2) (hN : 0 < a ^ 4 - (1 - a ^ 2) ^ 3) : Hyp a :=
  ⟨ha, hb, by unfold gK; positivity, hN, by unfold gM; nlinarith [sq_nonneg (a ^ 2 - 1)]⟩

variable {a : ℝ}

theorem det_A (h : Hyp a) : det3 (sP a) (tP a) (sV a) (tV a) (sX a) (tX a) = -1 * (a ^ 2 * (gb a) ^ 3) := by unf; ring

theorem detne_A (h : Hyp a) : det3 (sP a) (tP a) (sV a) (tV a) (sX a) (tX a) ≠ 0 := by
  obtain ⟨ha, hb, hK, hN, hM⟩ := id h
  have e : det3 (sP a) (tP a) (sV a) (tV a) (sX a) (tX a) = -1 * (a ^ 2 * (gb a) ^ 3) := by unf; ring
  have hp : 0 < a ^ 2 * (gb a) ^ 3 := by positivity
  rw [e]; intro h0; nlinarith

theorem det_B (h : Hyp a) : det3 (sV a) (tV a) (sX a) (tX a) 0 (tZ a) = 1 * (a ^ 4 * (gb a) ^ 3) := by unf; ring

theorem detne_B (h : Hyp a) : det3 (sV a) (tV a) (sX a) (tX a) 0 (tZ a) ≠ 0 := by
  obtain ⟨ha, hb, hK, hN, hM⟩ := id h
  have e : det3 (sV a) (tV a) (sX a) (tX a) 0 (tZ a) = 1 * (a ^ 4 * (gb a) ^ 3) := by unf; ring
  have hp : 0 < a ^ 4 * (gb a) ^ 3 := by positivity
  rw [e]; intro h0; nlinarith

theorem det_C (h : Hyp a) : det3 (sX a) (tX a) 0 0 0 (tZ a) = 1 * (a ^ 6 * (gb a)) := by unf; ring

theorem detne_C (h : Hyp a) : det3 (sX a) (tX a) 0 0 0 (tZ a) ≠ 0 := by
  obtain ⟨ha, hb, hK, hN, hM⟩ := id h
  have e : det3 (sX a) (tX a) 0 0 0 (tZ a) = 1 * (a ^ 6 * (gb a)) := by unf; ring
  have hp : 0 < a ^ 6 * (gb a) := by positivity
  rw [e]; intro h0; nlinarith

theorem det_D (h : Hyp a) : det3 (sQ a) (tQ a) 0 (tZ a) (sV a) (tV a) = -1 * (a ^ 2 * (gb a) ^ 5) := by unf; ring

theorem detne_D (h : Hyp a) : det3 (sQ a) (tQ a) 0 (tZ a) (sV a) (tV a) ≠ 0 := by
  obtain ⟨ha, hb, hK, hN, hM⟩ := id h
  have e : det3 (sQ a) (tQ a) 0 (tZ a) (sV a) (tV a) = -1 * (a ^ 2 * (gb a) ^ 5) := by unf; ring
  have hp : 0 < a ^ 2 * (gb a) ^ 5 := by positivity
  rw [e]; intro h0; nlinarith

theorem det_E (h : Hyp a) : det3 0 (tS a) (sQ a) (tQ a) 0 (tZ a) = 1 * ((gb a) ^ 5) := by unf; ring

theorem detne_E (h : Hyp a) : det3 0 (tS a) (sQ a) (tQ a) 0 (tZ a) ≠ 0 := by
  obtain ⟨ha, hb, hK, hN, hM⟩ := id h
  have e : det3 0 (tS a) (sQ a) (tQ a) 0 (tZ a) = 1 * ((gb a) ^ 5) := by unf; ring
  have hp : 0 < (gb a) ^ 5 := by positivity
  rw [e]; intro h0; nlinarith

theorem det_F (h : Hyp a) : det3 0 0 (sR a) 0 (sQ a) (tQ a) = 1 * (a ^ 2 * (gK a) * (gN a)) := by unf; ring

theorem detne_F (h : Hyp a) : det3 0 0 (sR a) 0 (sQ a) (tQ a) ≠ 0 := by
  obtain ⟨ha, hb, hK, hN, hM⟩ := id h
  have e : det3 0 0 (sR a) 0 (sQ a) (tQ a) = 1 * (a ^ 2 * (gK a) * (gN a)) := by unf; ring
  have hp : 0 < a ^ 2 * (gK a) * (gN a) := by positivity
  rw [e]; intro h0; nlinarith

theorem det_G (h : Hyp a) : det3 0 0 (sQ a) (tQ a) 0 (tS a) = 1 * ((gN a) * (gb a) ^ 2) := by unf; ring

theorem detne_G (h : Hyp a) : det3 0 0 (sQ a) (tQ a) 0 (tS a) ≠ 0 := by
  obtain ⟨ha, hb, hK, hN, hM⟩ := id h
  have e : det3 0 0 (sQ a) (tQ a) 0 (tS a) = 1 * ((gN a) * (gb a) ^ 2) := by unf; ring
  have hp : 0 < (gN a) * (gb a) ^ 2 := by positivity
  rw [e]; intro h0; nlinarith

theorem det_T (h : Hyp a) : det3 0 0 (sR a) 0 (sP a) (tP a) = 1 * (a ^ 2 * (gK a) ^ 2) := by unf; ring

theorem detne_T (h : Hyp a) : det3 0 0 (sR a) 0 (sP a) (tP a) ≠ 0 := by
  obtain ⟨ha, hb, hK, hN, hM⟩ := id h
  have e : det3 0 0 (sR a) 0 (sP a) (tP a) = 1 * (a ^ 2 * (gK a) ^ 2) := by unf; ring
  have hp : 0 < a ^ 2 * (gK a) ^ 2 := by positivity
  rw [e]; intro h0; nlinarith

noncomputable def triA (h : Hyp a) : Tri := mkTri (sP a) (tP a) (sV a) (tV a) (sX a) (tX a) (detne_A h)
noncomputable def triB (h : Hyp a) : Tri := mkTri (sV a) (tV a) (sX a) (tX a) 0 (tZ a) (detne_B h)
noncomputable def triC (h : Hyp a) : Tri := mkTri (sX a) (tX a) 0 0 0 (tZ a) (detne_C h)
noncomputable def triD (h : Hyp a) : Tri := mkTri (sQ a) (tQ a) 0 (tZ a) (sV a) (tV a) (detne_D h)
noncomputable def triE (h : Hyp a) : Tri := mkTri 0 (tS a) (sQ a) (tQ a) 0 (tZ a) (detne_E h)
noncomputable def triF (h : Hyp a) : Tri := mkTri 0 0 (sR a) 0 (sQ a) (tQ a) (detne_F h)
noncomputable def triG (h : Hyp a) : Tri := mkTri 0 0 (sQ a) (tQ a) 0 (tS a) (detne_G h)
noncomputable def triT (h : Hyp a) : Tri := mkTri 0 0 (sR a) 0 (sP a) (tP a) (detne_T h)

theorem detpos_T (h : Hyp a) : 0 < det3 0 0 (sR a) 0 (sP a) (tP a) := by
  obtain ⟨ha, hb, hK, hN, hM⟩ := id h
  rw [det_T h]; positivity

theorem mT_L_0 (h : Hyp a) : 0 ≤ det3 0 0 (sR a) 0 (sP a) (tP a) := by
  obtain ⟨ha, hb, hK, hN, hM⟩ := id h
  have e : det3 0 0 (sR a) 0 (sP a) (tP a) = 1 * (a ^ 2 * (gK a) ^ 2) := by unf; ring
  have hp : 0 ≤ a ^ 2 * (gK a) ^ 2 := by positivity
  rw [e]; nlinarith

theorem mT_L_1 (h : Hyp a) : 0 ≤ det3 0 0 0 0 (sP a) (tP a) := by
  have e : det3 0 0 0 0 (sP a) (tP a) = 0 := by unf; ring
  exact le_of_eq e.symm

theorem mT_L_2 (h : Hyp a) : 0 ≤ det3 0 0 (sR a) 0 0 0 := by
  have e : det3 0 0 (sR a) 0 0 0 = 0 := by unf; ring
  exact le_of_eq e.symm

theorem memT_L (h : Hyp a) : mkPt 0 0 ∈ (triT h).carrier :=
  mem_carrier_of_dets (detpos_T h) (mT_L_0 h) (mT_L_1 h) (mT_L_2 h)

theorem mT_R_0 (h : Hyp a) : 0 ≤ det3 (sR a) 0 (sR a) 0 (sP a) (tP a) := by
  have e : det3 (sR a) 0 (sR a) 0 (sP a) (tP a) = 0 := by unf; ring
  exact le_of_eq e.symm

theorem mT_R_1 (h : Hyp a) : 0 ≤ det3 0 0 (sR a) 0 (sP a) (tP a) := by
  obtain ⟨ha, hb, hK, hN, hM⟩ := id h
  have e : det3 0 0 (sR a) 0 (sP a) (tP a) = 1 * (a ^ 2 * (gK a) ^ 2) := by unf; ring
  have hp : 0 ≤ a ^ 2 * (gK a) ^ 2 := by positivity
  rw [e]; nlinarith

theorem mT_R_2 (h : Hyp a) : 0 ≤ det3 0 0 (sR a) 0 (sR a) 0 := by
  have e : det3 0 0 (sR a) 0 (sR a) 0 = 0 := by unf; ring
  exact le_of_eq e.symm

theorem memT_R (h : Hyp a) : mkPt (sR a) 0 ∈ (triT h).carrier :=
  mem_carrier_of_dets (detpos_T h) (mT_R_0 h) (mT_R_1 h) (mT_R_2 h)

theorem mT_P_0 (h : Hyp a) : 0 ≤ det3 (sP a) (tP a) (sR a) 0 (sP a) (tP a) := by
  have e : det3 (sP a) (tP a) (sR a) 0 (sP a) (tP a) = 0 := by unf; ring
  exact le_of_eq e.symm

theorem mT_P_1 (h : Hyp a) : 0 ≤ det3 0 0 (sP a) (tP a) (sP a) (tP a) := by
  have e : det3 0 0 (sP a) (tP a) (sP a) (tP a) = 0 := by unf; ring
  exact le_of_eq e.symm

theorem mT_P_2 (h : Hyp a) : 0 ≤ det3 0 0 (sR a) 0 (sP a) (tP a) := by
  obtain ⟨ha, hb, hK, hN, hM⟩ := id h
  have e : det3 0 0 (sR a) 0 (sP a) (tP a) = 1 * (a ^ 2 * (gK a) ^ 2) := by unf; ring
  have hp : 0 ≤ a ^ 2 * (gK a) ^ 2 := by positivity
  rw [e]; nlinarith

theorem memT_P (h : Hyp a) : mkPt (sP a) (tP a) ∈ (triT h).carrier :=
  mem_carrier_of_dets (detpos_T h) (mT_P_0 h) (mT_P_1 h) (mT_P_2 h)

theorem mT_X_0 (h : Hyp a) : 0 ≤ det3 (sX a) (tX a) (sR a) 0 (sP a) (tP a) := by
  obtain ⟨ha, hb, hK, hN, hM⟩ := id h
  have e : det3 (sX a) (tX a) (sR a) 0 (sP a) (tP a) = 1 * (a ^ 2 * (gK a) * (gb a) ^ 2) := by unf; ring
  have hp : 0 ≤ a ^ 2 * (gK a) * (gb a) ^ 2 := by positivity
  rw [e]; nlinarith

theorem mT_X_1 (h : Hyp a) : 0 ≤ det3 0 0 (sX a) (tX a) (sP a) (tP a) := by
  have e : det3 0 0 (sX a) (tX a) (sP a) (tP a) = 0 := by unf; ring
  exact le_of_eq e.symm

theorem mT_X_2 (h : Hyp a) : 0 ≤ det3 0 0 (sR a) 0 (sX a) (tX a) := by
  obtain ⟨ha, hb, hK, hN, hM⟩ := id h
  have e : det3 0 0 (sR a) 0 (sX a) (tX a) = 1 * (a ^ 4 * (gK a)) := by unf; ring
  have hp : 0 ≤ a ^ 4 * (gK a) := by positivity
  rw [e]; nlinarith

theorem memT_X (h : Hyp a) : mkPt (sX a) (tX a) ∈ (triT h).carrier :=
  mem_carrier_of_dets (detpos_T h) (mT_X_0 h) (mT_X_1 h) (mT_X_2 h)

theorem mT_V_0 (h : Hyp a) : 0 ≤ det3 (sV a) (tV a) (sR a) 0 (sP a) (tP a) := by
  have e : det3 (sV a) (tV a) (sR a) 0 (sP a) (tP a) = 0 := by unf; ring
  exact le_of_eq e.symm

theorem mT_V_1 (h : Hyp a) : 0 ≤ det3 0 0 (sV a) (tV a) (sP a) (tP a) := by
  obtain ⟨ha, hb, hK, hN, hM⟩ := id h
  have e : det3 0 0 (sV a) (tV a) (sP a) (tP a) = 1 * (a ^ 2 * (gK a) * (gb a)) := by unf; ring
  have hp : 0 ≤ a ^ 2 * (gK a) * (gb a) := by positivity
  rw [e]; nlinarith

theorem mT_V_2 (h : Hyp a) : 0 ≤ det3 0 0 (sR a) 0 (sV a) (tV a) := by
  obtain ⟨ha, hb, hK, hN, hM⟩ := id h
  have e : det3 0 0 (sR a) 0 (sV a) (tV a) = 1 * (a ^ 6 * (gK a)) := by unf; ring
  have hp : 0 ≤ a ^ 6 * (gK a) := by positivity
  rw [e]; nlinarith

theorem memT_V (h : Hyp a) : mkPt (sV a) (tV a) ∈ (triT h).carrier :=
  mem_carrier_of_dets (detpos_T h) (mT_V_0 h) (mT_V_1 h) (mT_V_2 h)

theorem mT_Z_0 (h : Hyp a) : 0 ≤ det3 0 (tZ a) (sR a) 0 (sP a) (tP a) := by
  obtain ⟨ha, hb, hK, hN, hM⟩ := id h
  have e : det3 0 (tZ a) (sR a) 0 (sP a) (tP a) = 1 * (a ^ 2 * (gK a) * (gb a) ^ 2) := by unf; ring
  have hp : 0 ≤ a ^ 2 * (gK a) * (gb a) ^ 2 := by positivity
  rw [e]; nlinarith

theorem mT_Z_1 (h : Hyp a) : 0 ≤ det3 0 0 0 (tZ a) (sP a) (tP a) := by
  obtain ⟨ha, hb, hK, hN, hM⟩ := id h
  have e : det3 0 0 0 (tZ a) (sP a) (tP a) = 1 * (a ^ 4 * (gK a) * (gb a)) := by unf; ring
  have hp : 0 ≤ a ^ 4 * (gK a) * (gb a) := by positivity
  rw [e]; nlinarith

theorem mT_Z_2 (h : Hyp a) : 0 ≤ det3 0 0 (sR a) 0 0 (tZ a) := by
  obtain ⟨ha, hb, hK, hN, hM⟩ := id h
  have e : det3 0 0 (sR a) 0 0 (tZ a) = 1 * (a ^ 6 * (gK a)) := by unf; ring
  have hp : 0 ≤ a ^ 6 * (gK a) := by positivity
  rw [e]; nlinarith

theorem memT_Z (h : Hyp a) : mkPt 0 (tZ a) ∈ (triT h).carrier :=
  mem_carrier_of_dets (detpos_T h) (mT_Z_0 h) (mT_Z_1 h) (mT_Z_2 h)

theorem mT_S_0 (h : Hyp a) : 0 ≤ det3 0 (tS a) (sR a) 0 (sP a) (tP a) := by
  obtain ⟨ha, hb, hK, hN, hM⟩ := id h
  have e : det3 0 (tS a) (sR a) 0 (sP a) (tP a) = 1 * ((gK a) * (gb a) ^ 2) := by unf; ring
  have hp : 0 ≤ (gK a) * (gb a) ^ 2 := by positivity
  rw [e]; nlinarith

theorem mT_S_1 (h : Hyp a) : 0 ≤ det3 0 0 0 (tS a) (sP a) (tP a) := by
  obtain ⟨ha, hb, hK, hN, hM⟩ := id h
  have e : det3 0 0 0 (tS a) (sP a) (tP a) = 1 * ((gK a) * (gN a) * (gb a)) := by unf; ring
  have hp : 0 ≤ (gK a) * (gN a) * (gb a) := by positivity
  rw [e]; nlinarith

theorem mT_S_2 (h : Hyp a) : 0 ≤ det3 0 0 (sR a) 0 0 (tS a) := by
  obtain ⟨ha, hb, hK, hN, hM⟩ := id h
  have e : det3 0 0 (sR a) 0 0 (tS a) = 1 * (a ^ 2 * (gK a) * (gN a)) := by unf; ring
  have hp : 0 ≤ a ^ 2 * (gK a) * (gN a) := by positivity
  rw [e]; nlinarith

theorem memT_S (h : Hyp a) : mkPt 0 (tS a) ∈ (triT h).carrier :=
  mem_carrier_of_dets (detpos_T h) (mT_S_0 h) (mT_S_1 h) (mT_S_2 h)

theorem mT_Q_0 (h : Hyp a) : 0 ≤ det3 (sQ a) (tQ a) (sR a) 0 (sP a) (tP a) := by
  have e : det3 (sQ a) (tQ a) (sR a) 0 (sP a) (tP a) = 0 := by unf; ring
  exact le_of_eq e.symm

theorem mT_Q_1 (h : Hyp a) : 0 ≤ det3 0 0 (sQ a) (tQ a) (sP a) (tP a) := by
  obtain ⟨ha, hb, hK, hN, hM⟩ := id h
  have e : det3 0 0 (sQ a) (tQ a) (sP a) (tP a) = 1 * (a ^ 2 * (gK a) * (gM a) * (gb a)) := by unf; ring
  have hp : 0 ≤ a ^ 2 * (gK a) * (gM a) * (gb a) := by positivity
  rw [e]; nlinarith

theorem mT_Q_2 (h : Hyp a) : 0 ≤ det3 0 0 (sR a) 0 (sQ a) (tQ a) := by
  obtain ⟨ha, hb, hK, hN, hM⟩ := id h
  have e : det3 0 0 (sR a) 0 (sQ a) (tQ a) = 1 * (a ^ 2 * (gK a) * (gN a)) := by unf; ring
  have hp : 0 ≤ a ^ 2 * (gK a) * (gN a) := by positivity
  rw [e]; nlinarith

theorem memT_Q (h : Hyp a) : mkPt (sQ a) (tQ a) ∈ (triT h).carrier :=
  mem_carrier_of_dets (detpos_T h) (mT_Q_0 h) (mT_Q_1 h) (mT_Q_2 h)

private theorem htri7 : ∀ k : Fin 3, k = 0 ∨ k = 1 ∨ k = 2 := by decide

theorem sub_A (h : Hyp a) : (triA h).carrier ⊆ (triT h).carrier :=
  convexHull_min (Set.range_subset_iff.mpr (fun k => by rcases htri7 k with rfl | rfl | rfl <;> [exact memT_P h; exact memT_V h; exact memT_X h])) (convex_convexHull ℝ _)

theorem sub_B (h : Hyp a) : (triB h).carrier ⊆ (triT h).carrier :=
  convexHull_min (Set.range_subset_iff.mpr (fun k => by rcases htri7 k with rfl | rfl | rfl <;> [exact memT_V h; exact memT_X h; exact memT_Z h])) (convex_convexHull ℝ _)

theorem sub_C (h : Hyp a) : (triC h).carrier ⊆ (triT h).carrier :=
  convexHull_min (Set.range_subset_iff.mpr (fun k => by rcases htri7 k with rfl | rfl | rfl <;> [exact memT_X h; exact memT_L h; exact memT_Z h])) (convex_convexHull ℝ _)

theorem sub_D (h : Hyp a) : (triD h).carrier ⊆ (triT h).carrier :=
  convexHull_min (Set.range_subset_iff.mpr (fun k => by rcases htri7 k with rfl | rfl | rfl <;> [exact memT_Q h; exact memT_Z h; exact memT_V h])) (convex_convexHull ℝ _)

theorem sub_E (h : Hyp a) : (triE h).carrier ⊆ (triT h).carrier :=
  convexHull_min (Set.range_subset_iff.mpr (fun k => by rcases htri7 k with rfl | rfl | rfl <;> [exact memT_S h; exact memT_Q h; exact memT_Z h])) (convex_convexHull ℝ _)

theorem sub_F (h : Hyp a) : (triF h).carrier ⊆ (triT h).carrier :=
  convexHull_min (Set.range_subset_iff.mpr (fun k => by rcases htri7 k with rfl | rfl | rfl <;> [exact memT_L h; exact memT_R h; exact memT_Q h])) (convex_convexHull ℝ _)

theorem sub_G (h : Hyp a) : (triG h).carrier ⊆ (triT h).carrier :=
  convexHull_min (Set.range_subset_iff.mpr (fun k => by rcases htri7 k with rfl | rfl | rfl <;> [exact memT_L h; exact memT_Q h; exact memT_S h])) (convex_convexHull ℝ _)

noncomputable def lfXV (a : ℝ) : Plane →ᵃ[ℝ] ℝ := lineF (sX a) (tX a) (sV a) (tV a)

theorem lfXV_al (h : Hyp a) : -((tV a) - (tX a)) ≠ 0 := by
  obtain ⟨ha, hb, hK, hN, hM⟩ := id h
  have e : -((tV a) - (tX a)) = 1 * (a ^ 2 * (gb a)) := by unf; ring
  have hp : 0 < a ^ 2 * (gb a) := by positivity
  rw [e]; intro h0; nlinarith

theorem lfXV_ne (h : Hyp a) : (lfXV a).linear ≠ 0 :=
  coordFun_linear_ne_zero _ (Or.inl (lfXV_al h))

noncomputable def lfXZ (a : ℝ) : Plane →ᵃ[ℝ] ℝ := lineF (sX a) (tX a) 0 (tZ a)

theorem lfXZ_al (h : Hyp a) : -((tZ a) - (tX a)) ≠ 0 := by
  obtain ⟨ha, hb, hK, hN, hM⟩ := id h
  have e : -((tZ a) - (tX a)) = 1 * (a ^ 2 * (gb a)) := by unf; ring
  have hp : 0 < a ^ 2 * (gb a) := by positivity
  rw [e]; intro h0; nlinarith

theorem lfXZ_ne (h : Hyp a) : (lfXZ a).linear ≠ 0 :=
  coordFun_linear_ne_zero _ (Or.inl (lfXZ_al h))

noncomputable def lfZV (a : ℝ) : Plane →ᵃ[ℝ] ℝ := lineF 0 (tZ a) (sV a) (tV a)

theorem lfZV_be (h : Hyp a) : (sV a) - 0 ≠ 0 := by
  obtain ⟨ha, hb, hK, hN, hM⟩ := id h
  have e : (sV a) - 0 = 1 * (a ^ 2 * (gb a) ^ 2) := by unf; ring
  have hp : 0 < a ^ 2 * (gb a) ^ 2 := by positivity
  rw [e]; intro h0; nlinarith

theorem lfZV_ne (h : Hyp a) : (lfZV a).linear ≠ 0 :=
  coordFun_linear_ne_zero _ (Or.inr (lfZV_be h))

noncomputable def lfZS (a : ℝ) : Plane →ᵃ[ℝ] ℝ := lineF 0 (tZ a) 0 (tS a)

theorem lfZS_al (h : Hyp a) : -((tS a) - (tZ a)) ≠ 0 := by
  obtain ⟨ha, hb, hK, hN, hM⟩ := id h
  have e : -((tS a) - (tZ a)) = 1 * ((gb a) ^ 3) := by unf; ring
  have hp : 0 < (gb a) ^ 3 := by positivity
  rw [e]; intro h0; nlinarith

theorem lfZS_ne (h : Hyp a) : (lfZS a).linear ≠ 0 :=
  coordFun_linear_ne_zero _ (Or.inl (lfZS_al h))

noncomputable def lfZQ (a : ℝ) : Plane →ᵃ[ℝ] ℝ := lineF 0 (tZ a) (sQ a) (tQ a)

theorem lfZQ_al (h : Hyp a) : -((tQ a) - (tZ a)) ≠ 0 := by
  obtain ⟨ha, hb, hK, hN, hM⟩ := id h
  have e : -((tQ a) - (tZ a)) = 1 * ((gb a) ^ 3) := by unf; ring
  have hp : 0 < (gb a) ^ 3 := by positivity
  rw [e]; intro h0; nlinarith

theorem lfZQ_ne (h : Hyp a) : (lfZQ a).linear ≠ 0 :=
  coordFun_linear_ne_zero _ (Or.inl (lfZQ_al h))

noncomputable def lfSQ (a : ℝ) : Plane →ᵃ[ℝ] ℝ := lineF 0 (tS a) (sQ a) (tQ a)

theorem lfSQ_be (h : Hyp a) : (sQ a) - 0 ≠ 0 := by
  obtain ⟨ha, hb, hK, hN, hM⟩ := id h
  have e : (sQ a) - 0 = 1 * ((gb a) ^ 2) := by unf; ring
  have hp : 0 < (gb a) ^ 2 := by positivity
  rw [e]; intro h0; nlinarith

theorem lfSQ_ne (h : Hyp a) : (lfSQ a).linear ≠ 0 :=
  coordFun_linear_ne_zero _ (Or.inr (lfSQ_be h))

noncomputable def lfLQ (a : ℝ) : Plane →ᵃ[ℝ] ℝ := lineF 0 0 (sQ a) (tQ a)

theorem lfLQ_al (h : Hyp a) : -((tQ a) - 0) ≠ 0 := by
  obtain ⟨ha, hb, hK, hN, hM⟩ := id h
  have e : -((tQ a) - 0) = -1 * ((gN a)) := by unf; ring
  have hp : 0 < (gN a) := by positivity
  rw [e]; intro h0; nlinarith

theorem lfLQ_ne (h : Hyp a) : (lfLQ a).linear ≠ 0 :=
  coordFun_linear_ne_zero _ (Or.inl (lfLQ_al h))

theorem vf_XV_L_le (h : Hyp a) : lfXV a (mkPt 0 0) ≤ 0 := by
  obtain ⟨ha, hb, hK, hN, hM⟩ := id h
  have e : lfXV a (mkPt 0 0) = -1 * (a ^ 4 * (gb a)) := by unfold lfXV; unf; ring
  have hp : 0 ≤ a ^ 4 * (gb a) := by positivity
  rw [e]; nlinarith

theorem vf_XV_P_ge (h : Hyp a) : 0 ≤ lfXV a (mkPt (sP a) (tP a)) := by
  obtain ⟨ha, hb, hK, hN, hM⟩ := id h
  have e : lfXV a (mkPt (sP a) (tP a)) = 1 * (a ^ 2 * (gb a) ^ 3) := by unfold lfXV; unf; ring
  have hp : 0 ≤ a ^ 2 * (gb a) ^ 3 := by positivity
  rw [e]; nlinarith

theorem vf_XV_Q_le (h : Hyp a) : lfXV a (mkPt (sQ a) (tQ a)) ≤ 0 := by
  obtain ⟨ha, hb, hK, hN, hM⟩ := id h
  have e : lfXV a (mkPt (sQ a) (tQ a)) = -1 * (a ^ 2 * (gb a) ^ 5) := by unfold lfXV; unf; ring
  have hp : 0 ≤ a ^ 2 * (gb a) ^ 5 := by positivity
  rw [e]; nlinarith

theorem vf_XV_R_le (h : Hyp a) : lfXV a (mkPt (sR a) 0) ≤ 0 := by
  obtain ⟨ha, hb, hK, hN, hM⟩ := id h
  have e : lfXV a (mkPt (sR a) 0) = -1 * (a ^ 6 * (gb a) ^ 2) := by unfold lfXV; unf; ring
  have hp : 0 ≤ a ^ 6 * (gb a) ^ 2 := by positivity
  rw [e]; nlinarith

theorem vf_XV_S_le (h : Hyp a) : lfXV a (mkPt 0 (tS a)) ≤ 0 := by
  obtain ⟨ha, hb, hK, hN, hM⟩ := id h
  have e : lfXV a (mkPt 0 (tS a)) = -1 * (a ^ 2 * (gM a) * (gb a) ^ 3) := by unfold lfXV; unf; ring
  have hp : 0 ≤ a ^ 2 * (gM a) * (gb a) ^ 3 := by positivity
  rw [e]; nlinarith

theorem vf_XV_V_le (h : Hyp a) : lfXV a (mkPt (sV a) (tV a)) ≤ 0 := by
  have e : lfXV a (mkPt (sV a) (tV a)) = 0 := by unfold lfXV; unf; ring
  exact le_of_eq e

theorem vf_XV_V_ge (h : Hyp a) : 0 ≤ lfXV a (mkPt (sV a) (tV a)) := by
  have e : lfXV a (mkPt (sV a) (tV a)) = 0 := by unfold lfXV; unf; ring
  exact le_of_eq e.symm

theorem vf_XV_X_le (h : Hyp a) : lfXV a (mkPt (sX a) (tX a)) ≤ 0 := by
  have e : lfXV a (mkPt (sX a) (tX a)) = 0 := by unfold lfXV; unf; ring
  exact le_of_eq e

theorem vf_XV_X_ge (h : Hyp a) : 0 ≤ lfXV a (mkPt (sX a) (tX a)) := by
  have e : lfXV a (mkPt (sX a) (tX a)) = 0 := by unfold lfXV; unf; ring
  exact le_of_eq e.symm

theorem vf_XV_Z_le (h : Hyp a) : lfXV a (mkPt 0 (tZ a)) ≤ 0 := by
  obtain ⟨ha, hb, hK, hN, hM⟩ := id h
  have e : lfXV a (mkPt 0 (tZ a)) = -1 * (a ^ 4 * (gb a) ^ 3) := by unfold lfXV; unf; ring
  have hp : 0 ≤ a ^ 4 * (gb a) ^ 3 := by positivity
  rw [e]; nlinarith

theorem vf_XZ_L_le (h : Hyp a) : lfXZ a (mkPt 0 0) ≤ 0 := by
  obtain ⟨ha, hb, hK, hN, hM⟩ := id h
  have e : lfXZ a (mkPt 0 0) = -1 * (a ^ 6 * (gb a)) := by unfold lfXZ; unf; ring
  have hp : 0 ≤ a ^ 6 * (gb a) := by positivity
  rw [e]; nlinarith

theorem vf_XZ_Q_ge (h : Hyp a) : 0 ≤ lfXZ a (mkPt (sQ a) (tQ a)) := by
  obtain ⟨ha, hb, hK, hN, hM⟩ := id h
  have e : lfXZ a (mkPt (sQ a) (tQ a)) = 1 * (a ^ 4 * (gb a) ^ 3) := by unfold lfXZ; unf; ring
  have hp : 0 ≤ a ^ 4 * (gb a) ^ 3 := by positivity
  rw [e]; nlinarith

theorem vf_XZ_V_ge (h : Hyp a) : 0 ≤ lfXZ a (mkPt (sV a) (tV a)) := by
  obtain ⟨ha, hb, hK, hN, hM⟩ := id h
  have e : lfXZ a (mkPt (sV a) (tV a)) = 1 * (a ^ 4 * (gb a) ^ 3) := by unfold lfXZ; unf; ring
  have hp : 0 ≤ a ^ 4 * (gb a) ^ 3 := by positivity
  rw [e]; nlinarith

theorem vf_XZ_X_le (h : Hyp a) : lfXZ a (mkPt (sX a) (tX a)) ≤ 0 := by
  have e : lfXZ a (mkPt (sX a) (tX a)) = 0 := by unfold lfXZ; unf; ring
  exact le_of_eq e

theorem vf_XZ_X_ge (h : Hyp a) : 0 ≤ lfXZ a (mkPt (sX a) (tX a)) := by
  have e : lfXZ a (mkPt (sX a) (tX a)) = 0 := by unfold lfXZ; unf; ring
  exact le_of_eq e.symm

theorem vf_XZ_Z_le (h : Hyp a) : lfXZ a (mkPt 0 (tZ a)) ≤ 0 := by
  have e : lfXZ a (mkPt 0 (tZ a)) = 0 := by unfold lfXZ; unf; ring
  exact le_of_eq e

theorem vf_XZ_Z_ge (h : Hyp a) : 0 ≤ lfXZ a (mkPt 0 (tZ a)) := by
  have e : lfXZ a (mkPt 0 (tZ a)) = 0 := by unfold lfXZ; unf; ring
  exact le_of_eq e.symm

theorem vf_ZV_L_le (h : Hyp a) : lfZV a (mkPt 0 0) ≤ 0 := by
  obtain ⟨ha, hb, hK, hN, hM⟩ := id h
  have e : lfZV a (mkPt 0 0) = -1 * (a ^ 6 * (gb a) ^ 2) := by unfold lfZV; unf; ring
  have hp : 0 ≤ a ^ 6 * (gb a) ^ 2 := by positivity
  rw [e]; nlinarith

theorem vf_ZV_Q_le (h : Hyp a) : lfZV a (mkPt (sQ a) (tQ a)) ≤ 0 := by
  obtain ⟨ha, hb, hK, hN, hM⟩ := id h
  have e : lfZV a (mkPt (sQ a) (tQ a)) = -1 * (a ^ 2 * (gb a) ^ 5) := by unfold lfZV; unf; ring
  have hp : 0 ≤ a ^ 2 * (gb a) ^ 5 := by positivity
  rw [e]; nlinarith

theorem vf_ZV_R_le (h : Hyp a) : lfZV a (mkPt (sR a) 0) ≤ 0 := by
  obtain ⟨ha, hb, hK, hN, hM⟩ := id h
  have e : lfZV a (mkPt (sR a) 0) = -1 * (a ^ 6 * (gb a) ^ 2) := by unfold lfZV; unf; ring
  have hp : 0 ≤ a ^ 6 * (gb a) ^ 2 := by positivity
  rw [e]; nlinarith

theorem vf_ZV_S_le (h : Hyp a) : lfZV a (mkPt 0 (tS a)) ≤ 0 := by
  obtain ⟨ha, hb, hK, hN, hM⟩ := id h
  have e : lfZV a (mkPt 0 (tS a)) = -1 * (a ^ 2 * (gb a) ^ 5) := by unfold lfZV; unf; ring
  have hp : 0 ≤ a ^ 2 * (gb a) ^ 5 := by positivity
  rw [e]; nlinarith

theorem vf_ZV_V_le (h : Hyp a) : lfZV a (mkPt (sV a) (tV a)) ≤ 0 := by
  have e : lfZV a (mkPt (sV a) (tV a)) = 0 := by unfold lfZV; unf; ring
  exact le_of_eq e

theorem vf_ZV_V_ge (h : Hyp a) : 0 ≤ lfZV a (mkPt (sV a) (tV a)) := by
  have e : lfZV a (mkPt (sV a) (tV a)) = 0 := by unfold lfZV; unf; ring
  exact le_of_eq e.symm

theorem vf_ZV_X_ge (h : Hyp a) : 0 ≤ lfZV a (mkPt (sX a) (tX a)) := by
  obtain ⟨ha, hb, hK, hN, hM⟩ := id h
  have e : lfZV a (mkPt (sX a) (tX a)) = 1 * (a ^ 4 * (gb a) ^ 3) := by unfold lfZV; unf; ring
  have hp : 0 ≤ a ^ 4 * (gb a) ^ 3 := by positivity
  rw [e]; nlinarith

theorem vf_ZV_Z_le (h : Hyp a) : lfZV a (mkPt 0 (tZ a)) ≤ 0 := by
  have e : lfZV a (mkPt 0 (tZ a)) = 0 := by unfold lfZV; unf; ring
  exact le_of_eq e

theorem vf_ZV_Z_ge (h : Hyp a) : 0 ≤ lfZV a (mkPt 0 (tZ a)) := by
  have e : lfZV a (mkPt 0 (tZ a)) = 0 := by unfold lfZV; unf; ring
  exact le_of_eq e.symm

theorem vf_ZS_L_le (h : Hyp a) : lfZS a (mkPt 0 0) ≤ 0 := by
  have e : lfZS a (mkPt 0 0) = 0 := by unfold lfZS; unf; ring
  exact le_of_eq e

theorem vf_ZS_L_ge (h : Hyp a) : 0 ≤ lfZS a (mkPt 0 0) := by
  have e : lfZS a (mkPt 0 0) = 0 := by unfold lfZS; unf; ring
  exact le_of_eq e.symm

theorem vf_ZS_Q_ge (h : Hyp a) : 0 ≤ lfZS a (mkPt (sQ a) (tQ a)) := by
  obtain ⟨ha, hb, hK, hN, hM⟩ := id h
  have e : lfZS a (mkPt (sQ a) (tQ a)) = 1 * ((gb a) ^ 5) := by unfold lfZS; unf; ring
  have hp : 0 ≤ (gb a) ^ 5 := by positivity
  rw [e]; nlinarith

theorem vf_ZS_R_ge (h : Hyp a) : 0 ≤ lfZS a (mkPt (sR a) 0) := by
  obtain ⟨ha, hb, hK, hN, hM⟩ := id h
  have e : lfZS a (mkPt (sR a) 0) = 1 * (a ^ 2 * (gK a) * (gb a) ^ 3) := by unfold lfZS; unf; ring
  have hp : 0 ≤ a ^ 2 * (gK a) * (gb a) ^ 3 := by positivity
  rw [e]; nlinarith

theorem vf_ZS_S_ge (h : Hyp a) : 0 ≤ lfZS a (mkPt 0 (tS a)) := by
  have e : lfZS a (mkPt 0 (tS a)) = 0 := by unfold lfZS; unf; ring
  exact le_of_eq e.symm

theorem vf_ZS_X_le (h : Hyp a) : lfZS a (mkPt (sX a) (tX a)) ≤ 0 := by
  obtain ⟨ha, hb, hK, hN, hM⟩ := id h
  have e : lfZS a (mkPt (sX a) (tX a)) = -1 * (a ^ 2 * (gb a) ^ 4) := by unfold lfZS; unf; ring
  have hp : 0 ≤ a ^ 2 * (gb a) ^ 4 := by positivity
  rw [e]; nlinarith

theorem vf_ZS_Z_le (h : Hyp a) : lfZS a (mkPt 0 (tZ a)) ≤ 0 := by
  have e : lfZS a (mkPt 0 (tZ a)) = 0 := by unfold lfZS; unf; ring
  exact le_of_eq e

theorem vf_ZS_Z_ge (h : Hyp a) : 0 ≤ lfZS a (mkPt 0 (tZ a)) := by
  have e : lfZS a (mkPt 0 (tZ a)) = 0 := by unfold lfZS; unf; ring
  exact le_of_eq e.symm

theorem vf_ZQ_L_le (h : Hyp a) : lfZQ a (mkPt 0 0) ≤ 0 := by
  obtain ⟨ha, hb, hK, hN, hM⟩ := id h
  have e : lfZQ a (mkPt 0 0) = -1 * (a ^ 4 * (gb a) ^ 2) := by unfold lfZQ; unf; ring
  have hp : 0 ≤ a ^ 4 * (gb a) ^ 2 := by positivity
  rw [e]; nlinarith

theorem vf_ZQ_Q_le (h : Hyp a) : lfZQ a (mkPt (sQ a) (tQ a)) ≤ 0 := by
  have e : lfZQ a (mkPt (sQ a) (tQ a)) = 0 := by unfold lfZQ; unf; ring
  exact le_of_eq e

theorem vf_ZQ_Q_ge (h : Hyp a) : 0 ≤ lfZQ a (mkPt (sQ a) (tQ a)) := by
  have e : lfZQ a (mkPt (sQ a) (tQ a)) = 0 := by unfold lfZQ; unf; ring
  exact le_of_eq e.symm

theorem vf_ZQ_R_le (h : Hyp a) : lfZQ a (mkPt (sR a) 0) ≤ 0 := by
  obtain ⟨ha, hb, hK, hN, hM⟩ := id h
  have e : lfZQ a (mkPt (sR a) 0) = -1 * (a ^ 2 * (gN a) * (gb a) ^ 2) := by unfold lfZQ; unf; ring
  have hp : 0 ≤ a ^ 2 * (gN a) * (gb a) ^ 2 := by positivity
  rw [e]; nlinarith

theorem vf_ZQ_S_le (h : Hyp a) : lfZQ a (mkPt 0 (tS a)) ≤ 0 := by
  obtain ⟨ha, hb, hK, hN, hM⟩ := id h
  have e : lfZQ a (mkPt 0 (tS a)) = -1 * ((gb a) ^ 5) := by unfold lfZQ; unf; ring
  have hp : 0 ≤ (gb a) ^ 5 := by positivity
  rw [e]; nlinarith

theorem vf_ZQ_V_ge (h : Hyp a) : 0 ≤ lfZQ a (mkPt (sV a) (tV a)) := by
  obtain ⟨ha, hb, hK, hN, hM⟩ := id h
  have e : lfZQ a (mkPt (sV a) (tV a)) = 1 * (a ^ 2 * (gb a) ^ 5) := by unfold lfZQ; unf; ring
  have hp : 0 ≤ a ^ 2 * (gb a) ^ 5 := by positivity
  rw [e]; nlinarith

theorem vf_ZQ_Z_le (h : Hyp a) : lfZQ a (mkPt 0 (tZ a)) ≤ 0 := by
  have e : lfZQ a (mkPt 0 (tZ a)) = 0 := by unfold lfZQ; unf; ring
  exact le_of_eq e

theorem vf_ZQ_Z_ge (h : Hyp a) : 0 ≤ lfZQ a (mkPt 0 (tZ a)) := by
  have e : lfZQ a (mkPt 0 (tZ a)) = 0 := by unfold lfZQ; unf; ring
  exact le_of_eq e.symm

theorem vf_SQ_L_le (h : Hyp a) : lfSQ a (mkPt 0 0) ≤ 0 := by
  obtain ⟨ha, hb, hK, hN, hM⟩ := id h
  have e : lfSQ a (mkPt 0 0) = -1 * ((gN a) * (gb a) ^ 2) := by unfold lfSQ; unf; ring
  have hp : 0 ≤ (gN a) * (gb a) ^ 2 := by positivity
  rw [e]; nlinarith

theorem vf_SQ_Q_le (h : Hyp a) : lfSQ a (mkPt (sQ a) (tQ a)) ≤ 0 := by
  have e : lfSQ a (mkPt (sQ a) (tQ a)) = 0 := by unfold lfSQ; unf; ring
  exact le_of_eq e

theorem vf_SQ_Q_ge (h : Hyp a) : 0 ≤ lfSQ a (mkPt (sQ a) (tQ a)) := by
  have e : lfSQ a (mkPt (sQ a) (tQ a)) = 0 := by unfold lfSQ; unf; ring
  exact le_of_eq e.symm

theorem vf_SQ_R_le (h : Hyp a) : lfSQ a (mkPt (sR a) 0) ≤ 0 := by
  obtain ⟨ha, hb, hK, hN, hM⟩ := id h
  have e : lfSQ a (mkPt (sR a) 0) = -1 * ((gN a) * (gb a) ^ 2) := by unfold lfSQ; unf; ring
  have hp : 0 ≤ (gN a) * (gb a) ^ 2 := by positivity
  rw [e]; nlinarith

theorem vf_SQ_S_le (h : Hyp a) : lfSQ a (mkPt 0 (tS a)) ≤ 0 := by
  have e : lfSQ a (mkPt 0 (tS a)) = 0 := by unfold lfSQ; unf; ring
  exact le_of_eq e

theorem vf_SQ_S_ge (h : Hyp a) : 0 ≤ lfSQ a (mkPt 0 (tS a)) := by
  have e : lfSQ a (mkPt 0 (tS a)) = 0 := by unfold lfSQ; unf; ring
  exact le_of_eq e.symm

theorem vf_SQ_Z_ge (h : Hyp a) : 0 ≤ lfSQ a (mkPt 0 (tZ a)) := by
  obtain ⟨ha, hb, hK, hN, hM⟩ := id h
  have e : lfSQ a (mkPt 0 (tZ a)) = 1 * ((gb a) ^ 5) := by unfold lfSQ; unf; ring
  have hp : 0 ≤ (gb a) ^ 5 := by positivity
  rw [e]; nlinarith

theorem vf_LQ_L_le (h : Hyp a) : lfLQ a (mkPt 0 0) ≤ 0 := by
  have e : lfLQ a (mkPt 0 0) = 0 := by unfold lfLQ; unf; ring
  exact le_of_eq e

theorem vf_LQ_L_ge (h : Hyp a) : 0 ≤ lfLQ a (mkPt 0 0) := by
  have e : lfLQ a (mkPt 0 0) = 0 := by unfold lfLQ; unf; ring
  exact le_of_eq e.symm

theorem vf_LQ_Q_le (h : Hyp a) : lfLQ a (mkPt (sQ a) (tQ a)) ≤ 0 := by
  have e : lfLQ a (mkPt (sQ a) (tQ a)) = 0 := by unfold lfLQ; unf; ring
  exact le_of_eq e

theorem vf_LQ_Q_ge (h : Hyp a) : 0 ≤ lfLQ a (mkPt (sQ a) (tQ a)) := by
  have e : lfLQ a (mkPt (sQ a) (tQ a)) = 0 := by unfold lfLQ; unf; ring
  exact le_of_eq e.symm

theorem vf_LQ_R_le (h : Hyp a) : lfLQ a (mkPt (sR a) 0) ≤ 0 := by
  obtain ⟨ha, hb, hK, hN, hM⟩ := id h
  have e : lfLQ a (mkPt (sR a) 0) = -1 * (a ^ 2 * (gK a) * (gN a)) := by unfold lfLQ; unf; ring
  have hp : 0 ≤ a ^ 2 * (gK a) * (gN a) := by positivity
  rw [e]; nlinarith

theorem vf_LQ_S_ge (h : Hyp a) : 0 ≤ lfLQ a (mkPt 0 (tS a)) := by
  obtain ⟨ha, hb, hK, hN, hM⟩ := id h
  have e : lfLQ a (mkPt 0 (tS a)) = 1 * ((gN a) * (gb a) ^ 2) := by unfold lfLQ; unf; ring
  have hp : 0 ≤ (gN a) * (gb a) ^ 2 := by positivity
  rw [e]; nlinarith

theorem d_AB (h : Hyp a) : Disjoint (interior (triA h).carrier) (interior (triB h).carrier) :=
  (sep_vertices (lfXV a) (lfXV_ne h) 0 (vf_XV_V_le h) (vf_XV_X_le h) (vf_XV_Z_le h) (vf_XV_P_ge h) (vf_XV_V_ge h) (vf_XV_X_ge h)).symm

theorem d_AC (h : Hyp a) : Disjoint (interior (triA h).carrier) (interior (triC h).carrier) :=
  (sep_vertices (lfXV a) (lfXV_ne h) 0 (vf_XV_X_le h) (vf_XV_L_le h) (vf_XV_Z_le h) (vf_XV_P_ge h) (vf_XV_V_ge h) (vf_XV_X_ge h)).symm

theorem d_AD (h : Hyp a) : Disjoint (interior (triA h).carrier) (interior (triD h).carrier) :=
  (sep_vertices (lfXV a) (lfXV_ne h) 0 (vf_XV_Q_le h) (vf_XV_Z_le h) (vf_XV_V_le h) (vf_XV_P_ge h) (vf_XV_V_ge h) (vf_XV_X_ge h)).symm

theorem d_AE (h : Hyp a) : Disjoint (interior (triA h).carrier) (interior (triE h).carrier) :=
  (sep_vertices (lfXV a) (lfXV_ne h) 0 (vf_XV_S_le h) (vf_XV_Q_le h) (vf_XV_Z_le h) (vf_XV_P_ge h) (vf_XV_V_ge h) (vf_XV_X_ge h)).symm

theorem d_AF (h : Hyp a) : Disjoint (interior (triA h).carrier) (interior (triF h).carrier) :=
  (sep_vertices (lfXV a) (lfXV_ne h) 0 (vf_XV_L_le h) (vf_XV_R_le h) (vf_XV_Q_le h) (vf_XV_P_ge h) (vf_XV_V_ge h) (vf_XV_X_ge h)).symm

theorem d_AG (h : Hyp a) : Disjoint (interior (triA h).carrier) (interior (triG h).carrier) :=
  (sep_vertices (lfXV a) (lfXV_ne h) 0 (vf_XV_L_le h) (vf_XV_Q_le h) (vf_XV_S_le h) (vf_XV_P_ge h) (vf_XV_V_ge h) (vf_XV_X_ge h)).symm

theorem d_BC (h : Hyp a) : Disjoint (interior (triB h).carrier) (interior (triC h).carrier) :=
  (sep_vertices (lfXZ a) (lfXZ_ne h) 0 (vf_XZ_X_le h) (vf_XZ_L_le h) (vf_XZ_Z_le h) (vf_XZ_V_ge h) (vf_XZ_X_ge h) (vf_XZ_Z_ge h)).symm

theorem d_BD (h : Hyp a) : Disjoint (interior (triB h).carrier) (interior (triD h).carrier) :=
  (sep_vertices (lfZV a) (lfZV_ne h) 0 (vf_ZV_Q_le h) (vf_ZV_Z_le h) (vf_ZV_V_le h) (vf_ZV_V_ge h) (vf_ZV_X_ge h) (vf_ZV_Z_ge h)).symm

theorem d_BE (h : Hyp a) : Disjoint (interior (triB h).carrier) (interior (triE h).carrier) :=
  (sep_vertices (lfZV a) (lfZV_ne h) 0 (vf_ZV_S_le h) (vf_ZV_Q_le h) (vf_ZV_Z_le h) (vf_ZV_V_ge h) (vf_ZV_X_ge h) (vf_ZV_Z_ge h)).symm

theorem d_BF (h : Hyp a) : Disjoint (interior (triB h).carrier) (interior (triF h).carrier) :=
  (sep_vertices (lfZV a) (lfZV_ne h) 0 (vf_ZV_L_le h) (vf_ZV_R_le h) (vf_ZV_Q_le h) (vf_ZV_V_ge h) (vf_ZV_X_ge h) (vf_ZV_Z_ge h)).symm

theorem d_BG (h : Hyp a) : Disjoint (interior (triB h).carrier) (interior (triG h).carrier) :=
  (sep_vertices (lfZV a) (lfZV_ne h) 0 (vf_ZV_L_le h) (vf_ZV_Q_le h) (vf_ZV_S_le h) (vf_ZV_V_ge h) (vf_ZV_X_ge h) (vf_ZV_Z_ge h)).symm

theorem d_CD (h : Hyp a) : Disjoint (interior (triC h).carrier) (interior (triD h).carrier) :=
  sep_vertices (lfXZ a) (lfXZ_ne h) 0 (vf_XZ_X_le h) (vf_XZ_L_le h) (vf_XZ_Z_le h) (vf_XZ_Q_ge h) (vf_XZ_Z_ge h) (vf_XZ_V_ge h)

theorem d_CE (h : Hyp a) : Disjoint (interior (triC h).carrier) (interior (triE h).carrier) :=
  sep_vertices (lfZS a) (lfZS_ne h) 0 (vf_ZS_X_le h) (vf_ZS_L_le h) (vf_ZS_Z_le h) (vf_ZS_S_ge h) (vf_ZS_Q_ge h) (vf_ZS_Z_ge h)

theorem d_CF (h : Hyp a) : Disjoint (interior (triC h).carrier) (interior (triF h).carrier) :=
  sep_vertices (lfZS a) (lfZS_ne h) 0 (vf_ZS_X_le h) (vf_ZS_L_le h) (vf_ZS_Z_le h) (vf_ZS_L_ge h) (vf_ZS_R_ge h) (vf_ZS_Q_ge h)

theorem d_CG (h : Hyp a) : Disjoint (interior (triC h).carrier) (interior (triG h).carrier) :=
  sep_vertices (lfZS a) (lfZS_ne h) 0 (vf_ZS_X_le h) (vf_ZS_L_le h) (vf_ZS_Z_le h) (vf_ZS_L_ge h) (vf_ZS_Q_ge h) (vf_ZS_S_ge h)

theorem d_DE (h : Hyp a) : Disjoint (interior (triD h).carrier) (interior (triE h).carrier) :=
  (sep_vertices (lfZQ a) (lfZQ_ne h) 0 (vf_ZQ_S_le h) (vf_ZQ_Q_le h) (vf_ZQ_Z_le h) (vf_ZQ_Q_ge h) (vf_ZQ_Z_ge h) (vf_ZQ_V_ge h)).symm

theorem d_DF (h : Hyp a) : Disjoint (interior (triD h).carrier) (interior (triF h).carrier) :=
  (sep_vertices (lfZQ a) (lfZQ_ne h) 0 (vf_ZQ_L_le h) (vf_ZQ_R_le h) (vf_ZQ_Q_le h) (vf_ZQ_Q_ge h) (vf_ZQ_Z_ge h) (vf_ZQ_V_ge h)).symm

theorem d_DG (h : Hyp a) : Disjoint (interior (triD h).carrier) (interior (triG h).carrier) :=
  (sep_vertices (lfZQ a) (lfZQ_ne h) 0 (vf_ZQ_L_le h) (vf_ZQ_Q_le h) (vf_ZQ_S_le h) (vf_ZQ_Q_ge h) (vf_ZQ_Z_ge h) (vf_ZQ_V_ge h)).symm

theorem d_EF (h : Hyp a) : Disjoint (interior (triE h).carrier) (interior (triF h).carrier) :=
  (sep_vertices (lfSQ a) (lfSQ_ne h) 0 (vf_SQ_L_le h) (vf_SQ_R_le h) (vf_SQ_Q_le h) (vf_SQ_S_ge h) (vf_SQ_Q_ge h) (vf_SQ_Z_ge h)).symm

theorem d_EG (h : Hyp a) : Disjoint (interior (triE h).carrier) (interior (triG h).carrier) :=
  (sep_vertices (lfSQ a) (lfSQ_ne h) 0 (vf_SQ_L_le h) (vf_SQ_Q_le h) (vf_SQ_S_le h) (vf_SQ_S_ge h) (vf_SQ_Q_ge h) (vf_SQ_Z_ge h)).symm

theorem d_FG (h : Hyp a) : Disjoint (interior (triF h).carrier) (interior (triG h).carrier) :=
  sep_vertices (lfLQ a) (lfLQ_ne h) 0 (vf_LQ_L_le h) (vf_LQ_R_le h) (vf_LQ_Q_le h) (vf_LQ_L_ge h) (vf_LQ_Q_ge h) (vf_LQ_S_ge h)

noncomputable def tile (h : Hyp a) : Fin 7 → Tri := ![triA h, triB h, triC h, triD h, triE h, triF h, triG h]

set_option maxHeartbeats 1600000 in
theorem tile_disj (h : Hyp a) :
    Pairwise fun i j : Fin 7 => Disjoint (interior (tile h i).carrier) (interior (tile h j).carrier) := by
  intro i j hij
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij
  · exact d_AB h
  · exact d_AC h
  · exact d_AD h
  · exact d_AE h
  · exact d_AF h
  · exact d_AG h
  · exact (d_AB h).symm
  · exact absurd rfl hij
  · exact d_BC h
  · exact d_BD h
  · exact d_BE h
  · exact d_BF h
  · exact d_BG h
  · exact (d_AC h).symm
  · exact (d_BC h).symm
  · exact absurd rfl hij
  · exact d_CD h
  · exact d_CE h
  · exact d_CF h
  · exact d_CG h
  · exact (d_AD h).symm
  · exact (d_BD h).symm
  · exact (d_CD h).symm
  · exact absurd rfl hij
  · exact d_DE h
  · exact d_DF h
  · exact d_DG h
  · exact (d_AE h).symm
  · exact (d_BE h).symm
  · exact (d_CE h).symm
  · exact (d_DE h).symm
  · exact absurd rfl hij
  · exact d_EF h
  · exact d_EG h
  · exact (d_AF h).symm
  · exact (d_BF h).symm
  · exact (d_CF h).symm
  · exact (d_DF h).symm
  · exact (d_EF h).symm
  · exact absurd rfl hij
  · exact d_FG h
  · exact (d_AG h).symm
  · exact (d_BG h).symm
  · exact (d_CG h).symm
  · exact (d_DG h).symm
  · exact (d_EG h).symm
  · exact (d_FG h).symm
  · exact absurd rfl hij

theorem tile_sub (h : Hyp a) : ∀ i, (tile h i).carrier ⊆ (triT h).carrier := by
  intro i
  fin_cases i
  · exact sub_A h
  · exact sub_B h
  · exact sub_C h
  · exact sub_D h
  · exact sub_E h
  · exact sub_F h
  · exact sub_G h

theorem detTri_A (h : Hyp a) : Erdos634.AreaDet.detTri (triA h) = -1 * (a ^ 2 * (gb a) ^ 3) := by
  unfold triA; rw [detTri_mkTri]; exact det_A h

theorem detTri_B (h : Hyp a) : Erdos634.AreaDet.detTri (triB h) = 1 * (a ^ 4 * (gb a) ^ 3) := by
  unfold triB; rw [detTri_mkTri]; exact det_B h

theorem detTri_C (h : Hyp a) : Erdos634.AreaDet.detTri (triC h) = 1 * (a ^ 6 * (gb a)) := by
  unfold triC; rw [detTri_mkTri]; exact det_C h

theorem detTri_D (h : Hyp a) : Erdos634.AreaDet.detTri (triD h) = -1 * (a ^ 2 * (gb a) ^ 5) := by
  unfold triD; rw [detTri_mkTri]; exact det_D h

theorem detTri_E (h : Hyp a) : Erdos634.AreaDet.detTri (triE h) = 1 * ((gb a) ^ 5) := by
  unfold triE; rw [detTri_mkTri]; exact det_E h

theorem detTri_F (h : Hyp a) : Erdos634.AreaDet.detTri (triF h) = 1 * (a ^ 2 * (gK a) * (gN a)) := by
  unfold triF; rw [detTri_mkTri]; exact det_F h

theorem detTri_G (h : Hyp a) : Erdos634.AreaDet.detTri (triG h) = 1 * ((gN a) * (gb a) ^ 2) := by
  unfold triG; rw [detTri_mkTri]; exact det_G h

theorem detTri_T (h : Hyp a) : Erdos634.AreaDet.detTri (triT h) = 1 * (a ^ 2 * (gK a) ^ 2) := by
  unfold triT; rw [detTri_mkTri]; exact det_T h

theorem tile_vol (h : Hyp a) :
    ∑ i, |Erdos634.AreaDet.detTri (tile h i)| = |Erdos634.AreaDet.detTri (triT h)| := by
  have h' := h
  obtain ⟨ha, hb, hK, hN, hM⟩ := h'
  rw [Fin.sum_univ_seven]
  show |Erdos634.AreaDet.detTri (triA h)| + |Erdos634.AreaDet.detTri (triB h)| + |Erdos634.AreaDet.detTri (triC h)| + |Erdos634.AreaDet.detTri (triD h)| + |Erdos634.AreaDet.detTri (triE h)| + |Erdos634.AreaDet.detTri (triF h)| + |Erdos634.AreaDet.detTri (triG h)| = |Erdos634.AreaDet.detTri (triT h)|
  rw [detTri_A h, detTri_B h, detTri_C h, detTri_D h, detTri_E h, detTri_F h, detTri_G h, detTri_T h]
  have pA : 0 < a ^ 2 * (gb a) ^ 3 := by positivity
  rw [abs_of_neg (by nlinarith [pA] : -1 * (a ^ 2 * (gb a) ^ 3) < 0)]
  have pB : 0 < a ^ 4 * (gb a) ^ 3 := by positivity
  rw [abs_of_pos (by nlinarith [pB] : 0 < 1 * (a ^ 4 * (gb a) ^ 3))]
  have pC : 0 < a ^ 6 * (gb a) := by positivity
  rw [abs_of_pos (by nlinarith [pC] : 0 < 1 * (a ^ 6 * (gb a)))]
  have pD : 0 < a ^ 2 * (gb a) ^ 5 := by positivity
  rw [abs_of_neg (by nlinarith [pD] : -1 * (a ^ 2 * (gb a) ^ 5) < 0)]
  have pE : 0 < (gb a) ^ 5 := by positivity
  rw [abs_of_pos (by nlinarith [pE] : 0 < 1 * ((gb a) ^ 5))]
  have pF : 0 < a ^ 2 * (gK a) * (gN a) := by positivity
  rw [abs_of_pos (by nlinarith [pF] : 0 < 1 * (a ^ 2 * (gK a) * (gN a)))]
  have pG : 0 < (gN a) * (gb a) ^ 2 := by positivity
  rw [abs_of_pos (by nlinarith [pG] : 0 < 1 * ((gN a) * (gb a) ^ 2))]
  have pT : 0 < a ^ 2 * (gK a) ^ 2 := by positivity
  rw [abs_of_pos (by nlinarith [pT] : 0 < 1 * (a ^ 2 * (gK a) ^ 2))]
  simp only [gb, gK, gN]; ring

/-- **Fig. 5 (first picture) in the chart**: the seven pieces cover the target `T`. -/
theorem tile_cover (h : Hyp a) : (⋃ i, (tile h i).carrier) = (triT h).carrier :=
  covers_of_volume_tri (triT h) (tile h) (tile_sub h) (tile_disj h)
    (Erdos634.AreaDet.area_identity_of_det (triT h) (tile h) (tile_vol h))

end Erdos634.LaczL26
