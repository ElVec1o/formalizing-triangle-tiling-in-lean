import Erdos634.Draft.BeesonL28b
import Erdos634.Draft.BeesonColoringThm1Colour

/-!
# Beeson (arXiv 1206.2229v4) Lemma 28, step 1: the printed integers `M1, M2` as sums of tile signs

NOTE, UNAUDITED.  Credit: Michael Beeson (arXiv 1206.2229 v4, Lemmas 21-23, Thm 3, Thm 4), Laczkovich (DCG 48 (2012)),
Beeson-Zhang.  Formalization debt, not progress on the /goal outcomes.

Printed (Thm 3): `M1 = sum_j (-1)^{eps_j}`, `M2 = sum_j (-1)^{n_j+eps_j}`, where `Phi_1(t) = (-1)^eps (a+b+c)` and
`Phi_2(t) = (-1)^{n+eps} (a-b-c)` are the two flux values of a tile, and the signs of `Phi_i` are normalised so that
`Phi_i = +1` on `AB` (Lemma 23).  Here `Phi_1 = chiAt alpha _ 1 anc`, `Phi_2 = chiAt alpha _ 0 anc` with the anchor
`anc` the direction of the target edge `AB` (target edge 0, vertices `0,1,2 = A,B,C`), which is exactly the
normalisation `Phi_i = +1` on `AB`.  `M_i := sum eps^i` where `eps^i : Fin N -> Z` records the sign of each tile's flux
against the model's tile value (`SignsFor`).  `M1` is blacks minus whites when `eps^1` is also a proper colouring
(`sum_eq_black_sub_white`); the existence of such `eps^1`, `eps^2` is `exists_signs1`, `exists_signs2`.
This file: the generic boundary identities `phi1_sum`, `phi2_sum` for a target with angles `p alpha + q beta`.
-/

open scoped Classical

namespace Erdos634.BeesonColoring

open Erdos634.Geometry Erdos634.Geometry.A1Field

variable {N : ℕ}

/-- `Phi_1` of the printed text: the character `(-1)^{p-q}` on `p alpha + q beta`, anchored at the direction of `AB`. -/
noncomputable def Phi1 (D : CongruentDissection N) (α : ℝ) (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) : GridChar ℝ :=
  chiAt α hα 1 (D.target.leftUnit 0).angle

/-- `Phi_2` of the printed text: the character `(-1)^{p}` on `p alpha + q beta`, anchored at the direction of `AB`. -/
noncomputable def Phi2 (D : CongruentDissection N) (α : ℝ) (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) : GridChar ℝ :=
  chiAt α hα 0 (D.target.leftUnit 0).angle

/-- `eps i` is the sign of the `G`-flux of tile `i` against the model's tile value (`(-1)^eps`, resp. `(-1)^{n+eps}`). -/
def SignsFor (D : CongruentDissection N) (G : GridChar ℝ) (ε : Fin N → ℤ) : Prop :=
  ∀ i, (D.tile i).flux G.weight = (ε i : ℝ) * G.tileValue D.model

/-- parity sign of `Phi_2` on `p alpha + q beta` -/
noncomputable def sg0 (p : ℤ) : ℝ := if ((p : ℤ) : ZMod 2) = 0 then 1 else -1

theorem sg0_0 : sg0 0 = 1 := by unfold sg0; rw [if_pos (by decide)]
theorem sg0_1 : sg0 1 = -1 := by unfold sg0; rw [if_neg (by decide)]
theorem sg0_2 : sg0 2 = 1 := by unfold sg0; rw [if_pos (by decide)]
theorem sg0_3 : sg0 3 = -1 := by unfold sg0; rw [if_neg (by decide)]

theorem sg_00 : sg 2 0 = 1 := sg_20
theorem sg_22 : sg 0 2 = 1 := sg_02

/-- the anchored boundary identity with tile signs -/
theorem anc_sum (D : CongruentDissection N) (G : GridChar ℝ)
    (hsq : ∀ l ∈ G.L, G.chi l * G.chi l = 1)
    (hmodel : ∀ k, ((D.model.angleAt k : ℝ) : Real.Angle) ∈ G.L)
    (htarget : ∀ k, ((D.target.angleAt k : ℝ) : Real.Angle) ∈ G.L)
    (hanc : G.anchor = (D.target.leftUnit 0).angle) (ε : Fin N → ℤ) (hε : SignsFor D G ε) :
    ((∑ i, ε i : ℤ) : ℝ) * G.paperK D.model
      = - G.chi ((D.target.angleAt (0 + 2) : ℝ) : Real.Angle) * G.paperK D.target := by
  have h1 := D.target.flux_eq_of_anchor G hsq htarget 0 hanc
  rw [← G.tileValue_eq_paperK hsq _ hmodel, ← h1, ← D.flux_cancel G.weight G.weight_odd,
    Finset.sum_congr rfl fun i _ => hε i, ← Finset.sum_mul]
  push_cast
  rfl

theorem rep_angle {α β : ℝ} (hrel : 3 * α + 2 * β = Real.pi) (p q : ℤ) :
    (p : ℝ) * α + (q : ℝ) * β
      = ((2 * q - p : ℤ) : ℝ) * Real.pi + ((2 * p - 3 * q : ℤ) : ℝ) * (α / 2 + Real.pi / 2) := by
  have hβ : β = (Real.pi - 3 * α) / 2 := by linarith
  rw [hβ]; push_cast; ring

theorem chi1_val {α β : ℝ} (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hrel : 3 * α + 2 * β = Real.pi)
    (anc : Real.Angle) (p q : ℤ) :
    (chiAt α hα 1 anc).chi (((p : ℝ) * α + (q : ℝ) * β : ℝ) : Real.Angle) = sg p q := by
  rw [rep_angle hrel, chiAt_chi]
  unfold sg
  have : ((2 * q - p : ℤ) : ZMod 2) + 1 * ((2 * p - 3 * q : ℤ) : ZMod 2) = ((p - q : ℤ) : ZMod 2) := by
    push_cast; ring
  rw [this]

theorem chi0_val {α β : ℝ} (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hrel : 3 * α + 2 * β = Real.pi)
    (anc : Real.Angle) (p q : ℤ) :
    (chiAt α hα 0 anc).chi (((p : ℝ) * α + (q : ℝ) * β : ℝ) : Real.Angle) = sg0 p := by
  rw [rep_angle hrel, chiAt_chi]
  unfold sg0
  have h2 : (2 : ZMod 2) = 0 := by decide
  have : ((2 * q - p : ℤ) : ZMod 2) + 0 * ((2 * p - 3 * q : ℤ) : ZMod 2) = ((p : ℤ) : ZMod 2) := by
    push_cast; linear_combination ((q : ZMod 2) - (p : ZMod 2)) * h2
  rw [this]

theorem target_mem {α β : ℝ} (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hrel : 3 * α + 2 * β = Real.pi)
    (b : ZMod 2) (anc : Real.Angle) (D : CongruentDissection N) (p0 q0 p1 q1 p2 q2 : ℤ)
    (h0 : D.target.angleAt 0 = (p0 : ℝ) * α + (q0 : ℝ) * β)
    (h1 : D.target.angleAt 1 = (p1 : ℝ) * α + (q1 : ℝ) * β)
    (h2 : D.target.angleAt 2 = (p2 : ℝ) * α + (q2 : ℝ) * β) :
    ∀ k, ((D.target.angleAt k : ℝ) : Real.Angle) ∈ (chiAt α hα b anc).L := by
  intro k
  fin_cases k
  · show ((D.target.angleAt 0 : ℝ) : Real.Angle) ∈ _
    rw [h0, rep_angle hrel]; exact chiAt_mem _ _ _ _ _ _
  · show ((D.target.angleAt 1 : ℝ) : Real.Angle) ∈ _
    rw [h1, rep_angle hrel]; exact chiAt_mem _ _ _ _ _ _
  · show ((D.target.angleAt 2 : ℝ) : Real.Angle) ∈ _
    rw [h2, rep_angle hrel]; exact chiAt_mem _ _ _ _ _ _

/-- **`Phi_1` boundary identity**: `M1 (a+b+c) = chi(C) * (chi(A) |BC| + chi(B) |CA| + chi(C) |AB|)`. -/
theorem phi1_sum (D : CongruentDissection N) {α β a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hrel : 3 * α + 2 * β = Real.pi)
    (h : D.model.ThreeAlphaData α β a b c) (p0 q0 p1 q1 p2 q2 : ℤ)
    (h0 : D.target.angleAt 0 = (p0 : ℝ) * α + (q0 : ℝ) * β)
    (h1 : D.target.angleAt 1 = (p1 : ℝ) * α + (q1 : ℝ) * β)
    (h2 : D.target.angleAt 2 = (p2 : ℝ) * α + (q2 : ℝ) * β)
    (ε : Fin N → ℤ) (hε : SignsFor D (Phi1 D α hα) ε) :
    ((∑ i, ε i : ℤ) : ℝ) * (a + b + c)
      = sg p2 q2 * (sg p0 q0 * D.target.oppLen 0 + sg p1 q1 * D.target.oppLen 1
          + sg p2 q2 * D.target.oppLen 2) := by
  have hmodel : ∀ k, ((D.model.angleAt k : ℝ) : Real.Angle)
      ∈ (chiAt α hα 1 (D.target.leftUnit 0).angle).L := D.model.threeAlpha_angles_mem hα hrel h 1
  have hMm : (chiAt α hα 1 (D.target.leftUnit 0).angle).paperK D.model = a + b + c := by
    rw [← GridChar.tileValue_eq_paperK _ (chiAt_sq _ _ _ _) _ hmodel, chiAt_tileValue]
    exact threeAlpha_tileValue_minus D.model hα hrel h
  have hs := anc_sum D (chiAt α hα 1 (D.target.leftUnit 0).angle) (chiAt_sq _ _ _ _) hmodel
    (target_mem hα hrel 1 _ D p0 q0 p1 q1 p2 q2 h0 h1 h2) rfl ε hε
  have hPK : (chiAt α hα 1 (D.target.leftUnit 0).angle).paperK D.target
      = -(sg p0 q0 * D.target.oppLen 0 + sg p1 q1 * D.target.oppLen 1 + sg p2 q2 * D.target.oppLen 2) := by
    unfold GridChar.paperK
    rw [Fin.sum_univ_three, h0, h1, h2, chi1_val hα hrel, chi1_val hα hrel, chi1_val hα hrel]
  rw [hMm, hPK, show (0 : Fin 3) + 2 = 2 from rfl, h2, chi1_val hα hrel] at hs
  rw [hs]; ring

/-- **`Phi_2` boundary identity**: `M2 (a-b-c) = chi(C) * (chi(A) |BC| + chi(B) |CA| + chi(C) |AB|)`. -/
theorem phi2_sum (D : CongruentDissection N) {α β a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hrel : 3 * α + 2 * β = Real.pi)
    (h : D.model.ThreeAlphaData α β a b c) (p0 q0 p1 q1 p2 q2 : ℤ)
    (h0 : D.target.angleAt 0 = (p0 : ℝ) * α + (q0 : ℝ) * β)
    (h1 : D.target.angleAt 1 = (p1 : ℝ) * α + (q1 : ℝ) * β)
    (h2 : D.target.angleAt 2 = (p2 : ℝ) * α + (q2 : ℝ) * β)
    (ε : Fin N → ℤ) (hε : SignsFor D (Phi2 D α hα) ε) :
    ((∑ i, ε i : ℤ) : ℝ) * (a - b - c)
      = sg0 p2 * (sg0 p0 * D.target.oppLen 0 + sg0 p1 * D.target.oppLen 1
          + sg0 p2 * D.target.oppLen 2) := by
  have hmodel : ∀ k, ((D.model.angleAt k : ℝ) : Real.Angle)
      ∈ (chiAt α hα 0 (D.target.leftUnit 0).angle).L := D.model.threeAlpha_angles_mem hα hrel h 0
  have hMp : (chiAt α hα 0 (D.target.leftUnit 0).angle).paperK D.model = -(c + b - a) := by
    rw [← GridChar.tileValue_eq_paperK _ (chiAt_sq _ _ _ _) _ hmodel, chiAt_tileValue]
    exact threeAlpha_tileValue_plus D.model hα hrel h
  have hs := anc_sum D (chiAt α hα 0 (D.target.leftUnit 0).angle) (chiAt_sq _ _ _ _) hmodel
    (target_mem hα hrel 0 _ D p0 q0 p1 q1 p2 q2 h0 h1 h2) rfl ε hε
  have hPK : (chiAt α hα 0 (D.target.leftUnit 0).angle).paperK D.target
      = -(sg0 p0 * D.target.oppLen 0 + sg0 p1 * D.target.oppLen 1 + sg0 p2 * D.target.oppLen 2) := by
    unfold GridChar.paperK
    rw [Fin.sum_univ_three, h0, h1, h2, chi0_val hα hrel, chi0_val hα hrel, chi0_val hα hrel]
  rw [hMp, hPK, show (0 : Fin 3) + 2 = 2 from rfl, h2, chi0_val hα hrel] at hs
  have : ((∑ i, ε i : ℤ) : ℝ) * (a - b - c) = ((∑ i, ε i : ℤ) : ℝ) * (-(c + b - a)) := by ring
  rw [this, hs]; ring

end Erdos634.BeesonColoring

#print axioms Erdos634.BeesonColoring.phi1_sum
#print axioms Erdos634.BeesonColoring.phi2_sum
