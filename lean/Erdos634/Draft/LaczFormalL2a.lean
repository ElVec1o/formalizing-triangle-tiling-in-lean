-- Draft/LaczFormalL2a.lean -- atom L2a: Beeson-Rosu Lemma 1, first claim.
-- Source of the statement: Beeson-Rosu, "Tiling a triangle into a prime number of congruent triangles"
-- (arXiv 2607.23453), Lemma 1: "Let triangle T be tiled by triangle R. If R has commensurable angles,
-- so does T."  (The second claim is atom L2b, citing Laczkovich 1995, Thm 5.3.)
-- Proof here: angle sum at a corner of the target (`sum_localAngle_eq`) with the tile corner angles
-- (`target_angle_nat`, our own Lean proof, Dissection framework); then rationality bookkeeping.
-- UNAUDITED beyond the statement-match note in (private working notes, not included)
import Erdos634.Draft.CaseALemmaVDissection
import Erdos634.Draft.CaseAR0c
import Erdos634.Draft.LaczFormalBase

open scoped Classical
open Erdos634.Geometry Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal

/-- A triangle has *commensurable angles*: every angle is a rational multiple of every other. -/
def CommAngles (T : Tri) : Prop := ∀ i j : Fin 3, ∃ q : ℚ, T.angleAt i = (q : ℝ) * T.angleAt j

/-- Commensurable angles are the same as: all angles in `ℚπ` (the angle sum is `π`). -/
theorem commAngles_iff (T : Tri) : CommAngles T ↔ ∀ k, ∃ q : ℚ, T.angleAt k = (q : ℝ) * Real.pi := by
  have hpos : ∀ k, 0 < T.angleAt k := fun k => Erdos634.MarchFlank.cornerAngle_pos T k
  constructor
  · intro h k
    choose q hq using fun i => h i 0
    have hsum := angleAt_sum T
    have h0 := hq 0; have h1 := hq 1; have h2 := hq 2
    have hS : Real.pi = ((q 0 : ℝ) + q 1 + q 2) * T.angleAt 0 := by
      rw [← hsum]; linear_combination h0 + h1 + h2
    have hS0 : ((q 0 : ℝ) + q 1 + q 2) ≠ 0 := by
      intro h; rw [h, zero_mul] at hS; exact Real.pi_pos.ne' hS
    refine ⟨q k / (q 0 + q 1 + q 2), ?_⟩
    push_cast
    rw [hq k]
    have : T.angleAt 0 = Real.pi / ((q 0 : ℝ) + q 1 + q 2) := by
      field_simp; linarith
    rw [this]; field_simp
  · rintro h i j
    obtain ⟨a, ha⟩ := h i
    obtain ⟨b, hb⟩ := h j
    have hb0 : (b : ℝ) ≠ 0 := by
      intro h0; have := hpos j; rw [hb, h0] at this; simp at this
    refine ⟨a / b, ?_⟩
    rw [ha, hb]; push_cast; field_simp

/-- **L2a (Beeson-Rosu Lemma 1, first claim), for a congruent dissection of the target.**
If the tile has commensurable angles, so does the target triangle tiled by it. -/
theorem lemma1a {N : ℕ} (D : CongruentDissection N) (h : CommAngles D.model) :
    CommAngles D.target := by
  rw [commAngles_iff] at h ⊢
  choose q hq using h
  -- common denominator n of the three rationals
  set n : ℕ := (q 0).den * (q 1).den * (q 2).den with hn
  have hnpos : 0 < n := by
    simp only [hn]; exact Nat.mul_pos (Nat.mul_pos (q 0).den_pos (q 1).den_pos) (q 2).den_pos
  have hpos : ∀ k, 0 < D.model.angleAt k := fun k => Erdos634.MarchFlank.cornerAngle_pos D.model k
  have hqpos : ∀ k, 0 < q k := by
    intro k
    have := hpos k; rw [hq k] at this
    have h' : (0 : ℝ) < (q k : ℝ) := by
      by_contra hc; push Not at hc
      nlinarith [Real.pi_pos, mul_nonpos_of_nonpos_of_nonneg hc Real.pi_pos.le]
    exact_mod_cast h'
  have hnat : ∀ k, ∃ a : ℕ, D.model.angleAt k = a * Real.pi / n := by
    intro k
    have hd : (q k).den ∣ n := by
      fin_cases k
      · exact dvd_mul_of_dvd_left (dvd_mul_right _ _) _
      · exact dvd_mul_of_dvd_left (dvd_mul_left _ _) _
      · exact dvd_mul_left _ _
    refine ⟨(q k).num.toNat * (n / (q k).den), ?_⟩
    have hden : ((q k).den : ℝ) ≠ 0 := by exact_mod_cast (q k).den_nz
    have hnz : (n : ℝ) ≠ 0 := by exact_mod_cast hnpos.ne'
    have hcast : ((n / (q k).den : ℕ) : ℝ) = (n : ℝ) / (q k).den :=
      Nat.cast_div hd hden
    have hnum : (((q k).num.toNat : ℕ) : ℝ) = ((q k).num : ℝ) := by
      have : (0 : ℤ) ≤ (q k).num := Rat.num_nonneg.mpr (hqpos k).le
      exact_mod_cast Int.toNat_of_nonneg this
    rw [hq k, Rat.cast_def]
    push_cast
    rw [hcast, hnum]
    field_simp
  choose a ha using hnat
  intro k
  obtain ⟨u, hu⟩ := Erdos634.Geometry.CaseA.LemmaV.target_angle_nat D hnpos a ha k
  exact ⟨(u : ℚ) / n, by rw [hu]; push_cast; ring⟩

/-- Non-vacuity: a real congruent dissection whose model has commensurable angles exists
(`CaseALemmaHPiFour.dissection`, all model angles rational multiples of `π`), so the hypothesis of
`lemma1a` is satisfied, and its conclusion is then non-trivial (target angles are `π/4`). -/
theorem lemma1a_witness :
    CommAngles Erdos634.Draft.CaseALemmaHPiFour.dissection.model := by
  rw [commAngles_iff]; exact Erdos634.CaseA.R0c.hrat_witness

theorem lemma1a_witness_target : CommAngles Erdos634.Draft.CaseALemmaHPiFour.dissection.target :=
  lemma1a _ lemma1a_witness

end Erdos634.Draft.LaczFormal

#print axioms Erdos634.Draft.LaczFormal.commAngles_iff
#print axioms Erdos634.Draft.LaczFormal.lemma1a
#print axioms Erdos634.Draft.LaczFormal.lemma1a_witness_target
