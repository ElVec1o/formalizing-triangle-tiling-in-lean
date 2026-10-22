import Mathlib
import Erdos634.Draft.BeesonRosu37b1

/-!
# Beeson-Rosu Theorem 37, gap (3): the corner angles of the isosceles-beta triangle from its side lengths

NOTE, UNAUDITED.  Credit: Michael Beeson and Rosu (arXiv 2607.23453 v2, Theorem 37 / Lemma 35: legs `kc = k^3`, base `m(b+2c)`),
Beeson, Laczkovich.  Formalization debt, not progress on the /goal outcomes.

A triangle with sides `(k^3, k^3, m(3k^2-m^2))` has base corners `modelBeta m k` and apex `3 modelAlpha m k`.  Law of cosines + angle sum;
hypotheses are the side lengths only (witness: `BaseBetaTargetCoord.baseBetaTarget_dist_*`, the coordinate triangle).
-/

namespace Erdos634.BeesonRosu37c1

open Erdos634.Geometry Erdos634.BaseBetaTargetCoord Erdos634.Draft.FDBBaseBetaE1

variable {N : ℕ}

/-- Corner angles from the side lengths, for the labelling `τ` of `HasSides` (`τ 2` apex, `τ 0, τ 1` base). -/
theorem corners_of_dists (T : Erdos634.Geometry.Tri) {e f : ℝ} (he : 0 < e) (hef : e < f) (τ : Equiv.Perm (Fin 3))
    (h1 : dist (T.pts (τ 1)) (T.pts (τ 2)) = f ^ 3) (h2 : dist (T.pts (τ 2)) (T.pts (τ 0)) = f ^ 3)
    (h3 : dist (T.pts (τ 0)) (T.pts (τ 1)) = e * (3 * f ^ 2 - e ^ 2)) :
    cornerAngle (T.pts (τ 1)) (T.pts (τ 0)) (T.pts (τ 2)) = modelBeta e f ∧
    cornerAngle (T.pts (τ 2)) (T.pts (τ 1)) (T.pts (τ 0)) = modelBeta e f ∧
    cornerAngle (T.pts (τ 0)) (T.pts (τ 2)) (T.pts (τ 1)) = 3 * modelAlpha e f := by
  have hf : 0 < f := lt_trans he hef
  have hbl : baseLen e f = e * (3 * f ^ 2 - e ^ 2) := by unfold baseLen Nq; rfl
  have hpos := baseLen_pos he hef
  have hb := cos_modelBeta he hef
  have hmb : modelBeta e f ∈ Set.Icc 0 Real.pi := ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩
  have hI : ∀ p q r : Plane, cornerAngle p q r ∈ Set.Icc 0 Real.pi := fun p q r =>
    ⟨EuclideanGeometry.angle_nonneg _ _ _, EuclideanGeometry.angle_le_pi _ _ _⟩
  have hbpos : e * (3 * f ^ 2 - e ^ 2) ≠ 0 := by rw [← hbl]; exact hpos.ne'
  have hf3 : f ^ 3 ≠ 0 := by positivity
  have hK : 3 * f ^ 2 - e ^ 2 ≠ 0 := by nlinarith
  have he0 := he.ne'
  have hf0 := hf.ne'
  have h1' : dist (T.pts (τ 2)) (T.pts (τ 1)) = f ^ 3 := by rw [dist_comm]; exact h1
  have h2' : dist (T.pts (τ 0)) (T.pts (τ 2)) = f ^ 3 := by rw [dist_comm]; exact h2
  have h3' : dist (T.pts (τ 1)) (T.pts (τ 0)) = e * (3 * f ^ 2 - e ^ 2) := by rw [dist_comm]; exact h3
  have hA : cornerAngle (T.pts (τ 1)) (T.pts (τ 0)) (T.pts (τ 2)) = modelBeta e f := by
    apply Real.injOn_cos (hI _ _ _) hmb
    rw [Erdos634.AngleThreshold.cos_of_sides _ _ _ (by rw [h3']; exact hbpos) (by rw [h2]; exact hf3)]
    rw [h3', h2, h1, hb, hbl]
    field_simp
    ring
  have hB : cornerAngle (T.pts (τ 2)) (T.pts (τ 1)) (T.pts (τ 0)) = modelBeta e f := by
    apply Real.injOn_cos (hI _ _ _) hmb
    rw [Erdos634.AngleThreshold.cos_of_sides _ _ _ (by rw [h1']; exact hf3) (by rw [h3]; exact hbpos)]
    rw [h1', h3, h2, hb, hbl, div_eq_div_iff (by simp [hf0, he0, hK]) (by simp [hf0])]
    ring
  refine ⟨hA, hB, ?_⟩
  have hne : T.pts (τ 1) ≠ T.pts (τ 0) := fun h => by
    have := τ.injective (T.indep.injective h)
    exact absurd this (by decide)
  have key := EuclideanGeometry.angle_add_angle_add_angle_eq_pi (V := Plane) (p₁ := T.pts (τ 0)) (p₂ := T.pts (τ 1)) (T.pts (τ 2)) hne
  have hrel := modelAngle_rel e f
  have c1 := EuclideanGeometry.angle_comm (V := Plane) (T.pts (τ 1)) (T.pts (τ 0)) (T.pts (τ 2))
  have c2 := EuclideanGeometry.angle_comm (V := Plane) (T.pts (τ 2)) (T.pts (τ 1)) (T.pts (τ 0))
  have c3 := EuclideanGeometry.angle_comm (V := Plane) (T.pts (τ 0)) (T.pts (τ 2)) (T.pts (τ 1))
  unfold cornerAngle at hA hB ⊢
  linarith [key, hA, hB, hrel, c1, c2, c3]


open Erdos634.BeesonRosu37b1 in
/-- **`thm37_no_a_edges_thick` with the leg angles DERIVED** (gap (3) closed): only the side lengths of the target and the model sides are
hypotheses; the corner angles are `corners_of_dists`.  Witness of the hypotheses: the coordinate triangle `baseBetaTarget` and the tile. -/
theorem thm37_no_a_edges_thick_sides (k m : ℕ) (hm : 1 ≤ m) (hthick : m + 1 = k) (D₀ : CongruentDissection N)
    (hT : HasSides D₀.target ((k : ℝ) ^ 3) ((k : ℝ) ^ 3) ((m : ℝ) * (3 * (k : ℝ) ^ 2 - (m : ℝ) ^ 2)))
    (hMod : HasSides D₀.model ((m : ℝ) * k) ((k : ℝ) ^ 2 - (m : ℝ) ^ 2) ((k : ℝ) ^ 2)) :
    (∃ x y z : ℕ, x = 0 ∧ y = m ∧ z = 2 * m) ∧
    ∃ x y z : ℕ, x = 0 ∧ (x : ℤ) * ((k : ℤ) * m) + y * ((k : ℤ) ^ 2 - (m : ℤ) ^ 2) + z * (k : ℤ) ^ 2 = (k : ℤ) ^ 3 := by
  obtain ⟨τ, h1, h2, h3⟩ := hT
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hmk : (m : ℝ) < k := by rw [← hthick]; push_cast; linarith
  obtain ⟨cA, cB, cC⟩ := corners_of_dists D₀.target hmR hmk τ h1 h2 h3
  refine thm37_no_a_edges_thick k m hm hthick D₀ ⟨τ, h1, h2, h3⟩ hMod ((finRotate 3).symm.trans τ) ?_ ?_ ?_
  · have : (finRotate 3).symm.trans τ 2 = τ 1 := rfl
    have h0 : (finRotate 3).symm.trans τ 0 = τ 2 := rfl
    have h1' : (finRotate 3).symm.trans τ 1 = τ 0 := rfl
    rw [this, h0, h1']
    rw [Erdos634.Geometry.cornerAngle, EuclideanGeometry.angle_comm]
    exact cC
  · have : (finRotate 3).symm.trans τ 2 = τ 1 := rfl
    have h0 : (finRotate 3).symm.trans τ 0 = τ 2 := rfl
    have h1' : (finRotate 3).symm.trans τ 1 = τ 0 := rfl
    rw [this, h0, h1']
    rw [Erdos634.Geometry.cornerAngle, EuclideanGeometry.angle_comm]
    exact cA
  · have h0 : (finRotate 3).symm.trans τ 0 = τ 2 := rfl
    have h1' : (finRotate 3).symm.trans τ 1 = τ 0 := rfl
    rw [h0, h1']; exact h2

end Erdos634.BeesonRosu37c1

#print axioms Erdos634.BeesonRosu37c1.corners_of_dists
#print axioms Erdos634.BeesonRosu37c1.thm37_no_a_edges_thick_sides
