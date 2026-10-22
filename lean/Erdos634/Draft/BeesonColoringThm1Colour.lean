import Erdos634.Draft.BeesonColoringLemma12
import Erdos634.Draft.BeesonColoringThm1

/-!
# Beeson (arXiv 1206.2229v4) Lemma 12 + Theorem 1: the flux integer `M` IS blacks minus whites

NOTE, UNAUDITED.  Credit: Michael Beeson (arXiv 1206.2229 v4, Lemma 12, Thm 1), Laczkovich (DCG 48 (2012)), Beeson-Zhang.
Formalization debt, not progress on the /goal outcomes.

For the five shapes of `Beeson.thm1` and the project hypothesis (H1) `alpha not in Q * pi` (replacing Beeson's Lemma 1):
there is a proper 2-colouring `eps` of the tiles (`Dissection.ProperColouring`, Beeson Lemma 12: adjacent tiles, i.e. tiles
with a common boundary segment of positive length inside an edge of each, have opposite colours) whose count
`M = #black - #white` is positive and satisfies Beeson's coloring equation `M (a + b + c) = X +- Y + Z` (same right
hand sides as `Beeson.thm1`).  The colour is the sign of the `Phi_1`-value of the tile (`chiMinus`).

Differences from the printed statement, all named:
* the printed proof of Lemma 12 (path parity) is not reproduced; the route is the direction character
  (`BeesonColoringLemma12`);
* uniqueness of the colouring up to swapping colours (connectivity of the adjacency graph) is NOT proved, so Beeson's
  normalisation "the tile at B with an edge on AB is black" is replaced by `M > 0`;  since `M (a+b+c) = RHS > 0`
  determines `M`, any proper colouring with `#black - #white > 0` that satisfies the equation has this `M`;
* the positivity `RHS > 0` is taken from `Beeson.thm1`.
-/

open scoped Classical

namespace Erdos634.BeesonColoring

open Erdos634.Geometry

variable {N : ℕ}

/-- The parity sign `(-1)^(p - q)` of the direction character `chiMinus` on `p alpha + q beta`. -/
noncomputable def sg (p q : ℤ) : ℝ := if ((p - q : ℤ) : ZMod 2) = 0 then 1 else -1

theorem sg_10 : sg 1 0 = -1 := by unfold sg; rw [if_neg (by decide)]
theorem sg_12 : sg 1 2 = -1 := by unfold sg; rw [if_neg (by decide)]
theorem sg_01 : sg 0 1 = -1 := by unfold sg; rw [if_neg (by decide)]
theorem sg_30 : sg 3 0 = -1 := by unfold sg; rw [if_neg (by decide)]
theorem sg_11 : sg 1 1 = 1 := by unfold sg; rw [if_pos (by decide)]
theorem sg_20 : sg 2 0 = 1 := by unfold sg; rw [if_pos (by decide)]
theorem sg_02 : sg 0 2 = 1 := by unfold sg; rw [if_pos (by decide)]

/-- All exterior-angle values of the model are `1` for `chiMinus` (Beeson Lemma 21: `eps` is constant on a tile). -/
theorem model_hext (T : Tri) {α β a b c : ℝ} (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (h : T.ThreeAlphaData α β a b c) (hrel : 3 * α + 2 * β = Real.pi) :
    ∀ k, (chiAt α hα 1 0).chi ((Real.pi - T.angleAt k : ℝ) : Real.Angle) = 1 := by
  obtain ⟨σ, h0, -, h1, -, h2, -⟩ := h
  intro k
  obtain ⟨m, rfl⟩ := σ.surjective k
  have hk : m = 0 ∨ m = 1 ∨ m = 2 := by fin_cases m <;> simp
  rcases hk with rfl | rfl | rfl
  · rw [h0, show Real.pi - α = ((2 : ℤ) : ℝ) * Real.pi + ((-2 : ℤ) : ℝ) * (α / 2 + Real.pi / 2) by
      push_cast; ring, chiAt_chi, if_pos (by decide)]
  · rw [h1, show Real.pi - β = ((-1 : ℤ) : ℝ) * Real.pi + ((3 : ℤ) : ℝ) * (α / 2 + Real.pi / 2) by
      push_cast; linarith, chiAt_chi, if_pos (by decide)]
  · rw [h2, show Real.pi - (2 * α + β) = ((1 : ℤ) : ℝ) * Real.pi + ((-1 : ℤ) : ℝ) * (α / 2 + Real.pi / 2) by
      push_cast; linarith, chiAt_chi, if_pos (by decide)]

/-- **Generic boundary identity with a proper colouring.**  Target angles `p_V alpha + q_V beta`: a proper colouring
`eps` with `(sum eps)(a+b+c) = e * (sg_0 X_0 + sg_1 X_1 + sg_2 X_2)`, `e = +-1`. -/
theorem boundary_gen (D : CongruentDissection N) {α β a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hrel : 3 * α + 2 * β = Real.pi)
    (h : D.model.ThreeAlphaData α β a b c) (p0 q0 p1 q1 p2 q2 : ℤ)
    (h0 : D.target.angleAt 0 = (p0 : ℝ) * α + (q0 : ℝ) * β)
    (h1 : D.target.angleAt 1 = (p1 : ℝ) * α + (q1 : ℝ) * β)
    (h2 : D.target.angleAt 2 = (p2 : ℝ) * α + (q2 : ℝ) * β) :
    ∃ ε : Fin N → ℤ, D.toDissection.ProperColouring ε ∧ ∃ e : ℝ, (e = 1 ∨ e = -1) ∧
      ((∑ i, ε i : ℤ) : ℝ) * (a + b + c) =
        e * (sg p0 q0 * D.target.oppLen 0 + sg p1 q1 * D.target.oppLen 1 + sg p2 q2 * D.target.oppLen 2) := by
  have hmodel : ∀ k, ((D.model.angleAt k : ℝ) : Real.Angle) ∈ (chiAt α hα 1 0).L :=
    D.model.threeAlpha_angles_mem hα hrel h 1
  obtain ⟨ε, hε, -, hS⟩ := D.flux_colouring (chiAt α hα 1 0) (chiAt_sq _ _ _ _) hmodel
    (model_hext D.model hα h hrel)
  have hK : (chiAt α hα 1 0).tileValue D.model = a + b + c :=
    threeAlpha_tileValue_minus D.model hα hrel h
  have hβ : β = (Real.pi - 3 * α) / 2 := by linarith
  have hrep : ∀ p q : ℤ, (p : ℝ) * α + (q : ℝ) * β
      = ((2 * q - p : ℤ) : ℝ) * Real.pi + ((2 * p - 3 * q : ℤ) : ℝ) * (α / 2 + Real.pi / 2) := by
    intro p q; rw [hβ]; push_cast; ring
  have hchi : ∀ p q : ℤ, (chiAt α hα 1 0).chi (((p : ℝ) * α + (q : ℝ) * β : ℝ) : Real.Angle)
      = sg p q := by
    intro p q
    rw [hrep, chiAt_chi]
    unfold sg
    have : ((2 * q - p : ℤ) : ZMod 2) + 1 * ((2 * p - 3 * q : ℤ) : ZMod 2) = ((p - q : ℤ) : ZMod 2) := by
      push_cast; ring
    rw [this]
  have htarget : ∀ k, ((D.target.angleAt k : ℝ) : Real.Angle) ∈ (chiAt α hα 1 0).L := by
    intro k
    fin_cases k
    · show ((D.target.angleAt 0 : ℝ) : Real.Angle) ∈ _
      rw [h0, hrep]; exact chiAt_mem _ _ _ _ _ _
    · show ((D.target.angleAt 1 : ℝ) : Real.Angle) ∈ _
      rw [h1, hrep]; exact chiAt_mem _ _ _ _ _ _
    · show ((D.target.angleAt 2 : ℝ) : Real.Angle) ∈ _
      rw [h2, hrep]; exact chiAt_mem _ _ _ _ _ _
  have hPK : (chiAt α hα 1 0).paperK D.target
      = -(sg p0 q0 * D.target.oppLen 0 + sg p1 q1 * D.target.oppLen 1 + sg p2 q2 * D.target.oppLen 2) := by
    unfold GridChar.paperK
    rw [Fin.sum_univ_three, h0, h1, h2, hchi, hchi, hchi]
  have hfl := D.target.flux_eq_edgeSign (chiAt α hα 1 0) (chiAt_sq _ _ _ _) htarget 0
  rw [← GridChar.tileValue_eq_paperK _ (chiAt_sq _ _ _ _) _ htarget] at hPK
  have hsq := (chiAt α hα 1 0).edgeSign_sq (chiAt_sq _ _ _ _) D.target htarget 0
  refine ⟨ε, hε, -(chiAt α hα 1 0).edgeSign D.target 0, ?_, ?_⟩
  · rcases mul_self_eq_one_iff.mp hsq with h' | h'
    · right; rw [h']
    · left; rw [h']; norm_num
  · rw [← hK, ← hS, hfl, hPK]; ring

/-- Blacks minus whites of a `+-1` colouring is the sum. -/
theorem sum_eq_black_sub_white (ε : Fin N → ℤ) (hε : ∀ i, ε i = 1 ∨ ε i = -1) :
    ∑ i, ε i = ((Finset.univ.filter fun i => ε i = 1).card : ℤ)
      - ((Finset.univ.filter fun i => ε i = -1).card : ℤ) := by
  rw [Finset.card_filter, Finset.card_filter]
  push_cast
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rcases hε i with h | h <;> rw [h] <;> norm_num

/-- Normalise the sign of a proper colouring so that `M = sum eps > 0`. -/
theorem finish {D : Dissection N} {ε : Fin N → ℤ} (hε : D.ProperColouring ε) {e R s : ℝ}
    (he : e = 1 ∨ e = -1) (hS : ((∑ i, ε i : ℤ) : ℝ) * s = e * R) (hs : 0 < s) (hR : 0 < R) :
    ∃ ε' : Fin N → ℤ, D.ProperColouring ε' ∧ ∃ M : ℤ,
      M = ((Finset.univ.filter fun i => ε' i = 1).card : ℤ)
          - ((Finset.univ.filter fun i => ε' i = -1).card : ℤ) ∧ 0 < M ∧ (M : ℝ) * s = R := by
  push_cast at hS
  rcases he with rfl | rfl
  · refine ⟨ε, hε, ∑ i, ε i, sum_eq_black_sub_white ε hε.1, pos_M hs hR (by push_cast; linarith), by push_cast; linarith⟩
  · have hε' : D.ProperColouring (fun i => - ε i) := by
      refine ⟨fun i => ?_, fun i j hij => ?_⟩
      · rcases hε.1 i with h | h <;> simp [h]
      · have := hε.2 i j hij; simp only; omega
    refine ⟨fun i => - ε i, hε', ∑ i, (- ε i), sum_eq_black_sub_white _ hε'.1, ?_, ?_⟩
    · refine pos_M hs hR ?_
      rw [Finset.sum_neg_distrib]; push_cast; linarith
    · rw [Finset.sum_neg_distrib]; push_cast; linarith

/-- **Beeson Lemma 12 + Theorem 1 (coloring equation), the five shapes.**  UNAUDITED; (H1) `alpha not in Q pi`.
Same shapes and right hand sides as `Beeson.thm1`; the integer `M` is blacks minus whites of a proper 2-colouring. -/
theorem thm1_colouring (D : CongruentDissection N) {α β a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hrel : 3 * α + 2 * β = Real.pi)
    (h : D.model.ThreeAlphaData α β a b c) :
    (let P : ℝ → Prop := fun R => ∃ ε' : Fin N → ℤ, D.toDissection.ProperColouring ε' ∧
        ∃ M : ℤ, M = ((Finset.univ.filter fun i => ε' i = 1).card : ℤ)
          - ((Finset.univ.filter fun i => ε' i = -1).card : ℤ) ∧ 0 < M ∧ (M : ℝ) * (a + b + c) = R
     ((D.target.angleAt 0 = α ∧ D.target.angleAt 1 = α ∧ D.target.angleAt 2 = α + 2 * β) →
        P (D.target.oppLen 0 + D.target.oppLen 1 + D.target.oppLen 2)) ∧
     ((D.target.angleAt 0 = β ∧ D.target.angleAt 1 = β ∧ D.target.angleAt 2 = 3 * α) →
        P (D.target.oppLen 0 + D.target.oppLen 1 + D.target.oppLen 2)) ∧
     ((D.target.angleAt 0 = α + β ∧ D.target.angleAt 1 = α + β ∧ D.target.angleAt 2 = α) →
        P (D.target.oppLen 0 + D.target.oppLen 1 - D.target.oppLen 2)) ∧
     ((D.target.angleAt 0 = 2 * α ∧ D.target.angleAt 1 = α ∧ D.target.angleAt 2 = 2 * β) →
        P (D.target.oppLen 0 - D.target.oppLen 1 + D.target.oppLen 2)) ∧
     ((D.target.angleAt 0 = 2 * α ∧ D.target.angleAt 1 = β ∧ D.target.angleAt 2 = α + β) →
        P (D.target.oppLen 0 - D.target.oppLen 1 + D.target.oppLen 2))) := by
  obtain ⟨ha0, hb0, hc0, hαpos, hβpos⟩ := model_abc_pos h
  have hsum : 0 < a + b + c := by linarith
  obtain ⟨t1, t2, t3, t4, t5⟩ := thm1 D hα hrel h
  have pos_of : ∀ {M : ℤ} {R : ℝ}, 0 < M → (M : ℝ) * (a + b + c) = R → 0 < R := by
    intro M R hM hR
    rw [← hR]; exact mul_pos (by exact_mod_cast hM) hsum
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro hh
    obtain ⟨e0, e1, e2⟩ := hh
    obtain ⟨M0, hM0, hM0e⟩ := t1 ⟨e0, e1, e2⟩
    obtain ⟨ε, hε, e, he, hS⟩ := boundary_gen D hα hrel h 1 0 1 0 1 2
      (by rw [e0]; push_cast; ring) (by rw [e1]; push_cast; ring) (by rw [e2]; push_cast; ring)
    rw [sg_10, sg_12] at hS
    refine finish hε (e := -e) (by rcases he with h | h <;> rw [h] <;> norm_num) ?_ hsum
      (pos_of hM0 hM0e)
    rw [hS]; ring
  · intro hh
    obtain ⟨e0, e1, e2⟩ := hh
    obtain ⟨M0, hM0, hM0e⟩ := t2 ⟨e0, e1, e2⟩
    obtain ⟨ε, hε, e, he, hS⟩ := boundary_gen D hα hrel h 0 1 0 1 3 0
      (by rw [e0]; push_cast; ring) (by rw [e1]; push_cast; ring) (by rw [e2]; push_cast; ring)
    rw [sg_01, sg_30] at hS
    refine finish hε (e := -e) (by rcases he with h | h <;> rw [h] <;> norm_num) ?_ hsum
      (pos_of hM0 hM0e)
    rw [hS]; ring
  · intro hh
    obtain ⟨e0, e1, e2⟩ := hh
    obtain ⟨M0, hM0, hM0e⟩ := t3 ⟨e0, e1, e2⟩
    obtain ⟨ε, hε, e, he, hS⟩ := boundary_gen D hα hrel h 1 1 1 1 1 0
      (by rw [e0]; push_cast; ring) (by rw [e1]; push_cast; ring) (by rw [e2]; push_cast; ring)
    rw [sg_11, sg_10] at hS
    refine finish hε (e := e) he ?_ hsum (pos_of hM0 hM0e)
    rw [hS]; ring
  · intro hh
    obtain ⟨e0, e1, e2⟩ := hh
    obtain ⟨M0, hM0, hM0e⟩ := t4 ⟨e0, e1, e2⟩
    obtain ⟨ε, hε, e, he, hS⟩ := boundary_gen D hα hrel h 2 0 1 0 0 2
      (by rw [e0]; push_cast; ring) (by rw [e1]; push_cast; ring) (by rw [e2]; push_cast; ring)
    rw [sg_20, sg_10, sg_02] at hS
    refine finish hε (e := e) he ?_ hsum (pos_of hM0 hM0e)
    rw [hS]; ring
  · intro hh
    obtain ⟨e0, e1, e2⟩ := hh
    obtain ⟨M0, hM0, hM0e⟩ := t5 ⟨e0, e1, e2⟩
    obtain ⟨ε, hε, e, he, hS⟩ := boundary_gen D hα hrel h 2 0 0 1 1 1
      (by rw [e0]; push_cast; ring) (by rw [e1]; push_cast; ring) (by rw [e2]; push_cast; ring)
    rw [sg_20, sg_01, sg_11] at hS
    refine finish hε (e := e) he ?_ hsum (pos_of hM0 hM0e)
    rw [hS]; ring

end Erdos634.BeesonColoring

#print axioms Erdos634.BeesonColoring.boundary_gen
#print axioms Erdos634.BeesonColoring.thm1_colouring
