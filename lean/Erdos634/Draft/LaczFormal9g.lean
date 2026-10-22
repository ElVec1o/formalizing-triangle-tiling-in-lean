import Erdos634.Draft.LaczFormal9e

/-!
# Laczkovich, DCG 48 (2012), Theorem 3.4 (ii)

NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012) Thm 2.1, Thm 3.4; Niven, as in Mathlib `Real.niven`), Beeson, Beeson-Zhang.
Formalization debt, not progress on the /goal outcomes.

Printed Thm 3.4 (ii): if `N != 3, 4, 6` and `R_N` has a regular tiling with congruent triangles, then the tile angles are
`alpha = beta = pi/2 - pi/N`, `gamma = 2 pi / N`.

`thm34ii_2012`: `T : PolyTiling N M` whose polygon is regular (all sides equal, all angles equal), `M` not in `{3, 4, 6}`, regular
tiling (any of the three alternatives): the model angles, in some order, are `(pi/2 - pi/M, pi/2 - pi/M, 2 pi / M)`.
Proof (printed): Theorem 2.1 (`RG.theorem21_unconditional`) on the relabelled tiling, then `cos(2 pi / M)` rational (cases (ii),(iii),
via the sine rule) is excluded by Niven, (v) forces `q = 1`, hence `alpha = beta`, (vii) is the conclusion, (i),(iv),(vi),(viii),(ix)
need `M in {3, 4, 6}` or angles `pi/3, 2pi/3`.
-/

open scoped Classical
open Erdos634.Geometry Erdos634.TilePlacement Erdos634.RegionDissection Erdos634.Draft.TheoremPConditional
  Erdos634.Draft.LaczFormal Erdos634.Draft.LaczFormal.Thm21 Erdos634.Draft.LaczFormal.RG

namespace Erdos634.Laczkovich9

theorem cos_gamma_rat (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hsum : x + y + z = Real.pi)
    (c2 : Comm (Real.sin y) (Real.sin z)) (c3 : Comm (Real.sin x) (Real.sin z)) : ∃ r : ℚ, Real.cos z = r := by
  have sz := Real.sin_pos_of_pos_of_lt_pi hz (by linarith)
  have sx := Real.sin_pos_of_pos_of_lt_pi hx (by linarith)
  have sy := Real.sin_pos_of_pos_of_lt_pi hy (by linarith)
  obtain ⟨p, q, hp, hq, e3⟩ := c3
  obtain ⟨p', q', hp', hq', e2⟩ := c2
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hp'R : (0 : ℝ) < p' := by exact_mod_cast hp'
  have hq'R : (0 : ℝ) < q' := by exact_mod_cast hq'
  have hsx : Real.sin x = (q / p : ℝ) * Real.sin z := by field_simp; linarith
  have hsy : Real.sin y = (q' / p' : ℝ) * Real.sin z := by field_simp; linarith
  have key := Erdos634.LaczThm33If.sine_rule_cos z x y (by linarith)
  set ρ : ℝ := q / p with hρ
  set ρ' : ℝ := q' / p' with hρ'
  have hρpos : 0 < ρ := by positivity
  have hρ'pos : 0 < ρ' := by positivity
  rw [hsx, hsy] at key
  have h2 : Real.cos z = (ρ ^ 2 + ρ' ^ 2 - 1) / (2 * ρ * ρ') := by
    field_simp
    have hz2 : 0 < Real.sin z ^ 2 := by positivity
    apply mul_left_cancel₀ hz2.ne'
    linear_combination key
  refine ⟨(((q : ℚ) / p) ^ 2 + ((q' : ℚ) / p') ^ 2 - 1) / (2 * ((q : ℚ) / p) * ((q' : ℚ) / p')), ?_⟩
  rw [h2, hρ, hρ']
  push_cast
  rfl

theorem cos_two_pi_div (M : ℕ) (hM : 3 ≤ M) (hrat : ∃ q : ℚ, Real.cos (2 * Real.pi / M) = q) :
    M = 3 ∨ M = 4 ∨ M = 6 := by
  have hpi := Real.pi_pos
  have hMR : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have hMpos : (0 : ℝ) < M := by linarith
  have hθ : ∃ r : ℚ, 2 * Real.pi / M = r * Real.pi := ⟨2 / M, by push_cast; field_simp⟩
  have hmem := niven hθ hrat
  have hθ0 : 0 ≤ 2 * Real.pi / M := by positivity
  have hθπ : 2 * Real.pi / M ≤ Real.pi := by
    rw [div_le_iff₀ hMpos]; nlinarith
  have hc23 : Real.cos (2 * Real.pi / 3) = -1 / 2 := by
    rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring, Real.cos_pi_sub, Real.cos_pi_div_three]; norm_num
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  rcases hmem with h | h | h | h | h
  · -- cos = -1
    exfalso
    have := Real.injOn_cos ⟨hθ0, hθπ⟩ ⟨hpi.le, le_rfl⟩ (by rw [h, Real.cos_pi])
    field_simp at this
    nlinarith
  · left
    have h3 : (2 * Real.pi / 3) ∈ Set.Icc 0 Real.pi := ⟨by positivity, by linarith⟩
    have := Real.injOn_cos ⟨hθ0, hθπ⟩ h3 (by rw [h, hc23])
    field_simp at this
    have : (M : ℝ) = 3 := by nlinarith
    exact_mod_cast this
  · right; left
    have h3 : (Real.pi / 2) ∈ Set.Icc 0 Real.pi := ⟨by positivity, by linarith⟩
    have := Real.injOn_cos ⟨hθ0, hθπ⟩ h3 (by rw [h, Real.cos_pi_div_two])
    field_simp at this
    have : (M : ℝ) = 4 := by nlinarith
    exact_mod_cast this
  · right; right
    have h3 : (Real.pi / 3) ∈ Set.Icc 0 Real.pi := ⟨by positivity, by linarith⟩
    have := Real.injOn_cos ⟨hθ0, hθπ⟩ h3 (by rw [h, Real.cos_pi_div_three])
    field_simp at this
    have : (M : ℝ) = 6 := by nlinarith
    exact_mod_cast this
  · exfalso
    have := Real.injOn_cos ⟨hθ0, hθπ⟩ ⟨le_rfl, hpi.le⟩ (by rw [h, Real.cos_zero])
    have : 2 * Real.pi / M = 0 := this
    have : 0 < 2 * Real.pi / M := by positivity
    linarith

theorem sin_eq_angle {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (hs : α + β < Real.pi)
    (h : Real.sin α = Real.sin β) : α = β := by
  have hpi := Real.pi_pos
  obtain ⟨k, hk | hk⟩ := Real.sin_eq_sin_iff.mp h
  · -- β = 2 k π + α
    have h1 : (-1 : ℝ) < 2 * k := by nlinarith
    have h2 : (2 * k : ℝ) < 1 := by nlinarith
    have hk0 : k = 0 := by
      have : (-1 : ℤ) < 2 * k := by exact_mod_cast h1
      have : 2 * k < (1 : ℤ) := by exact_mod_cast h2
      omega
    subst hk0
    simpa using hk.symm
  · exfalso
    have h1 : (-1 : ℝ) < 2 * k := by nlinarith
    have h2 : (2 * k : ℝ) < 0 := by nlinarith
    have : (-1 : ℤ) < 2 * k := by exact_mod_cast h1
    have : 2 * k < (0 : ℤ) := by exact_mod_cast h2
    omega

theorem thm34ii_of_sigma {N M : ℕ} [NeZero M] (T : PolyTiling N M) (σ : Equiv.Perm (Fin 3))
    (hM : M ≠ 3 ∧ M ≠ 4 ∧ M ≠ 6)
    (hside : ∀ i, T.P.side i = T.P.side 0) (hang : ∀ i, T.P.angle i = T.P.angle 0)
    (h : ∃ idx : Fin N → Equiv.Perm (Fin 3), (∀ i v, angleAt T.C.model (idx i v) = angleAt (T.C.tile i) v) ∧
      ∀ X, cntR T.C idx X (σ 0) = cntR T.C idx X (σ 1)) :
    angleAt (relabel T.C σ).model 0 = Real.pi / 2 - Real.pi / M ∧ angleAt (relabel T.C σ).model 1 = Real.pi / 2 - Real.pi / M ∧
      angleAt (relabel T.C σ).model 2 = 2 * Real.pi / M := by
  have hreg := regular_relabel T.C σ h
  let T' : PolyTiling N M := ⟨relabel T.C σ, T.P, T.region_eq⟩
  have hc : Thm21Concl T'.C T'.P := theorem21_unconditional N M T' hreg
  have hpi := Real.pi_pos
  have hM3 : 3 ≤ M := T.P.three_le
  have hMR : (3 : ℝ) ≤ M := by exact_mod_cast hM3
  have hMpos : (0 : ℝ) < M := by linarith
  -- the common polygon angle
  have hsum := poly_angle_sum T.P
  have hconst : ∑ i : Fin M, T.P.angle i = M * T.P.angle 0 := by
    rw [Finset.sum_congr rfl (fun i _ => hang i)]; simp
  have hcast : (((M - 2 : ℕ) : ℝ)) = (M : ℝ) - 2 := by
    rw [Nat.cast_sub (by omega)]; norm_num
  have ha0 : T.P.angle 0 = Real.pi - 2 * Real.pi / M := by
    rw [hconst, hcast] at hsum
    field_simp
    nlinarith [hsum]
  have hsumT : angleAt T'.C.model 0 + angleAt T'.C.model 1 + angleAt T'.C.model 2 = Real.pi :=
    T'.C.model.angleAt_sum
  have hp0 : 0 < angleAt T'.C.model 0 := Erdos634.MarchFlank.cornerAngle_pos T'.C.model 0
  have hp1 : 0 < angleAt T'.C.model 1 := Erdos634.MarchFlank.cornerAngle_pos T'.C.model 1
  have hp2 : 0 < angleAt T'.C.model 2 := Erdos634.MarchFlank.cornerAngle_pos T'.C.model 2
  have notrat : ∀ θ : ℝ, θ = 2 * Real.pi / M → (∃ r : ℚ, Real.cos θ = r) → False := by
    intro θ hθ hr
    rw [hθ] at hr
    rcases cos_two_pi_div M hM3 hr with h3 | h4 | h6
    · exact hM.1 h3
    · exact hM.2.1 h4
    · exact hM.2.2 h6
  have exk : ∀ i j : Fin M, ∃ k : Fin M, k ≠ i ∧ k ≠ j := by
    intro i j
    by_contra hcon
    push Not at hcon
    have : (Finset.univ : Finset (Fin M)) ⊆ {i, j} := by
      intro k _
      by_cases hki : k = i
      · simp [hki]
      · simp [hcon k hki]
    have hc2 := Finset.card_le_card this
    have : (Finset.univ : Finset (Fin M)).card = M := by simp
    have h2 : ({i, j} : Finset (Fin M)).card ≤ 2 := Finset.card_le_two
    omega
  rcases hc with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9
  · exact absurd h1.1.1 hM.2.1
  · exfalso
    obtain ⟨-, ⟨i, j, hij, hk, -⟩, hsin⟩ := h2
    obtain ⟨k, hki, hkj⟩ := exk i j
    have hγ : angleAt T'.C.model 2 = Real.pi - 2 * Real.pi / M := by rw [← ha0, ← hang k]; exact (hk k hki hkj).symm
    obtain ⟨r, hr⟩ := cos_gamma_rat _ _ _ hp0 hp1 hp2 hsumT hsin.2.1 hsin.2.2
    apply notrat (2 * Real.pi / M) rfl
    refine ⟨-r, ?_⟩
    have : Real.cos (2 * Real.pi / M) = -Real.cos (angleAt T'.C.model 2) := by
      rw [hγ, Real.cos_pi_sub]; ring
    rw [this, hr]; push_cast; ring
  · exfalso
    obtain ⟨-, ⟨i, j, hij, hk, -⟩, hsin⟩ := h3
    obtain ⟨k, hki, hkj⟩ := exk i j
    have hab : angleAt T'.C.model 0 + angleAt T'.C.model 1 = Real.pi - 2 * Real.pi / M := by
      rw [← ha0, ← hang k]; exact (hk k hki hkj).symm
    have hγ : angleAt T'.C.model 2 = 2 * Real.pi / M := by linarith
    obtain ⟨r, hr⟩ := cos_gamma_rat _ _ _ hp0 hp1 hp2 hsumT hsin.2.1 hsin.2.2
    exact notrat _ hγ ⟨r, hr⟩
  · exact absurd h4.1 hM.1
  · obtain ⟨k, hMk, hk4, -, hang5, hs5, q, hq, s, rev, a, ha, hgeo, -⟩ := h5
    have hq1 : q = 1 := by
      have g0 := hgeo 0 (by omega)
      have a0 := ha 0
      have a1 := ha 1
      have e0 : a 0 = T.P.side 0 := by
        rw [a0]; split_ifs
        · exact hside _
        · exact hside _
      have e1 : a (0 + 1) = T.P.side 0 := by
        rw [ha (0 + 1)]; split_ifs
        · exact hside _
        · exact hside _
      rw [e1, e0] at g0
      have hs0 := side_pos T.P 0
      have : (q - 1) * T.P.side 0 = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · linarith
      · exact absurd h hs0.ne'
    have hsin : Real.sin (angleAt T'.C.model 0) = Real.sin (angleAt T'.C.model 1) := by
      have hs0 := sin_angleAt_pos T'.C.model 0
      have hs1 := sin_angleAt_pos T'.C.model 1
      rcases hq with hq | hq
      · rw [hq1] at hq; field_simp at hq; linarith
      · rw [hq1] at hq; field_simp at hq; linarith
    have hab : angleAt T'.C.model 0 = angleAt T'.C.model 1 :=
      sin_eq_angle hp0 hp1 (by linarith) hsin
    have hsum5 : angleAt T'.C.model 0 + angleAt T'.C.model 1 = Real.pi - 2 * Real.pi / M := by
      rw [← ha0, ← hang 0]; exact (hang5 0).symm
    have e : 2 * Real.pi / M = 2 * (Real.pi / M) := by ring
    refine ⟨?_, ?_, ?_⟩
    · show angleAt T'.C.model 0 = _
      linarith
    · show angleAt T'.C.model 1 = _
      linarith
    · show angleAt T'.C.model 2 = _
      linarith
  · exact absurd h6.1 hM.2.2
  · exact ⟨h7.2.2.2.1, h7.2.2.1 ▸ h7.2.2.2.1, h7.2.2.2.2⟩
  · exfalso
    have hA := h8.2.2.1 0
    rw [← hang 0, ha0] at hA
    rcases hA with e | e
    · have e2 : 2 * Real.pi / M = 2 * Real.pi / 3 := by linarith
      have := (div_eq_div_iff hMpos.ne' (by norm_num)).mp e2
      have : (M : ℝ) = 3 := by nlinarith
      exact hM.1 (by exact_mod_cast this)
    · have e2 : 2 * Real.pi / M = Real.pi / 3 := by linarith
      have := (div_eq_div_iff hMpos.ne' (by norm_num)).mp e2
      have : (M : ℝ) = 6 := by nlinarith
      exact hM.2.2 (by exact_mod_cast this)
  · exact absurd h9.1 hM.2.2

/-- **Laczkovich DCG 48 (2012), Theorem 3.4 (ii).** -/
theorem thm34ii_2012 {N M : ℕ} [NeZero M] (T : PolyTiling N M)
    (hM : M ≠ 3 ∧ M ≠ 4 ∧ M ≠ 6)
    (hside : ∀ i, T.P.side i = T.P.side 0) (hang : ∀ i, T.P.angle i = T.P.angle 0)
    (h : ∃ idx : Fin N → Equiv.Perm (Fin 3), (∀ i v, angleAt T.C.model (idx i v) = angleAt (T.C.tile i) v) ∧
      ((∀ X, cntR T.C idx X 0 = cntR T.C idx X 1) ∨ (∀ X, cntR T.C idx X 0 = cntR T.C idx X 2) ∨
        (∀ X, cntR T.C idx X 1 = cntR T.C idx X 2))) :
    ∃ σ : Equiv.Perm (Fin 3), angleAt T.C.model (σ 0) = Real.pi / 2 - Real.pi / M ∧
      angleAt T.C.model (σ 1) = Real.pi / 2 - Real.pi / M ∧ angleAt T.C.model (σ 2) = 2 * Real.pi / M := by
  have key : ∀ σ : Equiv.Perm (Fin 3), (∃ idx : Fin N → Equiv.Perm (Fin 3),
      (∀ i v, angleAt T.C.model (idx i v) = angleAt (T.C.tile i) v) ∧
      ∀ X, cntR T.C idx X (σ 0) = cntR T.C idx X (σ 1)) →
      ∃ σ : Equiv.Perm (Fin 3), angleAt T.C.model (σ 0) = Real.pi / 2 - Real.pi / M ∧
      angleAt T.C.model (σ 1) = Real.pi / 2 - Real.pi / M ∧ angleAt T.C.model (σ 2) = 2 * Real.pi / M := by
    intro σ hσ
    obtain ⟨e0, e1, e2⟩ := thm34ii_of_sigma T σ hM hside hang hσ
    rw [relabel_angleAt] at e0 e1 e2
    exact ⟨σ, e0, e1, e2⟩
  obtain ⟨idx, hA, h01 | h02 | h12⟩ := h
  · exact key 1 ⟨idx, hA, fun X => h01 X⟩
  · exact key (Equiv.swap 1 2) ⟨idx, hA, fun X => by simpa using h02 X⟩
  · exact key (Equiv.swap 0 2) ⟨idx, hA, fun X => by simpa using (h12 X).symm⟩

#print axioms Erdos634.Laczkovich9.cos_gamma_rat
#print axioms Erdos634.Laczkovich9.cos_two_pi_div
#print axioms Erdos634.Laczkovich9.sin_eq_angle
#print axioms Erdos634.Laczkovich9.thm34ii_2012
