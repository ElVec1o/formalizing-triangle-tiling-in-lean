-- Draft/LaczFormalRGCaseVc2.lean -- Case V, subcase Vc of Laczkovich's Theorem 2.1: `a, b` commensurable.  (1) if also `c` is a rational multiple of `a`, all sides of the
-- rectangle are rational multiples of `a`; (2) otherwise (c not a rational multiple of a) each side is `m c` or a combination of `a, b`, and the area equation `t a b = 2 s_1 s_2`
-- rules out one side of each kind.  In both cases the ratio of the sides is a rational multiple of `sin α / sin β = a / b`.
-- UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 9.1 end, Lemma 4.7), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalRGCaseVc1

open scoped Classical
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N : ℕ}

/-- The area equation of a tiled parallelogram, in polygon form: `t · a b = 2 s_0 s_3`. -/
theorem poly4_area {N : ℕ} (T : PolyTiling N 4) (hpg : T.P.v 0 + T.P.v 2 = T.P.v 1 + T.P.v 3)
    (hang : T.P.angle 0 = angleAt T.C.model 2 ∨ T.P.angle 0 = Real.pi - angleAt T.C.model 2) :
    (N : ℝ) * (sideOpp T.C.model 0 * sideOpp T.C.model 1) = 2 * (T.P.side 0 * T.P.side 3) := by
  have hreg : T.C.region = pgramSet (T.P.v 0) (T.P.v 1 - T.P.v 0) (T.P.v 3 - T.P.v 0) := by
    rw [T.region_eq]; exact poly4_carrier T.P hpg
  have h0 : ‖T.P.v 1 - T.P.v 0‖ = T.P.side 0 := by
    rw [← dist_eq_norm, ConvPoly.side, dist_comm]; rfl
  have h3 : ‖T.P.v 3 - T.P.v 0‖ = T.P.side 3 := by
    rw [← dist_eq_norm, ConvPoly.side]; rfl
  have hA : T.P.angle 0 = InnerProductGeometry.angle (T.P.v 1 - T.P.v 0) (T.P.v 3 - T.P.v 0) := by
    rw [InnerProductGeometry.angle_comm]; rfl
  have hsin : Real.sin (InnerProductGeometry.angle (T.P.v 1 - T.P.v 0) (T.P.v 3 - T.P.v 0)) = Real.sin (angleAt T.C.model 2) := by
    rw [← hA]; rcases hang with h | h
    · rw [h]
    · rw [h, Real.sin_pi_sub]
  have := pgram_area_eq T.C _ _ _ hreg hsin
  rwa [h0, h3] at this

/-- Assemble conclusion (i) from a rectangle and a ratio statement. -/
theorem concl1_of_rect {N : ℕ} (T : PolyTiling N 4) (hang : ∀ i, T.P.angle i = Real.pi / 2) (hγ : angleAt T.C.model 2 = Real.pi / 2)
    (hratio : ∃ q : ℚ, T.P.side 0 / T.P.side 3 = q * (Real.sin (angleAt T.C.model 0) / Real.sin (angleAt T.C.model 1))) : Concl1 T.C T.P := by
  have hrect := rect_of_angles T.P hang
  obtain ⟨hs2, hs1⟩ := side_rect T.P hrect
  refine ⟨⟨rfl, fun i => ?_⟩, ⟨0, by rw [hang 0, hγ]⟩, Or.inl ?_⟩
  · fin_cases i
    · exact hrect
    · show T.P.v 1 + T.P.v (1 + 2) = T.P.v (1 + 1) + T.P.v (1 + 3)
      have e1 : (1 : Fin 4) + 2 = 3 := by decide
      have e2 : (1 : Fin 4) + 1 = 2 := by decide
      have e3 : (1 : Fin 4) + 3 = 0 := by decide
      rw [e1, e2, e3]; exact hrect.symm.trans (add_comm _ _)
    · show T.P.v 2 + T.P.v (2 + 2) = T.P.v (2 + 1) + T.P.v (2 + 3)
      have e1 : (2 : Fin 4) + 2 = 0 := by decide
      have e2 : (2 : Fin 4) + 1 = 3 := by decide
      have e3 : (2 : Fin 4) + 3 = 1 := by decide
      rw [e1, e2, e3]; exact (add_comm _ _).trans (hrect.trans (add_comm _ _))
    · show T.P.v 3 + T.P.v (3 + 2) = T.P.v (3 + 1) + T.P.v (3 + 3)
      have e1 : (3 : Fin 4) + 2 = 1 := by decide
      have e2 : (3 : Fin 4) + 1 = 0 := by decide
      have e3 : (3 : Fin 4) + 3 = 2 := by decide
      rw [e1, e2, e3]; exact (add_comm _ _).trans hrect.symm
  · obtain ⟨q, hq⟩ := hratio
    exact ⟨q, by rw [hs1]; exact hq⟩

/-- Ratio of two sides, both rational multiples of `a`, and `a / b` rational. -/
theorem ratio_of_rat {x y a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hy : 0 < y) {r r' : ℚ} (hx : x = r * a) (hy' : y = r' * a)
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hab : (m : ℝ) * a = n * b) {s t : ℝ} (hst : s / t = a / b) (ht : 0 < t) (hs : 0 < s) :
    ∃ q : ℚ, x / y = q * (s / t) := by
  have hr' : (r' : ℝ) ≠ 0 := by
    intro h0; rw [h0, zero_mul] at hy'; linarith
  refine ⟨r / r' * m / n, ?_⟩
  rw [hst, hx, hy']
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hab' : a / b = n / m := by
    rw [div_eq_div_iff hb.ne' hm']; linarith
  rw [hab']
  push_cast
  field_simp

/-- Common set-up for Case V: the vertex correspondence and the four right angles. -/
theorem caseV_setup {N : ℕ} (T : PolyTiling N 4) (hreg : RegularPQ T.C) (hγ : angleAt T.C.model 2 = Real.pi / 2) :
    ∃ idx : Fin N → Equiv.Perm (Fin 3), (∀ i v, angleAt T.C.model (idx i v) = angleAt (T.C.tile i) v) ∧
      (∀ X, cnt T.C idx X 0 = cnt T.C idx X 1) ∧
      (∀ i k k', dist ((T.C.tile i).pts k) ((T.C.tile i).pts k') = dist (T.C.model.pts (idx i k)) (T.C.model.pts (idx i k'))) ∧
      (∀ i : Fin 4, T.P.angle i = Real.pi / 2) := by
  obtain ⟨idx, hA, hcnt⟩ := hreg
  haveI : HasFansC T.C.toRegionDissection := hasFansC_poly _ T.P T.region_eq
  refine ⟨idx, hA, fun X => hcnt X, idx_dist_of_angle T.C idx hA, fun i => ?_⟩
  have := polygon_angle_pi2 T.C idx hA hγ (fun X => hcnt X) T.P T.region_eq (i - 1)
  rwa [sub_add_cancel] at this

/-- **Case V, Vc, first sub-branch:** `a, b, c` pairwise commensurable. -/
theorem caseV_Vc_comm {N : ℕ} (T : PolyTiling N 4) (hreg : RegularPQ T.C) (hγ : angleAt T.C.model 2 = Real.pi / 2)
    {m n m' n' : ℕ} (hm : 0 < m) (hn : 0 < n) (hm' : 0 < m') (hn' : 0 < n')
    (hab : (m : ℝ) * slen T.C 0 = n * slen T.C 1) (hca : (m' : ℝ) * slen T.C 2 = n' * slen T.C 0) : Concl1 T.C T.P := by
  obtain ⟨idx, hA, hcnt, hidx, hang⟩ := caseV_setup T hreg hγ
  haveI : HasFansC T.C.toRegionDissection := hasFansC_poly _ T.P T.region_eq
  have ha := slen_pos T.C 0
  have hb := slen_pos T.C 1
  have hc := slen_pos T.C 2
  -- every side is a positive rational multiple of a
  have hside : ∀ i : Fin 4, ∃ r : ℚ, 0 < r ∧ T.P.side i = r * slen T.C 0 := by
    intro i
    obtain ⟨na, nb, nc, hpos, hs⟩ := edge_decomp T.C idx hidx T.P T.region_eq i
    have hbq : slen T.C 1 = (m / n : ℚ) * slen T.C 0 := by
      push_cast
      have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      field_simp; linarith
    have hcq : slen T.C 2 = (n' / m' : ℚ) * slen T.C 0 := by
      push_cast
      have hm0 : (m' : ℝ) ≠ 0 := by exact_mod_cast hm'.ne'
      field_simp; linarith
    refine ⟨na + nb * (m / n) + nc * (n' / m'), ?_, ?_⟩
    · have h1 : (0 : ℚ) ≤ na := Nat.cast_nonneg _
      have h2 : (0 : ℚ) ≤ nb * (m / n) := by positivity
      have h3 : (0 : ℚ) ≤ nc * (n' / m') := by positivity
      rcases Nat.eq_zero_or_pos na with h | h
      · rcases Nat.eq_zero_or_pos nb with h' | h'
        · have hnc : 0 < nc := by omega
          have : (0 : ℚ) < nc * (n' / m') := by positivity
          linarith
        · have : (0 : ℚ) < nb * (m / n) := by positivity
          linarith
      · have : (0 : ℚ) < na := by exact_mod_cast h
        linarith
    · rw [hs]; push_cast; rw [hbq, hcq]; push_cast; ring
  obtain ⟨r0, hr0, h0⟩ := hside 0
  obtain ⟨r3, hr3, h3⟩ := hside 3
  have hsin := side_ratio_eq_sin T.C.model
  refine concl1_of_rect T hang hγ ?_
  have := ratio_of_rat (x := T.P.side 0) (y := T.P.side 3) (a := slen T.C 0) (b := slen T.C 1) ha hb (side_pos T.P 3) h0 h3 hm hn hab
    (s := Real.sin (angleAt T.C.model 0)) (t := Real.sin (angleAt T.C.model 1)) hsin.symm
    (Erdos634.Draft.LaczFormal.Thm21.sin_angleAt_pos T.C.model 1) (Erdos634.Draft.LaczFormal.Thm21.sin_angleAt_pos T.C.model 0)
  exact this

theorem ratio_of_rat_g {x y a b g : ℝ} (ha : 0 < a) (hb : 0 < b) (hg : g ≠ 0) (hy : 0 < y) {r r' : ℚ} (hx : x = r * g) (hy' : y = r' * g)
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hab : (m : ℝ) * a = n * b) {s t : ℝ} (hst : s / t = a / b) :
    ∃ q : ℚ, x / y = q * (s / t) := by
  have hr' : (r' : ℝ) ≠ 0 := by
    intro h0; rw [h0, zero_mul] at hy'; linarith
  refine ⟨r / r' * m / n, ?_⟩
  rw [hst, hx, hy']
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hab' : a / b = n / m := by
    rw [div_eq_div_iff hb.ne' hm']; linarith
  rw [hab']
  push_cast
  field_simp

/-- A combination `na a + nb b` of commensurable `a, b` is a rational multiple of `a`. -/
theorem comb_rat {a b : ℝ} {m n : ℕ} (hn : 0 < n) (hab : (m : ℝ) * a = n * b) (na nb : ℕ) :
    ∃ r : ℚ, na * a + nb * b = r * a := by
  refine ⟨na + nb * (m / n), ?_⟩
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hbq : b = (m / n : ℚ) * a := by
    push_cast; field_simp; linarith
  push_cast
  rw [hbq]; push_cast; ring

/-- **Case V, Vc, second sub-branch:** `a, b` commensurable, `c` not a rational multiple of `a`. -/
theorem caseV_Vc_c {N : ℕ} (T : PolyTiling N 4) (hreg : RegularPQ T.C) (hγ : angleAt T.C.model 2 = Real.pi / 2)
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hab : (m : ℝ) * slen T.C 0 = n * slen T.C 1)
    (hc : ∀ m' n' : ℕ, 0 < m' → 0 < n' → (m' : ℝ) * slen T.C 2 ≠ n' * slen T.C 0) : Concl1 T.C T.P := by
  obtain ⟨idx, hA, hcnt, hidx, hang⟩ := caseV_setup T hreg hγ
  haveI : HasFansC T.C.toRegionDissection := hasFansC_poly _ T.P T.region_eq
  have ha := slen_pos T.C 0
  have hb := slen_pos T.C 1
  have hcpos := slen_pos T.C 2
  have hnc : NotComb (slen T.C 2) (slen T.C 1) (slen T.C 0) := by
    intro r p q hr h
    -- r c = p b + q a  with n b = m a:  n r c = (p m + q n) a
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    have e : ((n * r : ℕ) : ℝ) * slen T.C 2 = ((p * m + q * n : ℕ) : ℝ) * slen T.C 0 := by
      push_cast
      have : (n : ℝ) * (r * slen T.C 2) = n * (p * slen T.C 1 + q * slen T.C 0) := by rw [h]
      nlinarith [this, hab]
    have hpos : 0 < p * m + q * n := by
      by_contra h0
      have h0' : p * m + q * n = 0 := by omega
      have hl : (0:ℝ) < ((n * r : ℕ) : ℝ) * slen T.C 2 :=
        mul_pos (by exact_mod_cast Nat.mul_pos hn hr) hcpos
      rw [e, h0'] at hl
      simp at hl
    exact hc (n * r) (p * m + q * n) (Nat.mul_pos hn hr) hpos (by exact_mod_cast e)
  have hrect := rect_of_angles T.P hang
  have harea := poly4_area T hrect (Or.inl (by rw [hang 0, hγ]))
  have hareaS : (N : ℝ) * (slen T.C 0 * slen T.C 1) = 2 * (T.P.side 0 * T.P.side 3) := harea
  have hNpos : 0 < (N : ℝ) := by
    by_contra hh
    push_neg at hh
    have := mul_nonpos_of_nonpos_of_nonneg hh (le_of_lt (mul_pos ha hb))
    have h0 := side_pos T.P 0
    have h3 := side_pos T.P 3
    have : 0 < 2 * (T.P.side 0 * T.P.side 3) := by positivity
    linarith
  have d0 := edge_c_dichotomy T.C idx hidx hA hcnt hnc T.P T.region_eq 0
  have d3 := edge_c_dichotomy T.C idx hidx hA hcnt hnc T.P T.region_eq 3
  have hsin := side_ratio_eq_sin T.C.model
  have hs := Erdos634.Draft.LaczFormal.Thm21.sin_angleAt_pos T.C.model 0
  have ht := Erdos634.Draft.LaczFormal.Thm21.sin_angleAt_pos T.C.model 1
  refine concl1_of_rect T hang hγ ?_
  have p3 := side_pos T.P 3
  -- the mixed case contradiction
  have mixed : ∀ (m1 : ℕ) (na nb : ℕ), 0 < m1 → 0 < na + nb → (N : ℝ) * (slen T.C 0 * slen T.C 1) =
      2 * ((m1 * slen T.C 2) * (na * slen T.C 0 + nb * slen T.C 1)) ∨
      (N : ℝ) * (slen T.C 0 * slen T.C 1) = 2 * ((na * slen T.C 0 + nb * slen T.C 1) * (m1 * slen T.C 2)) → False := by
    intro m1 na nb hm1 hnab hA2
    have hA3 : (N : ℝ) * (slen T.C 0 * slen T.C 1) = 2 * ((m1 * slen T.C 2) * (na * slen T.C 0 + nb * slen T.C 1)) := by
      rcases hA2 with h | h
      · exact h
      · rw [h]; ring
    -- multiply by n and use n b = m a
    have e : (2 * m1 * (na * n + nb * m) : ℝ) * slen T.C 2 = (N * m : ℝ) * slen T.C 0 := by
      have hnb : (n : ℝ) * slen T.C 1 = m * slen T.C 0 := by linarith
      have : (n : ℝ) * ((N : ℝ) * (slen T.C 0 * slen T.C 1)) = n * (2 * ((m1 * slen T.C 2) * (na * slen T.C 0 + nb * slen T.C 1))) := by rw [hA3]
      have hcancel : (slen T.C 0) * ((2 * m1 * (na * n + nb * m) : ℝ) * slen T.C 2) = (slen T.C 0) * ((N * m : ℝ) * slen T.C 0) := by
        linear_combination (-1 : ℝ) * this + ((N : ℝ) * slen T.C 0 - 2 * m1 * slen T.C 2 * nb) * hnb
      exact mul_left_cancel₀ ha.ne' hcancel
    have hK : 0 < 2 * m1 * (na * n + nb * m) := by
      have : 0 < na * n + nb * m := by
        rcases Nat.eq_zero_or_pos na with h | h
        · have : 0 < nb := by omega
          have := Nat.mul_pos this hm
          omega
        · have := Nat.mul_pos h hn
          omega
      positivity
    have hL : 0 < N * m := Nat.mul_pos (by exact_mod_cast hNpos) hm
    exact hc (2 * m1 * (na * n + nb * m)) (N * m) hK hL (by exact_mod_cast e)
  rcases d0 with ⟨m0, hm0, h0⟩ | ⟨na0, nb0, hp0, h0⟩ <;> rcases d3 with ⟨m3, hm3, h3⟩ | ⟨na3, nb3, hp3, h3⟩
  · -- c, c
    exact ratio_of_rat_g (g := slen T.C 2) ha hb hcpos.ne' p3 (r := m0) (r' := m3) (by rw [h0]; norm_cast) (by rw [h3]; norm_cast) hm hn hab hsin.symm
  · -- c, a
    exfalso
    refine mixed m0 na3 nb3 hm0 hp3 (Or.inl ?_)
    rw [hareaS, h0, h3]
  · -- a, c
    exfalso
    refine mixed m3 na0 nb0 hm3 hp0 (Or.inr ?_)
    rw [hareaS, h0, h3]
  · -- a, a
    obtain ⟨r0, e0⟩ := comb_rat hn hab na0 nb0
    obtain ⟨r3, e3⟩ := comb_rat hn hab na3 nb3
    exact ratio_of_rat_g (g := slen T.C 0) ha hb ha.ne' p3 (r := r0) (r' := r3) (by rw [h0]; exact e0) (by rw [h3]; exact e3) hm hn hab hsin.symm

end Erdos634.Draft.LaczFormal.RG
