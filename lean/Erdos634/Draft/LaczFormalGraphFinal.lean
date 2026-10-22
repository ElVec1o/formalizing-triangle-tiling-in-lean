-- Draft/LaczFormalGraphFinal.lean -- D6 final: instantiation of `corner_kill` at the three equilateral-target tiles of Laczkovich (DCG 48 (2012), Thm 3.3 (5)):
-- (pi/12, 7pi/12, pi/3), (pi/30, 19pi/30, pi/3), (7pi/30, 13pi/30, pi/3), each with the regular-triangle target.  UNAUDITED.
-- Credit: Laczkovich (DCG 48 (2012)), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalGraphKill
import Erdos634.Draft.LaczFormalGraphArith30
import Erdos634.TriLawSin
import Erdos634.Draft.LaczFormalViiArith
import Erdos634.Draft.LaczFormalGraphReg
import Erdos634.Draft.LaczFormalGraphTypes

open scoped Classical
open Erdos634.Geometry Erdos634.KConj Erdos634.TilePlacement Erdos634.Draft.TheoremPConditional

namespace Erdos634.Draft.LaczFormal.Graph

variable {N : ℕ}

/-- Relabel the model of a congruent dissection by a permutation of its vertices. -/
noncomputable def relabelModel (D : CongruentDissection N) (τ : Equiv.Perm (Fin 3)) : CongruentDissection N where
  toDissection := D.toDissection
  model := D.model.relabel τ
  tiles_congruent := fun i => (D.tiles_congruent i).relabel τ

theorem angleAt_relabel (T : Tri) (τ : Equiv.Perm (Fin 3)) (j : Fin 3) : (T.relabel τ).angleAt j = T.angleAt (τ j) := by
  unfold Tri.angleAt
  simp only [Tri.relabel_pts]
  rcases perm_adj τ j with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
  · rw [h1, h2, Erdos634.Geometry.cornerAngle, Erdos634.Geometry.cornerAngle, EuclideanGeometry.angle_comm]

theorem slen_relabel (D : CongruentDissection N) (τ : Equiv.Perm (Fin 3)) (t : Fin 3) :
    slen (relabelModel D τ) t = slen D (τ t) := by
  unfold slen relabelModel
  simp only [Tri.relabel_pts]
  rcases perm_adj τ t with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
  · rw [h1, h2, dist_comm]

/-- Law of sines in the model: `a sin β = b sin α`, `a sin γ = c sin α`. -/
theorem slen_sin_rel (D : CongruentDissection N) :
    Real.sin (D.model.angleAt 1) * slen D 0 = Real.sin (D.model.angleAt 0) * slen D 1 ∧
    Real.sin (D.model.angleAt 0) * slen D 2 = Real.sin (D.model.angleAt 2) * slen D 0 := by
  have h0 := Erdos634.TriLawSin.sin_angleAt_mul_sideOpp D.model 0
  have h2 := Erdos634.TriLawSin.sin_angleAt_mul_sideOpp D.model 2
  exact ⟨h0, h2⟩

/-- `NotComb` from the corresponding statement on the sines of the model angles. -/
theorem notComb_of_sin (D : CongruentDissection N)
    (hs : ∀ r p q : ℕ, 0 < r → (r : ℝ) * Real.sin (D.model.angleAt 0) ≠
      p * Real.sin (D.model.angleAt 1) + q * Real.sin (D.model.angleAt 2)) :
    NotComb (slen D 0) (slen D 1) (slen D 2) := by
  intro r p q hr h
  obtain ⟨h1, h2⟩ := slen_sin_rel D
  have ha := slen_pos D 0
  apply hs r p q hr
  have : slen D 0 * ((r : ℝ) * Real.sin (D.model.angleAt 0)) = slen D 0 * (p * Real.sin (D.model.angleAt 1) + q * Real.sin (D.model.angleAt 2)) := by
    have e1 : (r : ℝ) * slen D 0 * Real.sin (D.model.angleAt 0) = (p * slen D 1 + q * slen D 2) * Real.sin (D.model.angleAt 0) := by rw [h]
    nlinarith [e1, h1, h2]
  exact mul_left_cancel₀ ha.ne' this

theorem slen_ne_of_sin (D : CongruentDissection N) (hsB : Real.sin (D.model.angleAt 0) ≠ Real.sin (D.model.angleAt 1))
    (hsC : Real.sin (D.model.angleAt 0) ≠ Real.sin (D.model.angleAt 2)) :
    slen D 0 ≠ slen D 1 ∧ slen D 0 ≠ slen D 2 := by
  obtain ⟨h1, h2⟩ := slen_sin_rel D
  have ha := slen_pos D 0
  constructor
  · intro e
    rw [← e] at h1
    exact hsB (mul_right_cancel₀ ha.ne' (by linarith))
  · intro e
    rw [← e] at h2
    exact hsC (mul_right_cancel₀ ha.ne' (by linarith))

section Trig

theorem sin_pi_div_12 : Real.sin (1 * Real.pi / 12) = (Real.sqrt 6 - Real.sqrt 2) / 4 := by
  rw [show (1 : ℝ) * Real.pi / 12 = Real.pi / 3 - Real.pi / 4 by ring, Real.sin_sub, Real.sin_pi_div_three, Real.cos_pi_div_four,
    Real.cos_pi_div_three, Real.sin_pi_div_four]
  have : Real.sqrt 6 = Real.sqrt 2 * Real.sqrt 3 := by rw [← Real.sqrt_mul (by norm_num)]; norm_num
  rw [this]; ring

theorem sin_7pi_div_12 : Real.sin (7 * Real.pi / 12) = (Real.sqrt 6 + Real.sqrt 2) / 4 := by
  rw [show (7 : ℝ) * Real.pi / 12 = Real.pi / 3 + Real.pi / 4 by ring, Real.sin_add, Real.sin_pi_div_three, Real.cos_pi_div_four,
    Real.cos_pi_div_three, Real.sin_pi_div_four]
  have : Real.sqrt 6 = Real.sqrt 2 * Real.sqrt 3 := by rw [← Real.sqrt_mul (by norm_num)]; norm_num
  rw [this]; ring

theorem sin_pi_div_3' : Real.sin (4 * Real.pi / 12) = Real.sqrt 3 / 2 := by
  rw [show (4 : ℝ) * Real.pi / 12 = Real.pi / 3 by ring, Real.sin_pi_div_three]

theorem sin_10_pi_div_30 : Real.sin (10 * Real.pi / 30) = Real.sqrt 3 / 2 := by
  rw [show (10 : ℝ) * Real.pi / 30 = Real.pi / 3 by ring, Real.sin_pi_div_three]

theorem cos5_sq : Real.sin (Real.pi / 5) ^ 2 = (5 - Real.sqrt 5) / 8 := by
  have h := Real.sin_sq_add_cos_sq (Real.pi / 5)
  rw [Real.cos_pi_div_five] at h
  have s5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  nlinarith [h, s5]

theorem sin_pi_div_10 : Real.sin (Real.pi / 10) = (Real.sqrt 5 - 1) / 4 := by
  rw [show Real.pi / 10 = Real.pi / 2 - 2 * (Real.pi / 5) by ring, Real.sin_pi_div_two_sub, Real.cos_two_mul, Real.cos_pi_div_five]
  have s5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  nlinarith [s5]

theorem cos10_sq : Real.cos (Real.pi / 10) ^ 2 = (5 + Real.sqrt 5) / 8 := by
  have h := Real.sin_sq_add_cos_sq (Real.pi / 10)
  rw [sin_pi_div_10] at h
  have s5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  nlinarith [h, s5]

theorem sin_pi_div_30 : Real.sin (1 * Real.pi / 30) = Real.sin (Real.pi / 5) * (Real.sqrt 3 / 2) - (1 + Real.sqrt 5) / 4 * (1 / 2) := by
  rw [show (1 : ℝ) * Real.pi / 30 = Real.pi / 5 - Real.pi / 6 by ring, Real.sin_sub, Real.cos_pi_div_six, Real.sin_pi_div_six,
    Real.cos_pi_div_five]

theorem sin_19pi_div_30 : Real.sin (19 * Real.pi / 30) = Real.sin (Real.pi / 5) * (Real.sqrt 3 / 2) + (1 + Real.sqrt 5) / 4 * (1 / 2) := by
  rw [show (19 : ℝ) * Real.pi / 30 = Real.pi - (Real.pi / 5 + Real.pi / 6) by ring, Real.sin_pi_sub, Real.sin_add, Real.cos_pi_div_six,
    Real.sin_pi_div_six, Real.cos_pi_div_five]

theorem sin_7pi_div_30 : Real.sin (7 * Real.pi / 30) = Real.sqrt 3 / 2 * Real.cos (Real.pi / 10) - 1 / 2 * ((Real.sqrt 5 - 1) / 4) := by
  rw [show (7 : ℝ) * Real.pi / 30 = Real.pi / 3 - Real.pi / 10 by ring, Real.sin_sub, Real.sin_pi_div_three, Real.cos_pi_div_three, sin_pi_div_10]

theorem sin_13pi_div_30 : Real.sin (13 * Real.pi / 30) = Real.sqrt 3 / 2 * Real.cos (Real.pi / 10) + 1 / 2 * ((Real.sqrt 5 - 1) / 4) := by
  rw [show (13 : ℝ) * Real.pi / 30 = Real.pi / 3 + Real.pi / 10 by ring, Real.sin_add, Real.sin_pi_div_three, Real.cos_pi_div_three, sin_pi_div_10]

/-- `n = 12`: `r sin(π/12) ≠ p sin(7π/12) + q sin(π/3)`. -/
theorem sin_rel_12 (r p q : ℕ) (hr : 0 < r) :
    (r : ℝ) * Real.sin (1 * Real.pi / 12) ≠ p * Real.sin (7 * Real.pi / 12) + q * Real.sin (4 * Real.pi / 12) := by
  intro h
  rw [sin_pi_div_12, sin_7pi_div_12, sin_pi_div_3'] at h
  have h4 : (((0 : ℚ)) : ℝ) + ((-(r + p) / 4 : ℚ) : ℝ) * Real.sqrt 2 + ((-q / 2 : ℚ) : ℝ) * Real.sqrt 3 + (((r - p) / 4 : ℚ) : ℝ) * Real.sqrt 6 = 0 := by
    push_cast; linarith
  obtain ⟨-, h2, -, -⟩ := indep4 h4
  have : (r : ℚ) + p = 0 := by linarith
  have : r = 0 := by
    have h' : ((r + p : ℕ) : ℚ) = 0 := by push_cast; linarith
    have := Nat.cast_eq_zero.mp h'
    omega
  omega

theorem sin_rel_30a (r p q : ℕ) (hr : 0 < r) :
    (r : ℝ) * Real.sin (1 * Real.pi / 30) ≠ p * Real.sin (19 * Real.pi / 30) + q * Real.sin (10 * Real.pi / 30) := by
  intro h
  rw [sin_pi_div_30, sin_19pi_div_30, sin_10_pi_div_30] at h
  have hrel := rel30_a_Q ((r : ℚ) - p) ((r : ℚ) + p) (q : ℚ) (Real.sin (Real.pi / 5)) cos5_sq (by push_cast; linarith)
  have : (r : ℚ) + p = 0 := hrel.2.1
  have h' : ((r + p : ℕ) : ℚ) = 0 := by push_cast; linarith
  have := Nat.cast_eq_zero.mp h'
  omega

theorem sin_rel_30b (r p q : ℕ) (hr : 0 < r) :
    (r : ℝ) * Real.sin (7 * Real.pi / 30) ≠ p * Real.sin (13 * Real.pi / 30) + q * Real.sin (10 * Real.pi / 30) := by
  intro h
  rw [sin_7pi_div_30, sin_13pi_div_30, sin_10_pi_div_30] at h
  have hrel := rel30_b_Q ((r : ℚ) - p) ((r : ℚ) + p) (q : ℚ) (Real.cos (Real.pi / 10)) cos10_sq (by push_cast; linarith)
  have : (r : ℚ) + p = 0 := hrel.2.1
  have h' : ((r + p : ℕ) : ℚ) = 0 := by push_cast; linarith
  have := Nat.cast_eq_zero.mp h'
  omega

end Trig

theorem kill_of_tile (D : CongruentDissection N) {w0 w1 w2 : ℕ} {u : ℝ} (W : WtData D w0 w1 w2 u)
    (hw3 : (w0, w1, w2) = (1, 7, 4) ∨ (w0, w1, w2) = (1, 19, 10) ∨ (w0, w1, w2) = (7, 13, 10))
    (hnc : NotComb (slen D 0) (slen D 1) (slen D 2)) (hab : slen D 0 ≠ slen D 1) (hac : slen D 0 ≠ slen D 2)
    (hregf : ∀ idx : Fin N → Equiv.Perm (Fin 3), (∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v) →
      ∀ P, (∃ i k, (D.tile i).pts k = P) → cnt D idx P 0 = cnt D idx P 1)
    (hG : ∀ j, D.target.angleAt j = (w2 : ℝ) * u) : False := by
  obtain ⟨idx, hidx, hidxA⟩ := exists_idx_both D
  exact corner_kill D idx hidx (fun i v => hidxA i v) hnc hab hac W hw3 (hregf idx (fun i v => hidxA i v)) hG

theorem mem_vertSet_iff (D : CongruentDissection N) (P : Plane) : P ∈ vertSet D ↔ ∃ i k, (D.tile i).pts k = P := by
  unfold vertSet
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Prod.exists]

theorem fin3_vals_inj (f : Fin 3 → ℝ) (a b c : ℝ) (h0 : f 0 = a) (h1 : f 1 = b) (h2 : f 2 = c) (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) : ∀ x y, f x = f y → x = y := by
  intro x y h
  revert h
  fin_cases x <;> fin_cases y <;> simp [h0, h1, h2, hab, hac, hbc, hab.symm, hac.symm, hbc.symm]

theorem tgt_all (D : CongruentDissection N) {x : ℝ} (hG : TgtAngles D x x x) : ∀ j, D.target.angleAt j = x := by
  obtain ⟨τ, g0, g1, g2⟩ := hG
  intro j
  obtain ⟨m, hm⟩ := τ.surjective j
  fin_cases m
  · rw [← hm]; exact g0
  · rw [← hm]; exact g1
  · rw [← hm]; exact g2

/-- **No tiling of the regular triangle by the tile `(π/12, 7π/12, π/3)`** (Laczkovich, DCG 48 (2012), Thm 3.3 (5), Subcase IVa). -/
theorem no_tiling_12 (D : CongruentDissection N)
    (hT : TileAngles D (1 * Real.pi / 12) (7 * Real.pi / 12) (4 * Real.pi / 12))
    (hG : TgtAngles D (4 * Real.pi / 12) (4 * Real.pi / 12) (4 * Real.pi / 12)) : False := by
  classical
  obtain ⟨σ, h0, h1, h2⟩ := hT
  set D' := relabelModel D σ with hD'
  have a0 : D'.model.angleAt 0 = 1 * Real.pi / 12 := by show (D.model.relabel σ).angleAt 0 = _; rw [angleAt_relabel]; exact h0
  have a1 : D'.model.angleAt 1 = 7 * Real.pi / 12 := by show (D.model.relabel σ).angleAt 1 = _; rw [angleAt_relabel]; exact h1
  have a2 : D'.model.angleAt 2 = 4 * Real.pi / 12 := by show (D.model.relabel σ).angleAt 2 = _; rw [angleAt_relabel]; exact h2
  have hT' : TileAngles D' (1 * Real.pi / 12) (7 * Real.pi / 12) (4 * Real.pi / 12) := ⟨Equiv.refl _, a0, a1, a2⟩
  have hG' : TgtAngles D' (4 * Real.pi / 12) (4 * Real.pi / 12) (4 * Real.pi / 12) := hG
  have hpi := Real.pi_pos
  have W : WtData D' 1 7 4 (Real.pi / 12) :=
    ⟨by positivity, by rw [a0]; push_cast; ring, by rw [a1]; push_cast; ring, by rw [a2]; push_cast; ring,
      by push_cast; ring, by norm_num, by norm_num⟩
  have hnc : NotComb (slen D' 0) (slen D' 1) (slen D' 2) :=
    notComb_of_sin D' (fun r p q hr => by rw [a0, a1, a2]; exact sin_rel_12 r p q hr)
  have hs := slen_ne_of_sin D' (by
      rw [a0, a1, sin_pi_div_12, sin_7pi_div_12]
      intro e
      have : Real.sqrt 2 > 0 := by positivity
      linarith)
    (by
      rw [a0, a2]
      exact (Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith) (by linarith) (by linarith)).ne)
  have hinj : ∀ x y : Fin 3, D'.model.angleAt x = D'.model.angleAt y → x = y :=
    fin3_vals_inj (fun k => D'.model.angleAt k) _ _ _ a0 a1 a2 (by intro e; linarith) (by intro e; linarith) (by intro e; linarith)
  refine kill_of_tile D' W (Or.inl rfl) hnc hs.1 hs.2 ?_ (fun j => by rw [tgt_all D' hG' j]; push_cast; ring)
  intro idx hidxA P hP
  obtain ⟨σ', k0, k1, k2, hreg⟩ := regular_12 D' hT' hG' idx (fun i v => hidxA i v)
  have e0 : σ' 0 = 0 := hinj _ _ (k0.trans a0.symm)
  have e1 : σ' 1 = 1 := hinj _ _ (k1.trans a1.symm)
  have := hreg P ((mem_vertSet_iff D' P).mpr hP)
  rwa [e0, e1] at this

/-- **No tiling of the regular triangle by the tile `(π/30, 19π/30, π/3)`** (Laczkovich, DCG 48 (2012), Thm 3.3 (5), Subcase IVa). -/
theorem no_tiling_30a (D : CongruentDissection N)
    (hT : TileAngles D (1 * Real.pi / 30) (19 * Real.pi / 30) (10 * Real.pi / 30))
    (hG : TgtAngles D (10 * Real.pi / 30) (10 * Real.pi / 30) (10 * Real.pi / 30)) : False := by
  classical
  obtain ⟨σ, h0, h1, h2⟩ := hT
  set D' := relabelModel D σ with hD'
  have a0 : D'.model.angleAt 0 = 1 * Real.pi / 30 := by show (D.model.relabel σ).angleAt 0 = _; rw [angleAt_relabel]; exact h0
  have a1 : D'.model.angleAt 1 = 19 * Real.pi / 30 := by show (D.model.relabel σ).angleAt 1 = _; rw [angleAt_relabel]; exact h1
  have a2 : D'.model.angleAt 2 = 10 * Real.pi / 30 := by show (D.model.relabel σ).angleAt 2 = _; rw [angleAt_relabel]; exact h2
  have hT' : TileAngles D' (1 * Real.pi / 30) (19 * Real.pi / 30) (10 * Real.pi / 30) := ⟨Equiv.refl _, a0, a1, a2⟩
  have hG' : TgtAngles D' (10 * Real.pi / 30) (10 * Real.pi / 30) (10 * Real.pi / 30) := hG
  have hpi := Real.pi_pos
  have W : WtData D' 1 19 10 (Real.pi / 30) :=
    ⟨by positivity, by rw [a0]; push_cast; ring, by rw [a1]; push_cast; ring, by rw [a2]; push_cast; ring,
      by push_cast; ring, by norm_num, by norm_num⟩
  have hnc : NotComb (slen D' 0) (slen D' 1) (slen D' 2) :=
    notComb_of_sin D' (fun r p q hr => by rw [a0, a1, a2]; exact sin_rel_30a r p q hr)
  have hs := slen_ne_of_sin D' (by
      rw [a0, a1, sin_pi_div_30, sin_19pi_div_30]
      intro e
      have : Real.sqrt 5 ≥ 0 := Real.sqrt_nonneg 5
      linarith)
    (by
      rw [a0, a2]
      exact (Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith) (by linarith) (by linarith)).ne)
  have hinj : ∀ x y : Fin 3, D'.model.angleAt x = D'.model.angleAt y → x = y :=
    fin3_vals_inj (fun k => D'.model.angleAt k) _ _ _ a0 a1 a2 (by intro e; linarith) (by intro e; linarith) (by intro e; linarith)
  refine kill_of_tile D' W (Or.inr (Or.inl rfl)) hnc hs.1 hs.2 ?_ (fun j => by rw [tgt_all D' hG' j]; push_cast; ring)
  intro idx hidxA P hP
  obtain ⟨σ', k0, k1, k2, hreg⟩ := regular_30a D' hT' hG' idx (fun i v => hidxA i v)
  have e0 : σ' 0 = 0 := hinj _ _ (k0.trans a0.symm)
  have e1 : σ' 1 = 1 := hinj _ _ (k1.trans a1.symm)
  have := hreg P ((mem_vertSet_iff D' P).mpr hP)
  rwa [e0, e1] at this

/-- **No tiling of the regular triangle by the tile `(7π/30, 13π/30, π/3)`** (Laczkovich, DCG 48 (2012), Thm 3.3 (5), Subcase IVa). -/
theorem no_tiling_30b (D : CongruentDissection N)
    (hT : TileAngles D (7 * Real.pi / 30) (13 * Real.pi / 30) (10 * Real.pi / 30))
    (hG : TgtAngles D (10 * Real.pi / 30) (10 * Real.pi / 30) (10 * Real.pi / 30)) : False := by
  classical
  obtain ⟨σ, h0, h1, h2⟩ := hT
  set D' := relabelModel D σ with hD'
  have a0 : D'.model.angleAt 0 = 7 * Real.pi / 30 := by show (D.model.relabel σ).angleAt 0 = _; rw [angleAt_relabel]; exact h0
  have a1 : D'.model.angleAt 1 = 13 * Real.pi / 30 := by show (D.model.relabel σ).angleAt 1 = _; rw [angleAt_relabel]; exact h1
  have a2 : D'.model.angleAt 2 = 10 * Real.pi / 30 := by show (D.model.relabel σ).angleAt 2 = _; rw [angleAt_relabel]; exact h2
  have hT' : TileAngles D' (7 * Real.pi / 30) (13 * Real.pi / 30) (10 * Real.pi / 30) := ⟨Equiv.refl _, a0, a1, a2⟩
  have hG' : TgtAngles D' (10 * Real.pi / 30) (10 * Real.pi / 30) (10 * Real.pi / 30) := hG
  have hpi := Real.pi_pos
  have W : WtData D' 7 13 10 (Real.pi / 30) :=
    ⟨by positivity, by rw [a0]; push_cast; ring, by rw [a1]; push_cast; ring, by rw [a2]; push_cast; ring,
      by push_cast; ring, by norm_num, by norm_num⟩
  have hnc : NotComb (slen D' 0) (slen D' 1) (slen D' 2) :=
    notComb_of_sin D' (fun r p q hr => by rw [a0, a1, a2]; exact sin_rel_30b r p q hr)
  have hs := slen_ne_of_sin D' (by
      rw [a0, a1]
      exact (Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith) (by linarith) (by linarith)).ne)
    (by
      rw [a0, a2]
      exact (Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith) (by linarith) (by linarith)).ne)
  have hinj : ∀ x y : Fin 3, D'.model.angleAt x = D'.model.angleAt y → x = y :=
    fin3_vals_inj (fun k => D'.model.angleAt k) _ _ _ a0 a1 a2 (by intro e; linarith) (by intro e; linarith) (by intro e; linarith)
  refine kill_of_tile D' W (Or.inr (Or.inr rfl)) hnc hs.1 hs.2 ?_ (fun j => by rw [tgt_all D' hG' j]; push_cast; ring)
  intro idx hidxA P hP
  obtain ⟨σ', k0, k1, k2, hreg⟩ := regular_30b D' hT' hG' idx (fun i v => hidxA i v)
  have e0 : σ' 0 = 0 := hinj _ _ (k0.trans a0.symm)
  have e1 : σ' 1 = 1 := hinj _ _ (k1.trans a1.symm)
  have := hreg P ((mem_vertSet_iff D' P).mpr hP)
  rwa [e0, e1] at this

end Erdos634.Draft.LaczFormal.Graph
