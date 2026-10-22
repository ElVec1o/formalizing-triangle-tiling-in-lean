-- Draft/LaczFormalK2Kill.lean -- killing by K2 (`KConj.lemmaK`): the corner figure `f_j` must satisfy both `f_j . a = u_j` and the conjugate equation `f_j . x'(k) = x'_{u_j}(k)`;
-- when no natural vector does, there is no congruent dissection.  Instances: tile (1,3,8)/12 with targets (1,1,10), (1,5,6), (2,5,5), (3,4,5) (k = 5).  UNAUDITED.
-- Credit: Laczkovich (1995, 2020; conjugate tilings), our `KConj.lemmaK`.
import Erdos634.Draft.LaczFormalK1Kill2

open scoped BigOperators Classical
open Erdos634.Geometry Erdos634.KConj Erdos634.TilePlacement Erdos634.Draft.TheoremPConditional
open Erdos634.LemmaKStar Erdos634.Geometry.CaseA.LemmaK1

namespace Erdos634.Draft.LaczFormal

variable {N : ℕ}

theorem K2_kill (D : CongruentDissection N) (n : ℕ) (hn : 0 < n) (a u : Fin 3 → ℕ)
    (σ τ : Equiv.Perm (Fin 3))
    (hm : ∀ i, D.model.angleAt (σ i) = (a i : ℕ) * Real.pi / n)
    (ht : ∀ j, D.target.angleAt (τ j) = (u j : ℕ) * Real.pi / n)
    {k : ℤ} (hk : Int.gcd k n = 1) (x : Fin 3 → ℕ) (xu : ℕ) (j : Fin 3)
    (hx : ∀ i, xp n (fun l => a (σ.symm l)) k (σ i) = (x i : ℚ) / n)
    (hxu : ∀ f : Fin 3 → Fin 3 → ℕ, uu (fun l => a (σ.symm l)) f (τ j) = u j →
      xpu n (fun l => a (σ.symm l)) f k (τ j) = (xu : ℚ) / n)
    (hno : ∀ f : Fin 3 → ℕ, ∑ i, a i * f i = u j → ∑ i, x i * f i = xu → False) : False := by
  have hpi := Real.pi_pos
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hn'' : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  set A : Fin 3 → ℕ := fun l => a (σ.symm l) with hA
  have hmA : ∀ l, D.model.angleAt l = A l * Real.pi / n := fun l => by
    have := hm (σ.symm l); simpa [hA] using this
  obtain ⟨idx, hidx⟩ := KConj.exists_idx D A hmA
  obtain ⟨hf, hKK⟩ := KConj.lemmaK D hn A hmA idx hidx
  have huu : uu A (fig D idx) (τ j) = u j := by
    have h1 := hf (τ j)
    rw [ht j] at h1
    have : ((u j : ℕ) : ℝ) * Real.pi / n = ((uu A (fig D idx) (τ j) : ℕ) : ℝ) * Real.pi / n := h1
    have h2 : ((u j : ℕ) : ℝ) = ((uu A (fig D idx) (τ j) : ℕ) : ℝ) := by
      field_simp at this; exact this
    exact_mod_cast h2.symm
  have hK2 := (hKK k hk).2 (τ j)
  rw [hxu (fig D idx) huu] at hK2
  set f' : Fin 3 → ℕ := fun i => fig D idx (τ j) (σ i) with hf'
  apply hno f'
  · rw [← huu, uu]
    rw [← Equiv.sum_comp σ (fun i => fig D idx (τ j) i * A i)]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp [hA, hf', mul_comm]
  · rw [← Equiv.sum_comp σ (fun i => (fig D idx (τ j) i : ℚ) * xp n A k i)] at hK2
    simp only [hx] at hK2
    have : ((∑ i, x i * f' i : ℕ) : ℚ) / n = (xu : ℚ) / n := by
      rw [← hK2]; push_cast
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl (fun i _ => by simp [hf']; ring)
    have := (div_left_inj' hn'').mp this
    exact_mod_cast this

theorem xp_s1 {n : ℕ} (a : Fin 3 → ℕ) (σ : Equiv.Perm (Fin 3)) (k : ℤ) (hs : sT n a k = 1) (i : Fin 3) :
    xp n (fun l => a (σ.symm l)) k (σ i) = yv n a k i := by
  rw [xp_perm]; unfold xp; rw [if_pos hs]

theorem xpu_s1 {n : ℕ} (a : Fin 3 → ℕ) (σ : Equiv.Perm (Fin 3)) (k : ℤ) (hs : sT n a k = 1)
    (f : Fin 3 → Fin 3 → ℕ) (j : Fin 3) :
    xpu n (fun l => a (σ.symm l)) f k j = xv n (fun l => a (σ.symm l)) f k j := by
  unfold xpu; rw [sT_perm, if_pos hs]

/-- No congruent dissection has tile angles `(1,3,8)π/12` and target angles `(1,1,10)π/12`: at `k = 5` the corner `j = 2` has no figure
(`f . (1,3,8) = 10`, `f . (5,3,4) = 2` incompatible). -/
theorem k2kill_12_1_3_8_t1_1_10 (D : CongruentDissection N)
    (hT : TileAngles D (1 * Real.pi / 12) (3 * Real.pi / 12) (8 * Real.pi / 12))
    (hG : TgtAngles D (1 * Real.pi / 12) (1 * Real.pi / 12) (10 * Real.pi / 12)) : False := by
  obtain ⟨σ, h0, h1, h2⟩ := hT
  obtain ⟨τ, g0, g1, g2⟩ := hG
  have hs : sT 12 ![1, 3, 8] 5 = 1 := by
    simp [sT, yv, Fin.sum_univ_three, fract_int]; norm_num
  refine K2_kill D 12 (by norm_num) ![1, 3, 8] ![1, 1, 10] σ τ ?_ ?_ (k := 5) (by norm_num)
    ![5, 3, 4] 2 2 ?_ ?_ ?_
  · intro i; fin_cases i <;> simp [h0, h1, h2]
  · intro j; fin_cases j <;> simp [g0, g1, g2]
  · intro i; rw [xp_s1 _ σ 5 hs]; fin_cases i <;> simp [yv, fract_int] <;> norm_num
  · intro f hf; rw [xpu_s1 _ σ 5 hs]; unfold xv; simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at hf; rw [hf, fract_int _ 12 (by norm_num)]; norm_num
  · intro f h1 h2
    simp [Fin.sum_univ_three] at h1 h2
    omega

/-- No congruent dissection has tile angles `(1,3,8)π/12` and target angles `(1,5,6)π/12`: at `k = 5` the corner `j = 1` has no figure
(`f . (1,3,8) = 5`, `f . (5,3,4) = 1` incompatible). -/
theorem k2kill_12_1_3_8_t1_5_6 (D : CongruentDissection N)
    (hT : TileAngles D (1 * Real.pi / 12) (3 * Real.pi / 12) (8 * Real.pi / 12))
    (hG : TgtAngles D (1 * Real.pi / 12) (5 * Real.pi / 12) (6 * Real.pi / 12)) : False := by
  obtain ⟨σ, h0, h1, h2⟩ := hT
  obtain ⟨τ, g0, g1, g2⟩ := hG
  have hs : sT 12 ![1, 3, 8] 5 = 1 := by
    simp [sT, yv, Fin.sum_univ_three, fract_int]; norm_num
  refine K2_kill D 12 (by norm_num) ![1, 3, 8] ![1, 5, 6] σ τ ?_ ?_ (k := 5) (by norm_num)
    ![5, 3, 4] 1 1 ?_ ?_ ?_
  · intro i; fin_cases i <;> simp [h0, h1, h2]
  · intro j; fin_cases j <;> simp [g0, g1, g2]
  · intro i; rw [xp_s1 _ σ 5 hs]; fin_cases i <;> simp [yv, fract_int] <;> norm_num
  · intro f hf; rw [xpu_s1 _ σ 5 hs]; unfold xv; simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at hf; rw [hf, fract_int _ 12 (by norm_num)]; norm_num
  · intro f h1 h2
    simp [Fin.sum_univ_three] at h1 h2
    omega

/-- No congruent dissection has tile angles `(1,3,8)π/12` and target angles `(2,5,5)π/12`: at `k = 5` the corner `j = 1` has no figure
(`f . (1,3,8) = 5`, `f . (5,3,4) = 1` incompatible). -/
theorem k2kill_12_1_3_8_t2_5_5 (D : CongruentDissection N)
    (hT : TileAngles D (1 * Real.pi / 12) (3 * Real.pi / 12) (8 * Real.pi / 12))
    (hG : TgtAngles D (2 * Real.pi / 12) (5 * Real.pi / 12) (5 * Real.pi / 12)) : False := by
  obtain ⟨σ, h0, h1, h2⟩ := hT
  obtain ⟨τ, g0, g1, g2⟩ := hG
  have hs : sT 12 ![1, 3, 8] 5 = 1 := by
    simp [sT, yv, Fin.sum_univ_three, fract_int]; norm_num
  refine K2_kill D 12 (by norm_num) ![1, 3, 8] ![2, 5, 5] σ τ ?_ ?_ (k := 5) (by norm_num)
    ![5, 3, 4] 1 1 ?_ ?_ ?_
  · intro i; fin_cases i <;> simp [h0, h1, h2]
  · intro j; fin_cases j <;> simp [g0, g1, g2]
  · intro i; rw [xp_s1 _ σ 5 hs]; fin_cases i <;> simp [yv, fract_int] <;> norm_num
  · intro f hf; rw [xpu_s1 _ σ 5 hs]; unfold xv; simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at hf; rw [hf, fract_int _ 12 (by norm_num)]; norm_num
  · intro f h1 h2
    simp [Fin.sum_univ_three] at h1 h2
    omega

/-- No congruent dissection has tile angles `(1,3,8)π/12` and target angles `(3,4,5)π/12`: at `k = 5` the corner `j = 2` has no figure
(`f . (1,3,8) = 5`, `f . (5,3,4) = 1` incompatible). -/
theorem k2kill_12_1_3_8_t3_4_5 (D : CongruentDissection N)
    (hT : TileAngles D (1 * Real.pi / 12) (3 * Real.pi / 12) (8 * Real.pi / 12))
    (hG : TgtAngles D (3 * Real.pi / 12) (4 * Real.pi / 12) (5 * Real.pi / 12)) : False := by
  obtain ⟨σ, h0, h1, h2⟩ := hT
  obtain ⟨τ, g0, g1, g2⟩ := hG
  have hs : sT 12 ![1, 3, 8] 5 = 1 := by
    simp [sT, yv, Fin.sum_univ_three, fract_int]; norm_num
  refine K2_kill D 12 (by norm_num) ![1, 3, 8] ![3, 4, 5] σ τ ?_ ?_ (k := 5) (by norm_num)
    ![5, 3, 4] 1 2 ?_ ?_ ?_
  · intro i; fin_cases i <;> simp [h0, h1, h2]
  · intro j; fin_cases j <;> simp [g0, g1, g2]
  · intro i; rw [xp_s1 _ σ 5 hs]; fin_cases i <;> simp [yv, fract_int] <;> norm_num
  · intro f hf; rw [xpu_s1 _ σ 5 hs]; unfold xv; simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at hf; rw [hf, fract_int _ 12 (by norm_num)]; norm_num
  · intro f h1 h2
    simp [Fin.sum_univ_three] at h1 h2
    omega

end Erdos634.Draft.LaczFormal
