-- Draft/LaczFormalCondEConjKill.lean -- Condition (E) with the conjugate (K) constraints: the Farkas step `lp_core` fed with
--  (i) the plain vertex sums (`vertex_group`), (ii) the conjugate interior-vertex sums (`conj_interior_sum`), (iii) the conjugate corner sums (K2 of `KConj.lemmaK`).
-- Applied to the survivor n = 12, a = (2,3,7), which plain (E) cannot exclude.  UNAUDITED.  Credit: Laczkovich (Conditions (K),(E)); Beeson-Rosu; Farkas certificate ours.
import Erdos634.Draft.LaczFormalCondEConj
import Erdos634.Draft.LaczFormalBase
import Erdos634.Draft.TheoremPConditional

open scoped BigOperators Classical
open Erdos634.Geometry Erdos634.KConj Erdos634.TilePlacement Erdos634.Draft.TheoremPConditional
open Erdos634.LemmaKStar Erdos634.Draft.LaczFormal

namespace Erdos634.Draft.LaczFormal

variable {N : ℕ}

theorem xp_perm {n : ℕ} (a : Fin 3 → ℕ) (σ : Equiv.Perm (Fin 3)) (k : ℤ) (i : Fin 3) :
    xp n (fun l => a (σ.symm l)) k (σ i) = xp n a k i := by
  have hy : yv n (fun l => a (σ.symm l)) k (σ i) = yv n a k i := by simp [yv]
  have hs : sT n (fun l => a (σ.symm l)) k = sT n a k := by
    unfold sT
    exact Equiv.sum_comp σ (fun l => yv n (fun l => a (σ.symm l)) k l) |>.symm ▸
      (Finset.sum_congr rfl (fun i _ => by simp [yv]))
  unfold xp; rw [hs, hy]

/-- **Condition (E) + (K), killing form.**  As `E_kill`, with the additional conjugate data at the unit `k`: `x i / n = x'(k)_i` (tile) and `xu j / n` the conjugate target
angles; the extra Farkas hypotheses restrict non-corner vectors by `x·c ∈ {n,2n}` and corner vectors by `x·f_j = xu_j`. -/
theorem E_kill_conj (D : CongruentDissection N) (n : ℕ) (hn : 0 < n) (a u : Fin 3 → ℕ) (Y : Fin 3 → ℤ)
    (σ σt : Equiv.Perm (Fin 3))
    (hm : ∀ i, D.model.angleAt (σ i) = a i * Real.pi / n)
    (ht : ∀ j, D.target.angleAt (σt j) = u j * Real.pi / n)
    {k : ℤ} (hk : Int.gcd k n = 1) (x xu : Fin 3 → ℕ)
    (hx : ∀ i, xp n (fun l => a (σ.symm l)) k (σ i) = (x i : ℚ) / n)
    (hxu : ∀ j (f : Fin 3 → Fin 3 → ℕ), uu (fun l => a (σ.symm l)) f (σt j) = u j →
      xpu n (fun l => a (σ.symm l)) f k (σt j) = (xu j : ℚ) / n)
    (cert1 : ∀ c : Fin 3 → ℕ, (∑ i, a i * c i = n ∨ ∑ i, a i * c i = 2 * n) →
      (∑ i, x i * c i = n ∨ ∑ i, x i * c i = 2 * n) → 0 ≤ ∑ i, Y i * (c i : ℤ))
    (cert2 : ∑ i, Y i ≤ 0)
    (cert3 : ∀ f : Fin 3 → Fin 3 → ℕ, (∀ j, ∑ i, a i * f j i = u j) → (∀ j, ∑ i, x i * f j i = xu j) →
      0 < ∑ j, ∑ i, Y i * (f j i : ℤ)) : False := by
  have hpi := Real.pi_pos
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set A : Fin 3 → ℕ := fun l => a (σ.symm l) with hA
  have hmA : ∀ l, D.model.angleAt l = A l * Real.pi / n := fun l => by
    have := hm (σ.symm l); simpa [hA] using this
  obtain ⟨idx, hidx⟩ := KConj.exists_idx D A hmA
  have hidx0 : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v := fun i v => by
    rw [hidx i v, hmA]
  obtain ⟨hf, hKK⟩ := KConj.lemmaK D hn A hmA idx hidx
  set c : Plane → Fin 3 → ℕ := fun P i => cnt D idx P (σ i) with hc
  have hconv : ∀ P, ∑ l, (cnt D idx P l : ℝ) * D.model.angleAt l
      = ((∑ i, a i * c P i : ℕ) : ℝ) * Real.pi / n := by
    intro P
    rw [← Equiv.sum_comp σ (fun l => (cnt D idx P l : ℝ) * D.model.angleAt l)]
    push_cast
    rw [Finset.sum_mul, Finset.sum_div]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hm i]; simp only [hc]; ring
  have hcast : ∀ (X K : ℕ), (X : ℝ) * Real.pi / n = K * Real.pi → X = K * n := by
    intro X K h
    have : (X : ℝ) = K * n := by
      field_simp at h
      nlinarith
    exact_mod_cast this
  have hcast1 : ∀ (X : ℕ), (X : ℝ) * Real.pi / n = Real.pi → X = n := by
    intro X h
    have := hcast X 1 (by simpa using h); simpa using this
  have hcast2 : ∀ (X : ℕ), (X : ℝ) * Real.pi / n = 2 * Real.pi → X = 2 * n := by
    intro X h
    have := hcast X 2 (by simpa using h); simpa [mul_comm] using this
  have hinj : Function.Injective (fun j => D.target.pts (σt j)) :=
    D.target.indep.injective.comp σt.injective
  have hcV : ∀ j, D.target.pts (σt j) ∈ vertSet D := fun j => by
    obtain ⟨i, m, h⟩ := A1Pos.target_vertex_is_tile_vertex D.toDissection (σt j)
    exact Finset.mem_image.mpr ⟨(i, m), Finset.mem_univ _, h.symm⟩
  -- conjugate sum in the permuted index
  have hqperm : ∀ P, ∑ l, (cnt D idx P l : ℚ) * xp n A k l = ∑ i, (c P i : ℚ) * ((x i : ℚ) / n) := by
    intro P
    rw [← Equiv.sum_comp σ (fun l => (cnt D idx P l : ℚ) * xp n A k l)]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [show xp n A k (σ i) = (x i : ℚ) / n from hx i]
  have hn'' : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  have hnat : ∀ P (K : ℕ), ∑ l, (cnt D idx P l : ℚ) * xp n A k l = (K : ℚ) / n → ∑ i, x i * c P i = K := by
    intro P K h
    rw [hqperm] at h
    have e : ∑ i, (c P i : ℚ) * ((x i : ℚ) / n) = (∑ i, (x i : ℚ) * c P i) / n := by
      rw [Finset.sum_div]; exact Finset.sum_congr rfl (fun i _ => by ring)
    rw [e, div_left_inj' hn''] at h
    exact_mod_cast h
  refine lp_core (vertSet D) c Y N (fun j => D.target.pts (σt j)) hinj hcV
    (fun i => sum_cnt D idx (σ i)) ?_ cert2 ?_
  · intro P hP hnc
    have hP' : ∃ p : Fin N × Fin 3, (D.tile p.1).pts p.2 = P := by
      obtain ⟨p, -, hp⟩ := Finset.mem_image.mp hP
      exact ⟨p, hp⟩
    have hnc' : ∀ j, P ≠ D.target.pts j := fun j h => hnc (σt.symm j) (by simpa using h)
    have hconj := conj_interior_sum D hn A hmA idx hidx hk P hP' hnc'
    rcases vertex_group D idx hidx0 P hP' with ⟨j, hj, -⟩ | ⟨-, h⟩
    · exact absurd hj (hnc' j)
    · rw [hconv P] at h
      refine cert1 (c P) ?_ ?_
      · rcases h with h | h
        · exact Or.inl (hcast1 _ h)
        · exact Or.inr (hcast2 _ h)
      · rcases hconj with h' | h'
        · exact Or.inl (hnat P n (by rw [h', div_self hn'']))
        · exact Or.inr (hnat P (2 * n) (by rw [h']; push_cast; field_simp))
  · refine cert3 (fun j => c (D.target.pts (σt j))) ?_ ?_
    · intro j
      have hP' : ∃ p : Fin N × Fin 3, (D.tile p.1).pts p.2 = D.target.pts (σt j) := by
        obtain ⟨p, -, hp⟩ := Finset.mem_image.mp (hcV j)
        exact ⟨p, hp⟩
      rcases vertex_group D idx hidx0 _ hP' with ⟨j', hj', h⟩ | ⟨h0, -⟩
      · have : j' = σt j := (D.target.indep.injective hj').symm
        subst this
        rw [hconv, ht j] at h
        have h' : ((∑ i, a i * c (D.target.pts (σt j)) i : ℕ) : ℝ) * Real.pi / n
            = (u j : ℝ) * Real.pi / n := h
        have hX : ((∑ i, a i * c (D.target.pts (σt j)) i : ℕ) : ℝ) = (u j : ℝ) := by
          field_simp at h'
          exact h'
        exact_mod_cast hX
      · exact absurd rfl (h0 (σt j))
    · intro j
      -- u j via the plain corner sum
      have hP' : ∃ p : Fin N × Fin 3, (D.tile p.1).pts p.2 = D.target.pts (σt j) := by
        obtain ⟨p, -, hp⟩ := Finset.mem_image.mp (hcV j)
        exact ⟨p, hp⟩
      have huj : ∑ i, a i * c (D.target.pts (σt j)) i = u j := by
        rcases vertex_group D idx hidx0 _ hP' with ⟨j', hj', h⟩ | ⟨h0, -⟩
        · have : j' = σt j := (D.target.indep.injective hj').symm
          subst this
          rw [hconv, ht j] at h
          have h' : ((∑ i, a i * c (D.target.pts (σt j)) i : ℕ) : ℝ) * Real.pi / n
              = (u j : ℝ) * Real.pi / n := h
          have hX : ((∑ i, a i * c (D.target.pts (σt j)) i : ℕ) : ℝ) = (u j : ℝ) := by
            field_simp at h'
            exact h'
          exact_mod_cast hX
        · exact absurd rfl (h0 (σt j))
      have hK2 := (hKK k hk).2 (σt j)
      have hfig : ∀ l, fig D idx (σt j) l = cnt D idx (D.target.pts (σt j)) l := fun l => rfl
      have huu : uu A (fig D idx) (σt j) = u j := by
        rw [← huj, uu]
        rw [← Equiv.sum_comp σ (fun l => fig D idx (σt j) l * A l)]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        simp only [hc, hfig, hA]; simp [mul_comm]
      have h1 := hxu j (fig D idx) huu
      exact hnat _ (xu j) (by
        show ∑ i, (fig D idx (σt j) i : ℚ) * xp n A k i = _
        rw [hK2, h1])

theorem sT_perm {n : ℕ} (a : Fin 3 → ℕ) (σ : Equiv.Perm (Fin 3)) (k : ℤ) :
    sT n (fun l => a (σ.symm l)) k = sT n a k := by
  unfold sT
  rw [← Equiv.sum_comp σ (fun l => yv n (fun l => a (σ.symm l)) k l)]
  exact Finset.sum_congr rfl (fun i _ => by simp [yv])

theorem fract_of (q : ℚ) (z : ℤ) (h1 : (z : ℚ) ≤ q) (h2 : q < z + 1) : Int.fract q = q - z := by
  rw [Int.fract, Int.floor_eq_iff.mpr ⟨h1, h2⟩]

theorem sT_237 : sT 12 ![2, 3, 7] 5 = 2 := by
  have e1 : yv 12 ![2, 3, 7] 5 0 = 10 / 12 := by
    unfold yv; simp only [Matrix.cons_val_zero]; push_cast
    rw [fract_of _ 0 (by norm_num) (by norm_num)]; norm_num
  have e2 : yv 12 ![2, 3, 7] 5 1 = 3 / 12 := by
    unfold yv; simp only [Matrix.cons_val_one, Matrix.head_cons]; push_cast
    rw [fract_of _ 1 (by norm_num) (by norm_num)]; norm_num
  have e3 : yv 12 ![2, 3, 7] 5 2 = 11 / 12 := by
    unfold yv; simp only [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]; push_cast
    rw [fract_of _ 2 (by norm_num) (by norm_num)]; norm_num
  unfold sT; rw [Fin.sum_univ_three, e1, e2, e3]; norm_num

theorem xp_237 (i : Fin 3) : xp 12 ![2, 3, 7] 5 i = ((![2, 9, 1] : Fin 3 → ℕ) i : ℚ) / 12 := by
  have h := sT_237
  have e1 : yv 12 ![2, 3, 7] 5 0 = 10 / 12 := by
    unfold yv; simp only [Matrix.cons_val_zero]; push_cast
    rw [fract_of _ 0 (by norm_num) (by norm_num)]; norm_num
  have e2 : yv 12 ![2, 3, 7] 5 1 = 3 / 12 := by
    unfold yv; simp only [Matrix.cons_val_one, Matrix.head_cons]; push_cast
    rw [fract_of _ 1 (by norm_num) (by norm_num)]; norm_num
  have e3 : yv 12 ![2, 3, 7] 5 2 = 11 / 12 := by
    unfold yv; simp only [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]; push_cast
    rw [fract_of _ 2 (by norm_num) (by norm_num)]; norm_num
  have hne : sT 12 ![2, 3, 7] 5 ≠ 1 := by rw [h]; norm_num
  unfold xp; rw [if_neg hne]
  fin_cases i
  · simp [e1]; norm_num
  · simp [e2]; norm_num
  · simp [e3]; norm_num

theorem xpu_237 (A : Fin 3 → ℕ) (σ : Equiv.Perm (Fin 3)) (hA : A = fun l => (![2, 3, 7] : Fin 3 → ℕ) (σ.symm l))
    (f : Fin 3 → Fin 3 → ℕ) (j : Fin 3) (v : ℕ) (hv : uu A f j = v) (hv' : v = 2 ∨ v = 4 ∨ v = 6 ∨ v = 8) :
    xpu 12 A f 5 j = (v : ℚ) / 12 := by
  have hs : sT 12 A 5 = 2 := by rw [hA, sT_perm]; exact sT_237
  have hne : sT 12 A 5 ≠ 1 := by rw [hs]; norm_num
  unfold xpu xv; rw [if_neg hne, hv]
  rcases hv' with rfl | rfl | rfl | rfl
  · rw [show (((5 : ℤ) * ((2 : ℕ) : ℤ) : ℤ) : ℚ) / ((12 : ℕ) : ℚ) = 10 / 12 by norm_num,
      fract_of _ 0 (by norm_num) (by norm_num)]; norm_num
  · rw [show (((5 : ℤ) * ((4 : ℕ) : ℤ) : ℤ) : ℚ) / ((12 : ℕ) : ℚ) = 20 / 12 by norm_num,
      fract_of _ 1 (by norm_num) (by norm_num)]; norm_num
  · rw [show (((5 : ℤ) * ((6 : ℕ) : ℤ) : ℤ) : ℚ) / ((12 : ℕ) : ℚ) = 30 / 12 by norm_num,
      fract_of _ 2 (by norm_num) (by norm_num)]; norm_num
  · rw [show (((5 : ℤ) * ((8 : ℕ) : ℤ) : ℤ) : ℚ) / ((12 : ℕ) : ℚ) = 40 / 12 by norm_num,
      fract_of _ 3 (by norm_num) (by norm_num)]; norm_num

/-- No congruent dissection has tile angles `(2,3,7)π/12` and target angles `(2,2,8)π/12`: Condition (E) with the conjugate (K) constraints at `k = 5`
(conjugate tile angles `(2,9,1)π/12`), Farkas vector `Y = (2,-3,1)`.  (Plain Condition (E) is feasible here.) -/
theorem kill_12_2_3_7_t2_2_8 (D : CongruentDissection N)
    (hT : TileAngles D (2 * Real.pi / 12) (3 * Real.pi / 12) (7 * Real.pi / 12))
    (hG : TgtAngles D (2 * Real.pi / 12) (2 * Real.pi / 12) (8 * Real.pi / 12)) : False := by
  obtain ⟨σ, h0, h1, h2⟩ := hT
  obtain ⟨τ, g0, g1, g2⟩ := hG
  refine E_kill_conj D 12 (by norm_num) ![2, 3, 7] ![2, 2, 8] ![2, -3, 1] σ τ ?_ ?_
    (k := 5) (by norm_num) ![2, 9, 1] ![2, 2, 8] ?_ ?_ ?_ (by simp [Fin.sum_univ_three]) ?_
  · intro i; fin_cases i <;> simp [h0, h1, h2]
  · intro j; fin_cases j <;> simp [g0, g1, g2]
  · intro i
    rw [xp_perm]; exact xp_237 i
  · intro j f hf
    exact xpu_237 _ σ rfl f (τ j) _ hf (by fin_cases j <;> simp)
  · intro c h1 h2
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at h1 h2 ⊢
    push_cast
    omega
  · intro f hf hg
    have e0 := hf 0
    have e1 := hf 1
    have e2 := hf 2
    have d0 := hg 0
    have d1 := hg 1
    have d2 := hg 2
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at e0 e1 e2 d0 d1 d2 ⊢
    push_cast
    omega

/-- No congruent dissection has tile angles `(2,3,7)π/12` and target angles `(2,4,6)π/12`: Condition (E) with the conjugate (K) constraints at `k = 5`
(conjugate tile angles `(2,9,1)π/12`), Farkas vector `Y = (2,-3,1)`.  (Plain Condition (E) is feasible here.) -/
theorem kill_12_2_3_7_t2_4_6 (D : CongruentDissection N)
    (hT : TileAngles D (2 * Real.pi / 12) (3 * Real.pi / 12) (7 * Real.pi / 12))
    (hG : TgtAngles D (2 * Real.pi / 12) (4 * Real.pi / 12) (6 * Real.pi / 12)) : False := by
  obtain ⟨σ, h0, h1, h2⟩ := hT
  obtain ⟨τ, g0, g1, g2⟩ := hG
  refine E_kill_conj D 12 (by norm_num) ![2, 3, 7] ![2, 4, 6] ![2, -3, 1] σ τ ?_ ?_
    (k := 5) (by norm_num) ![2, 9, 1] ![2, 4, 6] ?_ ?_ ?_ (by simp [Fin.sum_univ_three]) ?_
  · intro i; fin_cases i <;> simp [h0, h1, h2]
  · intro j; fin_cases j <;> simp [g0, g1, g2]
  · intro i
    rw [xp_perm]; exact xp_237 i
  · intro j f hf
    exact xpu_237 _ σ rfl f (τ j) _ hf (by fin_cases j <;> simp)
  · intro c h1 h2
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at h1 h2 ⊢
    push_cast
    omega
  · intro f hf hg
    have e0 := hf 0
    have e1 := hf 1
    have e2 := hf 2
    have d0 := hg 0
    have d1 := hg 1
    have d2 := hg 2
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at e0 e1 e2 d0 d1 d2 ⊢
    push_cast
    omega

/-- No congruent dissection has tile angles `(2,3,7)π/12` and target angles `(4,4,4)π/12`: Condition (E) with the conjugate (K) constraints at `k = 5`
(conjugate tile angles `(2,9,1)π/12`), Farkas vector `Y = (2,-3,1)`.  (Plain Condition (E) is feasible here.) -/
theorem kill_12_2_3_7_t4_4_4 (D : CongruentDissection N)
    (hT : TileAngles D (2 * Real.pi / 12) (3 * Real.pi / 12) (7 * Real.pi / 12))
    (hG : TgtAngles D (4 * Real.pi / 12) (4 * Real.pi / 12) (4 * Real.pi / 12)) : False := by
  obtain ⟨σ, h0, h1, h2⟩ := hT
  obtain ⟨τ, g0, g1, g2⟩ := hG
  refine E_kill_conj D 12 (by norm_num) ![2, 3, 7] ![4, 4, 4] ![2, -3, 1] σ τ ?_ ?_
    (k := 5) (by norm_num) ![2, 9, 1] ![4, 4, 4] ?_ ?_ ?_ (by simp [Fin.sum_univ_three]) ?_
  · intro i; fin_cases i <;> simp [h0, h1, h2]
  · intro j; fin_cases j <;> simp [g0, g1, g2]
  · intro i
    rw [xp_perm]; exact xp_237 i
  · intro j f hf
    exact xpu_237 _ σ rfl f (τ j) _ hf (by fin_cases j <;> simp)
  · intro c h1 h2
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at h1 h2 ⊢
    push_cast
    omega
  · intro f hf hg
    have e0 := hf 0
    have e1 := hf 1
    have e2 := hf 2
    have d0 := hg 0
    have d1 := hg 1
    have d2 := hg 2
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at e0 e1 e2 d0 d1 d2 ⊢
    push_cast
    omega

end Erdos634.Draft.LaczFormal
