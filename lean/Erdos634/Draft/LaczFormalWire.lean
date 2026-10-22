-- Draft/LaczFormalWire.lean -- WIRING of Condition (E) into a table-driven classification step.
--   * `okCert n a u Y` : a decidable Farkas certificate (plain Condition (E)) for "tile a/n, target u/n";
--   * `E_kill_dec` : okCert = true => no congruent dissection has these angles (via `E_kill`);
--   * `tgt_nums` : the target angles of a dissection by a rational tile are u_j pi/n with natural u_j (sum n, each a nonneg integer combination of the tile angles);
--   * `wire_tile` : table-checked classification step: the sorted target numerators equal the tile's own sorted triple (similar) or lie in the survivor list.
-- UNAUDITED.  Credit: Laczkovich (1995, Condition (E) of 2020); Beeson-Rosu.
import Erdos634.Draft.LaczFormalCondE3

open scoped BigOperators Classical
open Erdos634.Geometry Erdos634.KConj Erdos634.TilePlacement Erdos634.Draft.TheoremPConditional
open Erdos634.LemmaKStar

namespace Erdos634.Draft.LaczFormal

variable {N : ℕ}

/-- All `(x,y,z)` with `a0 x + a1 y + a2 z = t`. -/
def vecs3 (a : ℕ × ℕ × ℕ) (t : ℕ) : List (ℕ × ℕ × ℕ) :=
  (List.range (t / a.1 + 1)).flatMap fun x => (List.range (t / a.2.1 + 1)).flatMap fun y =>
    (List.range (t / a.2.2 + 1)).filterMap fun z =>
      if a.1 * x + a.2.1 * y + a.2.2 * z = t then some (x, y, z) else none

theorem mem_vecs3 {a : ℕ × ℕ × ℕ} (h0 : 0 < a.1) (h1 : 0 < a.2.1) (h2 : 0 < a.2.2) {t x y z : ℕ} :
    (x, y, z) ∈ vecs3 a t ↔ a.1 * x + a.2.1 * y + a.2.2 * z = t := by
  unfold vecs3
  simp only [List.mem_flatMap, List.mem_range, List.mem_filterMap]
  constructor
  · rintro ⟨x', -, y', -, z', -, h⟩
    by_cases hh : a.1 * x' + a.2.1 * y' + a.2.2 * z' = t
    · rw [if_pos hh] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h; exact hh
    · rw [if_neg hh] at h; exact absurd h (by simp)
  · intro h
    refine ⟨x, ?_, y, ?_, z, ?_, by simp [h]⟩
    · rw [Nat.lt_succ_iff]; exact Nat.le_div_iff_mul_le h0 |>.mpr (by nlinarith)
    · rw [Nat.lt_succ_iff]; exact Nat.le_div_iff_mul_le h1 |>.mpr (by nlinarith)
    · rw [Nat.lt_succ_iff]; exact Nat.le_div_iff_mul_le h2 |>.mpr (by nlinarith)

/-- Decidable Farkas certificate for plain Condition (E). -/
def okCert (n : ℕ) (a u : ℕ × ℕ × ℕ) (Y : ℤ × ℤ × ℤ) : Bool :=
  ((vecs3 a n ++ vecs3 a (2 * n)).all fun c =>
      decide (0 ≤ Y.1 * c.1 + Y.2.1 * c.2.1 + Y.2.2 * c.2.2)) &&
    decide (Y.1 + Y.2.1 + Y.2.2 ≤ 0) &&
    (vecs3 a u.1).all fun f0 => (vecs3 a u.2.1).all fun f1 => (vecs3 a u.2.2).all fun f2 =>
      decide (0 < Y.1 * ((f0.1 : ℤ) + f1.1 + f2.1) + Y.2.1 * ((f0.2.1 : ℤ) + f1.2.1 + f2.2.1) +
        Y.2.2 * ((f0.2.2 : ℤ) + f1.2.2 + f2.2.2))

theorem E_kill_dec (D : CongruentDissection N) (n : ℕ) (hn : 0 < n) (a u : ℕ × ℕ × ℕ) (Y : ℤ × ℤ × ℤ)
    (h0 : 0 < a.1) (h1 : 0 < a.2.1) (h2 : 0 < a.2.2) (σ σt : Equiv.Perm (Fin 3))
    (hm : ∀ i, D.model.angleAt (σ i) = (![a.1, a.2.1, a.2.2] i : ℕ) * Real.pi / n)
    (ht : ∀ j, D.target.angleAt (σt j) = (![u.1, u.2.1, u.2.2] j : ℕ) * Real.pi / n)
    (h : okCert n a u Y = true) : False := by
  unfold okCert at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_append] at h
  obtain ⟨⟨hc1, hc2⟩, hc3⟩ := h
  refine E_kill D n hn ![a.1, a.2.1, a.2.2] ![u.1, u.2.1, u.2.2] ![Y.1, Y.2.1, Y.2.2] σ σt hm ht ?_ ?_ ?_
  · intro c hc
    have hmem : (c 0, c 1, c 2) ∈ vecs3 a n ∨ (c 0, c 1, c 2) ∈ vecs3 a (2 * n) := by
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons] at hc
      rcases hc with hc | hc
      · exact Or.inl ((mem_vecs3 h0 h1 h2).mpr hc)
      · exact Or.inr ((mem_vecs3 h0 h1 h2).mpr hc)
    have := hc1 _ hmem
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    exact this
  · simpa [Fin.sum_univ_three] using hc2
  · intro f hf
    have e0 := hf 0
    have e1 := hf 1
    have e2 := hf 2
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons] at e0 e1 e2
    have m0 : (f 0 0, f 0 1, f 0 2) ∈ vecs3 a u.1 := (mem_vecs3 h0 h1 h2).mpr e0
    have m1 : (f 1 0, f 1 1, f 1 2) ∈ vecs3 a u.2.1 := (mem_vecs3 h0 h1 h2).mpr e1
    have m2 : (f 2 0, f 2 1, f 2 2) ∈ vecs3 a u.2.2 := (mem_vecs3 h0 h1 h2).mpr e2
    have := hc3 _ m0 _ m1 _ m2
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    linarith

open Erdos634.Geometry.CaseA.LemmaV in
/-- **Target numerators.**  A congruent dissection by a tile with angles `a_i π/n` has target angles `u_j π/n` with natural `u_j`, summing to `n`,
each a nonnegative integer combination of the tile numerators (the corner figure). -/
theorem tgt_nums (D : CongruentDissection N) {n : ℕ} (hn : 0 < n) (a : Fin 3 → ℕ) (σ : Equiv.Perm (Fin 3))
    (hm : ∀ i, D.model.angleAt (σ i) = (a i : ℕ) * Real.pi / n) :
    ∃ u : Fin 3 → ℕ, (∀ j, D.target.angleAt j = (u j : ℕ) * Real.pi / n) ∧ ∑ j, u j = n ∧
      (∀ j, 0 < u j) ∧ ∀ j, ∃ f : Fin 3 → ℕ, ∑ i, a i * f i = u j := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  set A : Fin 3 → ℕ := fun l => a (σ.symm l) with hA
  have hmA : ∀ l, D.model.angleAt l = A l * Real.pi / n := fun l => by
    have := hm (σ.symm l); simpa [hA] using this
  obtain ⟨idx, hidx⟩ := KConj.exists_idx D A hmA
  obtain ⟨hf, -⟩ := KConj.lemmaK D hn A hmA idx hidx
  refine ⟨fun j => uu A (fig D idx) j, hf, ?_, ?_, ?_⟩
  · have hs := D.target.angleAt_sum
    rw [hf 0, hf 1, hf 2] at hs
    have hnn : (n : ℝ) * (Real.pi / n) = Real.pi := by field_simp
    have key : ((((uu A (fig D idx) 0 + uu A (fig D idx) 1 + uu A (fig D idx) 2 : ℕ)) : ℝ) - n) *
        (Real.pi / n) = 0 := by
      push_cast; linear_combination hs - hnn
    have := sub_eq_zero.mp ((mul_eq_zero.mp key).resolve_right (div_ne_zero Real.pi_ne_zero hn'))
    rw [Fin.sum_univ_three]; exact_mod_cast this
  · intro j
    exact (nat_bounds hn (hf j) (angle_pos _ j) (angle_lt_pi _ j)).1
  · intro j
    refine ⟨fun i => fig D idx j (σ i), ?_⟩
    show _ = ∑ i, fig D idx j i * A i
    rw [← Equiv.sum_comp σ (fun i => fig D idx j i * A i)]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp [hA, mul_comm]

/-- Table coverage: every sorted target triple of sum `n` is the tile's own triple, a listed survivor, or has a certificate in `entries`. -/
def Cover (n : ℕ) (a : ℕ × ℕ × ℕ) (surv : List (ℕ × ℕ × ℕ)) (entries : List ((ℕ × ℕ × ℕ) × (ℤ × ℤ × ℤ))) : Prop :=
  ∀ u0 ∈ List.range (n + 1), ∀ u1 ∈ List.range (n + 1),
    (0 < u0 ∧ u0 ≤ u1 ∧ u1 ≤ n - u0 - u1 ∧ u0 + u1 ≤ n ∧ vecs3 a u0 ≠ [] ∧ vecs3 a u1 ≠ [] ∧
      vecs3 a (n - u0 - u1) ≠ []) →
      ((u0, u1, n - u0 - u1) = a ∨ (u0, u1, n - u0 - u1) ∈ surv ∨
        ∃ e ∈ entries, e.1 = (u0, u1, n - u0 - u1) ∧ okCert n a e.1 e.2 = true)

instance (n a surv entries) : Decidable (Cover n a surv entries) := by unfold Cover; infer_instance

theorem wire_tile (D : CongruentDissection N) (n : ℕ) (hn : 0 < n) (a : ℕ × ℕ × ℕ)
    (h0 : 0 < a.1) (h1 : 0 < a.2.1) (h2 : 0 < a.2.2) (surv : List (ℕ × ℕ × ℕ))
    (entries : List ((ℕ × ℕ × ℕ) × (ℤ × ℤ × ℤ))) (hc : Cover n a surv entries)
    (σ : Equiv.Perm (Fin 3))
    (hm : ∀ i, D.model.angleAt (σ i) = (![a.1, a.2.1, a.2.2] i : ℕ) * Real.pi / n) :
    ∃ u : ℕ × ℕ × ℕ, TgtAngles D (u.1 * Real.pi / n) (u.2.1 * Real.pi / n) (u.2.2 * Real.pi / n) ∧
      0 < u.1 ∧ u.1 ≤ u.2.1 ∧ u.2.1 ≤ u.2.2 ∧ u.1 + u.2.1 + u.2.2 = n ∧ (u = a ∨ u ∈ surv) := by
  obtain ⟨u', hu', hsum, hpos, hrep⟩ := tgt_nums D hn ![a.1, a.2.1, a.2.2] σ hm
  have hnemp : ∀ j, vecs3 a (u' j) ≠ [] := by
    intro j hj
    obtain ⟨f, hf⟩ := hrep j
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons] at hf
    have := (mem_vecs3 h0 h1 h2 (t := u' j) (x := f 0) (y := f 1) (z := f 2)).mpr (by linarith)
    rw [hj] at this; simp at this
  set τ := Tuple.sort u' with hτ
  have hmono := Tuple.monotone_sort u'
  have m01 : u' (τ 0) ≤ u' (τ 1) := hmono (by decide : (0 : Fin 3) ≤ 1)
  have m12 : u' (τ 1) ≤ u' (τ 2) := hmono (by decide : (1 : Fin 3) ≤ 2)
  have hs3 : u' (τ 0) + u' (τ 1) + u' (τ 2) = n := by
    have := Equiv.sum_comp τ u'
    rw [Fin.sum_univ_three, Fin.sum_univ_three] at this
    rw [Fin.sum_univ_three] at hsum
    omega
  have hp0 := hpos (τ 0)
  set u : ℕ × ℕ × ℕ := (u' (τ 0), u' (τ 1), u' (τ 2)) with hu
  have hT : TgtAngles D (u.1 * Real.pi / n) (u.2.1 * Real.pi / n) (u.2.2 * Real.pi / n) :=
    ⟨τ, (hu' _), (hu' _), (hu' _)⟩
  refine ⟨u, hT, hp0, m01, m12, hs3, ?_⟩
  by_contra hne
  push Not at hne
  have e1 : u.1 = u' (τ 0) := rfl
  have e2 : u.2.1 = u' (τ 1) := rfl
  have e3 : u.2.2 = u' (τ 2) := rfl
  have hmem0 : u.1 ∈ List.range (n + 1) := by rw [List.mem_range]; omega
  have hmem1 : u.2.1 ∈ List.range (n + 1) := by rw [List.mem_range]; omega
  have hu2 : n - u.1 - u.2.1 = u.2.2 := by omega
  have hcu := hc u.1 hmem0 u.2.1 hmem1 ⟨hp0, m01, by rw [hu2]; exact m12, by omega, by rw [e1]; exact hnemp _, by rw [e2]; exact hnemp _, by rw [hu2, e3]; exact hnemp _⟩
  rw [hu2] at hcu
  have hueq : ((u.1, u.2.1, u.2.2) : ℕ × ℕ × ℕ) = u := rfl
  rw [hueq] at hcu
  rcases hcu with h | h | ⟨e, -, he1, he2⟩
  · exact hne.1 h
  · exact hne.2 h
  · refine E_kill_dec D n hn a e.1 e.2 h0 h1 h2 σ τ hm ?_ he2
    intro j
    rw [he1]
    fin_cases j <;> simp [hu, hu']

end Erdos634.Draft.LaczFormal
