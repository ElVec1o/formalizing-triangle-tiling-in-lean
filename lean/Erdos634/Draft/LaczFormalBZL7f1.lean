-- Draft/LaczFormalBZL7f1.lean -- Beeson, "Tilings of an isosceles triangle" (arXiv 1206.1974v7), Section 10: the PURE COMBINATORIAL / ARITHMETIC CORES of
-- Theorem 10.7 and Lemmas 10.3, 10.4, 10.5 (no geometry):
--   `thm107_algebra`     : the final algebra of Thm 10.7 (relations ja=pb+qc, Jb=Pa+Qc, j'c=p'a+q'b with positive coefficients j,J,j' => a/b, c/a rational);
--   `link_graph_contra`  : the counting step of Lemma 10.4 / 10.6 (finite digraph, in-degree <= 1, out>0 wherever in>0, one vertex with out>0 and in=0: impossible);
--   `cyc_parity`         : parity of unmatched edge ends in a cyclic fan (core of Lemma 10.3), `centre_ab_or_ac_bc`: at a centre (types 0,2,3) there is an a/b ray or both an a/c and a b/c ray;
--   `lin_parity`         : the half-plane version (core of Lemma 10.5): a linear fan whose first ray has an x-end from sector 0 and whose last ray has none, with an even number of x-ends, has an interior mismatched ray involving x.
-- NOT here (printed gap, see (private working notes, not included)): the link from a real fan (rays, sector edge lengths, Def. 6.1 links) to these abstract data.  NOTE, UNAUDITED.
-- Credit: Beeson (arXiv 1206.1974v7, Lemmas 10.3-10.6, Thm 10.7), Beeson-Zhang (arXiv 2604.01314), Laczkovich (DCG 48 (2012), Lemma 8.1 style link graph).
import Erdos634.Draft.LaczFormalRegArith

open scoped Classical

namespace Erdos634.Draft.LaczFormal.RG

/-- **Theorem 10.7, final algebra.**  `a,b,c > 0`; `j a = p b + q c`, `J b = P a + Q c`, `j' c = p' a + q' b` with `j, J, j' > 0` (naturals).  Then `a = r b` and `c = s a` with `r, s` rational. -/
theorem thm107_algebra {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (j p q J P Q j' p' q' : ℕ) (hj : 0 < j) (hJ : 0 < J) (hj' : 0 < j')
    (h1 : (j : ℝ) * a = p * b + q * c) (h2 : (J : ℝ) * b = P * a + Q * c) (h3 : (j' : ℝ) * c = p' * a + q' * b) :
    ∃ r s : ℚ, a = (r : ℝ) * b ∧ c = (s : ℝ) * a := by
  have hjR : (0 : ℝ) < j := by exact_mod_cast hj
  have hJR : (0 : ℝ) < J := by exact_mod_cast hJ
  have hj'R : (0 : ℝ) < j' := by exact_mod_cast hj'
  have key : ∃ r : ℚ, a = (r : ℝ) * b := by
    by_cases hq : q = 0
    · subst hq
      push_cast at h1
      refine ⟨(p : ℚ) / j, ?_⟩
      push_cast
      field_simp
      linarith
    by_cases hQ : Q = 0
    · subst hQ
      push_cast at h2
      have hP : (0 : ℝ) < P := by
        by_contra hP
        have : (P : ℝ) = 0 := le_antisymm (not_lt.mp hP) (Nat.cast_nonneg _)
        have h2' : (J : ℝ) * b = 0 := by rw [h2, this]; simp
        linarith [mul_pos hJR hb]
      refine ⟨(J : ℚ) / P, ?_⟩
      push_cast
      field_simp
      linarith
    · have hqR : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero hq
      have hQR : (0 : ℝ) < Q := by exact_mod_cast Nat.pos_of_ne_zero hQ
      have e : ((j : ℝ) * Q + q * P) * a = ((J : ℝ) * q + p * Q) * b := by
        have : (Q : ℝ) * (j * a - p * b) = q * (J * b - P * a) := by
          have e1 : (j : ℝ) * a - p * b = q * c := by linarith
          have e2 : (J : ℝ) * b - P * a = Q * c := by linarith
          rw [e1, e2]; ring
        linarith
      have hpos : (0 : ℝ) < (j : ℝ) * Q + q * P := by positivity
      refine ⟨((J : ℚ) * q + p * Q) / (j * Q + q * P), ?_⟩
      push_cast
      field_simp
      linarith
  obtain ⟨r, hr⟩ := key
  refine ⟨r, ((p' : ℚ) + q' / r) / j', hr, ?_⟩
  have hrpos : (0 : ℝ) < r := by
    by_contra h
    have : (r : ℝ) * b ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (not_lt.mp h) hb.le
    linarith
  have hb' : b = a / r := by rw [hr]; field_simp
  push_cast
  rw [hb'] at h3
  field_simp
  field_simp at h3
  linarith

/-- **Counting step of Lemma 10.4 / 10.6.**  A finite digraph in which every vertex has in-degree at most one, every vertex with an incoming link has an outgoing link
(a normal vertex), and some vertex has an outgoing link and no incoming one (a centre or a star), is impossible. -/
theorem link_graph_contra {V : Type*} [Fintype V] [DecidableEq V] (E : Finset (V × V))
    (hin : ∀ v, (E.filter fun e => e.2 = v).card ≤ 1)
    (hout : ∀ v, 0 < (E.filter fun e => e.2 = v).card → 0 < (E.filter fun e => e.1 = v).card)
    (c : V) (hc_out : 0 < (E.filter fun e => e.1 = c).card) (hc_in : (E.filter fun e => e.2 = c).card = 0) : False := by
  have := digraph_balance E hin hout c
  omega

/-- indicator -/
noncomputable def ind (p : Prop) : ℕ := if p then 1 else 0

theorem ind_mod (p : Prop) : ind p % 2 = ind p := by
  unfold ind; split_ifs <;> simp

theorem ray_parity {α : Type*} (u v x : α) :
    (ind (u = x) + ind (v = x)) % 2 = ind (u ≠ v ∧ (u = x ∨ v = x)) := by
  unfold ind
  by_cases h1 : u = x <;> by_cases h2 : v = x <;> simp [h1, h2] <;> (try (intro h; subst h; simp_all))

/-- **Cyclic parity.**  Sectors `i : Fin k` of a cyclic fan with left edge label `l i` and right edge label `r i`; ray `i` is shared by sector `i` (right) and `i+1` (left).  The number of edge ends
labelled `x` is congruent mod 2 to the number of mismatched rays that carry `x` on one side. -/
theorem cyc_parity {k : ℕ} [NeZero k] {α : Type*} (l r : Fin k → α) (x : α) :
    (∑ i, (ind (r i = x) + ind (l i = x))) % 2 = (∑ i, ind (r i ≠ l (i + 1) ∧ (r i = x ∨ l (i + 1) = x))) % 2 := by
  have hre : ∑ i, ind (l i = x) = ∑ i, ind (l (i + 1) = x) :=
    (Equiv.sum_comp (Equiv.addRight (1 : Fin k)) (fun i => ind (l i = x))).symm
  rw [Finset.sum_add_distrib, hre, ← Finset.sum_add_distrib, Finset.sum_nat_mod, Finset.sum_nat_mod (s := Finset.univ) (f := fun i => ind (r i ≠ l (i + 1) ∧ (r i = x ∨ l (i + 1) = x)))]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact (ray_parity (r i) (l (i + 1)) x).trans (ind_mod _).symm

/-- **Lemma 10.3 (combinatorial core).**  A cyclic fan of 5 sectors with `types ty` (0 = alpha, 1 = beta, 2 = gamma; counts 0, 2, 3, a "centre"), each sector's two edge labels being the two sides not
opposite its type (side `0` = a, `1` = b, `2` = c).  Then some mismatched ray carries `a` and `b`, or there are mismatched rays carrying `a,c` and carrying `b,c`. -/
theorem centre_ab_or_ac_bc {k : ℕ} [NeZero k] (ty l r : Fin k → Fin 3)
    (hl : ∀ i, l i ≠ ty i) (hr : ∀ i, r i ≠ ty i) (hlr : ∀ i, l i ≠ r i)
    (h0 : (Finset.univ.filter fun i => ty i = 0).card = 0) (h1 : (Finset.univ.filter fun i => ty i = 1).card = 2)
    (h2 : (Finset.univ.filter fun i => ty i = 2).card = 3) :
    (∃ i, (r i = 0 ∧ l (i + 1) = 1) ∨ (r i = 1 ∧ l (i + 1) = 0)) ∨
    ((∃ i, (r i = 0 ∧ l (i + 1) = 2) ∨ (r i = 2 ∧ l (i + 1) = 0)) ∧ (∃ i, (r i = 1 ∧ l (i + 1) = 2) ∨ (r i = 2 ∧ l (i + 1) = 1))) := by
  -- ends of label x: sector i has the label x on exactly one of its two edges iff ty i ≠ x
  have hend : ∀ (x : Fin 3) i, ind (r i = x) + ind (l i = x) = ind (ty i ≠ x) := by
    intro x i
    have a1 := hl i; have a2 := hr i; have a3 := hlr i
    unfold ind
    revert a1 a2 a3
    generalize l i = u; generalize r i = v; generalize ty i = t
    revert u v t
    fin_cases x <;> intro u v t <;> fin_cases u <;> fin_cases v <;> fin_cases t <;> simp
  have hsum : ∀ x : Fin 3, ∑ i, (ind (r i = x) + ind (l i = x)) = (Finset.univ.filter fun i => ty i ≠ x).card := by
    intro x
    simp_rw [hend x]
    unfold ind
    rw [Finset.card_filter]
    exact Finset.sum_congr rfl fun i _ => by split_ifs <;> rfl
  have c0 : (Finset.univ.filter fun i => ty i ≠ 0).card = 5 := by
    have : (Finset.univ.filter fun i => ty i ≠ 0) = (Finset.univ.filter fun i => ty i = 1) ∪ (Finset.univ.filter fun i => ty i = 2) := by
      ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]; revert i; generalize ty = t
      intro i; generalize t i = z; revert z; decide
    rw [this, Finset.card_union_of_disjoint, h1, h2]
    rw [Finset.disjoint_filter]; intro i _ a b; rw [a] at b; exact absurd b (by decide)
  have c1 : (Finset.univ.filter fun i => ty i ≠ 1).card = 3 := by
    have : (Finset.univ.filter fun i => ty i ≠ 1) = (Finset.univ.filter fun i => ty i = 0) ∪ (Finset.univ.filter fun i => ty i = 2) := by
      ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]; revert i; generalize ty = t
      intro i; generalize t i = z; revert z; decide
    rw [this, Finset.card_union_of_disjoint, h0, h2]
    rw [Finset.disjoint_filter]; intro i _ a b; rw [a] at b; exact absurd b (by decide)
  have p0 := cyc_parity l r 0
  have p1 := cyc_parity l r 1
  rw [hsum, c0] at p0
  rw [hsum, c1] at p1
  have e0 : 0 < ∑ i, ind (r i ≠ l (i + 1) ∧ (r i = 0 ∨ l (i + 1) = 0)) := by
    by_contra h; have : ∑ i, ind (r i ≠ l (i + 1) ∧ (r i = 0 ∨ l (i + 1) = 0)) = 0 := by omega
    rw [this] at p0; omega
  have e1 : 0 < ∑ i, ind (r i ≠ l (i + 1) ∧ (r i = 1 ∨ l (i + 1) = 1)) := by
    by_contra h; have : ∑ i, ind (r i ≠ l (i + 1) ∧ (r i = 1 ∨ l (i + 1) = 1)) = 0 := by omega
    rw [this] at p1; omega
  obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero (Nat.pos_iff_ne_zero.mp e0)
  obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero (Nat.pos_iff_ne_zero.mp e1)
  have hi' : r i ≠ l (i + 1) ∧ (r i = 0 ∨ l (i + 1) = 0) := by
    by_contra hh; exact hi (by simp [ind, hh])
  have hj' : r j ≠ l (j + 1) ∧ (r j = 1 ∨ l (j + 1) = 1) := by
    by_contra hh; exact hj (by simp [ind, hh])
  obtain ⟨hi1, hi2⟩ := hi'
  obtain ⟨hj1, hj2⟩ := hj'
  have fi : ∀ u v : Fin 3, u ≠ v → (u = 0 ∨ v = 0) → (u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 0) ∨ (u = 0 ∧ v = 2) ∨ (u = 2 ∧ v = 0) := by decide
  have fj : ∀ u v : Fin 3, u ≠ v → (u = 1 ∨ v = 1) → (u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 0) ∨ (u = 1 ∧ v = 2) ∨ (u = 2 ∧ v = 1) := by decide
  rcases fi _ _ hi1 hi2 with a | a | a | a
  · exact Or.inl ⟨i, Or.inl a⟩
  · exact Or.inl ⟨i, Or.inr a⟩
  · rcases fj _ _ hj1 hj2 with b | b | b | b
    · exact Or.inl ⟨j, Or.inl b⟩
    · exact Or.inl ⟨j, Or.inr b⟩
    · exact Or.inr ⟨⟨i, Or.inl a⟩, ⟨j, Or.inl b⟩⟩
    · exact Or.inr ⟨⟨i, Or.inl a⟩, ⟨j, Or.inr b⟩⟩
  · rcases fj _ _ hj1 hj2 with b | b | b | b
    · exact Or.inl ⟨j, Or.inl b⟩
    · exact Or.inl ⟨j, Or.inr b⟩
    · exact Or.inr ⟨⟨i, Or.inr a⟩, ⟨j, Or.inl b⟩⟩
    · exact Or.inr ⟨⟨i, Or.inr a⟩, ⟨j, Or.inr b⟩⟩

/-- **Lemma 10.5 (combinatorial core).**  Linear fan of `m + 1` sectors `0..m` (left/right edge labels `l i`, `r i`; interior ray `j` is shared by sectors `j`, `j+1`).  If the first edge (`l 0`) is `x`, the last edge
(`r m`) is not `x`, and the number of `x`-ends is even, then some interior ray is mismatched and carries `x`. -/
theorem lin_parity {α : Type*} (l r : ℕ → α) (x : α) (m : ℕ) (h0 : l 0 = x) (hm : r m ≠ x)
    (hev : (∑ i ∈ Finset.range (m + 1), (ind (l i = x) + ind (r i = x))) % 2 = 0) :
    ∃ j, j < m ∧ r j ≠ l (j + 1) ∧ (r j = x ∨ l (j + 1) = x) := by
  have key : ∀ m, (∑ i ∈ Finset.range (m + 1), (ind (l i = x) + ind (r i = x))) % 2 =
      (ind (l 0 = x) + ind (r m = x) + ∑ j ∈ Finset.range m, ind (r j ≠ l (j + 1) ∧ (r j = x ∨ l (j + 1) = x))) % 2 := by
    intro m
    induction m with
    | zero => simp [ind]
    | succ n ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ (fun j => ind (r j ≠ l (j + 1) ∧ (r j = x ∨ l (j + 1) = x)))]
      have rp := ray_parity (r n) (l (n + 1)) x
      omega
  by_contra hno
  push Not at hno
  have hz : ∑ j ∈ Finset.range m, ind (r j ≠ l (j + 1) ∧ (r j = x ∨ l (j + 1) = x)) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    have := hno j (Finset.mem_range.mp hj)
    simp only [ind]; split_ifs with h
    · rcases this h.1 with ⟨n1, n2⟩
      rcases h.2 with h' | h'
      · exact absurd h' n1
      · exact absurd h' n2
    · rfl
  have := key m
  have i1 : ind (l 0 = x) = 1 := by simp [ind, h0]
  have i2 : ind (r m = x) = 0 := by simp [ind, hm]
  rw [hz, i1, i2] at this
  omega

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.thm107_algebra
#print axioms Erdos634.Draft.LaczFormal.RG.link_graph_contra
#print axioms Erdos634.Draft.LaczFormal.RG.cyc_parity
#print axioms Erdos634.Draft.LaczFormal.RG.centre_ab_or_ac_bc
#print axioms Erdos634.Draft.LaczFormal.RG.lin_parity
