import Erdos634.Draft.F1c4aSide
import Erdos634.Draft.FluxDRow4Bk
import Erdos634.Draft.FluxCRow5TwoPiThreeFull
import Erdos634.Draft.CompositeE5Gen

open scoped Classical

namespace Erdos634.Draft.F1KappaSide

open Erdos634.Geometry Erdos634.Draft.TheoremPConditional Erdos634.Draft.F1c4aSide

private lemma c_sq' (T : Tri) {α a b c : ℝ} (h : T.TwoPiThreeData α a b c) :
    c ^ 2 = a ^ 2 + a * b + b ^ 2 := by
  obtain ⟨σ, -, ha, -, hb, hγ, hc⟩ := h
  have hl := T.lawCos_perm σ
  rw [ha, hb, hc, hγ,
      show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 from by ring,
      Real.cos_pi_sub, Real.cos_pi_div_three] at hl
  linarith

/-- general form of `F1c4aSide.tile_b_edge_gamma`: needs only `b ≠ a`, `b ≠ c`, `a ≠ c`. -/
lemma tile_b_edge_gamma_gen {N : ℕ} (D : CongruentDissection N) {α a b c : ℝ}
    (hm : D.model.TwoPiThreeData α a b c) (hba : b ≠ a) (hbc : b ≠ c) (hac : a ≠ c)
    (j : Fin N) (k : Fin 3) (hk : dist ((D.tile j).pts k) ((D.tile j).pts (k + 1)) = b) :
    (D.tile j).localAngle ((D.tile j).pts k) = 2 * Real.pi / 3 ∨
    (D.tile j).localAngle ((D.tile j).pts (k + 1)) = 2 * Real.pi / 3 := by
  obtain ⟨-, hc0, ha0, hb0⟩ := cos_alpha_of_TwoPiThree D.model hm
  have hc2 : c ^ 2 = a ^ 2 + a * b + b ^ 2 := c_sq' D.model hm
  have hmulti := (D.tiles_congruent j).sideMultiset_eq
  have hmodel_mem : ∀ t : Fin 3, D.model.oppLen t ∈
      ({dist (D.model.pts 0) (D.model.pts 1), dist (D.model.pts 2) (D.model.pts 0),
        dist (D.model.pts 1) (D.model.pts 2)} : Multiset ℝ) := by
    intro t
    have hshift := Tri.sideMultiset_shift D.model t
    rw [← hshift]
    simp [Tri.oppLen]
  obtain ⟨σ, -, ha_op, -, hb_op, -, hc_op⟩ := hm
  have ha_mem := hmodel_mem (σ 0)
  have hc_mem := hmodel_mem (σ 2)
  rw [ha_op] at ha_mem
  rw [hc_op] at hc_mem
  rw [← hmulti] at ha_mem hc_mem
  simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at ha_mem hc_mem
  apply gamma_of_yz (D.tile j) k ha0 hb0 hc2 hk
  have key : ∀ x y z : ℝ, x = b → (a = x ∨ a = y ∨ a = z) → (c = x ∨ c = y ∨ c = z) →
      (y = a ∧ z = c) ∨ (y = c ∧ z = a) := by
    intro x y z hx h1 h2
    subst hx
    rcases h1 with h | h | h <;> rcases h2 with h' | h' | h'
    all_goals first
      | (exfalso; exact hba h.symm)
      | (exfalso; exact hbc h'.symm)
      | (exfalso; exact hac (h.trans h'.symm))
      | (first | exact Or.inl ⟨h.symm, h'.symm⟩ | exact Or.inr ⟨h'.symm, h.symm⟩)
  have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by fin_cases k <;> simp
  rcases hk3 with rfl | rfl | rfl
  · have e1 : (0 : Fin 3) + 1 = 1 := rfl
    have e2 : (0 : Fin 3) + 2 = 2 := rfl
    rw [e1] at hk; rw [e1, e2]
    exact key _ _ _ hk (by tauto) (by tauto)
  · have e1 : (1 : Fin 3) + 1 = 2 := rfl
    have e2 : (1 : Fin 3) + 2 = 0 := rfl
    rw [e1] at hk; rw [e1, e2]
    exact key _ _ _ hk (by tauto) (by tauto)
  · have e1 : (2 : Fin 3) + 1 = 0 := rfl
    have e2 : (2 : Fin 3) + 2 = 1 := rfl
    rw [e1] at hk; rw [e1, e2]
    exact key _ _ _ hk (by tauto) (by tauto)

/-- one `b`-edge per tile (lengths `a, b, c` pairwise distinct). -/
lemma b_edge_unique_F1 {N : ℕ} (D : CongruentDissection N) {α a b c : ℝ}
    (hm : D.model.TwoPiThreeData α a b c) (hba : b ≠ a) (hbc : b ≠ c) (i : Fin N)
    {k k' : Fin 3} (hk : D.eLen (i, k) = b) (hk' : D.eLen (i, k') = b) : k = k' := by
  obtain ⟨σ', hσ'⟩ := (D.tiles_congruent i).exists_perm
  have hopp : ∀ k : Fin 3, D.eLen (i, k) = (D.tile i).oppLen (k + 2) := by
    intro k
    unfold Tri.oppLen Dissection.eLen
    rw [show k + 2 + 1 = k by fin_cases k <;> rfl, show k + 2 + 2 = k + 1 by fin_cases k <;> rfl]
  obtain ⟨τ, -, o0, -, o1, -, o2⟩ := hm
  have key : ∀ m : Fin 3, D.model.oppLen m = b → m = τ 1 := by
    intro m hmb
    obtain ⟨t, rfl⟩ := τ.surjective m
    fin_cases t
    · exact absurd (o0.symm.trans hmb) (Ne.symm hba)
    · rfl
    · exact absurd (o2.symm.trans hmb) (Ne.symm hbc)
  rw [hopp, (hσ' _).2] at hk hk'
  have e1 := key _ hk
  have e2 := key _ hk'
  have : σ' (k + 2) = σ' (k' + 2) := e1.trans e2.symm
  have := σ'.injective this
  simpa using this

/-- side decomposition on an arbitrary side `j`, with the "no `a`, no `c`" criterion. -/
theorem side_decomp_j {N : ℕ} (D : CongruentDissection N) {α a b c : ℝ}
    (h : D.model.TwoPiThreeData α a b c) (hac : a ≠ c) (hbc : b ≠ c) (hba : b ≠ a) (j : Fin 3) :
    ∃ p q r : ℕ, dist (D.target.pts j) (D.target.pts (j + 1)) = (p : ℝ) * a + (q : ℝ) * b + (r : ℝ) * c ∧
      (p = 0 → r = 0 → ∀ e ∈ D.sideEdges j, D.eLen e = b) := by
  set s := D.sideEdges j
  set len := D.eLen
  have hsum := D.toDissection.side_len_sum j
  set s' := s.filter fun e => ¬ len e = a
  refine ⟨(s.filter fun e => len e = a).card, (s'.filter fun e => len e = b).card,
    (s'.filter fun e => ¬ len e = b).card, ?_, ?_⟩
  · rw [← hsum, ← Finset.sum_filter_add_sum_filter_not s (fun e => len e = a),
      ← Finset.sum_filter_add_sum_filter_not s' (fun e => len e = b)]
    have hA : ∑ e ∈ s.filter (fun e => len e = a), len e
        = ((s.filter fun e => len e = a).card : ℝ) * a := by
      rw [Finset.sum_congr rfl (fun e he => (Finset.mem_filter.mp he).2),
        Finset.sum_const, nsmul_eq_mul]
    have hB : ∑ e ∈ s'.filter (fun e => len e = b), len e
        = ((s'.filter fun e => len e = b).card : ℝ) * b := by
      rw [Finset.sum_congr rfl (fun e he => (Finset.mem_filter.mp he).2),
        Finset.sum_const, nsmul_eq_mul]
    have hC : ∑ e ∈ s'.filter (fun e => ¬ len e = b), len e
        = ((s'.filter fun e => ¬ len e = b).card : ℝ) * c := by
      rw [Finset.sum_congr rfl (fun e he => ?_), Finset.sum_const, nsmul_eq_mul]
      have hm := Finset.mem_filter.mp he
      have hm' := Finset.mem_filter.mp hm.1
      rcases Row5TwoPiThreeFull.edge_len D h e with h1 | h1 | h1
      · exact absurd h1 hm'.2
      · exact absurd h1 hm.2
      · exact h1
    rw [hA, hB, hC]
    ring
  · intro hp hr e he
    rcases Row5TwoPiThreeFull.edge_len D h e with h1 | h1 | h1
    · exfalso
      have : e ∈ s.filter (fun e => len e = a) := Finset.mem_filter.mpr ⟨he, h1⟩
      have := Finset.card_pos.mpr ⟨e, this⟩
      omega
    · exact h1
    · exfalso
      have hne1 : ¬ len e = a := fun hh => hac (hh.symm.trans h1)
      have hne2 : ¬ len e = b := fun hh => hbc (hh.symm.trans h1)
      have : e ∈ s'.filter (fun e => ¬ len e = b) :=
        Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨he, hne1⟩, hne2⟩
      have := Finset.card_pos.mpr ⟨e, this⟩
      omega

/-- **The word is `b^κ`.**  `(Ma, Mb, N, κ)` with `Ma Mb = N`, `Mb = Ma + 2κ`, `c (Mb − Ma) = a (Mb + Ma)`, and
`(Ma + Mb)² + 12 N` not a perfect square: `P a + Q b + R c = κ b` forces `P = R = 0`. -/
theorem word_irr {a b c : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hc2 : c ^ 2 = a ^ 2 + a * b + b ^ 2) (Ma Mb N κ : ℕ) (hκ0 : 0 < κ) (hprod : Ma * Mb = N)
    (hκ : Mb = Ma + 2 * κ) (hcr : c * ((Mb : ℝ) - Ma) = a * ((Mb : ℝ) + Ma))
    (hns : ¬ IsSquare (((Ma : ℤ) + Mb) ^ 2 + 12 * (N : ℤ))) (P Q R : ℕ)
    (hsum : (P : ℝ) * a + Q * b + R * c = κ * b) : P = 0 ∧ R = 0 := by
  have hd : ((Mb : ℝ) - Ma) = 2 * κ := by
    have : (Mb : ℝ) = Ma + 2 * κ := by exact_mod_cast hκ
    linarith
  have hdpos : (0 : ℝ) < (Mb : ℝ) - Ma := by rw [hd]; positivity
  have hS : (0 : ℝ) < (Mb : ℝ) + Ma := by
    have : (0 : ℝ) ≤ Ma := Nat.cast_nonneg _
    have : (0 : ℝ) < Mb := by
      have : 0 < Mb := by omega
      exact_mod_cast this
    linarith
  -- a W = b d (κ − Q),  W = P d + R (Mb + Ma)
  have key : a * ((P : ℝ) * ((Mb : ℝ) - Ma) + R * ((Mb : ℝ) + Ma)) =
      b * ((Mb : ℝ) - Ma) * ((κ : ℝ) - Q) := by
    linear_combination ((Mb : ℝ) - Ma) * hsum - (R : ℝ) * hcr
  by_cases hQ : Q = κ
  · subst hQ
    have h0 : a * ((P : ℝ) * ((Mb : ℝ) - Ma) + R * ((Mb : ℝ) + Ma)) = 0 := by rw [key]; ring
    have hW : (P : ℝ) * ((Mb : ℝ) - Ma) + R * ((Mb : ℝ) + Ma) = 0 :=
      (mul_eq_zero.mp h0).resolve_left ha.ne'
    have hP : (P : ℝ) * ((Mb : ℝ) - Ma) = 0 := by
      have h1 : 0 ≤ (P : ℝ) * ((Mb : ℝ) - Ma) := by positivity
      have h2 : 0 ≤ (R : ℝ) * ((Mb : ℝ) + Ma) := by positivity
      linarith
    have hR : (R : ℝ) * ((Mb : ℝ) + Ma) = 0 := by
      have h1 : 0 ≤ (P : ℝ) * ((Mb : ℝ) - Ma) := by positivity
      have h2 : 0 ≤ (R : ℝ) * ((Mb : ℝ) + Ma) := by positivity
      linarith
    refine ⟨?_, ?_⟩
    · have := (mul_eq_zero.mp hP).resolve_right hdpos.ne'
      exact_mod_cast this
    · have := (mul_eq_zero.mp hR).resolve_right hS.ne'
      exact_mod_cast this
  · exfalso
    apply hns
    -- K = 2 W' + d (κ − Q), L = κ − Q, with W' = P d + R (Mb+Ma) (integers)
    set L : ℤ := (κ : ℤ) - Q with hLdef
    set dz : ℤ := (Mb : ℤ) - Ma with hdz
    set W : ℤ := (P : ℤ) * dz + R * ((Mb : ℤ) + Ma) with hWdef
    have hL0 : L ≠ 0 := by
      intro h; apply hQ; omega
    have hLR : (L : ℝ) = (κ : ℝ) - Q := by rw [hLdef]; push_cast; ring
    have hdR : (dz : ℝ) = (Mb : ℝ) - Ma := by rw [hdz]; push_cast; ring
    have hWR : (W : ℝ) = (P : ℝ) * ((Mb : ℝ) - Ma) + R * ((Mb : ℝ) + Ma) := by
      rw [hWdef]; push_cast; rw [hdR]
    have key' : a * (W : ℝ) = b * (dz : ℝ) * (L : ℝ) := by
      rw [hWR, hdR, hLR]; exact key
    refine Erdos634.Draft.CompositeE5Gen.isSquare_of_rat_sq _ (2 * W + dz * L) L hL0 ?_
    -- (2b + a) d = a (Mb + Ma) ... (2b+a)² d² = a² [(Ma+Mb)² + 12 N]
    have hN : (N : ℝ) = (Ma : ℝ) * Mb := by exact_mod_cast hprod.symm
    have h4 : ((2 * b + a) * ((Mb : ℝ) - Ma)) ^ 2 =
        a ^ 2 * (((Ma : ℝ) + Mb) ^ 2 + 12 * (N : ℝ)) := by
      have e1 : (c * ((Mb : ℝ) - Ma)) ^ 2 = (a * ((Mb : ℝ) + Ma)) ^ 2 := by rw [hcr]
      rw [hN]
      linear_combination (-4 * ((Mb : ℝ) - Ma) ^ 2) * hc2 + 4 * e1
    have hKR : ((2 * W + dz * L : ℤ) : ℝ) * a = ((2 * b + a) * ((Mb : ℝ) - Ma)) * (L : ℝ) := by
      push_cast
      rw [hdR] at key' ⊢
      linear_combination 2 * key'
    have hLne : (L : ℝ) ≠ 0 := by exact_mod_cast hL0
    have ha2 : a ^ 2 ≠ 0 := by positivity
    have h5 : (((2 * W + dz * L : ℤ) : ℝ)) ^ 2 =
        (L : ℝ) ^ 2 * (((Ma : ℝ) + Mb) ^ 2 + 12 * (N : ℝ)) := by
      have : a ^ 2 * (((2 * W + dz * L : ℤ) : ℝ)) ^ 2 =
          a ^ 2 * ((L : ℝ) ^ 2 * (((Ma : ℝ) + Mb) ^ 2 + 12 * (N : ℝ))) := by
        calc a ^ 2 * (((2 * W + dz * L : ℤ) : ℝ)) ^ 2
            = (((2 * W + dz * L : ℤ) : ℝ) * a) ^ 2 := by ring
          _ = (((2 * b + a) * ((Mb : ℝ) - Ma)) * (L : ℝ)) ^ 2 := by rw [hKR]
          _ = (L : ℝ) ^ 2 * (((2 * b + a) * ((Mb : ℝ) - Ma)) ^ 2) := by ring
          _ = (L : ℝ) ^ 2 * (a ^ 2 * (((Ma : ℝ) + Mb) ^ 2 + 12 * (N : ℝ))) := by rw [h4]
          _ = a ^ 2 * ((L : ℝ) ^ 2 * (((Ma : ℝ) + Mb) ^ 2 + 12 * (N : ℝ))) := by ring
      exact mul_left_cancel₀ ha2 this
    rw [div_pow, h5]
    push_cast
    field_simp

end Erdos634.Draft.F1KappaSide
