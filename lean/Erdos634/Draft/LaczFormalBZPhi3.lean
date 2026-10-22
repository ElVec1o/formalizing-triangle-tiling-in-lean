-- Draft/LaczFormalBZPhi3.lean -- the Phi-contradiction (Beeson-Zhang Sect. 4-5) for an equilateral target, formal.  See LaczFormalBZPhi2 for the overview.
-- UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), p. 351, 365: Phi), Beeson-Zhang (arXiv 2604.01314v1, Lemma 4.1, Thm 5.2).
import Erdos634.Draft.LaczFormalBZPhi2

open scoped Classical

namespace Erdos634.Geometry

variable {N : ℕ}

theorem Dissection.eLen_eq_oppLen (D : Dissection N) (e : Fin N × Fin 3) :
    D.eLen e = (D.tile e.1).oppLen (e.2 + 2) := by
  unfold Dissection.eLen Tri.oppLen
  have e1 : e.2 + 2 + 1 = e.2 := by obtain ⟨_, k⟩ := e; fin_cases k <;> rfl
  have e2 : e.2 + 2 + 2 = e.2 + 1 := by obtain ⟨_, k⟩ := e; fin_cases k <;> rfl
  rw [e1, e2]

/-- Classification of the edge lengths of a congruent dissection by the angle opposite the edge. -/
theorem CongruentDissection.edge_class (D : CongruentDissection N) {α a b c : ℝ} (h : D.model.TwoPiThreeData α a b c)
    (e : Fin N × Fin 3) :
    ((D.tile e.1).angleAt (e.2 + 2) = 2 * Real.pi / 3 ∧ D.eLen e = c) ∨
      ((D.tile e.1).angleAt (e.2 + 2) ≠ 2 * Real.pi / 3 ∧ (D.eLen e = a ∨ D.eLen e = b)) := by
  have hT : (D.tile e.1).TwoPiThreeData α a b c := Tri.TwoPiThreeData.of_congruent (D.tiles_congruent e.1) h
  have hr := (hT.alpha_range)
  have hpi := Real.pi_pos
  rw [D.eLen_eq_oppLen]
  rcases hT.cases (e.2 + 2) with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨h1, h2⟩
  · right
    refine ⟨?_, Or.inl h2⟩
    rw [h1]; intro hh; linarith [hr.1, hr.2]
  · right
    refine ⟨?_, Or.inr h2⟩
    rw [h1]; intro hh; linarith [hr.1, hr.2]

/-- **The `c`-count identity of the invariant Phi** (Beeson-Zhang, Sect. 4-5; their Lemma 4.1 and the sawtooth argument, replaced by a `Q`-linear functional).
For a congruent dissection of a triangle with equal sides by the tile `(α, π/3 - α, 2π/3)` (`α ∉ ℚπ`) with `a, b` commensurable and `c` not a rational multiple of `a`, and for any `±1` grid character `G`
whose tile flux is `weight(c-edge) * K`:  `K * X = L`, where `X` is the number of `c`-edges on a side (the same on all three sides) and `L` the side length. -/
theorem bz_phi_eq (D : CongruentDissection N) {α a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (h : D.model.TwoPiThreeData α a b c)
    (hab : ∃ p q : ℕ, 0 < p ∧ 0 < q ∧ (p : ℝ) * a = (q : ℝ) * b)
    (hc : ¬ ∃ r : ℚ, c = (r : ℝ) * a)
    (heq : ∀ j : Fin 3, dist (D.target.pts j) (D.target.pts (j + 1)) = dist (D.target.pts 0) (D.target.pts 1))
    (G : GridChar ℝ) (hsq : ∀ l ∈ G.L, G.chi l * G.chi l = 1) (K : ℝ)
    (hfl : ∀ (T : Tri) (kg : Fin 3), T.TwoPiThreeData α a b c → T.angleAt kg = 2 * Real.pi / 3 →
      T.flux G.weight = G.weight (T.leftUnit (kg + 1)) * K) :
    K * ((((D.sideEdges 0).filter (fun e => D.eLen e = c)).card : ℕ) : ℝ) = dist (D.target.pts 0) (D.target.pts 1) := by
  classical
  have hne_ab : a ≠ b := h.a_ne_b hα
  have hca : c ≠ a := fun e => hc ⟨1, by rw [e]; simp⟩
  obtain ⟨p, q, hp, hq, hpq⟩ := hab
  have hqR : (q : ℝ) ≠ 0 := by positivity
  have hcb : c ≠ b := by
    intro e
    apply hc
    refine ⟨(p : ℚ) / (q : ℚ), ?_⟩
    rw [e]
    push_cast
    field_simp
    linarith
  have hT : ∀ i, (D.tile i).TwoPiThreeData α a b c := fun i => Tri.TwoPiThreeData.of_congruent (D.tiles_congruent i) h
  -- `eLen = c` iff the opposite angle is `2π/3`
  have hlenC : ∀ e : Fin N × Fin 3, D.eLen e = c ↔ (D.tile e.1).angleAt (e.2 + 2) = 2 * Real.pi / 3 := by
    intro e
    rcases D.edge_class h e with ⟨h1, h2⟩ | ⟨h1, h2 | h2⟩
    · exact ⟨fun _ => h1, fun _ => h2⟩
    · exact ⟨fun hh => absurd (hh.symm.trans h2) hca, fun hh => absurd hh h1⟩
    · exact ⟨fun hh => absurd (hh.symm.trans h2) hcb, fun hh => absurd hh h1⟩
  have hlen3 : ∀ e : Fin N × Fin 3, D.eLen e = c ∨ D.eLen e = a ∨ D.eLen e = b := by
    intro e
    rcases D.edge_class h e with ⟨-, h2⟩ | ⟨-, h2 | h2⟩
    · exact Or.inl h2
    · exact Or.inr (Or.inl h2)
    · exact Or.inr (Or.inr h2)
  -- the Q-linear functional
  obtain ⟨φ, hφa, hφc⟩ := exists_qfunctional hc
  have hφb : φ b = 0 := by
    have e : (q : ℚ) • b = (p : ℚ) • a := by
      rw [Rat.smul_def, Rat.smul_def]; push_cast; linarith
    have e2 := congrArg φ e
    rw [map_smul, map_smul, hφa] at e2
    simp only [smul_eq_mul, mul_zero] at e2
    have hq' : (q : ℚ) ≠ 0 := by positivity
    exact (mul_eq_zero.mp e2).resolve_left hq'
  have hφlen : ∀ e : Fin N × Fin 3, φ (D.eLen e) = if D.eLen e = c then 1 else 0 := by
    intro e
    by_cases he : D.eLen e = c
    · rw [if_pos he, he, hφc]
    · rw [if_neg he]
      rcases hlen3 e with h1 | h1 | h1
      · exact absurd h1 he
      · rw [h1, hφa]
      · rw [h1, hφb]
  have hw1 : ∀ d : Dir, G.weight d = 1 ∨ G.weight d = -1 := fun d => mul_self_eq_one_iff.mp (G.val_sq hsq _)
  -- the signed indicator of c-edges
  let g' : Fin N × Fin 3 → ℝ := fun e => if D.eLen e = c then G.weight (D.eDir e) else 0
  -- (1) interior c-edges cancel
  have hint0 : ∑ e ∈ D.intEdges, g' e = 0 := by
    have hint := D.interior_flux_zero G.weight G.weight_odd
    have hφint := congrArg φ hint
    rw [map_sum, map_zero] at hφint
    have hterm : ∀ e : Fin N × Fin 3, φ (D.eLen e • G.weight (D.eDir e)) =
        (if G.weight (D.eDir e) = 1 then (1 : ℚ) else -1) * (if D.eLen e = c then 1 else 0) := by
      intro e
      rw [smul_eq_mul, mul_comm, ← hφlen e]
      rcases hw1 (D.eDir e) with hh | hh
      · rw [hh]; simp
      · rw [hh]
        have : ¬ ((-1 : ℝ) = 1) := by norm_num
        rw [if_neg this, neg_mul, one_mul, neg_mul, one_mul, map_neg]
    have hcast : ∀ e : Fin N × Fin 3, g' e =
        (((if G.weight (D.eDir e) = 1 then (1 : ℚ) else -1) * (if D.eLen e = c then 1 else 0) : ℚ) : ℝ) := by
      intro e
      simp only [g']
      by_cases he : D.eLen e = c
      · rw [if_pos he, if_pos he, mul_one]
        rcases hw1 (D.eDir e) with hh | hh
        · rw [hh]; simp
        · rw [hh]
          have : ¬ ((-1 : ℝ) = 1) := by norm_num
          rw [if_neg this]; simp
      · rw [if_neg he, if_neg he]; simp
    have hQ : ∑ e ∈ D.intEdges, ((if G.weight (D.eDir e) = 1 then (1 : ℚ) else -1) * (if D.eLen e = c then 1 else 0)) = 0 := by
      exact (Finset.sum_congr rfl fun e _ => (hterm e).symm).trans hφint
    calc ∑ e ∈ D.intEdges, g' e
        = ∑ e ∈ D.intEdges, (((if G.weight (D.eDir e) = 1 then (1 : ℚ) else -1) * (if D.eLen e = c then 1 else 0) : ℚ) : ℝ) :=
          Finset.sum_congr rfl fun e _ => hcast e
      _ = ((∑ e ∈ D.intEdges, ((if G.weight (D.eDir e) = 1 then (1 : ℚ) else -1) * (if D.eLen e = c then 1 else 0)) : ℚ) : ℝ) := by
          push_cast; rfl
      _ = 0 := by rw [hQ]; simp
  -- (2) the same number of c-edges on every side
  set L := dist (D.target.pts 0) (D.target.pts 1) with hL
  have hLpos : 0 < L := dist_pos.mpr fun hh => absurd (D.target.indep.injective hh) (by decide)
  let n : Fin 3 → ℕ := fun j => ((D.sideEdges j).filter (fun e => D.eLen e = c)).card
  have hn : ∀ j, (n j : ℚ) = φ L := by
    intro j
    have h1 := D.side_len_sum j
    rw [heq j] at h1
    have h2 := congrArg φ h1
    rw [map_sum] at h2
    rw [← h2]
    simp only [n]
    rw [Finset.card_filter]
    push_cast
    exact Finset.sum_congr rfl fun e _ => (hφlen e).symm
  have hn01 : n 0 = n 1 := by exact_mod_cast (hn 0).trans (hn 1).symm
  have hn02 : n 0 = n 2 := by exact_mod_cast (hn 0).trans (hn 2).symm
  -- (3) the flux identity
  obtain ⟨kg, hkg⟩ : ∃ kg : Fin N → Fin 3, ∀ i, (D.tile i).angleAt (kg i) = 2 * Real.pi / 3 ∧
      ∀ k, (D.tile i).angleAt k = 2 * Real.pi / 3 → k = kg i := by
    choose kg hkg using fun i => (hT i).gamma_unique
    exact ⟨kg, hkg⟩
  have hflux : ∀ i, (D.tile i).flux G.weight = G.weight ((D.tile i).leftUnit (kg i + 1)) * K :=
    fun i => hfl (D.tile i) (kg i) (hT i) (hkg i).1
  have hS1 : ∑ i, G.weight ((D.tile i).leftUnit (kg i + 1)) = ∑ e : Fin N × Fin 3, g' e := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single (kg i + 1)]
    · have hc1 : D.eLen (i, kg i + 1) = c := by
        rw [hlenC]
        have hk3 : ∀ k : Fin 3, k + 1 + 2 = k := by decide
        show (D.tile i).angleAt (kg i + 1 + 2) = _
        rw [hk3]; exact (hkg i).1
      simp only [g', if_pos hc1]
      rfl
    · intro k _ hk
      have : ¬ D.eLen (i, k) = c := by
        rw [hlenC]
        intro hh
        apply hk
        have h2 := (hkg i).2 (k + 2) hh
        have : k = kg i + 1 := by
          have e3 : k = k + 2 + 1 := by fin_cases k <;> rfl
          rw [e3, h2]
        exact this
      simp only [g', if_neg this]
    · intro hh; exact absurd (Finset.mem_univ _) hh
  have hsplit := D.sum_split g'
  have hside : ∀ j : Fin 3, ∑ e ∈ D.sideEdges j, g' e = (n j : ℝ) * G.weight (D.target.leftUnit j) := by
    intro j
    have : ∀ e ∈ D.sideEdges j, g' e = if D.eLen e = c then G.weight (D.target.leftUnit j) else 0 := by
      intro e he
      have hsub : D.eSet e ⊆ D.target.edge j := (Finset.mem_filter.mp he).2
      simp only [g']
      rw [D.eDir_of_side hsub]
    rw [Finset.sum_congr rfl this, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have hcancel := D.flux_cancel G.weight G.weight_odd
  have htarget : D.target.flux G.weight = L * ∑ j : Fin 3, G.weight (D.target.leftUnit j) := by
    unfold Tri.flux
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [heq j, smul_eq_mul]
  have hsum : K * ((n 0 : ℝ) * ∑ j : Fin 3, G.weight (D.target.leftUnit j)) = L * ∑ j : Fin 3, G.weight (D.target.leftUnit j) := by
    rw [← htarget, ← hcancel]
    have h1 : ∑ i, (D.tile i).flux G.weight = K * ∑ i, G.weight ((D.tile i).leftUnit (kg i + 1)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [hflux i]; ring
    rw [h1, hS1, hsplit, hint0, zero_add]
    congr 1
    rw [Fin.sum_univ_three, Fin.sum_univ_three, hside 0, hside 1, hside 2, ← hn01, ← hn02]
    ring
  have hs3 : ∑ j : Fin 3, G.weight (D.target.leftUnit j) ≠ 0 := by
    rw [Fin.sum_univ_three]
    rcases hw1 (D.target.leftUnit 0) with h0 | h0 <;> rcases hw1 (D.target.leftUnit 1) with h1 | h1 <;>
      rcases hw1 (D.target.leftUnit 2) with h2 | h2 <;> rw [h0, h1, h2] <;> norm_num
  have hX : K * (n 0 : ℝ) = L := by
    have := mul_right_cancel₀ hs3 (by linarith [hsum] : K * (n 0 : ℝ) * ∑ j : Fin 3, G.weight (D.target.leftUnit j) =
      L * ∑ j : Fin 3, G.weight (D.target.leftUnit j))
    exact this
  exact hX

/-- The `f_β` version of the sign lemma. -/
theorem Tri.flux_cedge_beta (T : Tri) {α a b c : ℝ} (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (h : T.TwoPiThreeData α a b c) (kg : Fin 3) (hkg : T.angleAt kg = 2 * Real.pi / 3) :
    T.flux (fBeta α hα).weight = (fBeta α hα).weight (T.leftUnit (kg + 1)) * (c + b - a) := by
  obtain ⟨s, hw, hf⟩ := T.weight_form (fBeta α hα) (GridChar.rankn_sq _ _ _ _ _ _ _) (T.data_angles_mem hα h 1)
  have hk : kg + 1 + 2 = kg := by fin_cases kg <;> rfl
  have hchi : (fBeta α hα).chi ((Real.pi - 2 * Real.pi / 3 : ℝ) : Real.Angle) = -1 := by
    unfold fBeta
    rw [show Real.pi - 2 * Real.pi / 3 = ((1 : ℤ) : ℝ) * (Real.pi / ((3 : ℕ) : ℝ)) + ((0 : ℤ) : ℝ) * α by
      push_cast; ring, GridChar.rankn_chi]
    simp
  have h1 := hw (kg + 1)
  rw [hk, hkg, hchi] at h1
  rw [h1, hf, data_tileValue_beta T hα h]
  ring

/-- **Beeson-Zhang Theorem 5.2 (equilateral target), `c`-part.**  A congruent dissection of an equilateral triangle by the tile `(α, π/3-α, 2π/3)`, `α ∉ ℚπ`, whose sides `a, b` are
commensurable has `c` a rational multiple of `a`: the two invariants `Φ_{f_α}`, `Φ_{f_β}` give `(c+a-b) X = L = (c+b-a) X`, so `(a-b) X = 0`, `X > 0`, `a = b`, contradicting `α ∉ ℚπ`.
(No boundary analysis `Lemma 3.4` and no sawtooth tiles are needed.) -/
theorem bz_c_rational (D : CongruentDissection N) {α a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (h : D.model.TwoPiThreeData α a b c)
    (hab : ∃ p q : ℕ, 0 < p ∧ 0 < q ∧ (p : ℝ) * a = (q : ℝ) * b)
    (heq : ∀ j : Fin 3, dist (D.target.pts j) (D.target.pts (j + 1)) = dist (D.target.pts 0) (D.target.pts 1)) :
    ∃ r : ℚ, c = (r : ℝ) * a := by
  by_contra hc
  have h1 := bz_phi_eq D hα h hab hc heq (fAlpha α hα) (GridChar.rankn_sq _ _ _ _ _ _ _) (c + a - b)
    (fun T kg hT hkg => T.flux_cedge hα hT kg hkg)
  have h2 := bz_phi_eq D hα h hab hc heq (fBeta α hα) (GridChar.rankn_sq _ _ _ _ _ _ _) (c + b - a)
    (fun T kg hT hkg => T.flux_cedge_beta hα hT kg hkg)
  have hLpos : 0 < dist (D.target.pts 0) (D.target.pts 1) := dist_pos.mpr fun hh => absurd (D.target.indep.injective hh) (by decide)
  set X : ℝ := ((((D.sideEdges 0).filter (fun e => D.eLen e = c)).card : ℕ) : ℝ) with hXdef
  have hXpos : 0 < X := by
    by_contra hX
    have : X = 0 := le_antisymm (not_lt.mp hX) (Nat.cast_nonneg _)
    rw [this, mul_zero] at h1
    linarith
  have hab' : (a - b) * X = 0 := by nlinarith [h1, h2]
  rcases mul_eq_zero.mp hab' with h3 | h3
  · exact h.a_ne_b hα (by linarith)
  · exact absurd h3 hXpos.ne'

end Erdos634.Geometry

#print axioms Erdos634.Geometry.bz_phi_eq
#print axioms Erdos634.Geometry.bz_c_rational
