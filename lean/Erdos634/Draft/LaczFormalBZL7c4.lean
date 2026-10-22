-- Draft/LaczFormalBZL7c4.lean -- the flux identity of the invariant Phi (Beeson-Zhang Sect. 4-5; Laczkovich DCG 48 (2012) p. 351, 365) for a congruent dissection of an ARBITRARY triangle target by the tile (alpha, pi/3 - alpha, 2 pi/3):
--   `bz_phi_gen` : alpha not in Q pi, a, b commensurable, c not commensurable with a, and a grid character G whose tile flux is weight(c-edge) * K  ==>
--                  K * sum_j n_j * weight(target side j) = flux of the target,   n_j = number of c-edges on side j.
-- (LaczFormalBZPhi3 `bz_phi_eq` is the equilateral case with n_0 = n_1 = n_2.)  The interior c-edges cancel by a Q-linear functional (phi a = phi b = 0, phi c = 1) applied to `interior_flux_zero`.
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), p. 351, 365), Beeson-Zhang (arXiv 2604.01314v1, Lemma 4.1, Thm 5.2, 5.3).
import Erdos634.Draft.LaczFormalBZPhi3

open scoped Classical

namespace Erdos634.Geometry

variable {N : ℕ}

theorem bz_phi_gen (D : CongruentDissection N) {α a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (h : D.model.TwoPiThreeData α a b c)
    (hab : ∃ p q : ℕ, 0 < p ∧ 0 < q ∧ (p : ℝ) * a = (q : ℝ) * b)
    (hc : ¬ ∃ r : ℚ, c = (r : ℝ) * a)
    (G : GridChar ℝ) (hsq : ∀ l ∈ G.L, G.chi l * G.chi l = 1) (K : ℝ)
    (hfl : ∀ (T : Tri) (kg : Fin 3), T.TwoPiThreeData α a b c → T.angleAt kg = 2 * Real.pi / 3 →
      T.flux G.weight = G.weight (T.leftUnit (kg + 1)) * K) :
    K * ∑ j : Fin 3, ((((D.sideEdges j).filter (fun e => D.eLen e = c)).card : ℕ) : ℝ) * G.weight (D.target.leftUnit j)
      = D.target.flux G.weight := by
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
  -- the flux identity
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
  have hside : ∀ j : Fin 3, ∑ e ∈ D.sideEdges j, g' e =
      ((((D.sideEdges j).filter (fun e => D.eLen e = c)).card : ℕ) : ℝ) * G.weight (D.target.leftUnit j) := by
    intro j
    have : ∀ e ∈ D.sideEdges j, g' e = if D.eLen e = c then G.weight (D.target.leftUnit j) else 0 := by
      intro e he
      have hsub : D.eSet e ⊆ D.target.edge j := (Finset.mem_filter.mp he).2
      simp only [g']
      rw [D.eDir_of_side hsub]
    rw [Finset.sum_congr rfl this, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have hcancel := D.flux_cancel G.weight G.weight_odd
  rw [← hcancel]
  have h1 : ∑ i, (D.tile i).flux G.weight = K * ∑ i, G.weight ((D.tile i).leftUnit (kg i + 1)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [hflux i]; ring
  rw [h1, hS1, hsplit, hint0, zero_add]
  congr 1
  exact (Finset.sum_congr rfl fun j _ => (hside j).symm)

end Erdos634.Geometry

#print axioms Erdos634.Geometry.bz_phi_gen
