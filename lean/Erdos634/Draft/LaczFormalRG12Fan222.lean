-- Draft/LaczFormalRG12Fan222.lean -- Laczkovich (DCG 48 (2012)), Sect. 6.2 (arrangement of the six tiles around a Gamma_kite vertex, "Fig. 5"), S0c piece (ii), part 2: ABSTRACT fan angle sums.
-- A cyclic fan of six sectors whose widths are the angles `alpha, beta, gamma` (each label twice per turn, `alpha + beta + gamma = pi`).  A ray `u_{j+m}` is OPPOSITE to `u_j` (a straight line through the vertex
-- along tile sides) iff the `m` widths between them add up to `pi` (`run_rotation`, `par_rot_neg_iff`); with `alpha, beta, gamma` pairwise distinct and none equal to `pi/2` this happens only for `m = 3`
-- and three DIFFERENT labels (`straight_run_labels`), and conversely (`straight_of_triple`): a straight line through a (2,2,2) vertex splits its six corners into two triples `{alpha, beta, gamma}`.
-- Tiling-free (hypotheses `AngGen`, `Fan6` are witnessed by the lattice-triangle fan, `fan6_witness`).  NOTE, UNAUDITED.
-- Credit: Laczkovich (DCG 48 (2012), Sect. 6.2, Lemma 4.8 / Fig. 5), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalRG12RunRot

open Erdos634.Draft.LaczFormal.Graph

namespace Erdos634.Draft.LaczFormal.Graph

/-- The three angles `alpha, beta, gamma = ω 0, ω 1, ω 2`: positive, sum `pi`, pairwise distinct, none a right angle. -/
structure AngGen (ω : Fin 3 → ℝ) : Prop where
  pos : ∀ l, 0 < ω l
  sum : ω 0 + ω 1 + ω 2 = Real.pi
  ne01 : ω 0 ≠ ω 1
  ne02 : ω 0 ≠ ω 2
  ne12 : ω 1 ≠ ω 2
  r0 : ω 0 ≠ Real.pi / 2
  r1 : ω 1 ≠ Real.pi / 2
  r2 : ω 2 ≠ Real.pi / 2

/-- **Straight sums**: `a α + b β + c γ = π` with `a, b, c ≤ 2` forces `a = b = c = 1`. -/
theorem straight_run_arith {ω : Fin 3 → ℝ} (G : AngGen ω) {a b c : ℕ} (ha : a ≤ 2) (hb : b ≤ 2) (hc : c ≤ 2)
    (h : (a : ℝ) * ω 0 + b * ω 1 + c * ω 2 = Real.pi) : a = 1 ∧ b = 1 ∧ c = 1 := by
  have p0 := G.pos 0
  have p1 := G.pos 1
  have p2 := G.pos 2
  have hs := G.sum
  have hpi := Real.pi_pos
  interval_cases a <;> interval_cases b <;> interval_cases c <;> norm_num at h ⊢ <;>
    first
    | (exfalso; linarith)
    | exact (G.ne01 (by linarith)).elim
    | exact (G.ne02 (by linarith)).elim
    | exact (G.ne12 (by linarith)).elim
    | exact (G.r0 (by linarith)).elim
    | exact (G.r1 (by linarith)).elim
    | exact (G.r2 (by linarith)).elim

theorem sum_label (f : Fin 3 → ℝ) (ℓ : ℕ → Fin 3) (j m : ℕ) :
    ∑ i ∈ Finset.range m, f (ℓ (j + i)) = ∑ l : Fin 3, (((Finset.range m).filter (fun i => ℓ (j + i) = l)).card : ℝ) * f l := by
  classical
  have h1 : ∀ i, f (ℓ (j + i)) = ∑ l : Fin 3, (if ℓ (j + i) = l then f l else 0) := fun i => by simp
  calc ∑ i ∈ Finset.range m, f (ℓ (j + i)) = ∑ i ∈ Finset.range m, ∑ l : Fin 3, (if ℓ (j + i) = l then f l else 0) :=
        Finset.sum_congr rfl (fun i _ => h1 i)
    _ = ∑ l : Fin 3, ∑ i ∈ Finset.range m, (if ℓ (j + i) = l then f l else 0) := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro l _
      rw [← Finset.sum_filter]
      simp [Finset.sum_const, nsmul_eq_mul]

theorem card_label (ℓ : ℕ → Fin 3) (j m : ℕ) :
    m = ∑ l : Fin 3, ((Finset.range m).filter (fun i => ℓ (j + i) = l)).card := by
  classical
  have := Finset.card_eq_sum_card_fiberwise (s := Finset.range m) (t := (Finset.univ : Finset (Fin 3))) (f := fun i => ℓ (j + i))
    (fun _ _ => Finset.mem_univ _)
  simpa using this

/-- The data of a cyclic fan of six sectors with labelled widths: `u_j` clockwise rays, `v_j` counterclockwise rays, `u_{j+1} ~ v_j`, `wd(u_j, v_j) = ω(ℓ_j)`, every label twice in every window of six. -/
structure Fan6 (ω : Fin 3 → ℝ) (u v : ℕ → V2) (ℓ : ℕ → Fin 3) : Prop where
  hu : ∀ j, u j ≠ 0
  hpar : ∀ j, Par (u (j + 1)) (v j)
  hwd : ∀ j, wd (u j) (v j) = ω (ℓ j)
  hcnt : ∀ j l, ((Finset.range 6).filter (fun i => ℓ (j + i) = l)).card = 2

theorem Fan6.run_sum {ω : Fin 3 → ℝ} {u v : ℕ → V2} {ℓ : ℕ → Fin 3} (F : Fan6 ω u v ℓ) (j m : ℕ) :
    ∑ i ∈ Finset.range m, wd (u (j + i)) (v (j + i)) = ∑ l : Fin 3, (((Finset.range m).filter (fun i => ℓ (j + i) = l)).card : ℝ) * ω l := by
  rw [← sum_label]
  exact Finset.sum_congr rfl (fun i _ => F.hwd (j + i))

theorem Fan6.turn {ω : Fin 3 → ℝ} (G : AngGen ω) {u v : ℕ → V2} {ℓ : ℕ → Fin 3} (F : Fan6 ω u v ℓ) (j : ℕ) :
    ∑ i ∈ Finset.range 6, wd (u (j + i)) (v (j + i)) = 2 * Real.pi := by
  rw [F.run_sum, Fin.sum_univ_three]
  simp only [F.hcnt]
  push_cast
  linarith [G.sum]

/-- **A straight line through the vertex along tile sides splits the six corners into two triples `α, β, γ`.** -/
theorem straight_run_labels {ω : Fin 3 → ℝ} (G : AngGen ω) {u v : ℕ → V2} {ℓ : ℕ → Fin 3} (F : Fan6 ω u v ℓ) (j m : ℕ)
    (hm1 : 1 ≤ m) (hm5 : m ≤ 5) (hstr : Par (u (j + m)) (-(u j).1, -(u j).2)) :
    m = 3 ∧ ℓ j ≠ ℓ (j + 1) ∧ ℓ j ≠ ℓ (j + 2) ∧ ℓ (j + 1) ≠ ℓ (j + 2) := by
  classical
  have hrot := run_rotation (fun i => u (j + i)) (fun i => v (j + i)) (fun i => F.hu _) (fun i => by
    have := F.hpar (j + i); simpa [add_assoc] using this) m
  simp only [add_zero] at hrot
  have hP : Par (rot (∑ i ∈ Finset.range m, wd (u (j + i)) (v (j + i))) (u j)) (-(u j).1, -(u j).2) := (hrot.symm).trans hstr
  obtain ⟨z, hz⟩ := (par_rot_neg_iff _ (F.hu j)).1 hP
  set S := ∑ i ∈ Finset.range m, wd (u (j + i)) (v (j + i)) with hS
  have hpos : ∀ i, 0 < wd (u (j + i)) (v (j + i)) := fun i => by rw [F.hwd]; exact G.pos _
  have hS0 : 0 < S := Finset.sum_pos (fun i _ => hpos i) (Finset.nonempty_range_iff.mpr (by omega))
  have hS6 : S < 2 * Real.pi := by
    rw [← F.turn G j]
    exact Finset.sum_lt_sum_of_subset (Finset.range_subset_range.mpr (by omega : m ≤ 6)) (Finset.mem_range.mpr (show m < 6 by omega))
      (by simp) (hpos m) (fun i _ _ => (hpos i).le)
  have hpi := Real.pi_pos
  have hz0 : z = 0 := by
    have h1 : (-1 : ℝ) < 2 * z := by nlinarith
    have h2 : (2 * z : ℝ) < 1 := by nlinarith
    have h1' : (-1 : ℤ) < 2 * z := by exact_mod_cast h1
    have h2' : 2 * z < (1 : ℤ) := by exact_mod_cast h2
    omega
  have hSpi : S = Real.pi := by rw [hz, hz0]; simp
  rw [hS, F.run_sum, Fin.sum_univ_three] at hSpi
  have hle : ∀ l, ((Finset.range m).filter (fun i => ℓ (j + i) = l)).card ≤ 2 := fun l => by
    rw [← F.hcnt j l]
    exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_subset_range.mpr (by omega)))
  obtain ⟨e0, e1, e2⟩ := straight_run_arith G (hle 0) (hle 1) (hle 2) hSpi
  have hm3 : m = 3 := by
    rw [card_label ℓ j m, Fin.sum_univ_three, e0, e1, e2]
  subst hm3
  have dist3 : ∀ a b : ℕ, a < 3 → b < 3 → a ≠ b → ℓ (j + a) ≠ ℓ (j + b) := by
    intro a b ha hb hab heq
    have hc := hle (ℓ (j + a))
    have hone : ((Finset.range 3).filter (fun i => ℓ (j + i) = ℓ (j + a))).card = 1 := by
      generalize ℓ (j + a) = l at *
      fin_cases l <;> simp_all
    have : 1 < ((Finset.range 3).filter (fun i => ℓ (j + i) = ℓ (j + a))).card :=
      Finset.one_lt_card.mpr ⟨a, by simp [ha], b, by simp [hb, heq], hab⟩
    omega
  refine ⟨rfl, ?_, ?_, ?_⟩
  · simpa using dist3 0 1 (by norm_num) (by norm_num) (by norm_num)
  · simpa using dist3 0 2 (by norm_num) (by norm_num) (by norm_num)
  · exact dist3 1 2 (by norm_num) (by norm_num) (by norm_num)

/-- **Converse**: three different labels in a row give a straight line (`α + β + γ = π`). -/
theorem straight_of_triple {ω : Fin 3 → ℝ} (G : AngGen ω) {u v : ℕ → V2} {ℓ : ℕ → Fin 3} (F : Fan6 ω u v ℓ) (j : ℕ)
    (h01 : ℓ j ≠ ℓ (j + 1)) (h02 : ℓ j ≠ ℓ (j + 2)) (h12 : ℓ (j + 1) ≠ ℓ (j + 2)) :
    Par (u (j + 3)) (-(u j).1, -(u j).2) := by
  have hrot := run_rotation (fun i => u (j + i)) (fun i => v (j + i)) (fun i => F.hu _) (fun i => by
    have := F.hpar (j + i); simpa [add_assoc] using this) 3
  simp only [add_zero] at hrot
  have hsum : ∑ i ∈ Finset.range 3, wd (u (j + i)) (v (j + i)) = Real.pi := by
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add, add_zero, F.hwd]
    have key : ∀ a b c : Fin 3, a ≠ b → a ≠ c → b ≠ c → ω a + ω b + ω c = Real.pi := by
      intro a b c hab hac hbc
      have := G.sum
      fin_cases a <;> fin_cases b <;> fin_cases c <;> simp_all <;> linarith
    exact key _ _ _ h01 h02 h12
  rw [hsum] at hrot
  exact hrot.trans ((par_rot_neg_iff _ (F.hu j)).2 ⟨0, by simp⟩)

/-! ### Non-vacuity: the lattice-triangle fan -/

/-- Angles `(π/3, 5π/12, π/4)`: positive, sum `π`, pairwise distinct, none a right angle. -/
noncomputable def ωW : Fin 3 → ℝ := ![Real.pi / 3, 5 * Real.pi / 12, Real.pi / 4]

theorem angGen_witness : AngGen ωW := by
  have hpi := Real.pi_pos
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [ωW, Fin.forall_fin_succ] <;> intros <;> first | linarith | (intro h; linarith)

/-- Labels `0,1,2,0,1,2,...`. -/
def ℓW (j : ℕ) : Fin 3 := ⟨j % 3, Nat.mod_lt _ (by norm_num)⟩

noncomputable def cumW (j : ℕ) : ℝ := ∑ i ∈ Finset.range j, ωW (ℓW i)

noncomputable def uW (j : ℕ) : V2 := (Real.cos (cumW j), Real.sin (cumW j))

theorem fan6_witness : Fan6 ωW uW (fun j => uW (j + 1)) ℓW := by
  have hpi := Real.pi_pos
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    simp only [uW, Prod.fst_zero, Prod.snd_zero] at h1 h2
    nlinarith [Real.cos_sq_add_sin_sq (cumW j)]
  · intro j
    refine ⟨by unfold crs; ring, ?_⟩
    unfold dt uW
    nlinarith [Real.cos_sq_add_sin_sq (cumW (j + 1))]
  · intro j
    have hθ : ωW (ℓW j) ∈ Set.Ioc (-Real.pi) Real.pi := by
      have : ∀ l : Fin 3, ωW l ∈ Set.Ioc (-Real.pi) Real.pi := by
        intro l; fin_cases l <;> simp [ωW, Set.mem_Ioc] <;> constructor <;> linarith
      exact this _
    have hc : cumW (j + 1) = cumW j + ωW (ℓW j) := by simp [cumW, Finset.sum_range_succ]
    have : (⟨dt (uW j) (uW (j + 1)), crs (uW j) (uW (j + 1))⟩ : ℂ) = Complex.cos (ωW (ℓW j)) + Complex.sin (ωW (ℓW j)) * Complex.I := by
      apply Complex.ext
      · simp [dt, uW, hc, Real.cos_add, Real.sin_add, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
        linear_combination (Real.cos (ωW (ℓW j))) * Real.cos_sq_add_sin_sq (cumW j)
      · simp [crs, uW, hc, Real.sin_add, Real.cos_add, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
        linear_combination (Real.sin (ωW (ℓW j))) * Real.cos_sq_add_sin_sq (cumW j)
    show Complex.arg _ = _
    rw [this]
    exact Complex.arg_cos_add_sin_mul_I hθ
  · intro j l
    have key : ∀ r l : Fin 3, ((Finset.range 6).filter (fun i => ((r : ℕ) + i) % 3 = (l : ℕ))).card = 2 := by decide
    have e : ((Finset.range 6).filter (fun i => ℓW (j + i) = l)) = (Finset.range 6).filter (fun i => (((⟨j % 3, Nat.mod_lt _ (by norm_num)⟩ : Fin 3) : ℕ) + i) % 3 = (l : ℕ)) := by
      ext i
      simp [ℓW, Fin.ext_iff, Nat.add_mod]
    rw [e]
    exact key _ _

end Erdos634.Draft.LaczFormal.Graph

#print axioms Erdos634.Draft.LaczFormal.Graph.angGen_witness
#print axioms Erdos634.Draft.LaczFormal.Graph.fan6_witness
#print axioms Erdos634.Draft.LaczFormal.Graph.straight_run_arith
#print axioms Erdos634.Draft.LaczFormal.Graph.straight_run_labels
#print axioms Erdos634.Draft.LaczFormal.Graph.straight_of_triple
