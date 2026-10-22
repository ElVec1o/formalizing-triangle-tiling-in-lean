-- Draft/LaczFormalIIcWN27.lean -- Laczkovich (DCG 48 (2012)), Sect. 6.2 ("Fig. 5"), second half of step (a): ABSTRACT fan lemmas, part 2.
-- Distinct sectors of a `Fan6` have non-parallel rays (`fan_par_mod`: `Par (u c) (u d) -> c = d mod 6`), rotation preserves `Par` and the norm, and two positively parallel vectors of equal norm are equal.
-- Tiling-free.  NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.2), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcWN26

open Erdos634.Draft.LaczFormal.Graph

namespace Erdos634.Draft.LaczFormal.Graph

theorem par_rot_self_false {S : ℝ} {y : V2} (hy : y ≠ 0) (h : Par (rot S y) y) (h0 : 0 < S) (h2 : S < 2 * Real.pi) : False := by
  obtain ⟨hc, hd⟩ := h
  have hn := nsq_pos hy
  have hn' : nsq y = y.1 ^ 2 + y.2 ^ 2 := rfl
  have hsin : Real.sin S * nsq y = 0 := by
    unfold crs at hc; simp only [rot] at hc; rw [hn']; linarith
  have hcos : 0 < Real.cos S * nsq y := by
    unfold dt at hd; simp only [rot] at hd; rw [hn']; nlinarith
  have hs0 : Real.sin S = 0 := (mul_eq_zero.1 hsin).resolve_right hn.ne'
  obtain ⟨n, hn1⟩ := Real.sin_eq_zero_iff.1 hs0
  have hpi := Real.pi_pos
  have h1 : (0 : ℝ) < n := by
    by_contra hh; push_neg at hh; nlinarith
  have h2' : (n : ℝ) < 2 := by
    by_contra hh; push_neg at hh; nlinarith
  have hn1' : n = 1 := by
    have a : (0 : ℤ) < n := by exact_mod_cast h1
    have b : n < (2 : ℤ) := by exact_mod_cast h2'
    omega
  subst hn1'
  have : Real.cos S = -1 := by rw [← hn1]; simp
  rw [this] at hcos
  nlinarith

theorem Fan6.run_bounds {ω : Fin 3 → ℝ} (G : AngGen ω) {u v : ℕ → V2} {ℓ : ℕ → Fin 3} (F : Fan6 ω u v ℓ) (j m : ℕ)
    (hm1 : 1 ≤ m) (hm5 : m ≤ 5) :
    0 < ∑ i ∈ Finset.range m, wd (u (j + i)) (v (j + i)) ∧ ∑ i ∈ Finset.range m, wd (u (j + i)) (v (j + i)) < 2 * Real.pi := by
  have hpos : ∀ i, 0 < wd (u (j + i)) (v (j + i)) := fun i => by rw [F.hwd]; exact G.pos _
  refine ⟨Finset.sum_pos (fun i _ => hpos i) (Finset.nonempty_range_iff.mpr (by omega)), ?_⟩
  rw [← F.turn G j]
  exact Finset.sum_lt_sum_of_subset (Finset.range_subset_range.mpr (by omega : m ≤ 6)) (Finset.mem_range.mpr (show m < 6 by omega))
    (by simp) (hpos m) (fun i _ _ => (hpos i).le)

theorem fan_par_mod {ω : Fin 3 → ℝ} (G : AngGen ω) {u v : ℕ → V2} {ℓ : ℕ → Fin 3} (F : Fan6 ω u v ℓ)
    (hu6 : ∀ j, u (j + 6) = u j) {c d : ℕ} (h : Par (u c) (u d)) : c % 6 = d % 6 := by
  have eu : ∀ n, u n = u (n % 6) := per_reduce u hu6
  rw [eu c, eu d] at h
  have key : ∀ c' d' : ℕ, c' < 6 → d' < 6 → c' < d' → Par (u c') (u d') → False := by
    intro c' d' hc hd hlt hp
    have hrun := run_rotation (fun i => u (c' + i)) (fun i => v (c' + i)) (fun i => F.hu _) (fun i => by
      have := F.hpar (c' + i); simpa [add_assoc] using this) (d' - c')
    simp only [add_zero] at hrun
    have hdc : c' + (d' - c') = d' := by omega
    rw [hdc] at hrun
    obtain ⟨hb1, hb2⟩ := F.run_bounds G c' (d' - c') (by omega) (by omega)
    exact par_rot_self_false (F.hu c') ((hrun.symm).trans hp.symm) hb1 hb2
  by_contra hne
  have hc6 : c % 6 < 6 := Nat.mod_lt _ (by norm_num)
  have hd6 : d % 6 < 6 := Nat.mod_lt _ (by norm_num)
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact key _ _ hc6 hd6 hlt h
  · exact key _ _ hd6 hc6 hlt h.symm

theorem rot_crs (θ : ℝ) (a b : V2) : crs (rot θ a) (rot θ b) = crs a b := by
  unfold crs rot; simp only
  have := Real.cos_sq_add_sin_sq θ
  linear_combination (a.1 * b.2 - a.2 * b.1) * this

theorem rot_dt (θ : ℝ) (a b : V2) : dt (rot θ a) (rot θ b) = dt a b := by
  unfold dt rot; simp only
  have := Real.cos_sq_add_sin_sq θ
  linear_combination (a.1 * b.1 + a.2 * b.2) * this

theorem par_rot (θ : ℝ) {a b : V2} (h : Par a b) : Par (rot θ a) (rot θ b) := by
  refine ⟨?_, ?_⟩
  · rw [rot_crs]; exact h.1
  · rw [rot_dt]; exact h.2

theorem nsq_rot (θ : ℝ) (a : V2) : nsq (rot θ a) = nsq a := by
  unfold nsq rot; simp only
  have := Real.cos_sq_add_sin_sq θ
  linear_combination (a.1 ^ 2 + a.2 ^ 2) * this

theorem eq_of_par_nsq {x y : V2} (h : Par x y) (hn : nsq x = nsq y) : x = y := by
  obtain ⟨c, hc, hxy⟩ := h.smul
  have hy := nsq_pos h.ne_right
  have h2 : nsq x = c ^ 2 * nsq y := by
    rw [hxy]; unfold nsq; simp only; ring
  have hc2 : c ^ 2 = 1 := by
    have : (c ^ 2 - 1) * nsq y = 0 := by linarith
    have := (mul_eq_zero.1 this).resolve_right hy.ne'
    linarith
  have hc1 : c = 1 := by nlinarith
  rw [hxy, hc1]; ext <;> simp

end Erdos634.Draft.LaczFormal.Graph
