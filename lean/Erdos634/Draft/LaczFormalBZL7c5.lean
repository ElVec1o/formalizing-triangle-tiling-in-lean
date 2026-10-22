-- Draft/LaczFormalBZL7c5.lean -- Beeson-Zhang (arXiv 2604.01314v1) Thm 5.3 (row (2 alpha, pi/3, 2 beta)), the Phi-contradiction, formal and WITHOUT Theorem 3.7 / Lemma 3.4 / sawtooth tiles:
--   `Tri.oppLen_lt_add_perm`  : strict triangle inequality for the sides of a `Tri`;
--   `target_sum`              : for a triangle whose angles are (2 alpha, pi/3, 2 beta) at the vertices rho 0, rho 1, rho 2, the weights of f_alpha and f_beta on the sides are s * (-1, +1, -1)
--                               (the sides opposite those vertices), s = +-1;
--   `bz_c_rational_row`       : a, b commensurable and alpha not in Q pi  ==>  c is a rational multiple of a.
-- Proof: bz_phi_gen for f_alpha (K = c+a-b) and f_beta (K = c+b-a) gives K M = Q for both, M = n_B - n_A - n_C (numbers of c-edges), Q = q - p - r (side lengths); so (a-b) M = 0, a != b, M = 0, Q = 0, contradicting q < p + r.
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), p. 351, 365: Phi), Beeson-Zhang (arXiv 2604.01314v1, Lemma 5.1, Thm 5.2, Thm 5.3).
import Erdos634.Draft.LaczFormalBZL7c4

open scoped Classical

namespace Erdos634.Geometry

variable {N : ℕ}

theorem Tri.range_pts_eq (T : Tri) : Set.range T.pts = {T.pts 0, T.pts 1, T.pts 2} := by
  ext x
  simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp
  · rintro (rfl | rfl | rfl) <;> exact ⟨_, rfl⟩

theorem Tri.not_collinear (T : Tri) : ¬ Collinear ℝ ({T.pts 0, T.pts 1, T.pts 2} : Set Plane) := by
  rw [← Tri.range_pts_eq]
  exact (affineIndependent_iff_not_collinear (k := ℝ) (p := T.pts)).mp T.indep

/-- **Strict triangle inequality** for the sides of a `Tri`. -/
theorem Tri.oppLen_lt_add (T : Tri) (k : Fin 3) : T.oppLen k < T.oppLen (k + 1) + T.oppLen (k + 2) := by
  have hle : ∀ x y z : Plane, dist x z ≤ dist x y + dist y z := fun x y z => dist_triangle x y z
  have key : ∀ x y z : Plane, ¬ Collinear ℝ ({x, y, z} : Set Plane) → dist x z < dist x y + dist y z := by
    intro x y z hcol
    refine lt_of_le_of_ne (hle x y z) ?_
    intro heq
    apply hcol
    have hw : Wbtw ℝ x y z := (dist_add_dist_eq_iff).mp heq.symm
    exact hw.collinear
  have nc := T.not_collinear
  unfold Tri.oppLen
  fin_cases k
  · -- oppLen 0 = dist p1 p2 ; oppLen 1 = dist p2 p0 ; oppLen 2 = dist p0 p1
    show dist (T.pts 1) (T.pts 2) < dist (T.pts 2) (T.pts 0) + dist (T.pts 0) (T.pts 1)
    have := key (T.pts 1) (T.pts 0) (T.pts 2) (by
      intro hc; apply nc
      have e : ({T.pts 1, T.pts 0, T.pts 2} : Set Plane) = {T.pts 0, T.pts 1, T.pts 2} := Set.insert_comm _ _ _
      rwa [e] at hc)
    rw [dist_comm (T.pts 2) (T.pts 0), dist_comm (T.pts 1) (T.pts 0)] at *
    linarith [this, dist_comm (T.pts 1) (T.pts 0)]
  · show dist (T.pts 2) (T.pts 0) < dist (T.pts 0) (T.pts 1) + dist (T.pts 1) (T.pts 2)
    have := key (T.pts 2) (T.pts 1) (T.pts 0) (by
      intro hc; apply nc
      have e : ({T.pts 2, T.pts 1, T.pts 0} : Set Plane) = {T.pts 0, T.pts 1, T.pts 2} := by
        ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
      rwa [e] at hc)
    linarith [this, dist_comm (T.pts 2) (T.pts 1), dist_comm (T.pts 1) (T.pts 0), dist_comm (T.pts 2) (T.pts 0)]
  · show dist (T.pts 0) (T.pts 1) < dist (T.pts 1) (T.pts 2) + dist (T.pts 2) (T.pts 0)
    have := key (T.pts 0) (T.pts 2) (T.pts 1) (by
      intro hc; apply nc
      have e : ({T.pts 0, T.pts 2, T.pts 1} : Set Plane) = {T.pts 0, T.pts 1, T.pts 2} := by
        ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
      rwa [e] at hc)
    linarith [this, dist_comm (T.pts 2) (T.pts 1), dist_comm (T.pts 0) (T.pts 2), dist_comm (T.pts 1) (T.pts 0)]

theorem Tri.oppLen_lt_add_perm (T : Tri) (x : Equiv.Perm (Fin 3)) :
    T.oppLen (x 1) < T.oppLen (x 0) + T.oppLen (x 2) := by
  have k0 : T.oppLen 0 < T.oppLen 1 + T.oppLen 2 := T.oppLen_lt_add 0
  have k1 : T.oppLen 1 < T.oppLen 2 + T.oppLen 0 := T.oppLen_lt_add 1
  have k2 : T.oppLen 2 < T.oppLen 0 + T.oppLen 1 := T.oppLen_lt_add 2
  have hall : ∀ i j l : Fin 3, i ≠ j → i ≠ l → j ≠ l → T.oppLen i < T.oppLen j + T.oppLen l := by
    have hc : ∀ i j l : Fin 3, i ≠ j → i ≠ l → j ≠ l →
        (i = 0 ∧ j = 1 ∧ l = 2) ∨ (i = 0 ∧ j = 2 ∧ l = 1) ∨ (i = 1 ∧ j = 0 ∧ l = 2) ∨
        (i = 1 ∧ j = 2 ∧ l = 0) ∨ (i = 2 ∧ j = 0 ∧ l = 1) ∨ (i = 2 ∧ j = 1 ∧ l = 0) := by decide
    intro i j l hij hil hjl
    rcases hc i j l hij hil hjl with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      linarith
  exact hall (x 1) (x 0) (x 2) (fun e => absurd (x.injective e) (by decide)) (fun e => absurd (x.injective e) (by decide))
    (fun e => absurd (x.injective e) (by decide))

end Erdos634.Geometry

#print axioms Erdos634.Geometry.Tri.oppLen_lt_add_perm
