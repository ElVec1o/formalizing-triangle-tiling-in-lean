-- Draft/LaczFormalBZPhi2.lean -- Beeson-Zhang (arXiv 2604.01314v1) Sect. 4-5: the Phi-contradiction for an EQUILATERAL target (the proof of Theorem 5.2 after Theorem 3.7), formal.
--   Hypotheses: D a congruent dissection of a triangle with equal sides (a Tri), the tile has angles (alpha, pi/3 - alpha, 2 pi/3), alpha not in Q pi (non-commensurable angles), a, b commensurable,
--   c not a rational multiple of a (non-commensurable sides), and (the output of Lemma 3.4 / Theorem 3.7) every side of the target is either covered only by `c`-edges or by no `c`-edge at all.
--   Conclusion: False.
-- Proof (all in Lean, no sawtooth tiles): flux of f_alpha: Sum_tiles = Phi(boundary) (`Dissection.flux_cancel`); each tile contributes sign * (c + a - b) with sign = weight of its c-edge (`Tri.flux_cedge`);
-- the c-edges: applying a Q-linear functional phi with phi(a) = 0 = phi(b), phi(c) = 1 to the interior balance `interior_flux_zero` shows the INTERIOR c-edges cancel (this is Beeson-Zhang Lemma 4.1 (perfect pairing)
-- in a form that needs no maximal segments); the side lengths give equally many c-edges X on each side; (c + a - b) X = L, and all-c sides give L = X c, so a = b: contradiction (a = b forces alpha = beta).
-- UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), p. 351, 365: Phi), Beeson-Zhang (arXiv 2604.01314v1, Lemma 4.1, Thm 5.2).
import Erdos634.Draft.LaczFormalBZPhi1

open scoped Classical

namespace Erdos634.Geometry

variable {N : ℕ}

/-- A `Q`-linear functional killing `a` and sending `c` to `1`, when `c` is not a rational multiple of `a`. -/
theorem exists_qfunctional {a c : ℝ} (hc : ¬ ∃ r : ℚ, c = (r : ℝ) * a) :
    ∃ φ : ℝ →ₗ[ℚ] ℚ, φ a = 0 ∧ φ c = 1 := by
  have hnot : c ∉ Submodule.span ℚ {a} := by
    intro hmem
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hmem
    exact hc ⟨r, by rw [← hr, Rat.smul_def]⟩
  obtain ⟨f, hf, hmap⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hnot inferInstance
  have hfa : f a = 0 := by
    have : f a ∈ (Submodule.span ℚ {a}).map f :=
      Submodule.mem_map_of_mem (Submodule.mem_span_singleton_self a)
    have h2 : f a ∈ (⊥ : Submodule ℚ ℚ) := hmap ▸ this
    exact (Submodule.mem_bot ℚ).mp h2
  refine ⟨(f c)⁻¹ • f, ?_, ?_⟩
  · show (f c)⁻¹ * f a = 0
    rw [hfa, mul_zero]
  · show (f c)⁻¹ * f c = 1
    exact inv_mul_cancel₀ hf

/-- Isosceles triangles have equal base angles (vertex form). -/
theorem cornerAngle_iso (u v w : Plane) (h : dist v w = dist w u) :
    cornerAngle v u w = cornerAngle w v u := by
  unfold cornerAngle
  have h1 : dist w v = dist w u := by rw [dist_comm]; exact h
  have := EuclideanGeometry.angle_eq_angle_of_dist_eq (V := Plane) h1
  rw [EuclideanGeometry.angle_comm v u w]
  exact this.symm

/-- Equal opposite sides give equal angles. -/
theorem Tri.angleAt_eq_of_oppLen_eq (T : Tri) {x y : Fin 3} (hxy : x ≠ y) (h : T.oppLen x = T.oppLen y) :
    T.angleAt x = T.angleAt y := by
  have key : ∀ k : Fin 3, T.oppLen k = T.oppLen (k + 1) → T.angleAt k = T.angleAt (k + 1) := by
    intro k hk
    unfold Tri.oppLen at hk
    unfold Tri.angleAt
    have e1 : k + 1 + 1 = k + 2 := by fin_cases k <;> rfl
    have e2 : k + 1 + 2 = k := by fin_cases k <;> rfl
    rw [e1, e2] at hk ⊢
    exact cornerAngle_iso (T.pts k) (T.pts (k + 1)) (T.pts (k + 2)) hk
  have k0 := key 0
  have k1 := key 1
  have k2 := key 2
  simp only [show (0:Fin 3) + 1 = 1 from rfl, show (1:Fin 3) + 1 = 2 from rfl, show (2:Fin 3) + 1 = 0 from rfl] at k0 k1 k2
  have hcases : (x = 0 ∧ y = 1) ∨ (x = 1 ∧ y = 2) ∨ (x = 2 ∧ y = 0) ∨ (x = 1 ∧ y = 0) ∨ (x = 2 ∧ y = 1) ∨ (x = 0 ∧ y = 2) := by
    fin_cases x <;> fin_cases y <;> simp at hxy ⊢
  rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact k0 h
  · exact k1 h
  · exact k2 h
  · exact (k0 h.symm).symm
  · exact (k1 h.symm).symm
  · exact (k2 h.symm).symm

/-- For a placement of the tile with `α ∉ ℚπ`, the sides `a` and `b` differ. -/
theorem Tri.TwoPiThreeData.a_ne_b {T : Tri} {α a b c : ℝ} (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (h : T.TwoPiThreeData α a b c) : a ≠ b := by
  intro hab
  obtain ⟨σ, h0, o0, h1, o1, h2, o2⟩ := h
  have hne : σ 0 ≠ σ 1 := fun e => absurd (σ.injective e) (by decide)
  have := T.angleAt_eq_of_oppLen_eq hne (by rw [o0, o1, hab])
  rw [h0, h1] at this
  apply hα
  refine ⟨1 / 6, ?_⟩
  push_cast
  linarith

end Erdos634.Geometry
