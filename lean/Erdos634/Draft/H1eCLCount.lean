/-
Draft/H1eCLCount.lean — atom H1.e (CL), part 2: the corner COUNTS at the target vertices of a `RightNormal`
dissection (model angles `α, π/2 - α, π/2` at vertices `0, 1, 2`; target angles `α, α, π - 2α` at `0, 1, 2`).
Irrationality of `α/π` is the field `RightNormal.irr` (nothing extra is needed).

* `angle_lin_irr`      : `m α + n π = 0 → m = 0 ∧ n = 0` for integers, when `α/π ∉ ℚ`.
* `RightNormal.vals`   : every tile's local angle at every target vertex is in `{α, π/2-α, π/2, π, 0}`.
* `RightNormal.cornerB_tile` : at the target vertex `0` ("B", angle `α`) SOME tile has local angle `α` there
  (the multiplicities are exactly `(1,0,0,0)`).
* `RightNormal.cornerA_vals` : at the target vertex `2` ("A", apex, angle `π - 2α = 2β`) every tile's local angle
  is `β = π/2 - α` or `0`; i.e. the counts are exactly `(0,2,0,0)` (we only need the "no other nonzero angle" half).
*** UNAUDITED.  Formalization debt, NOT /goal progress.  No sorry. ***
-/
import Erdos634.Draft.H1aSetup
import Erdos634.TilePlacement
import Erdos634.TileAt

open scoped Classical

namespace Erdos634.Draft.H1eCL

open Erdos634.Geometry Erdos634.Draft.H1a Erdos634.TilePlacement Erdos634.Geometry.Row3.RP

theorem angle_lin_irr {α : ℝ} (hirr : Irrational (α / Real.pi)) (m n : ℤ)
    (h : (m : ℝ) * α + (n : ℝ) * Real.pi = 0) : m = 0 ∧ n = 0 := by
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  have hm : m = 0 := by
    by_contra hm0
    apply hirr
    refine ⟨(-n : ℚ) / m, ?_⟩
    have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm0
    push_cast
    field_simp
    linarith
  subst hm
  refine ⟨rfl, ?_⟩
  by_contra hn
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have : (n : ℝ) * Real.pi = 0 := by simpa using h
  exact mul_ne_zero hn' hπ this

/-- The angle-count equation at `B`: `p α + q (π/2 - α) + z (π/2) + w π = α` forces `(p,q,z,w) = (1,0,0,0)`. -/
theorem countB {α : ℝ} (hirr : Irrational (α / Real.pi)) (p q z w : ℕ)
    (h : (p : ℝ) * α + (q : ℝ) * (Real.pi / 2 - α) + (z : ℝ) * (Real.pi / 2) + (w : ℝ) * Real.pi = α) :
    p = 1 ∧ q = 0 ∧ z = 0 ∧ w = 0 := by
  have h2 : ((2 * ((p : ℤ) - q - 1) : ℤ) : ℝ) * α + (((q : ℤ) + z + 2 * w : ℤ) : ℝ) * Real.pi = 0 := by
    push_cast; linarith
  obtain ⟨h1, h3⟩ := angle_lin_irr hirr _ _ h2
  refine ⟨by omega, by omega, by omega, by omega⟩

/-- The angle-count equation at `A`: `p α + q (π/2 - α) + z (π/2) + w π = π - 2α` forces `(0,2,0,0)`. -/
theorem countA {α : ℝ} (hirr : Irrational (α / Real.pi)) (p q z w : ℕ)
    (h : (p : ℝ) * α + (q : ℝ) * (Real.pi / 2 - α) + (z : ℝ) * (Real.pi / 2) + (w : ℝ) * Real.pi
      = Real.pi - 2 * α) :
    p = 0 ∧ q = 2 ∧ z = 0 ∧ w = 0 := by
  have h2 : ((2 * ((p : ℤ) - q + 2) : ℤ) : ℝ) * α + (((q : ℤ) + z + 2 * w - 2 : ℤ) : ℝ) * Real.pi = 0 := by
    push_cast; linarith
  obtain ⟨h1, h3⟩ := angle_lin_irr hirr _ _ h2
  refine ⟨by omega, by omega, by omega, by omega⟩

section
variable {N : ℕ} {D : CongruentDissection N} {α : ℝ}

theorem _root_.Erdos634.Draft.H1a.RightNormal.hβ (h : RightNormal D α) : D.model.angleAt 1 = Real.pi / 2 - α := by
  have := angle_third (T := D.model) (p := 0) (q := 1) (r := 2) (by decide) (by decide) (by decide)
  rw [h.m0, h.m2] at this; linarith

theorem _root_.Erdos634.Draft.H1a.RightNormal.ne_facts (h : RightNormal D α) :
    α ≠ Real.pi / 2 - α ∧ α ≠ Real.pi / 2 ∧ α ≠ Real.pi ∧ α ≠ 0 ∧ Real.pi / 2 - α ≠ Real.pi / 2 ∧
      Real.pi / 2 - α ≠ Real.pi ∧ Real.pi / 2 - α ≠ 0 := by
  have hπ := Real.pi_pos
  have h0 := h.pos
  have h2 := h.lt
  have hirr := h.irr
  have nr : ∀ r : ℚ, α ≠ (r : ℝ) * Real.pi := by
    intro r hr; apply hirr; exact ⟨r, by rw [hr]; field_simp⟩
  refine ⟨?_, ?_, by linarith, by linarith, by linarith, by linarith, by linarith⟩
  · intro e; exact nr (1 / 4) (by push_cast; linarith)
  · intro e; exact nr (1 / 2) (by push_cast; linarith)

/-- Every tile's local angle at a target vertex is one of `α, π/2 - α, π/2, π, 0`. -/
theorem _root_.Erdos634.Draft.H1a.RightNormal.vals (h : RightNormal D α) (k : Fin 3) (i : Fin N) :
    (D.tile i).localAngle (D.target.pts k)
      ∈ ({α, Real.pi / 2 - α, Real.pi / 2, Real.pi, 0} : Finset ℝ) := by
  have h1 := h.hβ
  exact Erdos634.Geometry.Dissection.congruentDissection_localAngle_mem D α (Real.pi / 2 - α)
    (Real.pi / 2) h.m0 h1 h.m2 k i

private theorem _root_.Erdos634.Draft.H1a.RightNormal.mult (h : RightNormal D α) (k : Fin 3) (θ : ℝ)
    (hθ : cornerAngle (D.target.pts (k + 1)) (D.target.pts k) (D.target.pts (k + 2)) = θ) :
    (({i | (D.tile i).localAngle (D.target.pts k) = α} : Finset (Fin N)).card : ℝ) * α
      + (({i | (D.tile i).localAngle (D.target.pts k) = Real.pi / 2 - α} : Finset (Fin N)).card : ℝ)
          * (Real.pi / 2 - α)
      + (({i | (D.tile i).localAngle (D.target.pts k) = Real.pi / 2} : Finset (Fin N)).card : ℝ)
          * (Real.pi / 2)
      + (({i | (D.tile i).localAngle (D.target.pts k) = Real.pi} : Finset (Fin N)).card : ℝ) * Real.pi
      = θ := by
  obtain ⟨n1, n2, n3, n4, n5, n6, n7⟩ := h.ne_facts
  have := corner_multiplicities D.toDissection α (Real.pi / 2 - α) (Real.pi / 2) n1 n2 n3 n4
    n5 n6 n7 (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]) Real.pi_ne_zero k (h.vals k)
  rw [hθ] at this
  exact this

/-- **Corner `B` (target vertex 0, angle `α`).**  Some tile has local angle exactly `α` at `B`. -/
theorem _root_.Erdos634.Draft.H1a.RightNormal.cornerB_tile (h : RightNormal D α) :
    ∃ i : Fin N, (D.tile i).localAngle (D.target.pts 0) = α := by
  have hc : cornerAngle (D.target.pts (0 + 1)) (D.target.pts 0) (D.target.pts (0 + 2)) = α := h.t0
  have hm := h.mult 0 α hc
  obtain ⟨hp, -, -, -⟩ := countB h.irr _ _ _ _ hm
  have : 0 < ({i | (D.tile i).localAngle (D.target.pts 0) = α} : Finset (Fin N)).card := by omega
  obtain ⟨i, hi⟩ := Finset.card_pos.mp this
  exact ⟨i, by simpa using hi⟩

/-- The apex angle: `π - 2α`. -/
theorem _root_.Erdos634.Draft.H1a.RightNormal.t2 (h : RightNormal D α) :
    cornerAngle (D.target.pts (2 + 1)) (D.target.pts 2) (D.target.pts (2 + 2)) = Real.pi - 2 * α := by
  have hs := D.target.angleAt_sum
  have e : D.target.angleAt 2 = Real.pi - 2 * α := by rw [h.t0, h.t1] at hs; linarith
  exact e

/-- **Corner `A` (target vertex 2, angle `π - 2α = 2β`).**  Every tile has local angle `β = π/2 - α` or `0` there. -/
theorem _root_.Erdos634.Draft.H1a.RightNormal.cornerA_vals (h : RightNormal D α) (i : Fin N) :
    (D.tile i).localAngle (D.target.pts 2) = Real.pi / 2 - α ∨
      (D.tile i).localAngle (D.target.pts 2) = 0 := by
  have hm := h.mult 2 _ h.t2
  obtain ⟨hp, -, hz, hw⟩ := countA h.irr _ _ _ _ hm
  have hv := h.vals 2 i
  simp only [Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with e | e | e | e | e
  · exfalso
    have : i ∈ ({i | (D.tile i).localAngle (D.target.pts 2) = α} : Finset (Fin N)) := by simpa using e
    rw [Finset.card_eq_zero.mp hp] at this; simp at this
  · exact Or.inl e
  · exfalso
    have : i ∈ ({i | (D.tile i).localAngle (D.target.pts 2) = Real.pi / 2} : Finset (Fin N)) := by simpa using e
    rw [Finset.card_eq_zero.mp hz] at this; simp at this
  · exfalso
    have : i ∈ ({i | (D.tile i).localAngle (D.target.pts 2) = Real.pi} : Finset (Fin N)) := by simpa using e
    rw [Finset.card_eq_zero.mp hw] at this; simp at this
  · exact Or.inr e

end

end Erdos634.Draft.H1eCL

#print axioms Erdos634.Draft.H1eCL.angle_lin_irr
#print axioms Erdos634.Draft.H1a.RightNormal.cornerB_tile
#print axioms Erdos634.Draft.H1a.RightNormal.cornerA_vals
