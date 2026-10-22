-- Draft/LemmaCFigures.lean — generic (tile-angle-agnostic) vertex-figure facts for Lemma C:
-- (F1) at every non-target-corner tile vertex, the corner figure sums to k·π, k ∈ {1,2}.
-- Imported via AllNew8.lean → All.lean:853 (stale "NOT imported" header corrected 2026-10-04).
import Erdos634.CornerAnglePerm
import Erdos634.VertexFigureReal
import Erdos634.PinPlumbing
import Erdos634.RouteOneVertexKill

open scoped Classical
open Erdos634.Geometry

namespace Erdos634.Draft.LemmaCFigures

/-- **(F1)** at a non-corner tile vertex, the counts of tiles presenting `α`, `β`, `γ` satisfy
`cα·α + cβ·β + cγ·γ = k·π` with `k ∈ {1,2}`.  No relation among `α, β, γ` beyond distinctness,
positivity and `< π` is used. -/
theorem vertex_figure_sum {N : ℕ} (D : CongruentDissection N) (α β γ : ℝ)
    (hmα : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hmβ : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hmγ : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hβγ : β ≠ γ)
    (hα0 : 0 < α) (hβ0 : 0 < β) (hγ0 : 0 < γ)
    (hαπ : α < Real.pi) (hβπ : β < Real.pi) (hγπ : γ < Real.pi)
    {v : Plane} (hv : v ∈ cornerPts D.toDissection) (hnc : v ∉ Set.range D.target.pts) :
    ∃ k : ℕ, (k = 1 ∨ k = 2) ∧
      (({i | (D.tile i).localAngle v = α} : Finset (Fin N)).card : ℝ) * α
      + (({i | (D.tile i).localAngle v = β} : Finset (Fin N)).card : ℝ) * β
      + (({i | (D.tile i).localAngle v = γ} : Finset (Fin N)).card : ℝ) * γ
      = (k : ℝ) * Real.pi := by
  obtain ⟨j, -, hj⟩ := Finset.mem_biUnion.mp hv
  obtain ⟨m, -, hm⟩ := Finset.mem_image.mp hj
  have hvals : ∀ i, (D.tile i).localAngle v ∈ ({α, β, γ, Real.pi, 0} : Finset ℝ) :=
    fun i => congruentDissection_localAngle_mem_at_corner D α β γ hmα hmβ hmγ j m hm i
  have hpi := Real.pi_pos
  have hsumv := VertexFigureReal.sum_by_value ({α, β, γ, Real.pi, 0} : Finset ℝ)
    (fun i => (D.tile i).localAngle v) hvals
  rw [show ({α, β, γ, Real.pi, 0} : Finset ℝ)
      = insert α (insert β (insert γ (insert Real.pi {0}))) from rfl] at hsumv
  rw [Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨hαβ, hαγ, hαπ.ne, hα0.ne'⟩),
      Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨hβγ, hβπ.ne, hβ0.ne'⟩),
      Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨hγπ.ne, hγ0.ne'⟩),
      Finset.sum_insert (by simp only [Finset.mem_singleton]; exact hpi.ne'),
      Finset.sum_singleton] at hsumv
  beta_reduce at hsumv
  set cα := (({i | (D.tile i).localAngle v = α} : Finset (Fin N)).card : ℝ) with hcα
  set cβ := (({i | (D.tile i).localAngle v = β} : Finset (Fin N)).card : ℝ) with hcβ
  set cγ := (({i | (D.tile i).localAngle v = γ} : Finset (Fin N)).card : ℝ) with hcγ
  set cπ := ({i | (D.tile i).localAngle v = Real.pi} : Finset (Fin N)).card with hcπ
  -- positivity of the corner part
  have hown : cα ≠ 0 ∨ cβ ≠ 0 ∨ cγ ≠ 0 := by
    have h := localAngle_at_own_vertex_mem D α β γ hmα hmβ hmγ j m
    rw [hm] at h
    have hne : ∀ c : Finset (Fin N), j ∈ c → (c.card : ℝ) ≠ 0 := fun c hc => by
      have := Finset.card_pos.mpr ⟨j, hc⟩; positivity
    rcases h with h | h | h
    · exact Or.inl (hne _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩))
    · exact Or.inr (Or.inl (hne _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)))
    · exact Or.inr (Or.inr (hne _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)))
  have hc0 : 0 ≤ cα := Nat.cast_nonneg _
  have hc1 : 0 ≤ cβ := Nat.cast_nonneg _
  have hc2 : 0 ≤ cγ := Nat.cast_nonneg _
  have hcp : 0 ≤ (cπ : ℝ) := Nat.cast_nonneg _
  have hFpos : 0 < cα * α + cβ * β + cγ * γ := by
    have p0 := mul_nonneg hc0 hα0.le
    have p1 := mul_nonneg hc1 hβ0.le
    have p2 := mul_nonneg hc2 hγ0.le
    rcases hown with h | h | h
    · have := mul_pos (lt_of_le_of_ne hc0 (Ne.symm h)) hα0; linarith
    · have := mul_pos (lt_of_le_of_ne hc1 (Ne.symm h)) hβ0; linarith
    · have := mul_pos (lt_of_le_of_ne hc2 (Ne.symm h)) hγ0; linarith
  rcases Erdos634.Geometry.cornerPts_trichotomy D.toDissection hv with h | ⟨hfr, -⟩ | hint
  · exact absurd h hnc
  · have htot := Erdos634.PinPlumbing.pin_angle_sum D.toDissection hfr hnc
    rw [hsumv] at htot
    have : (cπ : ℝ) < 1 := by nlinarith
    have hz : cπ = 0 := by exact_mod_cast (by exact_mod_cast this : cπ < 1) |> Nat.lt_one_iff.mp
    refine ⟨1, Or.inl rfl, ?_⟩
    rw [hz] at htot; push_cast at htot ⊢; linarith
  · have htot := Erdos634.PinPlumbing.pin_angle_sum_interior D.toDissection hint
    rw [hsumv] at htot
    have : (cπ : ℝ) < 2 := by nlinarith
    have hle : cπ ≤ 1 := by
      have : cπ < 2 := by exact_mod_cast this
      omega
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hle with hz | hz
    · refine ⟨2, Or.inr rfl, ?_⟩
      rw [hz] at htot; push_cast at htot ⊢; linarith
    · refine ⟨1, Or.inl rfl, ?_⟩
      rw [hz] at htot; push_cast at htot ⊢; linarith


/-- Counting a sum whose terms all lie in `{α,β,γ,π,0}`. -/
theorem count_sum {N : ℕ} (la : Fin N → ℝ) (α β γ : ℝ)
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hβγ : β ≠ γ)
    (hα0 : 0 < α) (hβ0 : 0 < β) (hγ0 : 0 < γ)
    (hαπ : α < Real.pi) (hβπ : β < Real.pi) (hγπ : γ < Real.pi)
    (hvals : ∀ i, la i ∈ ({α, β, γ, Real.pi, 0} : Finset ℝ)) :
    ∑ i, la i = (({i | la i = α} : Finset (Fin N)).card : ℝ) * α
      + (({i | la i = β} : Finset (Fin N)).card : ℝ) * β
      + (({i | la i = γ} : Finset (Fin N)).card : ℝ) * γ
      + (({i | la i = Real.pi} : Finset (Fin N)).card : ℝ) * Real.pi := by
  have hpi := Real.pi_pos
  have hsumv := VertexFigureReal.sum_by_value ({α, β, γ, Real.pi, 0} : Finset ℝ) la hvals
  rw [show ({α, β, γ, Real.pi, 0} : Finset ℝ)
      = insert α (insert β (insert γ (insert Real.pi {0}))) from rfl] at hsumv
  rw [Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨hαβ, hαγ, hαπ.ne, hα0.ne'⟩),
      Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨hβγ, hβπ.ne, hβ0.ne'⟩),
      Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨hγπ.ne, hγ0.ne'⟩),
      Finset.sum_insert (by simp only [Finset.mem_singleton]; exact hpi.ne'),
      Finset.sum_singleton] at hsumv
  rw [hsumv]; ring

/-- **(F3 ingredient) The figure at a target corner.**  The corner is a tile vertex, the
counts of `α, β, γ` there sum (weighted) to the target's angle, and at least one tile presents
one of them. -/
theorem corner_figure {N : ℕ} (D : CongruentDissection N) (α β γ : ℝ)
    (hmα : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hmβ : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hmγ : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hβγ : β ≠ γ)
    (hα0 : 0 < α) (hβ0 : 0 < β) (hγ0 : 0 < γ)
    (hαπ : α < Real.pi) (hβπ : β < Real.pi) (hγπ : γ < Real.pi) (k : Fin 3) :
    D.target.pts k ∈ cornerPts D.toDissection ∧
    (({i | (D.tile i).localAngle (D.target.pts k) = α} : Finset (Fin N)).card : ℝ) * α
      + (({i | (D.tile i).localAngle (D.target.pts k) = β} : Finset (Fin N)).card : ℝ) * β
      + (({i | (D.tile i).localAngle (D.target.pts k) = γ} : Finset (Fin N)).card : ℝ) * γ
      = cornerAngle (D.target.pts (k + 1)) (D.target.pts k) (D.target.pts (k + 2)) ∧
    1 ≤ ({i | (D.tile i).localAngle (D.target.pts k) = α} : Finset (Fin N)).card
      + ({i | (D.tile i).localAngle (D.target.pts k) = β} : Finset (Fin N)).card
      + ({i | (D.tile i).localAngle (D.target.pts k) = γ} : Finset (Fin N)).card := by
  have hpi := Real.pi_pos
  have hvals : ∀ i, (D.tile i).localAngle (D.target.pts k) ∈ ({α, β, γ, Real.pi, 0} : Finset ℝ) := by
    intro i
    have hmem := congruentDissection_localAngle_mem_all D α β γ hmα hmβ hmγ (D.target.pts k) i
    have h2 := Erdos634.Geometry.Dissection.localAngle_ne_two_pi_of_not_mem_interior
      (D.toDissection.target_vertex_not_interior_tile k i)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem ⊢
    rcases hmem with h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact absurd h h2
    · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
  have hcs := count_sum (fun i => (D.tile i).localAngle (D.target.pts k)) α β γ hαβ hαγ hβγ
    hα0 hβ0 hγ0 hαπ hβπ hγπ hvals
  have hθ := Erdos634.VertexFigureReal.corner_angle_sum D.toDissection k
  have hθlt := Erdos634.RouteOneVertexKill.cornerAngle_lt_pi D.target k
  have hθpos := Erdos634.MarchFlank.cornerAngle_pos D.target k
  beta_reduce at hcs
  set cα := (({i | (D.tile i).localAngle (D.target.pts k) = α} : Finset (Fin N)).card : ℝ)
  set cβ := (({i | (D.tile i).localAngle (D.target.pts k) = β} : Finset (Fin N)).card : ℝ)
  set cγ := (({i | (D.tile i).localAngle (D.target.pts k) = γ} : Finset (Fin N)).card : ℝ)
  set cπ := (({i | (D.tile i).localAngle (D.target.pts k) = Real.pi} : Finset (Fin N)).card : ℝ)
  have hc0 : 0 ≤ cα := Nat.cast_nonneg _
  have hc1 : 0 ≤ cβ := Nat.cast_nonneg _
  have hc2 : 0 ≤ cγ := Nat.cast_nonneg _
  have hcp : 0 ≤ cπ := Nat.cast_nonneg _
  have hcπ0 : cπ = 0 := by
    by_contra hne
    have : 1 ≤ cπ := by
      have : (({i | (D.tile i).localAngle (D.target.pts k) = Real.pi} : Finset (Fin N)).card) ≠ 0 := by
        intro h; apply hne; simp [cπ, h]
      exact Nat.one_le_cast.mpr (Nat.one_le_iff_ne_zero.mpr this)
    nlinarith [mul_nonneg hc0 hα0.le, mul_nonneg hc1 hβ0.le, mul_nonneg hc2 hγ0.le]
  rw [hcπ0] at hcs
  have hF : cα * α + cβ * β + cγ * γ = cornerAngle (D.target.pts (k + 1)) (D.target.pts k)
      (D.target.pts (k + 2)) := by linarith
  have hFpos : 0 < cα * α + cβ * β + cγ * γ := by rw [hF]; exact hθpos
  have hsum1 : 1 ≤ ({i | (D.tile i).localAngle (D.target.pts k) = α} : Finset (Fin N)).card
      + ({i | (D.tile i).localAngle (D.target.pts k) = β} : Finset (Fin N)).card
      + ({i | (D.tile i).localAngle (D.target.pts k) = γ} : Finset (Fin N)).card := by
    by_contra hlt
    have h0 : ({i | (D.tile i).localAngle (D.target.pts k) = α} : Finset (Fin N)).card = 0 := by omega
    have h1 : ({i | (D.tile i).localAngle (D.target.pts k) = β} : Finset (Fin N)).card = 0 := by omega
    have h2 : ({i | (D.tile i).localAngle (D.target.pts k) = γ} : Finset (Fin N)).card = 0 := by omega
    have e0 : cα = 0 := by simp [cα, h0]
    have e1 : cβ = 0 := by simp [cβ, h1]
    have e2 : cγ = 0 := by simp [cγ, h2]
    rw [e0, e1, e2] at hFpos; simp at hFpos
  refine ⟨?_, hF, hsum1⟩
  have : ∃ i, (D.tile i).localAngle (D.target.pts k) = α ∨ (D.tile i).localAngle (D.target.pts k) = β
      ∨ (D.tile i).localAngle (D.target.pts k) = γ := by
    by_contra hno
    push Not at hno
    have hz : ∀ (θ : ℝ), (∀ i, (D.tile i).localAngle (D.target.pts k) ≠ θ) →
        ({i | (D.tile i).localAngle (D.target.pts k) = θ} : Finset (Fin N)).card = 0 := by
      intro θ h; simp [Finset.card_eq_zero, Finset.filter_eq_empty_iff, h]
    have := hz α (fun i => (hno i).1)
    have := hz β (fun i => (hno i).2.1)
    have := hz γ (fun i => (hno i).2.2)
    omega
  obtain ⟨i, hi⟩ := this
  have hne : ∀ θ, (D.tile i).localAngle (D.target.pts k) = θ → 0 < θ → θ < Real.pi →
      D.target.pts k ∈ cornerPts D.toDissection := by
    intro θ h h0 hpi'
    obtain ⟨m, hm⟩ := vertex_of_localAngle_corner (D.tile i) h h0.ne' hpi'.ne (by linarith)
    rw [← hm]; exact mem_cornerPts D.toDissection i m
  rcases hi with h | h | h
  · exact hne α h hα0 hαπ
  · exact hne β h hβ0 hβπ
  · exact hne γ h hγ0 hγπ

end Erdos634.Draft.LemmaCFigures

#print axioms Erdos634.Draft.LemmaCFigures.vertex_figure_sum
#print axioms Erdos634.Draft.LemmaCFigures.corner_figure
