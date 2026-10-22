-- Draft/LaczFormalIIcWN13.lean -- Laczkovich (DCG 48 (2012)), Sect. 6.2/6.3, Route B: PLANE BRIDGE.
-- Polygons in `EuclideanSpace R (Fin 2)` (the project's `Plane`) are transported to the complex-number layer by the isometry
-- `Complex.orthonormalBasisOneI`; `simple_wind_dichotomy` is restated for plane polygons (`SimplePolyP`, `windP`, `edgeSetP`).
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.2/6.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcWN11
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Complex.Basic

open scoped Classical Fin.NatCast
open Complex

namespace Erdos634.Draft.LaczFormal.WN

variable {n : ℕ} [NeZero n]

/-- The standard isometry `EuclideanSpace R (Fin 2) -> C`. -/
noncomputable def toC : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] ℂ := Complex.orthonormalBasisOneI.repr.symm

theorem toC_segment (a b : EuclideanSpace ℝ (Fin 2)) :
    toC '' segment ℝ a b = segment ℝ (toC a) (toC b) := by
  have := image_segment ℝ (toC.toLinearEquiv.toLinearMap.toAffineMap) a b
  simpa using this

theorem mem_segment_toC (a b z : EuclideanSpace ℝ (Fin 2)) :
    z ∈ segment ℝ a b ↔ toC z ∈ segment ℝ (toC a) (toC b) := by
  rw [← toC_segment]
  exact (toC.injective.mem_set_image).symm

/-- The closed polygon in the plane. -/
def edgeSetP (p : Fin n → EuclideanSpace ℝ (Fin 2)) : Set (EuclideanSpace ℝ (Fin 2)) :=
  ⋃ i : Fin n, segment ℝ (p i) (p (i + 1))

/-- Simplicity for plane polygons (same shape as `SimplePoly`). -/
def SimplePolyP (p : Fin n → EuclideanSpace ℝ (Fin 2)) : Prop :=
  ∀ i j : Fin n, i ≠ j → ∀ z ∈ segment ℝ (p i) (p (i + 1)) ∩ segment ℝ (p j) (p (j + 1)),
    (z = p i ∨ z = p (i + 1)) ∧ (z = p j ∨ z = p (j + 1))

/-- Winding number of a plane polygon about a plane point. -/
noncomputable def windP (p : Fin n → EuclideanSpace ℝ (Fin 2)) (z : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  wind (fun i => toC (p i)) (toC z)

theorem mem_edgeSetP_iff (p : Fin n → EuclideanSpace ℝ (Fin 2)) (z : EuclideanSpace ℝ (Fin 2)) :
    z ∈ edgeSetP p ↔ toC z ∈ edgeSet (fun i => toC (p i)) := by
  unfold edgeSetP edgeSet
  simp only [Set.mem_iUnion, mem_segment_toC]

theorem simplePolyP_iff (p : Fin n → EuclideanSpace ℝ (Fin 2)) :
    SimplePolyP p ↔ SimplePoly (fun i => toC (p i)) := by
  constructor
  · intro h i j hij w hw
    obtain ⟨z, rfl⟩ := toC.surjective w
    have hz : z ∈ segment ℝ (p i) (p (i + 1)) ∩ segment ℝ (p j) (p (j + 1)) :=
      ⟨(mem_segment_toC _ _ _).2 hw.1, (mem_segment_toC _ _ _).2 hw.2⟩
    obtain ⟨h1, h2⟩ := h i j hij z hz
    refine ⟨?_, ?_⟩
    · rcases h1 with h1 | h1 <;> [left; right] <;> rw [h1]
    · rcases h2 with h2 | h2 <;> [left; right] <;> rw [h2]
  · intro h i j hij z hz
    have hw : toC z ∈ segment ℝ (toC (p i)) (toC (p (i + 1))) ∩ segment ℝ (toC (p j)) (toC (p (j + 1))) :=
      ⟨(mem_segment_toC _ _ _).1 hz.1, (mem_segment_toC _ _ _).1 hz.2⟩
    obtain ⟨h1, h2⟩ := h i j hij (toC z) hw
    refine ⟨?_, ?_⟩
    · rcases h1 with h1 | h1 <;> [left; right] <;> exact toC.injective h1
    · rcases h2 with h2 | h2 <;> [left; right] <;> exact toC.injective h2

/-- **Plane bridge for the Jordan-type dichotomy.** -/
theorem simple_wind_dichotomy_plane {p : Fin n → EuclideanSpace ℝ (Fin 2)} (hs : SimplePolyP p)
    (hinj : Function.Injective p) (hn : 3 ≤ n) :
    ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ ∀ z : EuclideanSpace ℝ (Fin 2), z ∉ edgeSetP p → windP p z = 0 ∨ windP p z = σ := by
  have hinjC : Function.Injective (fun i => toC (p i)) := fun a b h => hinj (toC.injective h)
  obtain ⟨σ, hσ, h⟩ := simple_wind_dichotomy ((simplePolyP_iff p).1 hs) hinjC hn
  exact ⟨σ, hσ, fun z hz => h (toC z) (fun hh => hz ((mem_edgeSetP_iff p z).2 hh))⟩

#print axioms simple_wind_dichotomy_plane

end Erdos634.Draft.LaczFormal.WN
