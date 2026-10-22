import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.Convex.Topology
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Topology.Connected.Basic
import Erdos634.Dissection

/-!
# Beeson (arXiv 1206.2229v4) Lemma 12, connectivity, part 2: a convex body is not a union of two closed sets meeting in a finite set

NOTE, UNAUDITED.  Credit: Michael Beeson (arXiv 1206.2229 v4, Lemma 12), Laczkovich (DCG 48 (2012)), Beeson-Zhang.

`no_split`: if `R` is convex in the plane with nonempty interior, `UA`, `UB` are closed, `UA ∪ UB = R`, `UA ∩ UB` is
finite, then `UA ⊆ UB` or `UB ⊆ UA`.  Route: pick `x ∈ UA \ UB`, `y ∈ UB \ UA`; pick `z` in the interior of `R` off the
finitely many lines through `x` or `y` and a point of `F = UA ∩ UB` (a null set); the broken segment `x z y` lies in `R`,
misses `F`, is preconnected, and is split by the closed sets `UA`, `UB`: contradiction.
-/

namespace Erdos634.Geometry

open MeasureTheory Set

private theorem line_ne_top (x f : Plane) : affineSpan ℝ ({x, f} : Set Plane) ≠ ⊤ := by
  intro h
  have hc : Collinear ℝ ({x, f} : Set Plane) := collinear_pair ℝ x f
  have hd : vectorSpan ℝ ({x, f} : Set Plane) = ⊤ := by
    rw [← direction_affineSpan, h, AffineSubspace.direction_top]
  have h1 : Module.rank ℝ (vectorSpan ℝ ({x, f} : Set Plane)) ≤ 1 := hc
  rw [hd, rank_top] at h1
  have h2 : Module.rank ℝ Plane = 2 := by
    rw [← Module.finrank_eq_rank]; simp
  rw [h2] at h1
  norm_num at h1

private theorem mem_line_of_seg {u v w : Plane} (hw : w ∈ segment ℝ u v) (hne : w ≠ u) :
    v ∈ affineSpan ℝ ({u, w} : Set Plane) := by
  obtain ⟨a, b, ha, hb, hab, hw⟩ := hw
  have hb0 : b ≠ 0 := by
    rintro rfl
    apply hne
    have : a = 1 := by linarith
    rw [← hw, this]; simp
  have ha' : a = 1 - b := by linarith
  have e : w -ᵥ u = b • (v - u) := by
    rw [← hw, vsub_eq_sub, ha', sub_smul, one_smul, smul_sub]; abel
  have : v = AffineMap.lineMap u w b⁻¹ := by
    rw [AffineMap.lineMap_apply, e, smul_smul, inv_mul_cancel₀ hb0, one_smul]
    simp [vadd_eq_add]
  rw [this]
  exact AffineMap.lineMap_mem_affineSpan_pair _ _ _

theorem no_split {R UA UB : Set Plane} (hR : Convex ℝ R) (hint : (interior R).Nonempty)
    (hA : IsClosed UA) (hB : IsClosed UB) (hU : UA ∪ UB = R) (hF : (UA ∩ UB).Finite) :
    UA ⊆ UB ∨ UB ⊆ UA := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hAB, hBA⟩ := hcon
  obtain ⟨x, hxA, hxB⟩ := Set.not_subset.mp hAB
  obtain ⟨y, hyB, hyA⟩ := Set.not_subset.mp hBA
  set F := UA ∩ UB with hFdef
  set bad : Set Plane := ⋃ f ∈ F, ((affineSpan ℝ ({x, f} : Set Plane) : Set Plane) ∪
    (affineSpan ℝ ({y, f} : Set Plane) : Set Plane)) with hbad
  have hbad0 : volume bad = 0 := by
    refine (measure_biUnion_null_iff hF.countable).2 fun f _ => ?_
    exact measure_union_null (Measure.addHaar_affineSubspace _ _ (line_ne_top _ _))
      (Measure.addHaar_affineSubspace _ _ (line_ne_top _ _))
  obtain ⟨z, hzint, hzbad⟩ : ∃ z ∈ interior R, z ∉ bad := by
    by_contra h
    push Not at h
    have := measure_mono_null h hbad0
    exact (isOpen_interior.measure_pos volume hint).ne' this
  have hxR : x ∈ R := hU ▸ Or.inl hxA
  have hyR : y ∈ R := hU ▸ Or.inr hyB
  have hzR : z ∈ R := interior_subset hzint
  have hxF : x ∉ F := fun h => hxB h.2
  have hyF : y ∉ F := fun h => hyA h.1
  set S : Set Plane := segment ℝ x z ∪ segment ℝ z y with hS
  have hSR : S ⊆ R := union_subset (hR.segment_subset hxR hzR) (hR.segment_subset hzR hyR)
  have hSF : S ∩ F = ∅ := by
    refine Set.eq_empty_iff_forall_notMem.mpr ?_
    rintro w ⟨hw, hwF⟩
    rcases hw with hw | hw
    · have hwx : w ≠ x := fun h => hxF (h ▸ hwF)
      exact hzbad (Set.mem_biUnion hwF (Or.inl (mem_line_of_seg hw hwx)))
    · have hwy : w ≠ y := fun h => hyF (h ▸ hwF)
      exact hzbad (Set.mem_biUnion hwF (Or.inr (mem_line_of_seg (segment_symm ℝ z y ▸ hw) hwy)))
  have hpre : IsPreconnected S :=
    ((convex_segment x z).isPreconnected).union z (right_mem_segment ℝ x z) (left_mem_segment ℝ z y)
      (convex_segment z y).isPreconnected
  have hsub : S ⊆ UA ∪ UB := hU ▸ hSR
  have hxS : x ∈ S := Or.inl (left_mem_segment ℝ x z)
  have hyS : y ∈ S := Or.inr (right_mem_segment ℝ z y)
  have := (isPreconnected_closed_iff.mp hpre) UA UB hA hB hsub ⟨x, hxS, hxA⟩ ⟨y, hyS, hyB⟩
  obtain ⟨w, hwS, hwA, hwB⟩ := this
  have : w ∈ S ∩ F := ⟨hwS, hwA, hwB⟩
  rw [hSF] at this
  exact this

end Erdos634.Geometry

#print axioms Erdos634.Geometry.no_split
