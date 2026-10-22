-- Draft/LaczFormalIVcRatB8c.lean -- Laczkovich DCG 48 (2012), Sect. 8.3 (Subcase IVc, rational branch), BLUEPRINT Part B, item B8 (P5), stage c: `complement_row`.
--   T a VWTiling of a convex A inside the quadrant {fa >= 0, fb >= 0} of the frame F = (X; p, q), the row R_0, ..., R_j (rhombus pieces Par (X + i p) p q, i <= j) ending at X + (j+1) p, and a point of A with fb > 1.
--   Then there is a nonempty Finset S of rhombus indices (the row rhombi) such that the region of `T.restrict S` (the union of the remaining kites and rhombi) equals A intersected with {fb >= 1}, which is convex.
--   Route: `fa_le_row` (B8a): A lies in {fa <= j+1}; `piece_above` (B8b): every remaining piece lies in {fb >= 1}; the points with fb > 1 lie in remaining pieces (a row rhombus has fb <= 1); fb = 1 by closure.
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 8.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIVcRatB8b

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement Erdos634.CertCoord

namespace Erdos634.Draft.LaczFormal.RG

theorem KiteData.isClosed {b : ℝ} (K : KiteData b) : IsClosed K.set :=
  (Tri.isCompact (ct K.v0 K.v1 (2 * K.s0) (2 * K.s1) (2 * K.w0) (2 * K.w1) (hD4 K.hD))).isClosed

theorem RhombData.isClosed {b : ℝ} (R : RhombData b) : IsClosed R.set := by
  rw [← R.set_eq_iUnion]; exact isClosed_iUnion_of_finite fun i => (R.cell i).isCompact.isClosed

theorem convex_fb_ge {b : ℝ} (F : Frame b) (c : ℝ) : Convex ℝ {y : Plane | c ≤ F.fb y} := by
  intro y hy z hz a b' ha hb' hab
  simp only [Set.mem_setOf_eq] at hy hz ⊢
  rw [F.fb_eq] at hy hz ⊢
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  have hb'' : b' = 1 - a := by linarith
  subst hb''
  nlinarith [mul_le_mul_of_nonneg_left hy ha, mul_le_mul_of_nonneg_left hz hb']

theorem fb_lineMap {b : ℝ} (F : Frame b) (y w : Plane) (s : ℝ) : F.fb (AffineMap.lineMap y w s) = F.fb y + s * (F.fb w - F.fb y) := by
  rw [F.fb_eq, F.fb_eq y, F.fb_eq w, AffineMap.lineMap_apply]
  simp only [vsub_eq_sub, vadd_eq_add, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
  ring

namespace VWTiling
variable {b : ℝ} {A : Set Plane} {ιK ιR : Type} [Fintype ιK] [Fintype ιR] (T : VWTiling b A ιK ιR)

/-- **B8c.** -/
theorem complement_row (hb : 0 < b) (hconv : Convex ℝ A) (F : Frame b) (hquad : ∀ y ∈ A, 0 ≤ F.fa y ∧ 0 ≤ F.fb y) (j : ℕ)
    (hrows : ∀ i : ℕ, i < j + 1 → ∃ r, (T.R r).set = rowPar F i) (hkA : F.pt (((j + 1 : ℕ) : ℝ)) 0 ∈ A)
    (hend : ∀ t : ℝ, ((j + 1 : ℕ) : ℝ) < t → F.pt t 0 ∉ A) (hw : ∃ w ∈ A, 1 < F.fb w) :
    ∃ S : Finset ιR, S.Nonempty ∧
      ((⋃ k, (T.K k).set) ∪ ⋃ r : {r // r ∉ S}, (T.R r.1).set) = A ∩ {y | 1 ≤ F.fb y} := by
  obtain ⟨r0, hr0⟩ := hrows j (Nat.lt_succ_self j)
  have hfa := T.fa_le_row hb hconv F (fun y hy => (hquad y hy).2) j hr0 hkA hend
  set S : Finset ιR := Finset.univ.filter (fun r : ιR => ∃ i, i < j + 1 ∧ (T.R r).set = rowPar F i) with hS
  have hmemS : ∀ r, r ∈ S ↔ ∃ i, i < j + 1 ∧ (T.R r).set = rowPar F i := by intro r; simp [hS]
  have hSne : S.Nonempty := ⟨r0, (hmemS _).2 ⟨j, Nat.lt_succ_self j, hr0⟩⟩
  refine ⟨S, hSne, ?_⟩
  have hbox : ∀ Q : Set Plane, Q ⊆ A → ∀ y ∈ Q, 0 ≤ F.fa y ∧ F.fa y ≤ ((j + 1 : ℕ) : ℝ) ∧ 0 ≤ F.fb y :=
    fun Q hQ y hy => ⟨(hquad y (hQ hy)).1, hfa y (hQ hy), (hquad y (hQ hy)).2⟩
  have hdisK : ∀ k, ∀ i : ℕ, i < j + 1 → Disjoint (interior (T.K k).set) (interior (rowPar F i)) := by
    intro k i hi
    obtain ⟨ri, hri⟩ := hrows i hi
    have := T.disjKR k ri
    rwa [hri] at this
  have hdisR : ∀ r, r ∉ S → ∀ i : ℕ, i < j + 1 → Disjoint (interior (T.R r).set) (interior (rowPar F i)) := by
    intro r hr i hi
    obtain ⟨ri, hri⟩ := hrows i hi
    have hne : r ≠ ri := fun h => hr ((hmemS r).2 ⟨i, hi, by rw [h]; exact hri⟩)
    have := T.disjRR r ri hne
    rwa [hri] at this
  have aboveK : ∀ k, ∀ y ∈ (T.K k).set, 1 ≤ F.fb y := fun k =>
    piece_above F hb (j + 1) (hbox _ (T.K_subset k)) ((T.K k).closure_interior) (hdisK k)
  have aboveR : ∀ r, r ∉ S → ∀ y ∈ (T.R r).set, 1 ≤ F.fb y := fun r hr =>
    piece_above F hb (j + 1) (hbox _ (T.R_subset r)) ((T.R r).closure_interior) (hdisR r hr)
  have strict : ∀ y ∈ A, 1 < F.fb y → y ∈ ((⋃ k, (T.K k).set) ∪ ⋃ r : {r // r ∉ S}, (T.R r.1).set) := by
    intro y hyA hy1
    have hy' := hyA
    rw [← T.cover] at hy'
    rcases hy' with h | h
    · exact Or.inl h
    · obtain ⟨r, hr⟩ := Set.mem_iUnion.mp h
      by_cases hrS : r ∈ S
      · exfalso
        obtain ⟨i, hi, hset⟩ := (hmemS r).1 hrS
        rw [hset] at hr
        have := (rowPar_fb_le F hb i y hr).2
        linarith
      · exact Or.inr (Set.mem_iUnion.mpr ⟨⟨r, hrS⟩, hr⟩)
  have hclosed : IsClosed ((⋃ k, (T.K k).set) ∪ ⋃ r : {r // r ∉ S}, (T.R r.1).set) :=
    (isClosed_iUnion_of_finite fun k => (T.K k).isClosed).union (isClosed_iUnion_of_finite fun r => (T.R r.1).isClosed)
  obtain ⟨w, hwA, hw1⟩ := hw
  ext y
  constructor
  · rintro (h | h)
    · obtain ⟨k, hk⟩ := Set.mem_iUnion.mp h
      exact ⟨T.K_subset k hk, aboveK k y hk⟩
    · obtain ⟨⟨r, hrS⟩, hr⟩ := Set.mem_iUnion.mp h
      exact ⟨T.R_subset r hr, aboveR r hrS y hr⟩
  · rintro ⟨hyA, hy1⟩
    by_cases h1 : 1 < F.fb y
    · exact strict y hyA h1
    · have hfy : F.fb y = 1 := le_antisymm (not_lt.mp h1) hy1
      rw [← hclosed.closure_eq]
      rw [Metric.mem_closure_iff]
      intro ε hε
      set s : ℝ := min 1 (ε / (2 * (dist y w + 1))) with hs
      have hsp : 0 < s := lt_min one_pos (by positivity)
      have hs1 : s ≤ 1 := min_le_left _ _
      refine ⟨AffineMap.lineMap y w s, strict _ (hconv.lineMap_mem hyA hwA ⟨hsp.le, hs1⟩) ?_, ?_⟩
      · rw [fb_lineMap, hfy]; nlinarith
      · rw [dist_comm, dist_lineMap_left, Real.norm_eq_abs, abs_of_pos hsp]
        have h1 : s * dist y w ≤ ε / (2 * (dist y w + 1)) * dist y w :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) dist_nonneg
        have h2 : ε / (2 * (dist y w + 1)) * dist y w < ε := by
          have hd := dist_nonneg (x := y) (y := w)
          rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
          nlinarith
        linarith

theorem convex_complement (hconv : Convex ℝ A) (F : Frame b) : Convex ℝ (A ∩ {y | 1 ≤ F.fb y}) :=
  hconv.inter (convex_fb_ge F 1)

end VWTiling

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.VWTiling.complement_row
