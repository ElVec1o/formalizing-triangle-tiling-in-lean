-- Draft/LaczFormalIVcRatB7j.lean -- Laczkovich DCG 48 (2012), Sect. 8.3 (Subcase IVc, rational branch), BLUEPRINT Part B, item B7 (P4, the row of rhombi), stage j: THE ROW.
--   `VWTiling.row_of_rhombi`: T a VWTiling of a convex A with nonempty interior, F = (X; p, q) a frame with A inside the quadrant {fa >= 0, fb >= 0} and X in A (X a corner of A with the two supporting rays X + R_{>=0} p, X + R_{>=0} q).
--   Then there is k >= 1 with: for every i < k a rhombus piece of T equal to Par (X + i p) p q (the row R_1, ..., R_k, R_{i+1} = R_i + p), the point X + k p in A, and X + t p not in A for t > k (so X + k p is the end Y of the side along p).
--   Route: `step_base` (corner) then `step_next` (side), induction on i with the frame shifted by i p (`Frame.shift`); the end exists because A is compact (fa is bounded on A).
--   Conclusion form: the blueprint's "union = parallelogram X + [0, |XY|] u + [0, b] w" follows (every Par (X + i p) p q is a rhombus, their union is Par X (k p) q); not stated here.
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 8.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIVcRatB7i

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement Erdos634.CertCoord

namespace Erdos634.Draft.LaczFormal.RG

/-- The frame translated by `c p`. -/
def Frame.shift {b : ℝ} (F : Frame b) (c : ℝ) : Frame b :=
  { F with U0 := F.U0 + c * F.p0, U1 := F.U1 + c * F.p1 }

theorem Frame.shift_pt {b : ℝ} (F : Frame b) (c a β : ℝ) : (F.shift c).pt a β = F.pt (c + a) β := by
  apply plane_ext'
  · rw [Frame.pt_zero, Frame.pt_zero]; simp only [Frame.shift]; ring
  · rw [Frame.pt_one, Frame.pt_one]; simp only [Frame.shift]; ring

theorem Frame.shift_fb {b : ℝ} (F : Frame b) (c : ℝ) (y : Plane) : (F.shift c).fb y = F.fb y := by
  unfold Frame.fb Frame.D; simp only [Frame.shift]; congr 1; ring

theorem exists_fa_pos {b : ℝ} (F : Frame b) (hb : 0 < b) {A : Set Plane} (hquad : ∀ y ∈ A, 0 ≤ F.fa y)
    (hint : (interior A).Nonempty) : ∃ y ∈ A, 0 < F.fa y := by
  obtain ⟨w, hw⟩ := hint
  have hwA : w ∈ A := interior_subset hw
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hw)
  set δ : ℝ := ε / (2 * b) with hδ
  have hδp : 0 < δ := by positivity
  set z : Plane := F.pt (F.fa w - δ) (F.fb w) with hz
  have hw' := F.recon hb w
  have hdist : dist z w = δ * b := by
    have h2 : dist z w ^ 2 = (δ * b) ^ 2 := by
      rw [dist_sq7]
      have e0 : z 0 - w 0 = -δ * F.p0 := by
        have h := congrArg (fun y : Plane => y 0) hw'
        simp only [F.pt_zero] at h
        rw [hz, F.pt_zero, h]; ring
      have e1 : z 1 - w 1 = -δ * F.p1 := by
        have h := congrArg (fun y : Plane => y 1) hw'
        simp only [F.pt_one] at h
        rw [hz, F.pt_one, h]; ring
      rw [e0, e1]
      linear_combination δ ^ 2 * F.hp
    have := dist_nonneg (x := z) (y := w)
    nlinarith [sq_nonneg (dist z w - δ * b), mul_pos hδp hb]
  have hδb : δ * b = ε / 2 := by rw [hδ]; field_simp
  have hzA : z ∈ A := hball (by rw [Metric.mem_ball, hdist, hδb]; linarith)
  have := hquad z hzA
  rw [hz, F.fa_pt hb] at this
  exact ⟨w, hwA, by linarith⟩

namespace VWTiling
variable {b : ℝ} {A : Set Plane} {ιK ιR : Type} [Fintype ιK] [Fintype ιR] (T : VWTiling b A ιK ιR)

/-- The parallelogram `Par (X + i p) p q`. -/
noncomputable def rowPar (F : Frame b) (i : ℕ) : Set Plane :=
  Par (F.U0 + (i : ℝ) * F.p0) (F.U1 + (i : ℝ) * F.p1) F.p0 F.p1 F.q0 F.q1

theorem mem_rowPar_vertex (F : Frame b) (i : ℕ) : F.pt ((i : ℝ) + 1) 0 ∈ rowPar F i :=
  ⟨1, 0, by norm_num, by norm_num, by norm_num, by norm_num, by rw [F.pt_zero]; ring, by rw [F.pt_one]; ring⟩

/-- **B7j (the row).** -/
theorem row_of_rhombi (hb : 0 < b) (hconv : Convex ℝ A) (F : Frame b) (hquad : ∀ y ∈ A, 0 ≤ F.fa y ∧ 0 ≤ F.fb y)
    (hXA : F.pt 0 0 ∈ A) (hint : (interior A).Nonempty) :
    ∃ k : ℕ, 1 ≤ k ∧ (∀ i : ℕ, i < k → ∃ r, (T.R r).set = rowPar F i) ∧ F.pt (k : ℝ) 0 ∈ A ∧
      ∀ t : ℝ, (k : ℝ) < t → F.pt t 0 ∉ A := by
  obtain ⟨y, hyA, hya⟩ := exists_fa_pos F hb (fun y hy => (hquad y hy).1) hint
  -- G i : the row up to i
  let G : ℕ → Prop := fun i => F.pt (i : ℝ) 0 ∈ A ∧ ∀ j : ℕ, j < i → ∃ r, (T.R r).set = rowPar F j
  have G0 : G 0 := ⟨by simpa using hXA, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  have extend : ∀ i, G i → (∃ t : ℝ, 0 < t ∧ F.pt ((i : ℝ) + t) 0 ∈ A) → G (i + 1) := by
    intro i ⟨hiA, hrows⟩ ⟨t, ht, htA⟩
    have hnew : ∃ r, (T.R r).set = rowPar F i := by
      rcases i with _ | j
      · obtain ⟨r, hr⟩ := T.step_base hb hconv F hquad (by simpa using hXA) hyA hya
        exact ⟨r, by rw [hr]; simp [rowPar]⟩
      · obtain ⟨r0, hr0⟩ := hrows j (Nat.lt_succ_self j)
        have hbel : ∀ y ∈ A, 0 ≤ (F.shift ((j + 1 : ℕ) : ℝ)).fb y := fun y hy => by rw [Frame.shift_fb]; exact (hquad y hy).2
        have hU : (F.shift ((j + 1 : ℕ) : ℝ)).pt 0 0 ∈ A := by rw [Frame.shift_pt]; simpa using hiA
        have htA' : (F.shift ((j + 1 : ℕ) : ℝ)).pt t 0 ∈ A := by rw [Frame.shift_pt]; exact htA
        have hrow : (T.R r0).set = prevPar (F.shift ((j + 1 : ℕ) : ℝ)) := by
          rw [hr0]; simp only [rowPar, prevPar, Frame.shift]; push_cast; congr 1 <;> ring
        obtain ⟨r, hr⟩ := T.step_next hb hconv (F.shift ((j + 1 : ℕ) : ℝ)) hbel hU ht htA' hrow
        exact ⟨r, by rw [hr]; simp [rowPar, Frame.shift]⟩
    obtain ⟨r, hr⟩ := hnew
    refine ⟨?_, fun j hj => ?_⟩
    · have := T.R_subset r (by rw [hr]; exact mem_rowPar_vertex F i)
      simpa using this
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | h
      · exact hrows j h
      · subst h; exact ⟨r, hr⟩
  -- boundedness of the indices
  have hcompact : IsCompact A := by
    have h := isCompact_iUnion fun c : CellIdx ιK ιR => (T.cellT c).isCompact
    rwa [T.cells_cover] at h
  obtain ⟨M, hM⟩ := (hcompact.image F.continuous_fa).bddAbove
  have hbdd : BddAbove {i : ℕ | G i} := by
    refine ⟨⌈M⌉₊, fun i hi => ?_⟩
    have h1 := hM ⟨F.pt (i : ℝ) 0, hi.1, rfl⟩
    rw [F.fa_pt hb] at h1
    have h2 : (i : ℝ) ≤ ⌈M⌉₊ := h1.trans (Nat.le_ceil M)
    exact_mod_cast h2
  have hne : {i : ℕ | G i}.Nonempty := ⟨0, G0⟩
  set k := sSup {i : ℕ | G i} with hk
  have hkG : G k := Nat.sSup_mem hne hbdd
  have hmax : ∀ t : ℝ, 0 < t → F.pt ((k : ℝ) + t) 0 ∉ A := by
    intro t ht hmem
    have := extend k hkG ⟨t, ht, hmem⟩
    have h2 : k + 1 ≤ k := le_csSup hbdd this
    omega
  refine ⟨k, ?_, hkG.2, hkG.1, fun t ht hmem => ?_⟩
  · by_contra h0
    have hk0 : k = 0 := by omega
    obtain ⟨r, hr⟩ := T.step_base hb hconv F hquad hXA hyA hya
    have hA1 : F.pt 1 0 ∈ A := T.R_subset r (by rw [hr]; exact ⟨1, 0, by norm_num, by norm_num, by norm_num, by norm_num, by rw [F.pt_zero], by rw [F.pt_one]⟩)
    have hA1' : F.pt (((0 : ℕ) : ℝ) + 1) 0 ∈ A := by simpa using hA1
    have h1 : G 1 := extend 0 G0 ⟨1, one_pos, hA1'⟩
    have h2 : 1 ≤ k := le_csSup hbdd h1
    omega
  · exact hmax (t - k) (by linarith) (by simpa using hmem)

end VWTiling

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.VWTiling.row_of_rhombi
