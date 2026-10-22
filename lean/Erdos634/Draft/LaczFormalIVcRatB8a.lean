-- Draft/LaczFormalIVcRatB8a.lean -- Laczkovich DCG 48 (2012), Sect. 8.3 (Subcase IVc, rational branch), BLUEPRINT Part B, item B8 (P5, the complement of the row), stage a.
--   `Frame.shift_fa`, `Frame.shiftq` (frame translated by q: fa' = fa, fb' = fb - 1), `exists_nhd_shift` (a point of an open set can be moved by small multiples of p and q inside it),
--   `VWTiling.fa_le_row` : with the row R_0, ..., R_{k-1} of B7 (rhombi Par (X + i p) p q) and the ray ending at X + k p, the whole of A lies in {fa <= k} (the side at Y goes along q:
--   otherwise the cell through Y with a point beyond would be the triangle Y, Y+p, Y+q by `step_next_y`, putting X + (k+1) p in A).  This replaces the printed "the corner Y has angle exactly 2 pi/3".
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 8.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIVcRatB7w

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement Erdos634.CertCoord

namespace Erdos634.Draft.LaczFormal.RG

theorem Frame.shift_fa {b : ℝ} (F : Frame b) (hb : 0 < b) (c : ℝ) (y : Plane) : (F.shift c).fa y = F.fa y - c := by
  have hD := F.D_ne hb
  have e : (F.shift c).D = F.D := rfl
  unfold Frame.fa; rw [e]; simp only [Frame.shift]; field_simp; first | (unfold Frame.D; ring) | ring

/-- The frame translated by `q`. -/
def Frame.shiftq {b : ℝ} (F : Frame b) : Frame b := { F with U0 := F.U0 + F.q0, U1 := F.U1 + F.q1 }

theorem Frame.shiftq_fa {b : ℝ} (F : Frame b) (hb : 0 < b) (y : Plane) : F.shiftq.fa y = F.fa y := by
  have hD := F.D_ne hb
  have e : F.shiftq.D = F.D := rfl
  unfold Frame.fa; rw [e]; simp only [Frame.shiftq]; field_simp; first | (unfold Frame.D; ring) | ring

theorem Frame.shiftq_fb {b : ℝ} (F : Frame b) (hb : 0 < b) (y : Plane) : F.shiftq.fb y = F.fb y - 1 := by
  have hD := F.D_ne hb
  have e : F.shiftq.D = F.D := rfl
  unfold Frame.fb; rw [e]; simp only [Frame.shiftq]; field_simp; first | (unfold Frame.D; ring) | ring

theorem Frame.shiftq_pt {b : ℝ} (F : Frame b) (a β : ℝ) : F.shiftq.pt a β = F.pt a (1 + β) := by
  apply plane_ext'
  · rw [Frame.pt_zero, Frame.pt_zero]; simp only [Frame.shiftq]; ring
  · rw [Frame.pt_one, Frame.pt_one]; simp only [Frame.shiftq]; ring

/-- Small moves along `p` and `q` stay in an open set. -/
theorem exists_nhd_shift {b : ℝ} (F : Frame b) (hb : 0 < b) {S : Set Plane} {w : Plane} (hw : w ∈ interior S) :
    ∃ δ > 0, ∀ s : ℝ, |s| ≤ δ → F.pt (F.fa w + s) (F.fb w) ∈ S ∧ F.pt (F.fa w) (F.fb w + s) ∈ S := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hw)
  refine ⟨ε / (2 * b), by positivity, fun s hs => ?_⟩
  have hw' := F.recon hb w
  have hw0 : w 0 = F.U0 + F.fa w * F.p0 + F.fb w * F.q0 := by
    have h := congrArg (fun y : Plane => y 0) hw'; simpa [F.pt_zero] using h
  have hw1 : w 1 = F.U1 + F.fa w * F.p1 + F.fb w * F.q1 := by
    have h := congrArg (fun y : Plane => y 1) hw'; simpa [F.pt_one] using h
  have hδb : ε / (2 * b) * b = ε / 2 := by field_simp
  have hsb : |s| * b ≤ ε / 2 := by rw [← hδb]; exact mul_le_mul_of_nonneg_right hs hb.le
  have key : ∀ (v0 v1 : ℝ) (z : Plane), z 0 - w 0 = s * v0 → z 1 - w 1 = s * v1 → v0 ^ 2 + v1 ^ 2 = b ^ 2 → dist z w < ε := by
    intro v0 v1 z e0 e1 hv
    have h2 : dist z w ^ 2 = (|s| * b) ^ 2 := by
      have hh : (|s| * b) ^ 2 = s ^ 2 * b ^ 2 := by rw [mul_pow, sq_abs]
      rw [dist_sq7, e0, e1, hh]; linear_combination s ^ 2 * hv
    have h3 : dist z w = |s| * b := (sq_eq_sq₀ dist_nonneg (by positivity)).mp h2
    linarith
  constructor
  · apply hball
    rw [Metric.mem_ball]
    exact key F.p0 F.p1 _ (by rw [F.pt_zero, hw0]; ring) (by rw [F.pt_one, hw1]; ring) F.hp
  · apply hball
    rw [Metric.mem_ball]
    exact key F.q0 F.q1 _ (by rw [F.pt_zero, hw0]; ring) (by rw [F.pt_one, hw1]; ring) F.hq

namespace VWTiling
variable {b : ℝ} {A : Set Plane} {ιK ιR : Type} [Fintype ιK] [Fintype ιR] (T : VWTiling b A ιK ιR)

/-- **B8a.** The whole of `A` lies in `{fa <= j + 1}` once the row `R_0, ..., R_j` ends at `X + (j+1) p`. -/
theorem fa_le_row (hb : 0 < b) (hconv : Convex ℝ A) (F : Frame b) (hbel : ∀ y ∈ A, 0 ≤ F.fb y) (j : ℕ)
    {r0 : ιR} (hr0 : (T.R r0).set = rowPar F j) (hkA : F.pt (((j + 1 : ℕ) : ℝ)) 0 ∈ A)
    (hend : ∀ t : ℝ, ((j + 1 : ℕ) : ℝ) < t → F.pt t 0 ∉ A) : ∀ y ∈ A, F.fa y ≤ ((j + 1 : ℕ) : ℝ) := by
  intro y hyA
  by_contra hcon
  push Not at hcon
  have hbelG : ∀ y ∈ A, 0 ≤ (F.shift ((j + 1 : ℕ) : ℝ)).fb y := fun y hy => by rw [Frame.shift_fb]; exact hbel y hy
  have hU : (F.shift ((j + 1 : ℕ) : ℝ)).pt 0 0 ∈ A := by rw [Frame.shift_pt]; simpa using hkA
  have hpos : 0 < (F.shift ((j + 1 : ℕ) : ℝ)).fa y := by rw [Frame.shift_fa F hb]; linarith
  have hrow : (T.R r0).set = prevPar (F.shift ((j + 1 : ℕ) : ℝ)) := by
    rw [hr0]; simp only [rowPar, prevPar, Frame.shift]; push_cast; congr 1 <;> ring
  obtain ⟨r, hr⟩ := T.step_next_y hb hconv (F.shift ((j + 1 : ℕ) : ℝ)) hbelG hU hyA hpos hrow
  have hv : F.pt (((j + 1 : ℕ) : ℝ) + 1) 0 ∈ A := by
    apply T.R_subset r
    rw [hr]
    refine ⟨1, 0, by norm_num, by norm_num, by norm_num, by norm_num, ?_, ?_⟩
    · rw [Frame.pt_zero]; simp only [Frame.shift]; push_cast; ring
    · rw [Frame.pt_one]; simp only [Frame.shift]; push_cast; ring
  exact hend _ (by linarith) hv

end VWTiling

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.VWTiling.fa_le_row
