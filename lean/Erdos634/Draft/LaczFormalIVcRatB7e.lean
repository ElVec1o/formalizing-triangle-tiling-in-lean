-- Draft/LaczFormalIVcRatB7e.lean -- Laczkovich DCG 48 (2012), Sect. 8.3 (Subcase IVc, rational branch), BLUEPRINT Part B, item B7, stage e: from the CELL to the RHOMBUS.
--   `cell_labels`: a cell with a vertex at U (in the half plane fb >= 0, missing the open box) has its three vertices at the frame labels (0,0), (1,0), (0,1) in some order (indexed 0,1,2).
--   `rhomb_cell0_identify`, `rhomb_cell1_identify`: if cell 0 (resp. 1) of a rhombus R = Par(x; s, w) is such a cell, and R lies in {fb >= 0} and misses the open box, then R.set = Par(U; p, q).
--   (Cell 0 has vertices (x+s, x+w, x), cell 1 has vertices (x+w, x+s, x+s+w); `rhomb_identify_core` of B7c does the 12 placements.)
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 8.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIVcRatB7d

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement Erdos634.CertCoord

namespace Erdos634.Draft.LaczFormal.RG

/-- The three frame labels. -/
def Lab (a b : ℝ) : Prop := (a = 0 ∧ b = 0) ∨ (a = 1 ∧ b = 0) ∨ (a = 0 ∧ b = 1)

theorem cell_labels {b : ℝ} (F : Frame b) (hb : 0 < b) (c : Tri) (hc : c.Congruent (eqT b hb))
    (hvert : ∃ j, c.pts j = F.pt 0 0) (hbel : ∀ y ∈ c.carrier, 0 ≤ F.fb y)
    (hmiss : ∀ y ∈ c.carrier, ¬ (-1 < F.fa y ∧ F.fa y < 0 ∧ 0 < F.fb y ∧ F.fb y < 1)) :
    ∃ a0 b0 a1 b1 a2 b2 : ℝ, Lab a0 b0 ∧ Lab a1 b1 ∧ Lab a2 b2 ∧ ¬ (a0 = a1 ∧ b0 = b1) ∧ ¬ (a0 = a2 ∧ b0 = b2) ∧ ¬ (a1 = a2 ∧ b1 = b2) ∧
      c.pts 0 = F.pt a0 b0 ∧ c.pts 1 = F.pt a1 b1 ∧ c.pts 2 = F.pt a2 b2 := by
  obtain ⟨j, hj⟩ := hvert
  have w := cell_wedge F hb c hc j hj hbel hmiss
  fin_cases j
  · simp only [Fin.zero_eta, Fin.isValue, zero_add] at hj w
    have h1 : ((0 : Fin 3) + 1) = 1 := rfl
    have h2 : ((0 : Fin 3) + 2) = 2 := rfl
    rcases w with ⟨h1', h2'⟩ | ⟨h1', h2'⟩
    · exact ⟨0, 0, 1, 0, 0, 1, Or.inl ⟨rfl, rfl⟩, Or.inr (Or.inl ⟨rfl, rfl⟩), Or.inr (Or.inr ⟨rfl, rfl⟩), by norm_num, by norm_num, by norm_num, hj, h1', h2'⟩
    · exact ⟨0, 0, 0, 1, 1, 0, Or.inl ⟨rfl, rfl⟩, Or.inr (Or.inr ⟨rfl, rfl⟩), Or.inr (Or.inl ⟨rfl, rfl⟩), by norm_num, by norm_num, by norm_num, hj, h1', h2'⟩
  · have h1 : ((1 : Fin 3) + 1) = 2 := rfl
    have h2 : ((1 : Fin 3) + 2) = 0 := rfl
    have hj' : c.pts 1 = F.pt 0 0 := hj
    rw [show ((⟨1, by norm_num⟩ : Fin 3) + 1) = 2 from rfl, show ((⟨1, by norm_num⟩ : Fin 3) + 2) = 0 from rfl] at w
    rcases w with ⟨h1', h2'⟩ | ⟨h1', h2'⟩
    · exact ⟨0, 1, 0, 0, 1, 0, Or.inr (Or.inr ⟨rfl, rfl⟩), Or.inl ⟨rfl, rfl⟩, Or.inr (Or.inl ⟨rfl, rfl⟩), by norm_num, by norm_num, by norm_num, h2', hj', h1'⟩
    · exact ⟨1, 0, 0, 0, 0, 1, Or.inr (Or.inl ⟨rfl, rfl⟩), Or.inl ⟨rfl, rfl⟩, Or.inr (Or.inr ⟨rfl, rfl⟩), by norm_num, by norm_num, by norm_num, h2', hj', h1'⟩
  · have hj' : c.pts 2 = F.pt 0 0 := hj
    rw [show ((⟨2, by norm_num⟩ : Fin 3) + 1) = 0 from rfl, show ((⟨2, by norm_num⟩ : Fin 3) + 2) = 1 from rfl] at w
    rcases w with ⟨h1', h2'⟩ | ⟨h1', h2'⟩
    · exact ⟨1, 0, 0, 1, 0, 0, Or.inr (Or.inl ⟨rfl, rfl⟩), Or.inr (Or.inr ⟨rfl, rfl⟩), Or.inl ⟨rfl, rfl⟩, by norm_num, by norm_num, by norm_num, h1', h2', hj'⟩
    · exact ⟨0, 1, 1, 0, 0, 0, Or.inr (Or.inr ⟨rfl, rfl⟩), Or.inr (Or.inl ⟨rfl, rfl⟩), Or.inl ⟨rfl, rfl⟩, by norm_num, by norm_num, by norm_num, h1', h2', hj'⟩

theorem mkPt_eq_pt {b : ℝ} (F : Frame b) {u v a β : ℝ} (h : mkPt u v = F.pt a β) :
    u = F.U0 + a * F.p0 + β * F.q0 ∧ v = F.U1 + a * F.p1 + β * F.q1 := by
  have h0 := congrArg (fun y : Plane => y 0) h
  have h1 := congrArg (fun y : Plane => y 1) h
  simp only [mkPt_zero, mkPt_one, F.pt_zero, F.pt_one] at h0 h1
  exact ⟨h0, h1⟩

theorem noBelow_of_fb {b : ℝ} (F : Frame b) (hb : 0 < b) {S : Set Plane} (hbel : ∀ y ∈ S, 0 ≤ F.fb y) :
    NoBelow S F.U0 F.U1 F.p0 F.p1 F.q0 F.q1 := by
  intro xx z hz hmem
  have := hbel _ hmem
  have e : mkPt (F.U0 + xx * F.p0 + z * F.q0) (F.U1 + xx * F.p1 + z * F.q1) = F.pt xx z := rfl
  rw [e, F.fb_pt hb] at this
  linarith

theorem missBox_of_fab {b : ℝ} (F : Frame b) (hb : 0 < b) {S : Set Plane}
    (hmiss : ∀ y ∈ S, ¬ (-1 < F.fa y ∧ F.fa y < 0 ∧ 0 < F.fb y ∧ F.fb y < 1)) :
    MissBox S F.U0 F.U1 F.p0 F.p1 F.q0 F.q1 := by
  intro xx z h1 h2 h3 h4 hmem
  have e : mkPt (F.U0 + xx * F.p0 + z * F.q0) (F.U1 + xx * F.p1 + z * F.q1) = F.pt xx z := rfl
  apply hmiss _ hmem
  rw [e, F.fa_pt hb, F.fb_pt hb]
  exact ⟨h1, h2, h3, h4⟩

def Tuple12 (xa xb sa sb wa wb : ℝ) : Prop :=
  (xa = 0 ∧ xb = 0 ∧ sa = 1 ∧ sb = 0 ∧ wa = 0 ∧ wb = 1) ∨ (xa = 0 ∧ xb = 0 ∧ sa = 0 ∧ sb = 1 ∧ wa = 1 ∧ wb = 0) ∨
      (xa = 1 ∧ xb = 1 ∧ sa = -1 ∧ sb = 0 ∧ wa = 0 ∧ wb = -1) ∨ (xa = 1 ∧ xb = 1 ∧ sa = 0 ∧ sb = -1 ∧ wa = -1 ∧ wb = 0) ∨
      (xa = 1 ∧ xb = 0 ∧ sa = -1 ∧ sb = 0 ∧ wa = -1 ∧ wb = 1) ∨ (xa = 1 ∧ xb = 0 ∧ sa = -1 ∧ sb = 1 ∧ wa = -1 ∧ wb = 0) ∨
      (xa = 0 ∧ xb = 1 ∧ sa = 0 ∧ sb = -1 ∧ wa = 1 ∧ wb = -1) ∨ (xa = 0 ∧ xb = 1 ∧ sa = 1 ∧ sb = -1 ∧ wa = 0 ∧ wb = -1) ∨
      (xa = -1 ∧ xb = 1 ∧ sa = 1 ∧ sb = 0 ∧ wa = 1 ∧ wb = -1) ∨ (xa = -1 ∧ xb = 1 ∧ sa = 1 ∧ sb = -1 ∧ wa = 1 ∧ wb = 0) ∨
      (xa = 1 ∧ xb = -1 ∧ sa = 0 ∧ sb = 1 ∧ wa = -1 ∧ wb = 1) ∨ (xa = 1 ∧ xb = -1 ∧ sa = -1 ∧ sb = 1 ∧ wa = 0 ∧ wb = 1)

/-- Cell 0 of a rhombus. -/
theorem rhomb_cell0_identify {b : ℝ} (F : Frame b) (hb : 0 < b) (R : RhombData b) {a0 b0 a1 b1 a2 b2 : ℝ}
    (hl0 : Lab a0 b0) (hl1 : Lab a1 b1) (hl2 : Lab a2 b2) (d01 : ¬ (a0 = a1 ∧ b0 = b1)) (d02 : ¬ (a0 = a2 ∧ b0 = b2)) (d12 : ¬ (a1 = a2 ∧ b1 = b2))
    (p0 : (R.cell 0).pts 0 = F.pt a0 b0) (p1 : (R.cell 0).pts 1 = F.pt a1 b1) (p2 : (R.cell 0).pts 2 = F.pt a2 b2)
    (hbel : ∀ y ∈ R.set, 0 ≤ F.fb y)
    (hmiss : ∀ y ∈ R.set, ¬ (-1 < F.fa y ∧ F.fa y < 0 ∧ 0 < F.fb y ∧ F.fb y < 1)) :
    R.set = Par F.U0 F.U1 F.p0 F.p1 F.q0 F.q1 := by
  have e0 : (R.cell 0).pts 0 = mkPt (R.x0 + R.s0) (R.x1 + R.s1) := by simp [RhombData.cell, rhombCell, ct, mkTri_pts]
  have e1 : (R.cell 0).pts 1 = mkPt (R.x0 + R.w0) (R.x1 + R.w1) := by simp [RhombData.cell, rhombCell, ct, mkTri_pts]
  have e2 : (R.cell 0).pts 2 = mkPt R.x0 R.x1 := by simp [RhombData.cell, rhombCell, ct, mkTri_pts]
  rw [e0] at p0; rw [e1] at p1; rw [e2] at p2
  obtain ⟨q00, q01⟩ := mkPt_eq_pt F p0
  obtain ⟨q10, q11⟩ := mkPt_eq_pt F p1
  obtain ⟨q20, q21⟩ := mkPt_eq_pt F p2
  have hcase : Tuple12 a2 b2 (a0 - a2) (b0 - b2) (a1 - a2) (b1 - b2) := by
    unfold Tuple12
    rcases hl0 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hl1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hl2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      first | exact absurd ⟨rfl, rfl⟩ d01 | exact absurd ⟨rfl, rfl⟩ d02 | exact absurd ⟨rfl, rfl⟩ d12 | norm_num
  exact rhomb_identify_core (U0 := F.U0) (U1 := F.U1) (p0 := F.p0) (p1 := F.p1) (q0 := F.q0) (q1 := F.q1) hcase
    q20 q21 (by linear_combination q00 - q20) (by linear_combination q01 - q21) (by linear_combination q10 - q20) (by linear_combination q11 - q21)
    (noBelow_of_fb F hb hbel) (missBox_of_fab F hb hmiss)

/-- Cell 1 of a rhombus. -/
theorem rhomb_cell1_identify {b : ℝ} (F : Frame b) (hb : 0 < b) (R : RhombData b) {a0 b0 a1 b1 a2 b2 : ℝ}
    (hl0 : Lab a0 b0) (hl1 : Lab a1 b1) (hl2 : Lab a2 b2) (d01 : ¬ (a0 = a1 ∧ b0 = b1)) (d02 : ¬ (a0 = a2 ∧ b0 = b2)) (d12 : ¬ (a1 = a2 ∧ b1 = b2))
    (p0 : (R.cell 1).pts 0 = F.pt a0 b0) (p1 : (R.cell 1).pts 1 = F.pt a1 b1) (p2 : (R.cell 1).pts 2 = F.pt a2 b2)
    (hbel : ∀ y ∈ R.set, 0 ≤ F.fb y)
    (hmiss : ∀ y ∈ R.set, ¬ (-1 < F.fa y ∧ F.fa y < 0 ∧ 0 < F.fb y ∧ F.fb y < 1)) :
    R.set = Par F.U0 F.U1 F.p0 F.p1 F.q0 F.q1 := by
  have e0 : (R.cell 1).pts 0 = mkPt (R.x0 + R.w0) (R.x1 + R.w1) :=
    plane_ext' (by simp [RhombData.cell, rhombCell, ct, mkTri_pts] <;> ring) (by simp [RhombData.cell, rhombCell, ct, mkTri_pts] <;> ring)
  have e1 : (R.cell 1).pts 1 = mkPt (R.x0 + R.s0) (R.x1 + R.s1) :=
    plane_ext' (by simp [RhombData.cell, rhombCell, ct, mkTri_pts] <;> ring) (by simp [RhombData.cell, rhombCell, ct, mkTri_pts] <;> ring)
  have e2 : (R.cell 1).pts 2 = mkPt (R.x0 + R.s0 + R.w0) (R.x1 + R.s1 + R.w1) := by simp [RhombData.cell, rhombCell, ct, mkTri_pts]
  rw [e0] at p0; rw [e1] at p1; rw [e2] at p2
  obtain ⟨q00, q01⟩ := mkPt_eq_pt F p0
  obtain ⟨q10, q11⟩ := mkPt_eq_pt F p1
  obtain ⟨q20, q21⟩ := mkPt_eq_pt F p2
  have hcase : Tuple12 (a0 + a1 - a2) (b0 + b1 - b2) (a2 - a0) (b2 - b0) (a2 - a1) (b2 - b1) := by
    unfold Tuple12
    rcases hl0 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hl1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hl2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      first | exact absurd ⟨rfl, rfl⟩ d01 | exact absurd ⟨rfl, rfl⟩ d02 | exact absurd ⟨rfl, rfl⟩ d12 | norm_num
  exact rhomb_identify_core (U0 := F.U0) (U1 := F.U1) (p0 := F.p0) (p1 := F.p1) (q0 := F.q0) (q1 := F.q1) hcase
    (by linear_combination q00 + q10 - q20) (by linear_combination q01 + q11 - q21) (by linear_combination q20 - q00) (by linear_combination q21 - q01)
    (by linear_combination q20 - q10) (by linear_combination q21 - q11)
    (noBelow_of_fb F hb hbel) (missBox_of_fab F hb hmiss)

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.rhomb_cell0_identify
#print axioms Erdos634.Draft.LaczFormal.RG.rhomb_cell1_identify
