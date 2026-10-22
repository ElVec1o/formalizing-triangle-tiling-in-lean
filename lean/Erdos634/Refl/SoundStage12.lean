import Erdos634.Refl.SoundStage11

/-! Stage 12: glue — `checkNode_sound` (with the two extra hypotheses named below). -/

set_option linter.unusedSimpArgs false
open Erdos634.CertNode Erdos634.PlacementCompleteness Erdos634.SixPlacements
open Erdos634.Geometry (Plane)

namespace Refl

/-- `Sound cfg`: no congruent dissection has all tiles of `cfg` among its tiles (as in `SoundSkel`). -/
def Sound (Dn : ℝ) (I : Inst) (M : Erdos634.Geometry.Tri) (cfg : List _root_.Tri) : Prop :=
  ∀ {N : ℕ} (D : Erdos634.Geometry.CongruentDissection N),
    D.target.carrier = I.tgt.carr Dn → D.model.Congruent M →
    (∀ t ∈ cfg, ∃ i, (D.tile i).carrier = t.carr Dn) → False

/-- the check the checker does NOT do today (needed for `Blocked.base`): the target lies in `y ≥ 0` -/
def _root_.Inst.baseY (I : Inst) : Bool :=
  decide (0 ≤ I.tgt.a.y) && decide (0 ≤ I.tgt.b.y) && decide (0 ≤ I.tgt.c.y)

theorem tgt_y_nonneg (Dn : ℝ) (hD : 0 < Dn) (I : Inst) (htok : I.tgt.ok = true) (hY : I.baseY = true) :
    ∀ p ∈ I.tgt.carr Dn, 0 ≤ p 1 := by
  simp only [Inst.baseY, Bool.and_eq_true, decide_eq_true_eq] at hY
  obtain ⟨⟨ha, hb⟩, hc⟩ := hY
  have hs := (sr_pos hD).le
  have hconv : Convex ℝ {p : Plane | 0 ≤ p 1} := by
    intro x hx y hy a b ha0 hb0 hab
    simp only [Set.mem_setOf_eq, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at hx hy ⊢
    nlinarith [mul_nonneg ha0 hx, mul_nonneg hb0 hy]
  refine convexHull_min ?_ hconv
  intro p hp
  have key : ∀ q : Pt, 0 ≤ q.y → (0 : ℤ) < q.w → 0 ≤ (q.re Dn) 1 := by
    intro q hq hw
    have hw' := Pt.w_pos q hw
    show 0 ≤ (rp Dn q.X q.Y) 1
    rw [rp_one]
    have : 0 ≤ q.Y := div_nonneg (by exact_mod_cast hq) hw'.le
    exact mul_nonneg this hs
  obtain ⟨wa, wb, wc⟩ := Tri.ok_w I.tgt htok
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl | rfl
  · exact key _ ha wa
  · exact key _ hb wb
  · exact key _ hc wc


theorem Inst_ok_facts (I : Inst) (h : I.ok = true) :
    I.tgt.ok = true ∧ 0 < I.Dn ∧ ∃ p1 p2 p3 p4 p5 p6 : Place,
      I.pl = [p1, p2, p3, p4, p5, p6] ∧
      placeOk I I.sides.1 I.sides.2.2 I.sides.2.1 p1 = true ∧
      placeOk I I.sides.2.2 I.sides.1 I.sides.2.1 p2 = true ∧
      placeOk I I.sides.1 I.sides.2.1 I.sides.2.2 p3 = true ∧
      placeOk I I.sides.2.1 I.sides.1 I.sides.2.2 p4 = true ∧
      placeOk I I.sides.2.2 I.sides.2.1 I.sides.1 p5 = true ∧
      placeOk I I.sides.2.1 I.sides.2.2 I.sides.1 p6 = true := by
  unfold Inst.ok at h
  generalize hs : I.sides = s at h
  obtain ⟨a, b, c⟩ := s
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨-, htok⟩, hDn⟩, hm⟩ := h
  refine ⟨htok, hDn, ?_⟩
  revert hm
  rcases hpl : I.pl with _ | ⟨p1, _ | ⟨p2, _ | ⟨p3, _ | ⟨p4, _ | ⟨p5, _ | ⟨p6, _ | ⟨p7, rest⟩⟩⟩⟩⟩⟩⟩ <;>
    simp only [Bool.and_eq_true]
  all_goals first | (intro hm; simp at hm; done) | skip
  intro hm
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := hm
  exact ⟨p1, p2, p3, p4, p5, p6, rfl, h1, h2, h3, h4, h5, h6⟩

end Refl
