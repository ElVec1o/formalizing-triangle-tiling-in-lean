-- Draft/LaczFormalIIcL8j.lean -- Laczkovich (DCG 48 (2012)), Sect. 6.3, L8 `gexc_disjoint`, step 3: `no_inner_cross` (B1).
-- A tile T1 with a point Q in the OPEN side of one of its sides (a tile having Q "inside a side") cannot sit on a point Q of the inner part of a walk (division of a segment into tile sides) along a
-- line NOT parallel to that side: the left division of the walk has, at Q, a tile whose wedge at Q towards +d or towards -d points strictly to the side of T1, so the interiors of the two tiles meet
-- (`tiles_overlap`), the tiles coincide, and a triangle cannot have Q in the open side of one side and in a second side not parallel to it.
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcL8i
import Erdos634.Draft.LaczFormalRG12GExcEndSplit
import Erdos634.Draft.LaczFormalIIcSharp2

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N : ℕ}

theorem pt_of_params {A B Q X : Plane} {d : V2} {t0 t1 v : ℝ} (hA : toV2 (A - X) = (t0 * d.1, t0 * d.2))
    (hB : toV2 (B - X) = (t1 * d.1, t1 * d.2)) (hQ : toV2 (Q - X) = (v * d.1, v * d.2)) (hlt : t0 < t1) :
    Q = A + ((v - t0) / (t1 - t0)) • (B - A) := by
  obtain ⟨a0, a1⟩ := coord_of hA
  obtain ⟨b0, b1⟩ := coord_of hB
  obtain ⟨q0, q1⟩ := coord_of hQ
  have hne : t1 - t0 ≠ 0 := by linarith
  apply pl_ext2
  · simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
    rw [a0, b0, q0]; field_simp; ring
  · simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
    rw [a1, b1, q1]; field_simp; ring

/-- At an inner parameter `v` of a left walk there are two tiles: one having `Q` in `[A, B)` (wedge towards `B`, i.e. towards `+d`) and one having `Q` in `(A, B]` (wedge towards `A`, i.e. towards `-d`). -/
theorem walk_fwd_back (D : RegionDissection N) {d : V2} (hd : d ≠ 0) {X Z : Plane} {L : List (Fin N × Plane × Plane)} (W : WalkU D true d X Z L)
    {T v : ℝ} (hT : toV2 (Z - X) = (T * d.1, T * d.2)) {Q : Plane} (hQ : toV2 (Q - X) = (v * d.1, v * d.2)) (hv0 : 0 < v) (hvT : v < T) :
    (∃ (i : Fin N) (A B : Plane) (σ : ℝ), TriStep (D.tile i) d A B ∧ Q = A + σ • (B - A) ∧ 0 ≤ σ ∧ σ < 1) ∧
    (∃ (i : Fin N) (A B : Plane) (σ : ℝ), TriStep (D.tile i) d A B ∧ Q = B + σ • (A - B) ∧ 0 ≤ σ ∧ σ < 1) := by
  constructor
  · obtain ⟨e, he, t0, t1, h0, h1, ht0, ht1⟩ := walkU_cover W hd hT v hv0.le hvT
    have hS := walkU_mem_step W e he
    simp only [StepU, if_true] at hS
    have hlt : t0 < t1 := by linarith
    refine ⟨e.1, e.2.1, e.2.2, (v - t0) / (t1 - t0), hS, pt_of_params h0 h1 hQ hlt, div_nonneg (by linarith) (by linarith), ?_⟩
    rw [div_lt_one (by linarith)]; linarith
  · obtain ⟨e, he, t0, t1, h0, h1, ht0, ht1⟩ := walkU_cover' W hd hT v hv0 hvT.le
    have hS := walkU_mem_step W e he
    simp only [StepU, if_true] at hS
    have hlt : t0 < t1 := by linarith
    refine ⟨e.1, e.2.1, e.2.2, (t1 - v) / (t1 - t0), hS, ?_, div_nonneg (by linarith) (by linarith), ?_⟩
    · have := pt_of_params h0 h1 hQ hlt
      rw [this]
      have hne : t1 - t0 ≠ 0 := by linarith
      have : (v - t0) / (t1 - t0) = 1 - (t1 - v) / (t1 - t0) := by field_simp; ring
      rw [this]; module
    · rw [div_lt_one (by linarith)]; linarith

end Erdos634.Draft.LaczFormal.RG
