import Erdos634.Draft.LaczFormalColumnMain
import Erdos634.Draft.LaczFormalMJControl

/-!
# Non-vacuity of the wall frame: `LFrame` is a `WFrame`, and the hypotheses on a genuine dissection

Erdős #634, base-`β` row, Column Lemma.  This file proves NOTHING new about #634.  Credit: AI assistant (Column Lemma
proposal), Beeson–Roșu, Beeson, Laczkovich, Paliy.  UNAUDITED.  Axiom-clean; no `sorry`.

* `ofLFrame`: the corner frame of a band target is a wall frame: the leg `{O + y v}` is a side of the target, so every
  tile lies in the closed right side (`hside` is the trivial alternative), the one-sided angle sum is the boundary angle
  sum `π` (`pin_angle_sum`), and the arena is the lattice triangle inside the target.  So `WFrame` generalises `LFrame`
  and `WFrame.MJ_main` contains `LFrame.MJ_main` at the levels `lv ≥ 1` (`ofLFrame_MJ`).
* `control_wall_207`: the hypothesis package of `WFrame.MJ_main` is satisfied on the GENUINE kernel-checked
  207-tiling of `T_3(2,3)` (`control_207`): a `WFrame` with `Bnd 1`.  (This wall is the leg of the target; an interior
  wall is exercised in `LaczFormalColumnGrid`.)
-/

namespace Erdos634.LaczMJ

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.LaczJunction Erdos634.LaczJunction.Walk
  Erdos634.LaczJunction.Grammar Erdos634.Draft.TraceCovering Set

variable {N : ℕ} {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ} {p q r : Fin 3}

namespace LFrame

variable (F : LFrame D e f α β γ p q r)

theorem pt_xc_ht (z : Plane) : F.pt (F.xc z) (F.ht z) = z := by
  have hκ : cross F.e0 F.v ≠ 0 := F.hcr.ne'
  have h := Erdos634.LaczCol.WFrame.cramer2 F.e0 F.v (z - D.target.pts p)
  unfold LFrame.pt LFrame.xc LFrame.ht
  have h' : z - D.target.pts p = (cross (z - D.target.pts p) F.v / cross F.e0 F.v) • F.e0 +
      (cross F.e0 (z - D.target.pts p) / cross F.e0 F.v) • F.v := by
    have h2 : (cross F.e0 F.v)⁻¹ • (cross F.e0 F.v • (z - D.target.pts p)) =
        (cross F.e0 F.v)⁻¹ • (cross (z - D.target.pts p) F.v • F.e0 + cross F.e0 (z - D.target.pts p) • F.v) := by
      rw [h]
    rw [smul_smul, inv_mul_cancel₀ hκ, one_smul, smul_add, smul_smul, smul_smul] at h2
    simp only [div_eq_inv_mul]
    exact h2
  rw [add_assoc, ← h'] ; abel

theorem xc_nonneg {z : Plane} (hz : z ∈ D.target.carrier) : 0 ≤ F.xc z := by
  by_contra hneg
  push_neg at hneg
  apply F.pt_not_mem_x (y := F.ht z) hneg
  rw [F.pt_xc_ht]; exact hz

theorem tile_right (i : Fin N) :
    (D.tile i).carrier ⊆ {z | (crossL F.v) z ≤ cross F.v (D.target.pts p)} := by
  intro z hz
  have hzT : z ∈ D.target.carrier := tile_subset_target D.toDissection i hz
  have hx := F.xc_nonneg hzT
  simp only [Set.mem_setOf_eq, crossL_apply]
  have hxc : F.xc z = cross (z - D.target.pts p) F.v / cross F.e0 F.v := rfl
  have hκ := F.hcr
  have h1 : 0 ≤ cross (z - D.target.pts p) F.v := by
    rw [hxc] at hx
    exact (div_nonneg_iff.mp hx).elim (fun h => h.1) (fun h => absurd h.2 (not_le.mpr hκ))
  have h2 : cross F.v z - cross F.v (D.target.pts p) = -cross (z - D.target.pts p) F.v := by
    simp [cross]; ring
  linarith


theorem lam_gt_one_of_mem (F : LFrame D e f α β γ p q r)
    (h : F.pt 1 0 ∈ openSegment ℝ (D.target.pts p) (D.target.pts q)) : 1 < F.lam := by
  obtain ⟨a, b, ha, hb, hab, hmem⟩ := h
  have hq := F.hq
  have e1 : F.pt 1 0 = D.target.pts p + F.e0 := by simp [LFrame.pt]
  rw [e1, hq] at hmem
  have hb1 : b < 1 := by linarith
  have h2 : (b * F.lam - 1) • F.e0 = 0 := by
    have : a • D.target.pts p + b • (D.target.pts p + F.lam • F.e0) = D.target.pts p + F.e0 := hmem
    have h3 : (a + b) • D.target.pts p + (b * F.lam) • F.e0 = D.target.pts p + F.e0 := by
      rw [← this]; simp only [add_smul, smul_add, smul_smul]; abel
    rw [hab, one_smul] at h3
    have h4 : (b * F.lam) • F.e0 = F.e0 := by simpa using h3
    rw [sub_smul, h4, one_smul]; simp
  rcases smul_eq_zero.mp h2 with h5 | h5
  · have : F.lam = 1 / b := by field_simp; linarith
    rw [this]; rw [lt_div_iff₀ hb]; linarith
  · exact absurd h5 F.e0_ne

theorem lam_mul (F : LFrame D e f α β γ p q r) :
    dist (D.target.pts p) (D.target.pts q) = F.lam * (tc e f : ℝ) := by
  rw [dist_comm, dist_eq_norm, F.hq]
  simp [norm_smul, F.he0, abs_of_pos F.hlam]

theorem mu_mul (F : LFrame D e f α β γ p q r) :
    dist (D.target.pts p) (D.target.pts r) = F.mu * (ta e f : ℝ) := by
  rw [dist_comm, dist_eq_norm, F.hr]
  simp [norm_smul, F.hv, abs_of_pos F.hmu]

theorem mu_gt_one_of_mem (F : LFrame D e f α β γ p q r)
    (h : F.pt 0 1 ∈ openSegment ℝ (D.target.pts p) (D.target.pts r)) : 1 < F.mu := by
  obtain ⟨a, b, ha, hb, hab, hmem⟩ := h
  have hr := F.hr
  have e1 : F.pt 0 1 = D.target.pts p + F.v := by simp [LFrame.pt]
  rw [e1, hr] at hmem
  have hb1 : b < 1 := by linarith
  have h2 : (b * F.mu - 1) • F.v = 0 := by
    have : a • D.target.pts p + b • (D.target.pts p + F.mu • F.v) = D.target.pts p + F.v := hmem
    have h3 : (a + b) • D.target.pts p + (b * F.mu) • F.v = D.target.pts p + F.v := by
      rw [← this]; simp only [add_smul, smul_add, smul_smul]; abel
    rw [hab, one_smul] at h3
    have h4 : (b * F.mu) • F.v = F.v := by simpa using h3
    rw [sub_smul, h4, one_smul]; simp
  rcases smul_eq_zero.mp h2 with h5 | h5
  · have : F.mu = 1 / b := by field_simp; linarith
    rw [this]; rw [lt_div_iff₀ hb]; linarith
  · exact absurd h5 F.v_ne

end LFrame

end Erdos634.LaczMJ

namespace Erdos634.LaczCol

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.LaczJunction Erdos634.LaczJunction.Walk
  Erdos634.LaczJunction.Grammar Erdos634.Draft.TraceCovering Erdos634.LaczMJ Erdos634.LaczWall
  Erdos634.VertexFigureReal Erdos634.BaseBetaTargetCoord Set

variable {N : ℕ} {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ} {p q r : Fin 3}



/-- **A corner frame is a wall frame**: the leg of the target is a wall (every tile lies on its right). -/
noncomputable def ofLFrame (F : LFrame D e f α β γ p q r) : WFrame D e f α β γ p q r where
  S := F.S
  O := D.target.pts p
  e0 := F.e0
  v := F.v
  he0 := F.he0
  hv := F.hv
  hu := F.hu
  hcr := F.hcr
  lam := F.lam
  mu := F.mu
  hlam := F.hlam
  hmu := F.hmu
  hint := fun x y hx hy hxy => F.pt_interior hx hy hxy
  hside := fun y _ _ i _ => Or.inl (F.tile_right i)
  hsum := by
    intro y h0 h1
    classical
    have hall : Side D.toDissection (crossL F.v) (cross F.v (D.target.pts p)) = Finset.univ := by
      apply Finset.eq_univ_of_forall
      intro i
      rw [mem_Side]
      exact F.tile_right i
    rw [hall]
    have hpt : D.target.pts p + y • F.v = F.pt 0 y := by simp [LFrame.pt]
    obtain ⟨hfr, hnv⟩ := F.leg_front h0 h1
    rw [hpt]
    exact Erdos634.PinPlumbing.pin_angle_sum D.toDissection hfr hnv

theorem ofLFrame_pt (F : LFrame D e f α β γ p q r) (x y : ℝ) : (ofLFrame F).pt x y = F.pt x y := rfl

theorem ofLFrame_Bnd (F : LFrame D e f α β γ p q r) (H : ℕ) : (ofLFrame F).Bnd H ↔ F.Bnd H := Iff.rfl

/-- **Consistency**: the wall theorem, applied to the wall frame of a corner frame, gives the rules `T(m)`, `A(m)`
of the corner at all levels `lv ≥ 1` (the old `LFrame.MJ_main`, without level 0). -/
theorem ofLFrame_MJ (F : LFrame D e f α β γ p q r) {H : ℕ} (hB : F.Bnd H) :
    ∀ m, (ofLFrame F).TRule H m ∧ (ofLFrame F).ARule H m := (ofLFrame F).MJ_main hB

/-- **The hypothesis package of `WFrame.MJ_main` on the genuine 207-tiling of `T_3(2,3)`**: a `WFrame` (band setting
`S`, arena, wall = the left leg, one-sided angle sum), with `Bnd 13` (`λ = 138/9`, `μ = 81/6`).  `control_207` is the
kernel-checked tiling; the frame is `ofLFrame` of the corner frame of `MJPackage`.  (On this tiling the premises of the rules
`T(m)`, `A(m)` are never met: the rules are proved by contradiction and the 207-tiling lies outside the band.  The premises
and the conclusion of `T(m)` are exercised on the grid: `LaczFormalColumnCtl.grid_TRule_exercised`.) -/
theorem control_wall_207 :
    ∃ (N : ℕ) (D : CongruentDissection N) (p q r : Fin 3)
      (W : WFrame D 2 3 (modelAlpha (2 : ℝ) 3) (modelBeta (2 : ℝ) 3)
        (2 * modelAlpha (2 : ℝ) 3 + modelBeta (2 : ℝ) 3) p q r), W.Bnd 13 := by
  obtain ⟨N, D, p, q, r, -, -, -, -, -, -, hdq, hdr, -, -, hP⟩ := control_207
  obtain ⟨S, F, L, hFS, h1, h2, -, -, -, -⟩ := hP
  refine ⟨N, D, p, q, r, ofLFrame F, ?_⟩
  have hc : (tc 2 3 : ℝ) = 9 := by norm_num [tc]
  have ha : (ta 2 3 : ℝ) = 6 := by norm_num [ta]
  have h1' := F.lam_mul
  have h2' := F.mu_mul
  rw [hdq, hc] at h1'
  rw [hdr, ha] at h2'
  refine ⟨?_, ?_⟩
  · show ((13 : ℕ) : ℝ) < F.lam
    norm_num at h1' ⊢
    linarith
  · show ((13 : ℕ) : ℝ) < F.mu
    norm_num at h2' ⊢
    linarith

#print axioms ofLFrame
#print axioms ofLFrame_MJ
#print axioms control_wall_207

end Erdos634.LaczCol
