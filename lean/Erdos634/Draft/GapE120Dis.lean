import Erdos634.Draft.Chain15X
import Erdos634.Draft.GapE120Arith
import Erdos634.Draft.GapE120SSS
import Erdos634.Refl.BridgeE120
import Erdos634.Realizable

/-! Draft/GapE120Dis.lean -- `GapE120 15` discharged, modulo the kernel-checked certificate of `Refl.BridgeE120`.
    Chain: `e120_shape` (N = 15: tile = λ(3,5,7), target side 15λ; the (3,15)/(15,3) cases refuted) →
    `scaleDissection` by 1/λ → SSS (`Tri.congruent_of_dist`) puts the scaled target/model congruent to `BridgeE120.TGT`/`MODEL`
    → `BridgeE120.not_dissection_refl` (chunked reflective certificate, 1860 nodes).  UNAUDITED. -/

open scoped Classical
open Erdos634.Geometry Erdos634.CertNode Erdos634.CertCoord

namespace Erdos634.Geometry.GapE120Dis

theorem TGT_sides : dist (Refl.BridgeE120.TGT.pts 0) (Refl.BridgeE120.TGT.pts 1) = 15 ∧
    dist (Refl.BridgeE120.TGT.pts 1) (Refl.BridgeE120.TGT.pts 2) = 15 ∧
    dist (Refl.BridgeE120.TGT.pts 0) (Refl.BridgeE120.TGT.pts 2) = 15 :=
  model_sides_rp Refl.BridgeE120.hD3 Refl.BridgeE120.TGT_pos (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem sw0 : (Equiv.swap (1 : Fin 3) 2) 0 = 0 := by decide
theorem sw1 : (Equiv.swap (1 : Fin 3) 2) 1 = 2 := by decide
theorem sw2 : (Equiv.swap (1 : Fin 3) 2) 2 = 1 := by decide
theorem fr0 : finRotate 3 0 = 1 := by decide
theorem fr1 : finRotate 3 1 = 2 := by decide
theorem fr2 : finRotate 3 2 = 0 := by decide

theorem perm_opp : ∀ σ : Equiv.Perm (Fin 3),
    ((σ 0 + 1 = σ 1 ∧ σ 0 + 2 = σ 2) ∨ (σ 0 + 1 = σ 2 ∧ σ 0 + 2 = σ 1)) ∧
    ((σ 1 + 1 = σ 0 ∧ σ 1 + 2 = σ 2) ∨ (σ 1 + 1 = σ 2 ∧ σ 1 + 2 = σ 0)) ∧
    ((σ 2 + 1 = σ 0 ∧ σ 2 + 2 = σ 1) ∨ (σ 2 + 1 = σ 1 ∧ σ 2 + 2 = σ 0)) := by decide

/-- the three side lengths of a tile in the order of a `TwoPiThreeData` permutation -/
theorem sides_of_perm (M : Tri) (σ : Equiv.Perm (Fin 3)) :
    dist (M.pts (σ 1)) (M.pts (σ 2)) = M.oppLen (σ 0) ∧
    dist (M.pts (σ 0)) (M.pts (σ 2)) = M.oppLen (σ 1) ∧
    dist (M.pts (σ 0)) (M.pts (σ 1)) = M.oppLen (σ 2) := by
  obtain ⟨h0, h1, h2⟩ := perm_opp σ
  refine ⟨?_, ?_, ?_⟩
  · unfold Tri.oppLen
    rcases h0 with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · rw [e1, e2]
    · rw [e1, e2, dist_comm]
  · unfold Tri.oppLen
    rcases h1 with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · rw [e1, e2]
    · rw [e1, e2, dist_comm]
  · unfold Tri.oppLen
    rcases h2 with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · rw [e1, e2]
    · rw [e1, e2, dist_comm]

/-- a relabelled, scaled model with sides `(3,5,7)` is congruent to `MODEL`. -/
theorem cong_of_sides (M : Tri) (r : ℝ) (hr : 0 < r) (τ : Equiv.Perm (Fin 3))
    (hx : r * dist (M.pts (τ 0)) (M.pts (τ 1)) = 3) (hy : r * dist (M.pts (τ 1)) (M.pts (τ 2)) = 5)
    (hz : r * dist (M.pts (τ 0)) (M.pts (τ 2)) = 7) :
    (Erdos634.DissectionMap.mapTri (Erdos634.Realizable.homothetyEquiv 0 r hr.ne') M).Congruent
      Refl.BridgeE120.MODEL := by
  set T := Erdos634.DissectionMap.mapTri (Erdos634.Realizable.homothetyEquiv 0 r hr.ne') M with hT
  have hdist : ∀ i j, dist ((T.relabel τ).pts i) ((T.relabel τ).pts j) = r * dist (M.pts (τ i)) (M.pts (τ j)) := by
    intro i j
    simp only [Tri.relabel_pts, hT, Erdos634.DissectionMap.mapTri, Function.comp]
    rw [Erdos634.Realizable.homothetyEquiv_dist 0 r hr.ne', abs_of_pos hr]
  obtain ⟨m1, m2, m3⟩ := Refl.BridgeE120.MODEL_sides
  have := Tri.congruent_of_dist (T.relabel τ) Refl.BridgeE120.MODEL
    (by rw [hdist, hx, m1]) (by rw [hdist, hy, m2]) (by rw [hdist, hz, m3])
  exact (T.congruent_relabel τ).trans this

/-- **`GapE120 15`**: no `CongruentDissection 15` has a `2π/3` tile with `α ∉ ℚπ` and an equilateral target. -/
theorem gapE120_15 : Erdos634.Draft.Chain15.GapE120 15 := by
  intro D α a b c hα h hP
  have hα' : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi := hα
  obtain ⟨l, hl, hS, hc, hab⟩ := GapE120.e120_shape D hα' h hP
  have hr : 0 < l⁻¹ := inv_pos.mpr hl
  have hrl : ∀ x : ℝ, l⁻¹ * (x * l) = x := fun x => by field_simp
  set D' := Erdos634.Realizable.scaleDissection 0 l⁻¹ hr.ne' D with hD'
  obtain ⟨e1, e2, -⟩ := Row5.equilateral_boundary D hα' 0 (fun k => D.model.data_angles_mem hα' h 0 k) hP
  have d01 : dist (D.target.pts 0) (D.target.pts 1) = 15 * l := by
    rw [← hS, ← e2]; unfold Tri.oppLen; rfl
  have d12 : dist (D.target.pts 1) (D.target.pts 2) = 15 * l := by
    rw [← hS]; unfold Tri.oppLen; rfl
  have d02 : dist (D.target.pts 0) (D.target.pts 2) = 15 * l := by
    rw [← hS, ← e1, dist_comm]; unfold Tri.oppLen; rfl
  have tdist : ∀ i j, dist (D'.target.pts i) (D'.target.pts j) = l⁻¹ * dist (D.target.pts i) (D.target.pts j) := by
    intro i j
    rw [hD', Erdos634.Realizable.scaleDissection_target_pts, Erdos634.Realizable.scaleDissection_target_pts,
      Erdos634.Realizable.homothetyEquiv_dist, abs_of_pos hr]
  obtain ⟨g1, g2, g3⟩ := TGT_sides
  have hT : D'.target.Congruent Refl.BridgeE120.TGT :=
    Tri.congruent_of_dist _ _ (by rw [tdist, d01, g1]; exact hrl 15) (by rw [tdist, d12, g2]; exact hrl 15)
      (by rw [tdist, d02, g3]; exact hrl 15)
  obtain ⟨σ, -, oa, -, ob, -, oc⟩ := h
  obtain ⟨s1, s2, s3⟩ := sides_of_perm D.model σ
  rw [oa] at s1; rw [ob] at s2; rw [oc] at s3
  have hM : D'.model.Congruent Refl.BridgeE120.MODEL := by
    rcases hab with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · refine cong_of_sides D.model l⁻¹ hr ((Equiv.swap (1 : Fin 3) 2).trans σ) ?_ ?_ ?_
      · have : ((Equiv.swap (1 : Fin 3) 2).trans σ) 0 = σ 0 := by simp [sw0]
        have h2 : ((Equiv.swap (1 : Fin 3) 2).trans σ) 1 = σ 2 := by simp [sw1]
        rw [this, h2, s2, hb]; exact hrl 3
      · have h1 : ((Equiv.swap (1 : Fin 3) 2).trans σ) 1 = σ 2 := by simp [sw1]
        have h2 : ((Equiv.swap (1 : Fin 3) 2).trans σ) 2 = σ 1 := by simp [sw2]
        rw [h1, h2, dist_comm, s1, ha]; exact hrl 5
      · have h0 : ((Equiv.swap (1 : Fin 3) 2).trans σ) 0 = σ 0 := by simp [sw0]
        have h2 : ((Equiv.swap (1 : Fin 3) 2).trans σ) 2 = σ 1 := by simp [sw2]
        rw [h0, h2, s3, hc]; exact hrl 7
    · refine cong_of_sides D.model l⁻¹ hr ((finRotate 3).trans σ) ?_ ?_ ?_
      · have h0 : ((finRotate 3).trans σ) 0 = σ 1 := by simp [fr0]
        have h1 : ((finRotate 3).trans σ) 1 = σ 2 := by simp [fr1]
        rw [h0, h1, s1, ha]; exact hrl 3
      · have h1 : ((finRotate 3).trans σ) 1 = σ 2 := by simp [fr1]
        have h2 : ((finRotate 3).trans σ) 2 = σ 0 := by simp [fr2]
        rw [h1, h2, dist_comm, s2, hb]; exact hrl 5
      · have h0 : ((finRotate 3).trans σ) 0 = σ 1 := by simp [fr0]
        have h2 : ((finRotate 3).trans σ) 2 = σ 0 := by simp [fr2]
        rw [h0, h2, dist_comm, s3, hc]; exact hrl 7
  exact Refl.BridgeE120.not_dissection_refl D' hT hM

end Erdos634.Geometry.GapE120Dis

#print axioms Erdos634.Geometry.GapE120Dis.gapE120_15

/-- `chain_fifteen6` with `GapE120 15` discharged: `N = 15` needs only `GapA2`. -/
theorem Erdos634.Geometry.GapE120Dis.chain_fifteen7 (A2 : Erdos634.CaseA.R0c15.GapA2) (D : CongruentDissection 15) :
    False :=
  Erdos634.Draft.Chain15.chain_fifteen6 A2 gapE120_15 D

#print axioms Erdos634.Geometry.GapE120Dis.chain_fifteen7
