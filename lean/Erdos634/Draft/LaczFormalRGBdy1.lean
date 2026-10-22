-- Draft/LaczFormalRGBdy1.lean -- S4 of PLAN_THM21: the fans at a boundary vertex of a dissection of a region WITH THE SHAPE of the virtual sectors exposed:
-- on an open side one virtual straight sector `(-pT, pT)` with target cone `{z | 0 <= crs pT z}`; at a corner two virtual sectors `(qT, -qT)` and `(-qT, pT)` with target cone `inCone pT qT`.
-- UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 4), Beeson, Beeson-Zhang; shape versions of the project's LaczFormalGraphExt constructions.
import Erdos634.Draft.LaczFormalRGExt

open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph

namespace Erdos634.Draft.LaczFormal.RG

variable {N : ℕ}

/-- Vertex in the relative interior of a side of the target. -/
theorem extFan_side_shape (D : RegionDissection N) (V : Plane) (T : Tri) (m : Fin 3) (h0 : T.basis.coord m V = 0)
    (hpos : ∀ j, j ≠ m → 0 < T.basis.coord j V) {ρ : ℝ} (hρ : 0 < ρ)
    (hiff : ∀ y, dist y V < ρ → (y ∈ D.region ↔ y ∈ T.carrier)) (hvert : ∃ i k, (D.tile i).pts k = V) :
    ∃ (pT : V2) (F : ExtFan D V Unit), pT ≠ 0 ∧ F.pe () = (-pT.1, -pT.2) ∧ F.qe () = pT ∧ F.Tgt = {z | inCone pT (-pT.1, -pT.2) z} := by
  classical
  have hN : 0 < N := by obtain ⟨i, _⟩ := hvert; exact Fin.pos i
  obtain ⟨pT, qT, hokT, hlocT, hwdT, hspecT⟩ := straight_sector T m V h0 hpos
  have hqT : qT = (-pT.1, -pT.2) := by
    rcases hspecT with ⟨k, hk, _⟩ | ⟨_, m', _, _, hq, _⟩
    · exact absurd hk (edge_coords_not_vertex T m V h0 hpos k)
    · exact hq
  subst hqT
  have hpT : pT ≠ 0 := hokT.ne_p
  obtain ⟨R, hR, hRT⟩ := hlocT
  suffices h : ∃ F : ExtFan D V Unit, F.Tgt = {z | inCone pT (-pT.1, -pT.2) z} ∧ F.pe = (fun _ : Unit => (-pT.1, -pT.2)) ∧ F.qe = (fun _ : Unit => pT) by
    obtain ⟨F, h1, h2, h3⟩ := h
    exact ⟨pT, F, hpT, by rw [h2], by rw [h3], h1⟩
  refine extFan_of' D V hvert {z | inCone pT (-pT.1, -pT.2) z} (min ρ R) (lt_min hρ hR)
    (fun y hy => by rw [hiff y (lt_of_lt_of_le hy (min_le_left _ _))]; simpa using hRT y (lt_of_lt_of_le hy (min_le_right _ _)))
    (fun z hz t ht => (inCone_smul_iff ht).mpr hz)
    (fun x hx y hy a b ha hb hab => inCone_convex hx hy ha hb hab)
    (fun _ : Unit => (-pT.1, -pT.2)) (fun _ : Unit => pT) (fun _ => secOK_ext hpT) ?_ ?_ ?_ ?_
  · intro z hz
    simp only [Set.mem_setOf_eq, inCone_straight_iff, not_le] at hz
    refine ⟨(), ?_, ?_⟩
    · show 0 ≤ crs (-pT.1, -pT.2) z; unfold crs at hz ⊢; nlinarith
    · show 0 ≤ crs z pT; unfold crs at hz ⊢; nlinarith
  · intro j j' hne; exact absurd (Subsingleton.elim j j') hne
  · intro j z hz hin
    simp only [Set.mem_setOf_eq, inCone_straight_iff] at hin
    have := hz.1
    unfold crs at this hin; simp only at this hin; nlinarith
  · rw [sum_localAngle_tri D hN T hρ hiff, Fintype.sum_unique]
    show T.localAngle V + wd (-pT.1, -pT.2) pT = 2 * Real.pi
    rw [wd_ext hpT, localAngle_of_edge_coords T m V h0 hpos]; ring

/-- Corner of the target. -/
theorem extFan_corner_shape (D : RegionDissection N) (T : Tri) (j : Fin 3) {ρ : ℝ} (hρ : 0 < ρ)
    (hiff : ∀ y, dist y (T.pts j) < ρ → (y ∈ D.region ↔ y ∈ T.carrier)) (hvert : ∃ i k, (D.tile i).pts k = T.pts j) :
    ∃ (pT qT : V2) (F : ExtFan D (T.pts j) Bool), 0 < crs pT qT ∧ F.pe true = (-qT.1, -qT.2) ∧ F.qe true = pT ∧ F.pe false = qT ∧ F.qe false = (-qT.1, -qT.2) ∧ F.Tgt = {z | inCone pT qT z} ∧ SectorSpec T (T.pts j) pT qT := by
  classical
  have hN : 0 < N := by obtain ⟨i, _⟩ := hvert; exact Fin.pos i
  obtain ⟨pT, qT, hokT, hlocT, hwdT, hspecT⟩ := corner_sector T j
  have hcrs : 0 < crs pT qT := crs_pos_of_corner hokT hspecT ⟨j, rfl⟩
  have hpT : pT ≠ 0 := hokT.ne_p
  have hqT : qT ≠ 0 := hokT.ne_q
  obtain ⟨R, hR, hRT⟩ := hlocT
  set pe : Bool → V2 := fun b => if b then (-qT.1, -qT.2) else qT with hpe
  set qe : Bool → V2 := fun b => if b then pT else (-qT.1, -qT.2) with hqe
  have hok1 : SecOK qT (-qT.1, -qT.2) := Or.inr ⟨crs_straight qT, dt_straight_neg hqT⟩
  have hok2 : SecOK (-qT.1, -qT.2) pT := by
    left
    have : crs (-qT.1, -qT.2) pT = crs pT qT := by unfold crs; ring
    rw [this]; exact hcrs
  suffices h : ∃ F : ExtFan D (T.pts j) Bool, F.Tgt = {z | inCone pT qT z} ∧ F.pe = pe ∧ F.qe = qe by
    obtain ⟨F, h1, h2, h3⟩ := h
    exact ⟨pT, qT, F, hcrs, by rw [h2]; simp [hpe], by rw [h3]; simp [hqe], by rw [h2]; simp [hpe], by rw [h3]; simp [hqe], h1, hspecT⟩
  refine extFan_of' D _ hvert {z | inCone pT qT z} (min ρ R) (lt_min hρ hR)
    (fun y hy => by rw [hiff y (lt_of_lt_of_le hy (min_le_left _ _))]; simpa using hRT y (lt_of_lt_of_le hy (min_le_right _ _)))
    (fun z hz t ht => (inCone_smul_iff ht).mpr hz)
    (fun x hx y hy a b ha hb hab => inCone_convex hx hy ha hb hab) pe qe
    (by intro b; cases b <;> simp [hpe, hqe, hok1, hok2]) ?_ ?_ ?_ ?_
  · intro z hz
    simp only [Set.mem_setOf_eq, inCone, not_and_or, not_le] at hz
    by_cases h : 0 ≤ crs qT z
    · exact ⟨false, by
        simp only [hpe, hqe, Bool.false_eq_true, if_false]
        exact (inCone_straight_iff qT z).mpr h⟩
    · push Not at h
      refine ⟨true, ?_, ?_⟩
      · simp only [hpe, hqe, if_true, eq_self_iff_true]
        unfold crs at h hz ⊢
        rcases hz with hz | hz <;> nlinarith
      · simp only [hpe, hqe, if_true, eq_self_iff_true]
        unfold crs at h hz ⊢
        rcases hz with hz | hz <;> nlinarith
  · intro b b' hbb z ⟨hz1, hz2⟩
    cases b <;> cases b' <;> simp only [hpe, hqe, Bool.false_eq_true, Bool.true_eq_false, if_true, if_false, eq_self_iff_true] at hz1 hz2
    · exact hbb rfl
    · obtain ⟨a1, a2⟩ := hz1
      obtain ⟨b1, b2⟩ := hz2
      unfold crs at a1 a2 b1 b2; nlinarith
    · obtain ⟨a1, a2⟩ := hz1
      obtain ⟨b1, b2⟩ := hz2
      unfold crs at a1 a2 b1 b2; nlinarith
    · exact hbb rfl
  · intro b z hz hin
    simp only [Set.mem_setOf_eq, inCone] at hin
    cases b <;> simp only [hpe, hqe, Bool.false_eq_true, Bool.true_eq_false, if_true, if_false, eq_self_iff_true] at hz
    · obtain ⟨a1, a2⟩ := hz; obtain ⟨b1, b2⟩ := hin
      unfold crs at a1 a2 b1 b2; nlinarith
    · obtain ⟨a1, a2⟩ := hz; obtain ⟨b1, b2⟩ := hin
      unfold crs at a1 a2 b1 b2; nlinarith
  · rw [sum_localAngle_tri D hN T hρ hiff, Fintype.sum_bool]
    simp only [hpe, hqe, Bool.false_eq_true, Bool.true_eq_false, if_true, if_false, eq_self_iff_true]
    rw [wd_straight hqT, wd_neg_left hcrs, ← hwdT]
    ring


end Erdos634.Draft.LaczFormal.RG
