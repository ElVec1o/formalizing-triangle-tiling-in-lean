-- Draft/LaczFormalIIcL8o.lean -- Laczkovich (DCG 48 (2012)), Sect. 6.3, L8 `gexc_disjoint`, step 8: DETERMINISM of Gamma_except.
--  `walkU_det`   : two maximal walks from the same start along the same direction coincide;  `walkU_congr_par` : the walk predicate only depends on the direction up to positive scaling;
--  `grun_det`    : the end of the gamma-run of a division is determined by the division;
--  `gexc_det`    : GExc X Y and GExc X Y' with Y - X, Y' - X positively parallel give Y = Y'.
--  `walkU_prefix_at_head`: a walk can be cut after any of its elements.
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcL8l

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ}

theorem triStep_congr_par {T : Tri} {d d' : V2} {U U' : Plane} (h : TriStep T d U U') (hp : Par d d') : TriStep T d' U U' := by
  obtain ⟨kk, f, g, hk, hf, hfk, hgk, hgf, hpar, hleft⟩ := h
  refine ⟨kk, f, g, hk, hf, hfk, hgk, hgf, hpar.trans hp, ?_⟩
  obtain ⟨c, hc, hcd⟩ := hp.smul
  have : crs d (toV2 (T.pts g - U)) = c * crs d' (toV2 (T.pts g - U)) := by
    rw [hcd]; unfold crs; ring
  rw [this] at hleft
  exact (mul_pos_iff_of_pos_left hc).mp hleft

theorem par_neg2 {d d' : V2} (hp : Par d d') : Par (neg2 d) (neg2 d') := by
  refine ⟨?_, ?_⟩
  · have := hp.1; unfold crs at this ⊢; simp only [neg2]; linarith
  · have := hp.2; unfold dt at this ⊢; simp only [neg2]; linarith

theorem stepU_congr_par (D : RegionDissection N) {b : Bool} {d d' : V2} {e : Fin N × Plane × Plane} (h : StepU D b d e) (hp : Par d d') : StepU D b d' e := by
  cases b
  · simp only [StepU, Bool.false_eq_true, if_false] at h ⊢
    exact triStep_congr_par h (par_neg2 hp)
  · simp only [StepU, if_true] at h ⊢
    exact triStep_congr_par h hp

theorem walkU_congr_par {D : RegionDissection N} {b : Bool} {d d' : V2} {X Y : Plane} {L : List (Fin N × Plane × Plane)} (W : WalkU D b d X Y L) (hp : Par d d') :
    WalkU D b d' X Y L := by
  induction W with
  | nil X => exact WalkU.nil X
  | cons hS _ ih => exact WalkU.cons (stepU_congr_par D hS hp) ih

theorem walkU_det (D : RegionDissection N) [HasFansC D] {b : Bool} {d : V2} {X Z : Plane} {L : List (Fin N × Plane × Plane)} (W : WalkU D b d X Z L) :
    ∀ {Z' : Plane} {L' : List (Fin N × Plane × Plane)}, WalkU D b d X Z' L' → (∀ i U', ¬ StepU D b d (i, Z, U')) → (∀ i U', ¬ StepU D b d (i, Z', U')) →
      Z = Z' ∧ L = L' := by
  induction W with
  | nil X =>
    intro Z' L' W' hZ hZ'
    cases W' with
    | nil => exact ⟨rfl, rfl⟩
    | cons hS _ => exact absurd hS (hZ _ _)
  | @cons i X X' Y L hS W ih =>
    intro Z' L' W' hZ hZ'
    cases W' with
    | nil => exact absurd hS (hZ' _ _)
    | @cons i' _ X'' _ L'' hS' W'' =>
      obtain ⟨hii, hXX⟩ := stepU_unique D hS hS'
      subst hii; subst hXX
      obtain ⟨h1, h2⟩ := ih W'' hZ hZ'
      exact ⟨h1, by rw [h2]⟩

theorem grun_det (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) {L : List (Fin N × Plane × Plane)} {H H' : Plane}
    (h : GRunEnd D idx L H) (h' : GRunEnd D idx L H') : H = H' := by
  obtain ⟨L1, L2, hL, hne, hall, hhead, e0, hlast, he0⟩ := h
  obtain ⟨M1, M2, hM, hne', hall', hhead', e0', hlast', he0'⟩ := h'
  have heq : L1 ++ L2 = M1 ++ M2 := hL.symm.trans hM
  have hL1M1 : L1 = M1 := by
    rcases List.append_eq_append_iff.mp heq with ⟨a', hM1, hL2⟩ | ⟨c', hL1, hM2⟩
    · cases a' with
      | nil => simpa using hM1.symm
      | cons x a'' =>
        exfalso
        have hx : x ∈ M1 := by rw [hM1]; simp
        have := hhead x (by rw [hL2]; simp)
        exact this (hall' x hx)
    · cases c' with
      | nil => simpa using hL1
      | cons x c'' =>
        exfalso
        have hx : x ∈ L1 := by rw [hL1]; simp
        have := hhead' x (by rw [hM2]; simp)
        exact this (hall x hx)
  subst hL1M1
  rw [hlast] at hlast'
  have := Option.some.inj hlast'
  subst this
  rw [← he0, ← he0']

/-- the data of an edge needed for determinism: both walks, their run ends, and `Y` on the ray. -/
theorem gexc_data (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (idx : Fin N → Equiv.Perm (Fin 3)) {X Y : Plane} (h : GExc D idx X Y) :
    ∃ (d : V2) (Z : Plane) (L1 L2 : List (Fin N × Plane × Plane)) (H1 H2 : Plane) (T1 T2 : ℝ), d ≠ 0 ∧ WalkU D.toRegionDissection true d X Z L1 ∧ WalkU D.toRegionDissection false d X Z L2 ∧
      (∀ i U', ¬ StepU D.toRegionDissection true d (i, Z, U')) ∧ (∀ i U', ¬ StepU D.toRegionDissection false d (i, Z, U')) ∧
      GRunEnd D idx L1 H1 ∧ GRunEnd D idx L2 H2 ∧ 0 < T1 ∧ 0 < T2 ∧ toV2 (H1 - X) = (T1 * d.1, T1 * d.2) ∧ toV2 (H2 - X) = (T2 * d.1, T2 * d.2) ∧
      ((Y = H1 ∧ dist X H1 ≤ dist X H2) ∨ (Y = H2 ∧ dist X H2 ≤ dist X H1)) := by
  obtain ⟨d, Z, L1, L2, H1, H2, hd, hnb, W1, W2, hL1, hL2, hnoL, hnoR, hr1, hr2, hY⟩ := h
  have WU1 := walkU_of_T W1
  have WU2 := walkU_of_R W2
  obtain ⟨P1, Q1, e1, -, hP1, w1, s1, hall1, hhead1, he1, he1H⟩ := grun_split' D idx WU1 hr1
  obtain ⟨P2, Q2, e2, -, hP2, w2, s2, hall2, hhead2, he2, he2H⟩ := grun_split' D idx WU2 hr2
  obtain ⟨T1, hT1n, hT1, hT1p, -⟩ := walkU_pos w1
  obtain ⟨T2, hT2n, hT2, hT2p, -⟩ := walkU_pos w2
  have hT1pos := hT1p hP1
  have hT2pos := hT2p hP2
  refine ⟨d, Z, L1, L2, H1, H2, T1, T2, hd, WU1, WU2, fun i U' => by simpa [StepU] using hnoL i U', fun i U' => by simpa [StepU] using hnoR i U', hr1, hr2, hT1pos, hT2pos, hT1, hT2, ?_⟩
  exact hY

/-- **Determinism of Gamma_except**: two edges from the same start along the same ray end at the same point. -/
theorem gexc_det (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (idx : Fin N → Equiv.Perm (Fin 3)) {X Y Y' : Plane}
    (h : GExc D idx X Y) (h' : GExc D idx X Y') (hpar : Par (toV2 (Y - X)) (toV2 (Y' - X))) : Y = Y' := by
  obtain ⟨d, Z, L1, L2, H1, H2, T1, T2, hd, W1, W2, hmL, hmR, hr1, hr2, hT1, hT2, hH1, hH2, hY⟩ := gexc_data D idx h
  obtain ⟨d', Z', L1', L2', H1', H2', T1', T2', hd', W1', W2', hmL', hmR', hr1', hr2', hT1', hT2', hH1', hH2', hY'⟩ := gexc_data D idx h'
  have hYd : Par (toV2 (Y - X)) d := by
    rcases hY with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact par_of_param hd hT1 hH1
    · exact par_of_param hd hT2 hH2
  have hYd' : Par (toV2 (Y' - X)) d' := by
    rcases hY' with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact par_of_param hd' hT1' hH1'
    · exact par_of_param hd' hT2' hH2'
  have hdd : Par d' d := (hYd'.symm.trans (hpar.symm.trans hYd))
  have hdd' : Par d d' := hdd.symm
  have W1'' := walkU_congr_par W1' hdd
  have W2'' := walkU_congr_par W2' hdd
  obtain ⟨hZ1, hL1⟩ := walkU_det D.toRegionDissection W1 W1'' hmL (fun i U' hS => hmL' i U' (stepU_congr_par D.toRegionDissection hS hdd'))
  obtain ⟨hZ2, hL2⟩ := walkU_det D.toRegionDissection W2 W2'' hmR (fun i U' hS => hmR' i U' (stepU_congr_par D.toRegionDissection hS hdd'))
  subst hL1; subst hL2
  have e1 : H1 = H1' := grun_det D idx hr1 hr1'
  have e2 : H2 = H2' := grun_det D idx hr2 hr2'
  subst e1; subst e2
  have heq : H1 = H2 → True := fun _ => trivial
  have hsame : ∀ (hl : dist X H1 ≤ dist X H2) (hl' : dist X H2 ≤ dist X H1), H1 = H2 := by
    intro hl hl'
    have a1 := pos_le_of_dist_le hd hT1.le hT2.le hH1 hH2 hl
    have a2 := pos_le_of_dist_le hd hT2.le hT1.le hH2 hH1 hl'
    have : T1 = T2 := le_antisymm a1 a2
    subst this
    exact pt_eq_of_pos hH1 hH2
  rcases hY with ⟨hYe, hle⟩ | ⟨hYe, hle⟩ <;> rcases hY' with ⟨hYe', hle'⟩ | ⟨hYe', hle'⟩
  · rw [hYe, hYe']
  · rw [hYe, hYe']; exact hsame hle hle'
  · rw [hYe, hYe']; exact (hsame hle' hle).symm
  · rw [hYe, hYe']

end Erdos634.Draft.LaczFormal.RG
