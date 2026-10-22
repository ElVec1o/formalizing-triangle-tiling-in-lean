-- Draft/LaczFormalIIcSpoke3.lean -- Laczkovich (DCG 48 (2012)), Sect. 6.3, step 3 (`spokes_angle`), item (c): the bridge from the sector widths `wd` (argument of dot + i cross on `V2`) to `EuclideanGeometry.angle`, and the placement of
-- the endpoint `W` of a `GExc` edge on the ray `V + t d`.  Result `gexc_spoke_angles`: at a (1,1,0) polygon corner `V = P.v (k+1)` an edge `GExc V W` satisfies
--   angle (P.v (k+2)) V W = model angle of the corner label of the OUTGOING tile,   angle (P.v k) V W = model angle of the corner label of the INCOMING tile,
-- with the two labels in {0,1}, distinct (so {alpha, beta}), and the tiles being those of the two boundary TriSteps (needed for the label consistency along the sides, item (d)).
-- Uses `corner_sector_data` (Spoke2) and the existing `wd_eq_angle` (LaczFormalGraphLocal).
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.3, Fig. 6), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcSpoke2

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ}

theorem walkT_head_ray {D : RegionDissection N} {d : V2} {X Y : Plane} {L : List (Fin N × Plane × Plane)} (W : WalkT D d X Y L) :
    ∀ e ∈ L, ∃ T : ℝ, 0 < T ∧ toV2 (e.2.2 - X) = (T * d.1, T * d.2) := by
  induction W with
  | nil X => intro e he; simp at he
  | @cons i X X' Y L hS W ih =>
    intro e he
    obtain ⟨-, -, -, -, -, -, -, -, hpar, -⟩ := id hS
    obtain ⟨c, hc, hcw⟩ := hpar.smul
    rcases List.mem_cons.mp he with h | h
    · subst h; exact ⟨c, hc, hcw⟩
    · obtain ⟨T, hT, hTe⟩ := ih e h
      refine ⟨c + T, by positivity, ?_⟩
      have : toV2 (e.2.2 - X) = ((toV2 (e.2.2 - X')).1 + (toV2 (X' - X)).1, (toV2 (e.2.2 - X')).2 + (toV2 (X' - X)).2) := by
        unfold toV2; ext <;> simp
      rw [this, hTe, hcw]
      ext <;> simp <;> ring

theorem walkR_head_ray {D : RegionDissection N} {d : V2} {X Y : Plane} {L : List (Fin N × Plane × Plane)} (W : WalkR D d X Y L) :
    ∀ e ∈ L, ∃ T : ℝ, 0 < T ∧ toV2 (e.2.2 - X) = (T * d.1, T * d.2) := by
  induction W with
  | nil X => intro e he; simp at he
  | @cons i X X' Y L hS W ih =>
    intro e he
    obtain ⟨-, -, -, -, -, -, -, -, hpar, -⟩ := id hS
    obtain ⟨c, hc, hcw⟩ := hpar.smul
    have hc' : toV2 (X' - X) = (c * d.1, c * d.2) := by
      have h1 : toV2 (X - X') = (c * (neg2 d).1, c * (neg2 d).2) := hcw
      unfold neg2 at h1
      have h2 := congrArg Prod.fst h1
      have h3 := congrArg Prod.snd h1
      simp [toV2] at h2 h3
      unfold toV2
      ext <;> simp <;> linarith
    rcases List.mem_cons.mp he with h | h
    · subst h; exact ⟨c, hc, hc'⟩
    · obtain ⟨T, hT, hTe⟩ := ih e h
      refine ⟨c + T, by positivity, ?_⟩
      have : toV2 (e.2.2 - X) = ((toV2 (e.2.2 - X')).1 + (toV2 (X' - X)).1, (toV2 (e.2.2 - X')).2 + (toV2 (X' - X)).2) := by
        unfold toV2; ext <;> simp
      rw [this, hTe, hc']
      ext <;> simp <;> ring

theorem par_of_smul' {u v : V2} (hv : v ≠ 0) {T : ℝ} (hT : 0 < T) (h : u = (T * v.1, T * v.2)) : Par u v := by
  subst h
  refine ⟨by unfold crs; ring, ?_⟩
  unfold dt
  have : 0 < v.1 * v.1 + v.2 * v.2 := by
    rcases hv' : v with ⟨a, b⟩
    have : a ≠ 0 ∨ b ≠ 0 := by
      by_contra hh; push Not at hh
      apply hv; rw [hv', hh.1, hh.2]; rfl
    rcases this with h | h
    · nlinarith [mul_self_pos.mpr h, mul_self_nonneg b]
    · nlinarith [mul_self_pos.mpr h, mul_self_nonneg a]
  nlinarith

/-- A `GExc` edge leaves its start along some `d` with a tile on both sides at the start, and ends on the ray `X + t d`, `t > 0`. -/
theorem gexc_ray {D : CongruentRegionDissection N} {idx : Fin N → Equiv.Perm (Fin 3)} {X Y : Plane} (h : GExc D idx X Y) :
    ∃ d : V2, d ≠ 0 ∧ (∃ i U, TriStep (D.tile i) d X U) ∧ (∃ i U, TriStep (D.tile i) (neg2 d) U X) ∧ ∃ T : ℝ, 0 < T ∧ toV2 (Y - X) = (T * d.1, T * d.2) := by
  obtain ⟨d, Z, L1, L2, H1, H2, hd, -, W1, W2, hL1, hL2, -, -, hr1, hr2, hY⟩ := h
  refine ⟨d, hd, ?_, ?_, ?_⟩
  · cases W1 with
    | nil => exact absurd rfl hL1
    | cons hS W' => exact ⟨_, _, hS⟩
  · cases W2 with
    | nil => exact absurd rfl hL2
    | cons hS W' => exact ⟨_, _, hS⟩
  · rcases hY with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · obtain ⟨L', L'', hL, -, -, -, e0, hlast, he0⟩ := hr1
      have hmem : e0 ∈ L1 := by rw [hL]; exact List.mem_append_left _ (List.mem_of_getLast? hlast)
      obtain ⟨T, hT, hTe⟩ := walkT_head_ray W1 e0 hmem
      exact ⟨T, hT, by rw [← he0]; exact hTe⟩
    · obtain ⟨L', L'', hL, -, -, -, e0, hlast, he0⟩ := hr2
      have hmem : e0 ∈ L2 := by rw [hL]; exact List.mem_append_left _ (List.mem_of_getLast? hlast)
      obtain ⟨T, hT, hTe⟩ := walkR_head_ray W2 e0 hmem
      exact ⟨T, hT, by rw [← he0]; exact hTe⟩


theorem toV2_zero_crs_right (u : Plane) (z : V2) (h : u = 0) : crs z (toV2 u) = 0 := by
  subst h; simp [crs, toV2]

theorem toV2_zero_crs_left (u : Plane) (z : V2) (h : u = 0) : crs (toV2 u) z = 0 := by
  subst h; simp [crs, toV2]

set_option maxHeartbeats 3200000 in
/-- **(c): the spoke angles at a (1,1,0) corner.** -/
theorem gexc_spoke_angles [NeZero M] (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hC : CaseC D idx) (k : Fin M)
    (hc0 : cnt D idx (P.v (k + 1)) 0 = 1) (hc1 : cnt D idx (P.v (k + 1)) 1 = 1) (hc2 : cnt D idx (P.v (k + 1)) 2 = 0)
    {W : Plane} (hW : GExc D idx (P.v (k + 1)) W) :
    ∃ (jx jy : Fin N) (kx ky : Fin 3) (Uo Ui : Plane),
      TriStep (D.tile jx) (toV2 (P.e (k + 1))) (P.v (k + 1)) Uo ∧ TriStep (D.tile jy) (toV2 (P.e k)) Ui (P.v (k + 1)) ∧
      (D.tile jx).pts kx = P.v (k + 1) ∧ (D.tile jy).pts ky = P.v (k + 1) ∧
      idx jx kx ≠ 2 ∧ idx jy ky ≠ 2 ∧ idx jx kx ≠ idx jy ky ∧ W ≠ P.v (k + 1) ∧
      EuclideanGeometry.angle (P.v (k + 1 + 1)) (P.v (k + 1)) W = D.model.angleAt (idx jx kx) ∧
      EuclideanGeometry.angle (P.v k) (P.v (k + 1)) W = D.model.angleAt (idx jy ky) := by
  obtain ⟨r, jx, jy, kx, ky, Uo, Ui, hr, hSo, hSi, hkx, hky, hlx, hly, hne, hcx, hwx, hcy, hwy, hb⟩ := corner_sector_data D P hreg idx hC k hc0 hc1 hc2
  obtain ⟨d, hd, hdl, hdr, T, hT, hTW⟩ := gexc_ray hW
  have hrd : Par r d := hb d hdl hdr
  have hWd : Par (toV2 (W - P.v (k + 1))) d := par_of_smul' hd hT hTW
  have hrW : Par r (toV2 (W - P.v (k + 1))) := hrd.trans hWd.symm
  have hWne : W ≠ P.v (k + 1) := by
    intro h
    have : toV2 (W - P.v (k + 1)) = (0, 0) := by rw [h]; simp [toV2]
    have h1 := hWd.ne_left
    exact h1 this
  have hw0 : W - P.v (k + 1) ≠ 0 := sub_ne_zero.mpr hWne
  refine ⟨jx, jy, kx, ky, Uo, Ui, hSo, hSi, hkx, hky, hlx, hly, hne, hWne, ?_, ?_⟩
  · have hu0 : P.e (k + 1) ≠ 0 := P.e_ne_zero P.three_le (k + 1)
    have hc : 0 ≤ cross (P.e (k + 1)) (W - P.v (k + 1)) := (crs_pos_par_right hrW hcx).le
    have := wd_eq_angle hu0 hw0 hc
    rw [← hwx, wd_par_right hrW]
    rw [this]
    unfold EuclideanGeometry.angle
    have e : P.v (k + 1 + 1) -ᵥ P.v (k + 1) = P.e (k + 1) := rfl
    rw [e]; rfl
  · have hv0 : P.v k - P.v (k + 1) ≠ 0 := by
      intro h
      have := toV2_zero_crs_right _ r h
      linarith
    have hc : 0 ≤ cross (W - P.v (k + 1)) (P.v k - P.v (k + 1)) := (crs_pos_par_left hrW hcy).le
    have := wd_eq_angle hw0 hv0 hc
    rw [← hwy, wd_par_left hrW]
    unfold EuclideanGeometry.angle
    rw [InnerProductGeometry.angle_comm]
    exact this.symm ▸ rfl

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.gexc_spoke_angles
