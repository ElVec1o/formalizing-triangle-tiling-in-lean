-- Draft/RowLineP2Real.lean — P2(j), THE Λ₂ ROW-LINE LEMMA, for REAL `m = 1` dissections in the apex
-- frame: the statement of (private working notes, not included) §1.2 (review record R1–R3;
-- proof_H_empty.md §5.10), proved by its induction (strong induction on `j`; the march over the
-- levels `N ≥ n_X` between the pierced ray `r` and `ℓ_j`), from Draft/ConvergingWallsLocal.lean and
-- CW (Draft/ConvergingWallsReal.lean).  Imported directly by All.lean (stale "NOT imported" header corrected 2026-10-04).
--
-- Build (scratch oleans; never .lake): ConvergingWallsReal olean in $S, then
--   lake env bash -c 'LEAN_PATH=$S:$LEAN_PATH lean Erdos634/Draft/RowLineP2Real.lean'
--
-- Formal route vs. the paper (proof_CW_P2.md §5): the same steps; as in CW, the half-turns across
-- `τ = [Y_{N+1}, (N+1)V]` are found by marching from the `ℓ_j` end (no PROP), and the terminals
-- "chain end" and "`D(N,0)` exits" (S5's `d* > b` and `d* < b` branches) need no separate proof: a
-- present tile has its vertices in the target, and the march `I′(N) ⇒ I′(N+1)` cannot run past
-- `N = n_X + f` (the chain tile `T₂ + (n_X + f − 1)V` would have its vertex at depth `(n_X+f)c > fb`).
-- (P2-c), T₁'s `b` on the far side of `r` (thm:pierce(i)), is the frame field `HFrame.hT1`, used through
-- `HalfTurnR4Real.pierced_of` (R4 Step 2).
import Erdos634.Draft.ConvergingWallsReal

namespace Erdos634.Draft.RowWallReal

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.Draft.HalfTurnR3R4
open Erdos634.Draft.HalfTurnR3R4Glue Erdos634.Draft.CornerAdjacency
open Erdos634.Draft.HalfTurnR3R4Order Erdos634.Draft.MirrorStripR2Real
open Erdos634.Draft.HalfTurnR4Real

variable {N : ℕ} {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ}
variable (F : HFrame D e f α β γ)

/-! ## §1 The ray `r` in lattice terms -/

theorem Vk_Q2 (FC : ApexPlacement.FrameCoords F) (k : ℕ) : F.Vk k = Q2 F k 0 := by
  rw [Vk_eq F FC]; simp only [Q2]; congr 1; ring

theorem h_vec (p q : ℝ) : F.h (vec F p q) = p * F.h (w F) + q * F.h (v F) := by
  simp only [vec, map_add, map_smul, smul_eq_mul]

/-- `r`'s normal functional is a multiple of `ellF` (`r = ℓ₀`). -/
theorem h_eq_ellF (FC : ApexPlacement.FrameCoords F) (x : Plane) :
    F.h x = F.h (w F) * ellF F x := by
  have hVA : F.h (vec F (1 + cb e f) (-1)) = 0 := by
    rw [← VA_vec F FC, F.hV, add_sub_cancel_left, map_smul, F.hhuR, smul_zero]
  rw [h_vec] at hVA
  rw [vec_coords F FC x, h_vec, ellF_vec F FC]
  linear_combination (-(rho F x)) * hVA

theorem hw_ne : F.h (w F) ≠ 0 := F.hw_neg.ne

theorem ind_h_ad (FC : ApexPlacement.FrameCoords F) :
    ∀ x : Plane, (-F.h) x = 0 → (-(adF F)) x = 0 → x = 0 := by
  intro x h1 h2
  apply ind_ell_ad F FC x _ h2
  rw [LinearMap.neg_apply, neg_eq_zero, h_eq_ellF F FC] at h1
  rw [LinearMap.neg_apply, neg_eq_zero]
  rcases mul_eq_zero.mp h1 with h | h
  · exact absurd h (hw_ne F)
  · exact h

include F in
/-- **Two straight tiles on two crossing lines, and a `β`**, at an interior point: impossible
(`n_β + 2n_π + 4n_{2π} + n_γ = 4`). -/
theorem no_two_straight_b {x : Plane} (hx : x ∈ interior D.target.carrier)
    {g1 g2 : Plane →ₗ[ℝ] ℝ} {d1 d2 : ℝ}
    (h1 : TraceCovering.Straddled D.toDissection g1 d1 x)
    (h2 : TraceCovering.Straddled D.toDissection g2 d2 x)
    (hind : ∀ v : Plane, g1 v = 0 → g2 v = 0 → v = 0)
    {iB : Fin N} (hB : (D.tile iB).localAngle x = β) : False := by
  classical
  obtain ⟨ε1, hε1, hx1⟩ := h1
  obtain ⟨ε2, hε2, hx2⟩ := h2
  obtain ⟨E1, E2⟩ := interior_card_eqs D F.hAng F.hM.hα' F.hM.hβ' F.hM.hγ' hx
  have cB := card_one hB
  by_cases h12 : ε1.1 = ε2.1
  · have hx2' : x ∈ openSegment ℝ ((D.tile ε1.1).pts ε2.2) ((D.tile ε1.1).pts (ε2.2 + 1)) := by
      rw [h12]; exact hx2
    have hm := Level2LemmaGReal.same_edge (D.tile ε1.1) hx1 hx2'
    obtain ⟨a1, a2, -⟩ := Dissection.mem_lineChain.mp hε1
    obtain ⟨b1, b2, -⟩ := Dissection.mem_lineChain.mp hε2
    rw [← h12, ← hm] at b1 b2
    have hv := hind ((D.tile ε1.1).pts (ε1.2 + 1) - (D.tile ε1.1).pts ε1.2)
      (by rw [map_sub, a1, a2, sub_self]) (by rw [map_sub, b1, b2, sub_self])
    exact pts_ne (D.tile ε1.1) (TraceCovering.fin3_succ_ne ε1.2) (sub_eq_zero.mp hv).symm
  · have := Level2LemmaGReal.two_straight h12 (straight_count hx1) (straight_count hx2)
    omega

/-! ## §2 The chain point: `L_c` or `L_b` -/

/-- **An `α`-tile at a `Λ₂` point with a flank positively along `w`** (on `m_i`), its other flank on
the far side of `ℝw` from `P′ − V`: the lattice cell `U(i,t)` (`b` along `w`) or the swap `Sw i t`
(`c` along `w`).  No `m = 1` input. -/
theorem alpha_at_w2 (FC : ApexPlacement.FrameCoords F) {z : Fin N} {mz : Fin 3} {i t : ℝ}
    {U W : Plane} {S : ℝ} (hmz : (D.tile z).pts mz = Q2 F i t)
    (hUW : IsFlankPair (D.tile z) mz (Q2 F i t) U W) (hS : 0 < S)
    (hU0 : vec F 1 0 = S • U)
    (hside : cross (vec F 1 0) W * cross (vec F 1 0) (vec F (-(cb e f)) 1) < 0)
    (hα : (D.tile z).localAngle (Q2 F i t) = α) :
    Set.range (D.tile z).pts = {Q2 F i t, Q2 F (i + 1) t, Q2 F i (t + 1)} ∨
      Set.range (D.tile z).pts = Sw F i t := by
  obtain ⟨ha0, hb0, hc0, hbc, hac⟩ := consts F
  have hK := K_ne F FC
  have hK2 : 0 < ((f : ℝ) ^ 2 * cross (w F) F.uL) * ((f : ℝ) ^ 2 * cross (w F) F.uL) :=
    mul_self_pos.mpr hK
  obtain ⟨hn, hopp⟩ := (corner_dataH F hmz hUW).2 hα
  have hL0 := norm_vec_10 F
  obtain ⟨hcb0, -⟩ := cb_pos F
  obtain ⟨hbr0, -, hbrcb⟩ := bcr_facts F
  rcases hn with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · -- `b` along `w`: the lattice cell
    left
    have hU : U = vec F 1 0 := by
      rw [flank_eq hS hU0 h1 hL0 hb0, div_self hb0.ne', one_smul]
    have hs2 : cross (vec F 1 0) (vec F (1 + cb e f) (-1)) *
        cross (vec F 1 0) (vec F (-(cb e f)) 1) < 0 := by
      rw [cross_vec, cross_vec]; nlinarith
    have hr := ident hmz hUW hU (by intro h; rw [h, norm_zero] at hL0; linarith)
      (by have := side_of_across hS hU0 hside hs2; rwa [hU] at this)
      (by rw [h2, norm_V]) (by
        rw [hopp, dist_add_vec, show (1 : ℝ) - (1 + cb e f) = -(cb e f) by ring,
          show (0 : ℝ) - (-1) = 1 by ring,
          show vec F (-(cb e f)) 1 = - vec F (cb e f) (-1) by rw [vec_neg]; norm_num,
          norm_neg, norm_VP])
    have e1 : Q2 F i t + vec F 1 0 = Q2 F i (t + 1) := by
      rw [Q2_add_eq F (di := 0) (dt := 1) (by ring) (by ring), add_zero]
    have e2 : Q2 F i t + vec F (1 + cb e f) (-1) = Q2 F (i + 1) t := by
      rw [Q2_add_eq F (di := 1) (dt := 0) (by ring) (by ring), add_zero]
    rw [hr, e1, e2]
    ext p; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  · -- `c` along `w`: the swap
    right
    have hU : U = vec F (cb e f) 0 := by
      rw [flank_eq hS hU0 h1 hL0 hb0, vec_smul, mul_one, mul_zero, cb]
    have hs2 : cross (vec F 1 0) (vec F (bcr e f * (1 + cb e f)) (-(bcr e f))) *
        cross (vec F 1 0) (vec F (-(cb e f)) 1) < 0 := by
      rw [cross_vec, cross_vec]
      have : 0 < bcr e f * (((f : ℝ) ^ 2 * cross (w F) F.uL) * ((f : ℝ) ^ 2 * cross (w F) F.uL)) :=
        mul_pos hbr0 hK2
      nlinarith
    have hUne : vec F (cb e f) 0 ≠ 0 := by
      intro h; rw [← vec_zero F] at h; have := (vec_inj F FC h).1; linarith
    have hWn : ‖vec F (bcr e f * (1 + cb e f)) (-(bcr e f))‖ = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
      rw [show vec F (bcr e f * (1 + cb e f)) (-(bcr e f)) = bcr e f • vec F (1 + cb e f) (-1) by
        rw [vec_smul]; congr 1; ring, norm_smul, norm_V, Real.norm_of_nonneg hbr0.le, bcr,
        div_mul_cancel₀ _ hc0.ne']
    have hr := ident hmz hUW hU hUne
      (by have := side_of_across hS hU0 hside hs2; rwa [hU] at this)
      (by rw [h2, hWn])
      (by
        rw [hopp, dist_add_vec]
        apply (norm_of_sq ha0.le _ (norm_nonneg _)).symm
        rw [norm_vec_sq, bcr, cb]
        have hf0 : (f : ℝ) ≠ 0 := (f_pos' F).ne'
        field_simp; ring)
    have e1 : Q2 F i t + vec F (cb e f) 0 = Q2 F i (t + cb e f) := by
      rw [Q2_add_eq F (di := 0) (dt := cb e f) (by ring) (by ring), add_zero]
    have e2 : Q2 F i t + vec F (bcr e f * (1 + cb e f)) (-(bcr e f)) = Q2 F (i + bcr e f) t := by
      rw [Q2_add_eq F (di := bcr e f) (dt := 0) (by ring) (by ring), add_zero]
    rw [hr, e1, e2, Sw]
    ext p; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto

set_option maxHeartbeats 2000000 in
/-- **The chain point `(M+1)V`** (proof_CW_P2.md §5, Step A′; R4 Step 2).  Given `T₂ + iV` for
`i ≤ M` (so `(M+1)V` is pierced: `pierced_of`, Lemma A, **m = 1**) and `D(M,0) = K + MV`: the near
side at `(M+1)V` carries `β` (`T₂ + MV`) and `γ` (`K + MV`), the piercer `π`, so the residual is one
`α`-tile, across `K + MV`'s flank along `m_{M+1}`: `L_c = T₂ + (M+1)V` or `L_b = B_{M+1}` (the swap). -/
theorem chain_alpha (L : LFrame F) (M' : ℕ) (hLc : ∀ i ≤ M', Present D (T2c F i 0))
    (hD : Present D (Kc F M' 0)) :
    Present D (T2c F (M' + 1) 0) ∨ Present D (Sw F ((M' : ℝ) + 1) 0) := by
  classical
  have FC := L.FC
  obtain ⟨iU, hrU⟩ := hLc M' le_rfl
  obtain ⟨iD, hrD⟩ := hD
  have gU : (D.tile iU).localAngle (Q2 F ((M' : ℝ) + 1) 0) = β := by
    have := (U_angles F FC hrU).2.1; simp only [Nat.cast_zero] at this; exact this
  have gD : (D.tile iD).localAngle (Q2 F ((M' : ℝ) + 1) 0) = γ := by
    have := (D_angles F FC hrD).1; simp only [Nat.cast_zero] at this; exact this
  have hNm : Q2 F ((M' : ℝ) + 1) 0 ∈ D.target.carrier := by
    apply mem_of_present ⟨iU, hrU⟩; rw [U_eq F FC]; simp only [Nat.cast_zero]; exact mem3_2
  have hNint : Q2 F ((M' : ℝ) + 1) 0 ∈ interior D.target.carrier := by
    have := Q2_int_of_mem F FC (M' + 1) 0 (by omega) (by push_cast; exact hNm)
    push_cast at this; exact this
  have hpier := pierced_of F M' (fun i hi => by rw [Lc_eq F]; exact hLc i hi)
    (by rw [Vk_Q2 F FC]; push_cast; exact hNm)
  rw [Vk_Q2 F FC] at hpier
  push_cast at hpier
  obtain ⟨εp, hεp, hxp⟩ := hpier
  have sp := straight_count hxp
  have rD : Set.range (D.tile iD).pts = {Q2 F ((M' : ℝ) + 1) 0, Q2 F ((M' : ℝ) + 1) 1,
      Q2 F (M' : ℝ) 1} := by
    rw [hrD, D_eq F FC]; simp only [Nat.cast_zero, zero_add]
    ext p; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  obtain ⟨mD, hmD, hflD⟩ := flank_of_range rD
  rw [Q2_sub_eq F (p := 1) (q := 0) (by ring) (by ring),
    Q2_sub_eq F (p := -(cb e f)) (q := 1) (by ring) (by ring)] at hflD
  obtain ⟨z, hzD, hXz, hcz⟩ := flank_neighbour_dissection D.toDissection hNint hmD hflD
  obtain ⟨E1, E2⟩ := interior_card_eqs D F.hAng F.hM.hα' F.hM.hβ' F.hM.hγ' hNint
  have cB := card_one gU
  have cC := card_one gD
  have cS : 1 ≤ ({i | (D.tile i).localAngle (Q2 F ((M' : ℝ) + 1) 0) = Real.pi} : Finset (Fin N)).card
      + ({i | (D.tile i).localAngle (Q2 F ((M' : ℝ) + 1) 0) = 2 * Real.pi} : Finset (Fin N)).card :=
    Level2LemmaGReal.one_straight sp
  rcases hcz with ⟨mz, hmz, U, W, hUW, S, hS, hU0, hside⟩ | ⟨m', -, hmpos, hcr, -⟩
  swap
  · exfalso
    have hznv : ∀ q, (D.tile z).pts q ≠ Q2 F ((M' : ℝ) + 1) 0 := fun q hq =>
      NearBaseVertex.vertex_not_edge _ q hq m' hmpos
    have hzs := localAngle_mem_pi_of_mem (D.tile z) hXz hznv
    by_cases hze : z = εp.1
    · obtain ⟨h0, h1, -⟩ := Dissection.mem_lineChain.mp hεp
      rw [← hze] at hxp h0 h1
      obtain ⟨c2, -, -⟩ := openSeg_coords (D.tile z) εp.2 hxp
      have hm : m' = εp.2 + 2 := by
        by_contra hne
        have := hmpos (εp.2 + 2) (Ne.symm hne)
        linarith
      subst hm
      rw [fin3_add_two_add_two, fin3_add_two_add_one] at hcr
      have hd0 := sub_ne_zero.mpr (pts_ne (D.tile z) (TraceCovering.fin3_succ_ne εp.2)).symm
      have hgd : (-F.h) ((D.tile z).pts (εp.2 + 1) - (D.tile z).pts εp.2) = 0 := by
        rw [map_sub, h0, h1, sub_self]
      have hgw : (-F.h) (vec F 1 0) ≠ 0 := by
        rw [LinearMap.neg_apply, neg_ne_zero, show vec F 1 0 = w F by simp [vec]]
        exact hw_ne F
      exact cross_ne_of_g (-F.h) hd0 hgd hgw hcr
    · have := Level2LemmaGReal.two_straight hze hzs sp
      omega
  have hang := localAngle_at_own_vertex_mem D α β γ F.hM.hα' F.hM.hβ' F.hM.hγ' z mz
  rw [hmz] at hang
  rcases hang with hz | hz | hz
  · rcases alpha_at_w2 F FC hmz hUW hS hU0 hside hz with h | h
    · left; refine ⟨z, ?_⟩; rw [h, U_eq F FC]; push_cast; rfl
    · right; exact ⟨z, h⟩
  · exfalso
    by_cases hzU : z = iU
    · subst hzU
      have rU : Set.range (D.tile z).pts = {Q2 F ((M' : ℝ) + 1) 0, Q2 F (M' : ℝ) 0,
          Q2 F (M' : ℝ) 1} := by
        rw [hrU, U_eq F FC]; simp only [Nat.cast_zero, zero_add]
        ext p; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
      exact ne_of_flank_Q2 F FC hmz hUW hS hU0 rU (d1 := -(1 + cb e f)) (e1 := 1)
        (d2 := -(cb e f)) (e2 := 1) (by ring) (by ring) (by ring) (by ring)
        (fun S' hS' h1 h2 => by linarith) (fun S' hS' h1 h2 => by linarith) rfl
    · have := card_two hzU hz gU
      omega
  · exfalso
    have := card_two hzD hz gD
    omega

/-- **`L_b`'s `c`-edge is an r-side edge of `m_i`** (the c-seed that `L_b = B_i` hands to CW). -/
theorem seedB_of_Sw (FC : ApexPlacement.FrameCoords F) (i t : ℝ) (hX : Present D (Sw F i t)) :
    ∃ ε ∈ rsChain F i, EdgeIs D ε (Q2 F i t) (Q2 F i (t + cb e f)) := by
  obtain ⟨hbr0, -, -⟩ := bcr_facts F
  obtain ⟨hcb0, -⟩ := cb_pos F
  obtain ⟨iX, hr⟩ := hX
  have hP : Q2 F i t ∈ Set.range (D.tile iX).pts := by rw [hr, Sw]; exact mem3_1
  have hQ : Q2 F i (t + cb e f) ∈ Set.range (D.tile iX).pts := by rw [hr, Sw]; exact mem3_3
  obtain ⟨m, hm⟩ := edge_idx hP hQ (Q2_ne F FC (Or.inr (by intro h; linarith)))
  have hall : ∀ k, rho F ((D.tile iX).pts k) ≤ rho F F.A - i := by
    intro k
    have : (D.tile iX).pts k ∈ Set.range (D.tile iX).pts := ⟨k, rfl⟩
    rw [hr, Sw] at this
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this
    rcases this with h | h | h <;> rw [h, rho_Q2 F FC] <;> linarith
  have hmem : ∀ {i1 i2 t1 t2 : ℝ}, i1 = i → i2 = i → (D.tile iX).pts m = Q2 F i1 t1 →
      (D.tile iX).pts (m + 1) = Q2 F i2 t2 → (iX, m) ∈ rsChain F i := by
    intro i1 i2 t1 t2 hi1 hi2 h1 h2
    rw [rsChain, Dissection.mem_lineChain]
    exact ⟨by rw [h1, rho_Q2 F FC, hi1], by rw [h2, rho_Q2 F FC, hi2], hall⟩
  rcases hm with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨(iX, m), hmem rfl rfl h1 h2, by simp only [EdgeIs]; rw [h1, h2]⟩
  · exact ⟨(iX, m), hmem rfl rfl h1 h2, by simp only [EdgeIs]; rw [h1, h2, Set.pair_comm]⟩

/-! ## §3 P2: the hypotheses, the invariant, the two steps -/

/-- **The march invariant `I′(M)`**: every cell of the strips `1..j` (`U(i,t)`, `D(i,t)`, `t < j`)
of level `≤ M` is a tile. -/
def P2Inv (F : HFrame D e f α β γ) (j M : ℕ) : Prop :=
  ∀ i t, t < j → i + t + 1 ≤ M → Present D (T2c F i t) ∧ Present D (Kc F i t)

/-- **The hypotheses of P2(j)** (proof_CW_P2.md §1.2), with `X = (n_X − j)V + jP′`:
* `1 ≤ j ≤ n_X`;
* (P2-a) b-seed: a band-side edge of `ℓ_j` from `X` to `X + b·u_r`;
* (P2-b) every cell of the strips `1..j` of level `≤ n_X` is a tile (this includes the level-`n_X`
  down cells and the chain tiles `T₂ + iV`, `i < n_X`);
* (P2-c) `T₁`'s `b` on the far side of `r` is the frame field `HFrame.hT1`. -/
structure P2H (F : HFrame D e f α β γ) (j nX : ℕ) : Prop where
  hj : 1 ≤ j
  hjX : j ≤ nX
  seed : ∃ ε ∈ bandChain F (j : ℝ),
    EdgeIs D ε (Q2 F ((nX : ℝ) - j) j) (Q2 F ((nX : ℝ) - j + bcr e f) j)
  cells : P2Inv F j nX

set_option maxHeartbeats 1000000 in
/-- **Step A′(M)**: the up cells of level `M+1`.  At the chain point `MV` (`t = 0`): `L_c` or
`L_b` (`chain_alpha`), and `L_b` hands a c-seed on `m_M` to **CW(ℓ_j, m_M)** (`cw_frame`; here
`k = M ≥ j`).  At the interior points (`slot2`): the lattice cell or a swap, which is a b-seed on
`ℓ_{M−i}`, `M − i < j`, killed by **P2(M−i)** (the induction). -/
theorem p2_up (L : LFrame F) {j nX M : ℕ} (hP : P2H F j nX)
    (IH : ∀ j' < j, ∀ nX' : ℕ, ¬ P2H F j' nX') (hM : nX ≤ M) (hI : P2Inv F j M) :
    ∀ i t, t < j → i + t = M → Present D (T2c F i t) := by
  have FC := L.FC
  have hj := hP.hj
  have hjX := hP.hjX
  intro i t ht hit
  rcases Nat.eq_zero_or_pos t with rfl | htpos
  · -- the chain point `MV`
    obtain ⟨M', rfl⟩ : ∃ M', i = M' + 1 := ⟨i - 1, by omega⟩
    rcases chain_alpha F L M' (fun i' hi' => (hI i' 0 (by omega) (by omega)).1)
        (hI M' 0 (by omega) (by omega)).2 with h | hSw
    · exact h
    · exfalso
      obtain ⟨ε, hε, hE⟩ := seedB_of_Sw F FC _ _ hSw
      rw [zero_add] at hE
      apply cw_frame F L j (M' + 1) nX (M' + 1)
      refine ⟨hj, by omega, hjX, by omega, le_rfl, by omega, hP.seed, ?_, ?_⟩
      · push_cast; exact ⟨ε, hε, hE⟩
      · intro i' t' hi' ht' hit'
        exact hI i' t' ht' (by omega)
  · -- an interior slot
    obtain ⟨a, rfl⟩ : ∃ a, i = a + 1 := ⟨i - 1, by omega⟩
    obtain ⟨b, rfl⟩ : ∃ b, t = b + 1 := ⟨t - 1, by omega⟩
    have hA := (hI a b (by omega) (by omega)).2
    have hXint := D_vertex_int F L hA
    rcases slot2 F L a b hXint hA (hI a (b + 1) (by omega) (by omega)).1
        (hI (a + 1) b (by omega) (by omega)).2 (hI (a + 1) b (by omega) (by omega)).1
        (hI a (b + 1) (by omega) (by omega)).2 with h | hSw
    · exact h
    · exfalso
      obtain ⟨ε, hε, hE⟩ := seed_of_Sw F FC _ _ hSw
      have hMR : ((M : ℕ) : ℝ) = (a : ℝ) + 1 + ((b : ℝ) + 1) := by
        rw [← hit]; push_cast; ring
      apply IH (b + 1) ht M
      refine ⟨by omega, by omega, ?_, ?_⟩
      · have e1 : ((M : ℝ) - ((b + 1 : ℕ) : ℝ)) = (a : ℝ) + 1 := by push_cast; linarith
        rw [e1]; push_cast; exact ⟨ε, hε, hE⟩
      · intro i' t' ht' hit'
        exact hI i' t' (by omega) hit'

set_option maxHeartbeats 2000000 in
/-- **Step B′(M+1)**: the down cells of level `M+1`.  On `τ = [Y, (M+1)V]` (`Y = (M+1−j)V + jP′`):
the band straddle at `Y` (`band_str`, Lemma A, **m = 1**), the piercing of `(M+1)V`
(`pierced_of`, Lemma A, **m = 1**) with `T₂ + MV`'s `β` there, so neither end is straddled from the
far side; the far word `a^j` (`far_word`, A1, **m = 1**); the half-turns (`ad_march`). -/
theorem p2_down (L : LFrame F) {j nX M : ℕ} (hP : P2H F j nX) (hM : nX ≤ M) (hI : P2Inv F j M)
    (hUp : ∀ i t, t < j → i + t = M → Present D (T2c F i t)) :
    ∀ i t, t < j → i + t = M → Present D (Kc F i t) := by
  classical
  have FC := L.FC
  obtain ⟨hcb0, hcb1⟩ := cb_pos F
  have hjX := hP.hjX
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by have := hP.hj; omega⟩
  obtain ⟨x0, rfl⟩ : ∃ x0, nX = j' + 1 + x0 := ⟨nX - (j' + 1), by omega⟩
  obtain ⟨a0, hMa⟩ : ∃ a0, M = j' + 1 + a0 := ⟨M - (j' + 1), by omega⟩
  -- the `ℓ_j` end `Y = (a0+1)V + jP′`
  have hDY := (hI a0 j' (by omega) (by omega)).2
  have hYint := D_vertex_int F L hDY
  have hYle := Q2_le F FC (interior_subset hYint)
  have hYne := O2 F (a0 + 1) (j' + 1) (by omega)
  push_cast at hYne
  have hYlt : ((j' : ℝ) + 1) + ((a0 : ℝ) + 1) * cb e f < f := lt_of_le_of_ne hYle hYne
  have hMaR : (M : ℝ) = (j' : ℝ) + 1 + a0 := by rw [hMa]; push_cast; ring
  -- the `r` end `(M+1)V`
  have hUM := hUp M 0 (by omega) (by omega)
  have hRm : Q2 F ((M : ℝ) + 1) 0 ∈ D.target.carrier := by
    apply mem_of_present hUM; rw [U_eq F FC]; simp only [Nat.cast_zero]; exact mem3_2
  have hRint : Q2 F ((M : ℝ) + 1) 0 ∈ interior D.target.carrier := by
    have := Q2_int_of_mem F FC (M + 1) 0 (by omega) (by push_cast; exact hRm)
    push_cast at this; exact this
  have hRle := Q2_le F FC (interior_subset hRint)
  have hRne := O2 F (M + 1) 0 (by omega)
  push_cast at hRne
  have hRlt : (0 : ℝ) + ((M : ℝ) + 1) * cb e f < f := lt_of_le_of_ne hRle hRne
  have hLc : ∀ i ≤ M, Present D (F.Lc i) := by
    intro i hi
    rw [Lc_eq F]
    rcases Nat.lt_or_ge i M with h | h
    · exact (hI i 0 (by omega) (by omega)).1
    · have : i = M := by omega
      rw [this]; exact hUM
  have hpier := pierced_of F M hLc (by rw [Vk_Q2 F FC]; push_cast; exact hRm)
  rw [Vk_Q2 F FC] at hpier
  push_cast at hpier
  -- (B1) the band straddle at `Y`
  have hBY : BStr F ((j' : ℝ) + 1) (Q2 F ((a0 : ℝ) + 1) ((j' : ℝ) + 1)) := by
    have h := band_str F L j' x0 (a0 + 1 - x0) (by omega) (by
        have : ((a0 + 1 : ℕ) : ℝ) < f := by push_cast; nlinarith
        have : a0 + 1 < f := by exact_mod_cast this
        omega)
      (by have : ((x0 : ℝ) + ((a0 + 1 - x0 : ℕ) : ℝ)) = (a0 : ℝ) + 1 := by
            rw [Nat.cast_sub (by omega)]; push_cast; ring
          rw [this]; exact hYlt)
      (fun s hs => (hI (x0 + s) j' (by omega) (by omega)).2)
      (by
        obtain ⟨ε, hε, hE⟩ := hP.seed
        have e1 : (((j' + 1 + x0 : ℕ) : ℝ) - ((j' + 1 : ℕ) : ℝ)) = (x0 : ℝ) := by push_cast; ring
        rw [e1] at hE; push_cast at hε hE; exact ⟨ε, hε, hE⟩)
    have : ((x0 : ℝ) + ((a0 + 1 - x0 : ℕ) : ℝ)) = (a0 : ℝ) + 1 := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [this] at h; exact h
  -- neither end is straddled from the far side of `AD_{M+1}`
  obtain ⟨iY, hrY⟩ := hDY
  obtain ⟨iR, hrR⟩ := hUM
  have gY := (D_angles F FC hrY).2.2
  have gR : (D.tile iR).localAngle (Q2 F ((M : ℝ) + 1) 0) = β := by
    have := (U_angles F FC hrR).2.1; simp only [Nat.cast_zero] at this; exact this
  have hYf : ¬ AStr F ((M + 1 : ℕ) : ℝ) (Q2 F ((a0 : ℝ) + 1) ((j' : ℝ) + 1)) := fun h =>
    no_two_straight F hYint hBY h (ind_ell_ad F FC) gY
  have hRf : ¬ AStr F ((M + 1 : ℕ) : ℝ) (Q2 F ((M : ℝ) + 1) 0) := fun h =>
    no_two_straight_b F hRint hpier h (ind_h_ad F FC) gR
  -- the whole segment is interior
  have hseg : ∀ s : ℝ, 0 ≤ s → s ≤ ((j' + 1 : ℕ) : ℝ) →
      Q2 F (((a0 + 1 : ℕ) : ℝ) + s) (((M + 1 : ℕ) : ℝ) - ((a0 + 1 : ℕ) : ℝ) - s)
        ∈ interior D.target.carrier := by
    intro s hs0 hs1
    push_cast at hs1 ⊢
    apply Q2_interior F FC (by positivity) (by linarith) (by linarith)
    have h1 : 0 ≤ ((j' : ℝ) + 1 - s) * (cb e f - 1) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith
  have hfar := far_word F L (M + 1) (a0 + 1) (j' + 1) (by omega) (by
      have : ((j' + 1 : ℕ) : ℝ) < f := by push_cast; nlinarith
      have : j' + 1 < f := by exact_mod_cast this
      omega) (by omega)
    (fun s hs0 hs1 => hseg s hs0.le hs1.le)
    (fun i t hi1 hi2 hit => hUp i t (by omega) (by omega))
    (by
      have : Q2 F (((a0 + 1 : ℕ) : ℝ)) (((M + 1 : ℕ) : ℝ) - ((a0 + 1 : ℕ) : ℝ))
          = Q2 F ((a0 : ℝ) + 1) ((j' : ℝ) + 1) := by push_cast; congr 1; linarith
      rw [this]; exact hYf)
    (by
      have : Q2 F (((a0 + 1 : ℕ) : ℝ) + ((j' + 1 : ℕ) : ℝ))
          (((M + 1 : ℕ) : ℝ) - ((a0 + 1 : ℕ) : ℝ) - ((j' + 1 : ℕ) : ℝ))
          = Q2 F ((M : ℝ) + 1) 0 := by
        push_cast; congr 1 <;> linarith
      rw [this]; exact hRf)
  have hmarch := ad_march F L (M + 1) (a0 + 1) (j' + 1) (by omega) (by omega) hfar
    (fun i t hi1 hi2 hit => by
      have h := hseg ((i : ℝ) - ((a0 + 1 : ℕ) : ℝ)) (by
          have : ((a0 + 1 : ℕ) : ℝ) ≤ i := by exact_mod_cast hi1
          linarith) (by
          have : (i : ℝ) < ((a0 + 1 + (j' + 1) : ℕ) : ℝ) := by exact_mod_cast hi2
          push_cast at this ⊢; linarith)
      have hitR : (i : ℝ) + t + 1 = (M : ℝ) + 1 := by exact_mod_cast hit
      convert h using 2 <;> push_cast <;> linarith)
    (fun i t hi1 hi2 hit => hUp i t (by omega) (by omega))
    (fun i t hi1 hi2 hit => (hI i t (by omega) (by omega)).2)
    ⟨-(ellF F), -(ellF F F.A + ((j' : ℝ) + 1)), by
      have : Q2 F (((a0 + 1 : ℕ) : ℝ)) (((M + 1 : ℕ) : ℝ) - ((a0 + 1 : ℕ) : ℝ))
          = Q2 F ((a0 : ℝ) + 1) ((j' : ℝ) + 1) := by push_cast; congr 1; linarith
      rw [this]; exact hBY, by
      rw [LinearMap.neg_apply, ellF_vec F FC]; intro h; linarith⟩
  intro i t ht hit
  exact hmarch i t (by omega) (by omega) (by omega)

/-- **P2(j) — THE Λ₂ ROW-LINE LEMMA, frame form — PROVED** (proof_CW_P2.md §§1.2, 5).  In the apex
frame of a dissection (with the target's cone coordinates), no `P2H F j n_X` holds.  Strong
induction on `j` (the swaps at the slots lower `j`); for fixed `j`, the march `I′(M) ⇒ I′(M+1)`,
`M ≥ n_X` (`p2_up`, `p2_down`; the `L_b` turn calls **CW** with `k = M ≥ j`), which cannot pass
`M = n_X + f`: the chain tile `T₂ + (n_X + f − 1)V` would have its vertex `(n_X + f)V` at depth
`(n_X + f)·c > f·b`.  The **m = 1** inputs: Lemma A on `ℓ_j` and on `r` (the piercing, R4 Step 2),
A1 on `AD_n`, and CW's (A2 on `m_k`).  P2 never calls S4, S5 or Λ3M; CW never calls P2
(proof_H_empty.md W4: no cycle). -/
theorem p2_frame (L : LFrame F) : ∀ j nX : ℕ, ¬ P2H F j nX := by
  have FC := L.FC
  intro j
  induction j using Nat.strong_induction_on with
  | _ j IH =>
  intro nX hP
  have hj := hP.hj
  have hjX := hP.hjX
  have key : ∀ d, P2Inv F j (nX + d) := by
    intro d
    induction d with
    | zero => rw [Nat.add_zero]; exact hP.cells
    | succ d ih =>
      have hUp := p2_up F L hP (fun j' hj' nX' => IH j' hj' nX') (by omega) ih
      have hDn := p2_down F L hP (by omega) ih hUp
      intro i t ht hit
      rcases Nat.lt_or_ge (i + t + 1) (nX + d + 1) with hlt | hge
      · exact ih i t ht (by omega)
      · exact ⟨hUp i t ht (by omega), hDn i t ht (by omega)⟩
  have hf1 : 1 ≤ f := by have := F.hef; omega
  obtain ⟨iU, hrU⟩ := (key f (nX + f - 1) 0 (by omega) (by omega)).1
  have hm : Q2 F (((nX + f - 1 : ℕ) : ℝ) + 1) 0 ∈ D.target.carrier := by
    apply mem_of_present ⟨iU, hrU⟩; rw [U_eq F FC]; simp only [Nat.cast_zero]; exact mem3_2
  have hle := Q2_le F FC hm
  obtain ⟨-, hcb1⟩ := cb_pos F
  have hcast : ((nX + f - 1 : ℕ) : ℝ) + 1 = (nX : ℝ) + f := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  rw [hcast] at hle
  have hnX : (0 : ℝ) ≤ nX := Nat.cast_nonneg nX
  have hfR : (1 : ℝ) ≤ f := by exact_mod_cast hf1
  nlinarith

/-! ## §4 For real dissections -/

/-- **P2(j) FOR EVERY APEX FRAME OF A REAL `m = 1` DISSECTION — PROVED.** -/
theorem p2_real_all {kk : Fin 3} (h : ApexFrameReal.M1Data D e f α β γ kk)
    (FC : ApexPlacement.FrameCoords F) : ∀ j nX : ℕ, ¬ P2H F j nX :=
  p2_frame F (lframe_real F h FC)

/-- **P2(j) FOR EVERY REAL `m = 1` DISSECTION — PROVED.**  Every congruent dissection of the `m = 1`
base-β target (coprime `2 ≤ e ≤ f − 2`, `M1Data`) carries its apex frame `F`, and in it no
`P2H F j n_X` holds. -/
theorem p2_real {kk : Fin 3} (h : ApexFrameReal.M1Data D e f α β γ kk) :
    ∃ F : Erdos634.Draft.HalfTurnR3R4Glue.HFrame D e f α β γ, ApexPlacement.FrameCoords F ∧
      ∀ j nX : ℕ, ¬ P2H F j nX := by
  obtain ⟨F, FC⟩ := ApexLegWord.exists_hframe_coords_m1 D h.hco h.he h.hef h.hM h.hAng kk
    h.hcorner h.hβ1 h.hβ2 h.hleg1 h.hleg2 h.hbase
  exact ⟨F, FC, p2_real_all F h FC⟩

end Erdos634.Draft.RowWallReal

#print axioms Erdos634.Draft.RowWallReal.h_eq_ellF
#print axioms Erdos634.Draft.RowWallReal.alpha_at_w2
#print axioms Erdos634.Draft.RowWallReal.chain_alpha
#print axioms Erdos634.Draft.RowWallReal.seedB_of_Sw
#print axioms Erdos634.Draft.RowWallReal.p2_up
#print axioms Erdos634.Draft.RowWallReal.p2_down
#print axioms Erdos634.Draft.RowWallReal.p2_frame
#print axioms Erdos634.Draft.RowWallReal.p2_real_all
#print axioms Erdos634.Draft.RowWallReal.p2_real
