-- Draft/L3MReal.lean — THEOREM L3M (the L_b subtree: base S(k+1), the march Λ3M(k, L), Terminal(k))
-- and THEOREM H ((H) is empty; with R2 inside S4(1), no m = 1 dissection at coprime 2 ≤ e ≤ f − 2),
-- for REAL `m = 1` dissections in the apex frame.  Statements of record: (private working notes, not included)
-- (corrected statement §0.2–0.3), proof_H_empty.md §§5.15, 5.16, 6.  Imported into All.lean (Erdos634/All.lean:432).
--
-- Build (scratch oleans; never .lake): LcPhaseReal olean in $S, then
--   lake env bash -c 'LEAN_PATH=$S:$LEAN_PATH lean Erdos634/Draft/L3MReal.lean'
--
-- The step Λ3M(k, L), in the paper's order 2 → 3 → 4:
--   2.2 row `L` far word, half-turn/mirror, PROP to `G_L`         `r8_row`
--   2.3 `m_k` from `kV` to `W_L`: r-side straddles `W_L`          `r_str` (A2, **m = 1**)
--   2.4 band segment `[LP′, W_L]` of `AD_L`: far word `a^k`         `far_word` (A1, **m = 1**)
--   3.1 the tile across the first band edge at `LP′`: `K + (L−1)P′` or `N_L`   `ad_first`
--   3.2 `N_L`: PK·a(L)                                               `pka_frame`
--       then every band half-turn of level `L` (march from `LP′`)    `junction`
--   3.3 `G_L`, `σ_b` at `LP′`: CW(ℓ_L, m_k)                         `cw_frame`
--   3.4 `σ_3` at `LP′`: RW(L) with C(L,L)                            `rw_frame`
--   3.5 the lattice corner                                          `corner_fills`
--   4.1 Λ₃ slots (RW(i)), 4.2 `J_L` (lem:sidenob), 4.4 Λ₂ slots (CW(ℓ_{L−i}, m_k)).
-- Terminal(k): at `L = L*` the march 3.1–3.2 produces `K + (k−1)V + (L*−k)P′`, whose vertex `W_{L*+1}`
-- has depth `kc + (L*−k+1)b > fb` (the paper's "H exits, so it is M, and M → N_{L*} → PK·a" is the
-- same contradiction reached through membership: a present tile has its vertices in the target).
import Erdos634.Draft.LcPhaseReal

namespace Erdos634.Draft.RowWallReal

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.Draft.HalfTurnR3R4
open Erdos634.Draft.HalfTurnR3R4Glue Erdos634.Draft.CornerAdjacency
open Erdos634.Draft.HalfTurnR3R4Order Erdos634.Draft.MirrorStripR2Real
open Erdos634.Draft.HalfTurnR4Real

variable {N : ℕ} {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ}
variable (F : HFrame D e f α β γ)

/-! ## §1 The corner `LP′` -/

set_option maxHeartbeats 2000000 in
/-- **3.1, the `AD_L` side of the corner `LP′`** (`L = L' + 1`): with the two `γ`'s of `T₂ + (L−1)P′`
and `T₃ + (L−1)P′` at `LP′` (no straight tile) and the band far word (`a`-edges), the tile across
`T₂ + (L−1)P′`'s `a`-flank is `K + (L−1)P′` (`β`) or `N_L` (`γ`). -/
theorem ad_first (L : LFrame F) (L' : ℕ)
    (hXint : Q2 F 0 ((L' : ℝ) + 1) ∈ interior D.target.carrier)
    (hall : ∀ ε ∈ adChain F ((L' + 1 : ℕ) : ℝ), ∀ ℓ : ℝ, 0 < ℓ →
      EdgeIs D ε (Q2 F 0 ((L' : ℝ) + 1))
        (Q2 F (ℓ / ((e : ℝ) * f)) ((L' : ℝ) + 1 - ℓ / ((e : ℝ) * f))) →
      ℓ = (e : ℝ) * f)
    (hT : Present D (T2c F 0 L')) (hU : Present D (Up F L' 0)) :
    Present D (Kc F 0 L') ∨ Present D (Nq F (L' + 1)) := by
  classical
  have FC := L.FC
  obtain ⟨ha0, hb0, hc0, hbc, hac⟩ := consts F
  obtain ⟨hab, hac', hbc'⟩ := sides_distinct F.hco F.he (by have := F.hef; omega)
  obtain ⟨hcb0, hcb1⟩ := cb_pos F
  obtain ⟨hbr0, -, hbrcb⟩ := bcr_facts F
  have hK := K_ne F FC
  have hK2 := mul_self_pos.mpr hK
  obtain ⟨iG, hrG⟩ := hT
  obtain ⟨iU, hrU⟩ := hU
  have hX0 : Q2 F 0 ((L' : ℝ) + 1) = Lam F ((L' : ℝ) + 1) 0 := by simp [Q2]
  have gG : (D.tile iG).localAngle (Q2 F 0 ((L' : ℝ) + 1)) = γ := by
    have := (U_angles F FC hrG).2.2; simp only [Nat.cast_zero] at this; exact this
  have gU : (D.tile iU).localAngle (Q2 F 0 ((L' : ℝ) + 1)) = γ := by
    rw [hX0]; have := (Up_angles F hrU).2.1; simp only [Nat.cast_zero] at this; exact this
  have rG : Set.range (D.tile iG).pts = {Q2 F 0 ((L' : ℝ) + 1), Q2 F 1 (L' : ℝ), Q2 F 0 (L' : ℝ)} := by
    rw [hrG, U_eq F FC]; simp only [Nat.cast_zero, zero_add]
    ext p; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  have hGU : iG ≠ iU := by
    intro h
    have h1 : Q2 F 1 (L' : ℝ) ∈ Set.range (D.tile iU).pts := by rw [← h, rG]; exact mem3_2
    rw [hrU] at h1
    simp only [Up, Nat.cast_zero, zero_add] at h1
    have : Q2 F 1 (L' : ℝ) = Lam F (1 * (1 + cb e f) + L') (-1) := rfl
    rw [this] at h1
    exact not_mem3 F FC (Or.inr (by norm_num)) (Or.inr (by norm_num)) (Or.inr (by norm_num)) h1
  have hns := count_gg F hXint hGU gG gU
  obtain ⟨mG, hmG, hflG⟩ := flank_of_range rG
  rw [Q2_sub_eq F (p := cb e f) (q := -1) (by ring) (by ring),
    Q2_sub_eq F (p := -1) (q := 0) (by ring) (by ring)] at hflG
  obtain ⟨z, hzG, hXz, hcz⟩ := flank_neighbour_dissection D.toDissection hXint hmG hflG
  obtain ⟨E1, E2⟩ := interior_card_eqs D F.hAng F.hM.hα' F.hM.hβ' F.hM.hγ' hXint
  rcases hcz with ⟨mz, hmz, U, W, hUW, S, hS, hU0, hside⟩ | ⟨m', -, hmpos, -, -⟩
  swap
  · exfalso
    have hznv : ∀ q, (D.tile z).pts q ≠ Q2 F 0 ((L' : ℝ) + 1) := fun q hq =>
      NearBaseVertex.vertex_not_edge _ q hq m' hmpos
    rcases localAngle_mem_pi_of_mem (D.tile z) hXz hznv with h | h
    · exact (hns z).2 h
    · exact (hns z).1 h
  have hU0n : ‖vec F (cb e f) (-1)‖ = (e : ℝ) * f := norm_VP F
  have hUne : U ≠ 0 := by
    intro h; rw [h, smul_zero] at hU0; rw [hU0, norm_zero] at hU0n; linarith
  obtain ⟨ℓ, hℓdef⟩ : ∃ ℓ : ℝ, ‖U‖ = ℓ := ⟨_, rfl⟩
  have hℓ : 0 < ℓ := hℓdef ▸ norm_pos_iff.mpr hUne
  have hUe : U = (ℓ / ((e : ℝ) * f)) • vec F (cb e f) (-1) := flank_eq hS hU0 hℓdef hU0n ha0
  have hadU : adF F U = 0 := by
    have h1 := congrArg (adF F) hU0
    rw [map_smul, adF_vec F FC, smul_eq_mul] at h1
    have h2 : S * adF F U = 0 := by rw [← h1]; ring
    rcases mul_eq_zero.mp h2 with h | h
    · linarith
    · exact h
  have hadW : 0 < adF F W := by
    have hW := vec_coords F FC W
    rw [hW, cross_vec, cross_vec] at hside
    rw [hW, adF_vec F FC]
    nlinarith
  have hXad : adF F (Q2 F 0 ((L' : ℝ) + 1)) = adF F F.A + ((L' + 1 : ℕ) : ℝ) := by
    rw [adF_Q2 F FC]; push_cast; ring
  have hall3 : ∀ k, adF F F.A + ((L' + 1 : ℕ) : ℝ) ≤ adF F ((D.tile z).pts k) := by
    intro k
    have hk : (D.tile z).pts k ∈ Set.range (D.tile z).pts := ⟨k, rfl⟩
    rw [ApexPlacement.range_of_flank hmz hUW] at hk
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hk
    rcases hk with h | h | h <;> rw [h]
    · rw [hXad]
    · rw [map_add, hXad, hadU, add_zero]
    · rw [map_add, hXad]; linarith
  obtain ⟨idx, hidx, hE⟩ : ∃ idx : Fin 3, (z, idx) ∈ adChain F ((L' + 1 : ℕ) : ℝ) ∧
      EdgeIs D (z, idx) (Q2 F 0 ((L' : ℝ) + 1)) (Q2 F 0 ((L' : ℝ) + 1) + U) := by
    rcases hUW with ⟨h1, -⟩ | ⟨h1, -⟩
    · have e1 : (D.tile z).pts (mz + 1) = Q2 F 0 ((L' : ℝ) + 1) + U := by rw [h1]; abel
      refine ⟨mz, mem_adChain F (by rw [hmz, hXad]) (by rw [e1, map_add, hXad, hadU, add_zero])
        hall3, ?_⟩
      simp only [EdgeIs]; rw [hmz, e1]
    · have e1 : (D.tile z).pts (mz + 2) = Q2 F 0 ((L' : ℝ) + 1) + U := by rw [h1]; abel
      have e2 : (D.tile z).pts (mz + 2 + 1) = Q2 F 0 ((L' : ℝ) + 1) := by
        rw [fin3_add_two_add_one]; exact hmz
      refine ⟨mz + 2, mem_adChain F (by rw [e1, map_add, hXad, hadU, add_zero])
        (by rw [e2, hXad]) hall3, ?_⟩
      simp only [EdgeIs]; rw [e1, e2, Set.pair_comm]
  have hUq : Q2 F 0 ((L' : ℝ) + 1) + U
      = Q2 F (ℓ / ((e : ℝ) * f)) ((L' : ℝ) + 1 - ℓ / ((e : ℝ) * f)) := by
    rw [hUe, vec_smul, Q2_add_eq F (di := ℓ / ((e : ℝ) * f)) (dt := -(ℓ / ((e : ℝ) * f)))
      (by ring) (by ring)]
    congr 1 <;> try ring
  rw [hUq] at hE
  have hla := hall (z, idx) hidx ℓ hℓ hE
  have hU1 : U = vec F (cb e f) (-1) := by rw [hUe, hla, div_self ha0.ne', one_smul]
  have hang := localAngle_at_own_vertex_mem D α β γ F.hM.hα' F.hM.hβ' F.hM.hγ' z mz
  rw [hmz] at hang
  have e1 : Q2 F 0 ((L' : ℝ) + 1) + vec F (cb e f) (-1) = Q2 F 1 (L' : ℝ) := by
    rw [Q2_add_eq F (di := 1) (dt := -1) (by ring) (by ring)]; congr 1 <;> ring
  rcases hang with hz | hz | hz
  · exfalso
    obtain ⟨hn, -⟩ := (corner_dataH F hmz hUW).2 hz
    rcases hn with ⟨h1, -⟩ | ⟨h1, -⟩
    · rw [hℓdef, hla] at h1; exact hab h1
    · rw [hℓdef, hla] at h1; exact hac' h1
  · -- `β`: the half-turn `K + (L−1)P′`
    left
    obtain ⟨hn, hopp⟩ := (corner_dataH F hmz hUW).1 hz
    have hWc : ‖W‖ = (f : ℝ) ^ 2 := by
      rcases hn with ⟨-, h2⟩ | ⟨h1, -⟩
      · exact h2
      · rw [hℓdef, hla] at h1; exact absurd h1 hac'
    have hs2 : cross (vec F (cb e f) (-1)) (vec F (1 + cb e f) (-1)) *
        cross (vec F (cb e f) (-1)) (vec F (-1) 0) < 0 := by
      rw [cross_vec, cross_vec]; nlinarith
    have hr := ident hmz hUW hU1 (by intro h; rw [h, norm_zero] at hU0n; linarith)
      (by have := side_of_across hS hU0 hside hs2; rwa [hU1] at this)
      (by rw [hWc, norm_V])
      (by rw [hopp, dist_add_vec, show cb e f - (1 + cb e f) = -1 by ring,
        show (-1 : ℝ) - (-1) = 0 by ring, norm_vec_m10])
    have e2 : Q2 F 0 ((L' : ℝ) + 1) + vec F (1 + cb e f) (-1) = Q2 F 1 ((L' : ℝ) + 1) := by
      rw [Q2_add_eq F (di := 1) (dt := 0) (by ring) (by ring)]; congr 1 <;> ring
    refine ⟨z, ?_⟩
    rw [hr, e1, e2, D_eq F FC]; simp only [Nat.cast_zero, zero_add]
    ext p; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  · -- `γ`: the level mirror `N_L`
    right
    obtain ⟨hn, hopp⟩ := corner_dataG F hmz hUW hz
    have hWb : ‖W‖ = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
      rcases hn with ⟨-, h2⟩ | ⟨h1, -⟩
      · exact h2
      · rw [hℓdef, hla] at h1; exact absurd h1 hab
    have hs2 : cross (vec F (cb e f) (-1)) (vec F 0 (bcr e f)) *
        cross (vec F (cb e f) (-1)) (vec F (-1) 0) < 0 := by
      rw [cross_vec, cross_vec]
      have : cb e f * bcr e f = 1 := by rw [mul_comm]; exact hbrcb
      nlinarith
    have hr := ident hmz hUW hU1 (by intro h; rw [h, norm_zero] at hU0n; linarith)
      (by have := side_of_across hS hU0 hside hs2; rwa [hU1] at this)
      (by rw [hWb, norm_vec_0q F hbr0.le, bcr, div_mul_cancel₀ _ hc0.ne'])
      (by rw [hopp, dist_add_vec, sub_zero, show (-1 : ℝ) - bcr e f = -1 - bcr e f by ring]
          exact (norm_MN F).symm)
    have e3 : Q2 F 0 ((L' : ℝ) + 1) + vec F 0 (bcr e f) = Lam F ((L' : ℝ) + 1) (bcr e f) := by
      rw [hX0]; apply Lam_add_eq F <;> ring
    have e1' : Q2 F 1 (L' : ℝ) = Lam F ((L' : ℝ) + 1 + cb e f) (-1) := by
      simp only [Q2]; congr 1; ring
    refine ⟨z, ?_⟩
    rw [hr, e1, e3, e1', hX0, Nq_eq F FC]; push_cast
    rw [show ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) / (f : ℝ) ^ 2 = bcr e f from rfl]
    ext p; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto

set_option maxHeartbeats 2000000 in
/-- **3.5, the two `α`'s at the corner `LP′`** (`L = L' + 1`): with `T₂ + (L−1)P′`, `T₃ + (L−1)P′`
(`γ`, `γ`), `K + (L−1)P′` and `Z₀ + (L−1)P′` (`β`, `β`) at `LP′` (figure `{2α, 2β, 2γ}`), the tile
across `K + (L−1)P′`'s flank along `ℓ_L` is `T₂ + LP′` or `σ_b`, and the tile across
`Z₀ + (L−1)P′`'s flank along `L_L` is `T₃ + LP′` or `σ_3` (`alpha_at_R2`, `alpha_at_v`; no `m = 1`
input). -/
theorem corner_fills (L : LFrame F) (L' : ℕ)
    (hXint : Q2 F 0 ((L' : ℝ) + 1) ∈ interior D.target.carrier)
    (hT : Present D (T2c F 0 L')) (hU : Present D (Up F L' 0))
    (hK : Present D (Kc F 0 L')) (hZ : Present D (Dn F L' 0)) :
    (Present D (T2c F 0 (L' + 1)) ∨ Present D (Sw F 0 ((L' : ℝ) + 1))) ∧
      (Present D (Up F (L' + 1) 0) ∨ Present D (Xs F ((L' : ℝ) + 1) 0)) := by
  classical
  have FC := L.FC
  obtain ⟨hcb0, hcb1⟩ := cb_pos F
  have hX0 : Q2 F 0 ((L' : ℝ) + 1) = Lam F ((L' : ℝ) + 1) 0 := by simp [Q2]
  obtain ⟨iT, hrT⟩ := hT
  obtain ⟨iU, hrU⟩ := hU
  obtain ⟨iK, hrK⟩ := hK
  obtain ⟨iZ, hrZ⟩ := hZ
  have gT : (D.tile iT).localAngle (Q2 F 0 ((L' : ℝ) + 1)) = γ := by
    have := (U_angles F FC hrT).2.2; simp only [Nat.cast_zero] at this; exact this
  have gU : (D.tile iU).localAngle (Q2 F 0 ((L' : ℝ) + 1)) = γ := by
    rw [hX0]; have := (Up_angles F hrU).2.1; simp only [Nat.cast_zero] at this; exact this
  have gK : (D.tile iK).localAngle (Q2 F 0 ((L' : ℝ) + 1)) = β := by
    have := (D_angles F FC hrK).2.1; simp only [Nat.cast_zero] at this; exact this
  have gZ : (D.tile iZ).localAngle (Q2 F 0 ((L' : ℝ) + 1)) = β := by
    rw [hX0]; have := (Dn_angles F hrZ).1; simp only [Nat.cast_zero] at this; exact this
  -- the four ranges in `Q2` form
  have qA : Lam F (L' : ℝ) 0 = Q2 F 0 (L' : ℝ) := by simp [Q2]
  have qB : Lam F (L' : ℝ) 1 = Q2 F (-1) ((L' : ℝ) + 1 + cb e f) := by simp only [Q2]; congr 1 <;> ring
  have qC : Lam F ((L' : ℝ) + 1) 1 = Q2 F (-1) ((L' : ℝ) + 1 + 1 + cb e f) := by
    simp only [Q2]; congr 1 <;> ring
  have rT : Set.range (D.tile iT).pts = {Q2 F 0 ((L' : ℝ) + 1), Q2 F 0 (L' : ℝ), Q2 F 1 (L' : ℝ)} := by
    rw [hrT, U_eq F FC]; simp only [Nat.cast_zero, zero_add]
    ext p; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  have rU : Set.range (D.tile iU).pts = {Q2 F 0 ((L' : ℝ) + 1), Q2 F 0 (L' : ℝ),
      Q2 F (-1) ((L' : ℝ) + 1 + cb e f)} := by
    rw [hrU]; simp only [Up, Nat.cast_zero, zero_add]
    rw [qA, qB, hX0]
    ext p; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  have rK : Set.range (D.tile iK).pts = {Q2 F 0 ((L' : ℝ) + 1), Q2 F 1 ((L' : ℝ) + 1),
      Q2 F 1 (L' : ℝ)} := by
    rw [hrK, D_eq F FC]; simp only [Nat.cast_zero, zero_add]
    ext p; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  have rZ : Set.range (D.tile iZ).pts = {Q2 F 0 ((L' : ℝ) + 1),
      Q2 F (-1) ((L' : ℝ) + 1 + 1 + cb e f), Q2 F (-1) ((L' : ℝ) + 1 + cb e f)} := by
    rw [hrZ]; simp only [Dn, Nat.cast_zero, zero_add]
    rw [qB, qC, hX0]
    ext p; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  have hTU : iT ≠ iU := ne_of_range rT rU (p := Q2 F 1 (L' : ℝ)) mem3_3 (by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨Q2_ne F FC (Or.inl (by norm_num)), Q2_ne F FC (Or.inl (by norm_num)),
      Q2_ne F FC (Or.inl (by norm_num))⟩)
  have hKZ : iK ≠ iZ := ne_of_range rK rZ (p := Q2 F 1 (L' : ℝ)) mem3_3 (by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨Q2_ne F FC (Or.inl (by norm_num)), Q2_ne F FC (Or.inl (by norm_num)),
      Q2_ne F FC (Or.inl (by norm_num))⟩)
  obtain ⟨E1, E2⟩ := interior_card_eqs D F.hAng F.hM.hα' F.hM.hβ' F.hM.hγ' hXint
  have cG := card_two hTU gT gU
  have cB := card_two hKZ gK gZ
  have hstr : ∀ z : Fin N, (D.tile z).localAngle (Q2 F 0 ((L' : ℝ) + 1)) = Real.pi ∨
      (D.tile z).localAngle (Q2 F 0 ((L' : ℝ) + 1)) = 2 * Real.pi → False := by
    intro z h
    rcases h with h | h <;> (have := card_one h; omega)
  -- the `Λ₂` side: across `K + (L−1)P′`'s flank along `V − A`
  have part2 : Present D (T2c F 0 (L' + 1)) ∨ Present D (Sw F 0 ((L' : ℝ) + 1)) := by
    obtain ⟨mK, hmK, hflK⟩ := flank_of_range rK
    rw [Q2_sub_eq F (p := 1 + cb e f) (q := -1) (by ring) (by ring),
      Q2_sub_eq F (p := cb e f) (q := -1) (by ring) (by ring)] at hflK
    obtain ⟨z, hzK, hXz, hcz⟩ := flank_neighbour_dissection D.toDissection hXint hmK hflK
    rcases hcz with ⟨mz, hmz, U, W, hUW, S, hS, hU0, hside⟩ | ⟨m', -, hmpos, -, -⟩
    swap
    · exfalso
      have hznv : ∀ q, (D.tile z).pts q ≠ Q2 F 0 ((L' : ℝ) + 1) := fun q hq =>
        NearBaseVertex.vertex_not_edge _ q hq m' hmpos
      rcases localAngle_mem_pi_of_mem (D.tile z) hXz hznv with h | h
      · exact hstr z (Or.inr h)
      · exact hstr z (Or.inl h)
    have hang := localAngle_at_own_vertex_mem D α β γ F.hM.hα' F.hM.hβ' F.hM.hγ' z mz
    rw [hmz] at hang
    rcases hang with hz | hz | hz
    · rcases alpha_at_R2 F FC hmz hUW hS hU0 hside hz with h | h
      · left; refine ⟨z, ?_⟩; rw [h, U_eq F FC]; push_cast; ring_nf
      · right; exact ⟨z, h⟩
    · exfalso
      rcases mem_of_card_two hKZ gK gZ (by omega) hz with rfl | rfl
      · exact hzK rfl
      · exact ne_of_flank_Q2 F FC hmz hUW hS hU0 rZ (d1 := 0) (e1 := 1) (d2 := -1) (e2 := 1)
          (by ring) (by ring) (by ring) (by ring)
          (fun S' hS' h1 h2 => by linarith) (fun S' hS' h1 h2 => by linarith) rfl
    · exfalso
      rcases mem_of_card_two hTU gT gU (by omega) hz with rfl | rfl
      · exact ne_of_flank_Q2 F FC hmz hUW hS hU0 rT (d1 := -1) (e1 := 0) (d2 := cb e f) (e2 := -1)
          (by ring) (by ring) (by ring) (by ring)
          (fun S' hS' h1 h2 => by linarith)
          (fun S' hS' h1 h2 => by
            have : S' = 1 := by linarith
            subst this; linarith) rfl
      · exact ne_of_flank_Q2 F FC hmz hUW hS hU0 rU (d1 := -1) (e1 := 0) (d2 := -1) (e2 := 1)
          (by ring) (by ring) (by ring) (by ring)
          (fun S' hS' h1 h2 => by linarith) (fun S' hS' h1 h2 => by linarith) rfl
  -- the `Λ₃` side: across `Z₀ + (L−1)P′`'s flank along `v` (down `L_L`)
  have part3 : Present D (Up F (L' + 1) 0) ∨ Present D (Xs F ((L' : ℝ) + 1) 0) := by
    have rZ' : Set.range (D.tile iZ).pts = {Lam F ((L' : ℝ) + 1) 0, Lam F ((L' : ℝ) + 1) 1,
        Lam F (L' : ℝ) 1} := by
      rw [hrZ]; simp only [Dn, Nat.cast_zero, zero_add]
      ext p; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
    obtain ⟨mZ, hmZ, hflZ⟩ := flank_of_range rZ'
    rw [Lam_sub_eq F (by ring : ((L' : ℝ) + 1) - ((L' : ℝ) + 1) = 0) (by ring : (1 : ℝ) - 0 = 1),
      Lam_sub_eq F (by ring : (L' : ℝ) - ((L' : ℝ) + 1) = -1) (by ring : (1 : ℝ) - 0 = 1)] at hflZ
    rw [← hX0] at hmZ hflZ
    obtain ⟨z, hzZ, hXz, hcz⟩ := flank_neighbour_dissection D.toDissection hXint hmZ hflZ
    rcases hcz with ⟨mz, hmz, U, W, hUW, S, hS, hU0, hside⟩ | ⟨m', -, hmpos, -, -⟩
    swap
    · exfalso
      have hznv : ∀ q, (D.tile z).pts q ≠ Q2 F 0 ((L' : ℝ) + 1) := fun q hq =>
        NearBaseVertex.vertex_not_edge _ q hq m' hmpos
      rcases localAngle_mem_pi_of_mem (D.tile z) hXz hznv with h | h
      · exact hstr z (Or.inr h)
      · exact hstr z (Or.inl h)
    have hang := localAngle_at_own_vertex_mem D α β γ F.hM.hα' F.hM.hβ' F.hM.hγ' z mz
    rw [hmz] at hang
    rcases hang with hz | hz | hz
    · rw [hX0] at hmz hUW hz
      rcases alpha_at_v F FC hmz hUW hS hU0 hside hz with h | h
      · left; refine ⟨z, ?_⟩; rw [h]; simp only [Up, Nat.cast_add, Nat.cast_one, Nat.cast_zero]
      · right; exact ⟨z, h⟩
    · exfalso
      rcases mem_of_card_two hKZ gK gZ (by omega) hz with rfl | rfl
      · have hq : vec F 0 1 = S • U := hU0
        exact ne_of_flank_Q2 F FC hmz hUW hS hq rK (d1 := 1 + cb e f) (e1 := -1) (d2 := cb e f)
          (e2 := -1) (by ring) (by ring) (by ring) (by ring)
          (fun S' hS' h1 h2 => by linarith) (fun S' hS' h1 h2 => by linarith) rfl
      · exact hzZ rfl
    · exfalso
      rcases mem_of_card_two hTU gT gU (by omega) hz with rfl | rfl
      · exact ne_of_flank_Q2 F FC hmz hUW hS hU0 rT (d1 := -1) (e1 := 0) (d2 := cb e f) (e2 := -1)
          (by ring) (by ring) (by ring) (by ring)
          (fun S' hS' h1 h2 => by linarith) (fun S' hS' h1 h2 => by linarith) rfl
      · exact ne_of_flank_Q2 F FC hmz hUW hS hU0 rU (d1 := -1) (e1 := 0) (d2 := -1) (e2 := 1)
          (by ring) (by ring) (by ring) (by ring)
          (fun S' hS' h1 h2 => by linarith) (fun S' hS' h1 h2 => by linarith) rfl
  exact ⟨part2, part3⟩

/-! ## §2 The state `S(L)` and the band half-turns of level `L` -/

/-- **The state `S(L)` of Λ3M** (proof_L3M.md §0.2–0.3; proof_H_empty.md §5.15) at the chain point
`kV`, `k = k' + 1`: (σ1) `B_k = L_b` is a tile; (σ2) the band `T₂ + iV + tP′` (`i ≤ k − 1`,
`i + t ≤ L − 1`) and `K + iV + tP′` (`i ≤ k − 1`, `i + t ≤ L − 2`); (σ3) `L·T₃`. -/
structure L3S (F : HFrame D e f α β γ) (k' L : ℕ) : Prop where
  hB : Present D (Sw F ((k' : ℝ) + 1) 0)
  band2 : ∀ i t, i ≤ k' → i + t + 1 ≤ L → Present D (T2c F i t)
  bandK : ∀ i t, i ≤ k' → i + t + 2 ≤ L → Present D (Kc F i t)
  up3 : ∀ i t, i + t + 1 ≤ L → Present D (Up F i t)
  dn3 : ∀ i t, i + t + 2 ≤ L → Present D (Dn F i t)

/-- `LP′` carries two `γ`'s (`T₂ + (L−1)P′`, `T₃ + (L−1)P′`): no straight tile there. -/
theorem lp_ns (L : LFrame F) (L' : ℕ)
    (hXint : Q2 F 0 ((L' : ℝ) + 1) ∈ interior D.target.carrier)
    (hT : Present D (T2c F 0 L')) (hU : Present D (Up F L' 0)) :
    ∀ z, (D.tile z).localAngle (Q2 F 0 ((L' : ℝ) + 1)) ≠ Real.pi ∧
      (D.tile z).localAngle (Q2 F 0 ((L' : ℝ) + 1)) ≠ 2 * Real.pi := by
  have FC := L.FC
  obtain ⟨iG, hrG⟩ := hT
  obtain ⟨iU, hrU⟩ := hU
  have hX0 : Q2 F 0 ((L' : ℝ) + 1) = Lam F ((L' : ℝ) + 1) 0 := by simp [Q2]
  have gG : (D.tile iG).localAngle (Q2 F 0 ((L' : ℝ) + 1)) = γ := by
    have := (U_angles F FC hrG).2.2; simp only [Nat.cast_zero] at this; exact this
  have gU : (D.tile iU).localAngle (Q2 F 0 ((L' : ℝ) + 1)) = γ := by
    rw [hX0]; have := (Up_angles F hrU).2.1; simp only [Nat.cast_zero] at this; exact this
  have hGU : iG ≠ iU := by
    intro h
    have h1 : Q2 F 1 (L' : ℝ) ∈ Set.range (D.tile iU).pts := by
      rw [← h, hrG, U_eq F FC]; simp only [Nat.cast_zero, zero_add]; exact mem3_2
    rw [hrU] at h1
    simp only [Up, Nat.cast_zero, zero_add] at h1
    have : Q2 F 1 (L' : ℝ) = Lam F (1 * (1 + cb e f) + L') (-1) := rfl
    rw [this] at h1
    exact not_mem3 F FC (Or.inr (by norm_num)) (Or.inr (by norm_num)) (Or.inr (by norm_num)) h1
  exact count_gg F hXint hGU gG gU

set_option maxHeartbeats 4000000 in
/-- **Λ3M 2.3, 2.4, 3.1, 3.2: every band half-turn of level `L`** (`L = L' + 1 ≥ k + 1`).  `W_L`
is interior (a vertex of `K + (k−1)V + (L−k−1)P′`), so `L < f`; the r-side of `m_k` straddles `W_L`
(`r_str`, A2, **m = 1**); `LP′` has two `γ`'s; so the band segment `[LP′, W_L]` of `AD_L` has far side
`a^k` (`far_word`, A1, **m = 1**); the tile across its first edge is `K + (L−1)P′` (`ad_first`; `N_L`
is killed by PK·a(L), `pka_frame`); and marching from `LP′` (`junction`, each half-turn the next
junction's blocker) every tile across the segment is the half-turn. -/
theorem l3m_band (L : LFrame F) (k' L' : ℕ) (hkL : k' + 1 ≤ L') (hS : L3S F k' (L' + 1)) :
    ∀ i t, i ≤ k' → i + t = L' → Present D (Kc F i t) := by
  classical
  have FC := L.FC
  obtain ⟨hcb0, hcb1⟩ := cb_pos F
  obtain ⟨w0, hw0⟩ : ∃ w0, L' = k' + 1 + w0 := ⟨L' - (k' + 1), by omega⟩
  have hL'R : (L' : ℝ) = (k' : ℝ) + 1 + w0 := by rw [hw0]; push_cast; ring
  have hDW := hS.bandK k' w0 le_rfl (by omega)
  have hWint := D_vertex_int F L hDW
  have hWle := Q2_le F FC (interior_subset hWint)
  have hWne := O2 F (k' + 1) (w0 + 1) (by omega)
  push_cast at hWne
  have hWlt : ((w0 : ℝ) + 1) + ((k' : ℝ) + 1) * cb e f < f := lt_of_le_of_ne hWle hWne
  have hXint : Q2 F 0 ((L' : ℝ) + 1) ∈ interior D.target.carrier := by
    apply Q2_interior F FC le_rfl (by positivity) (by positivity)
    rw [zero_mul, add_zero]; nlinarith
  -- (2.3) the r-side straddle at `W_L`
  have hMW : MStr F ((k' : ℝ) + 1) (Q2 F ((k' : ℝ) + 1) ((w0 : ℝ) + 1)) := by
    have h := r_str F L k' (w0 + 1) (by omega) (by
        have : ((w0 + 1 : ℕ) : ℝ) < f := by push_cast; nlinarith
        have : w0 + 1 < f := by exact_mod_cast this
        omega)
      (by push_cast; exact hWlt)
      (fun s hs => hS.bandK k' s le_rfl (by omega))
      (by obtain ⟨ε, hε, hE⟩ := seedB_of_Sw F FC _ _ hS.hB
          rw [zero_add] at hE; exact ⟨ε, hε, hE⟩)
    push_cast at h; exact h
  obtain ⟨iW, hrW⟩ := hDW
  have gW := (D_angles F FC hrW).2.2
  have hWf : ¬ AStr F ((L' + 1 : ℕ) : ℝ) (Q2 F ((k' : ℝ) + 1) ((w0 : ℝ) + 1)) := fun h =>
    no_two_straight F hWint hMW h (ind_rho_ad F FC) gW
  have hns := lp_ns F L L' hXint (hS.band2 0 L' (by omega) (by omega)) (hS.up3 L' 0 (by omega))
  have hYf : ¬ AStr F ((L' + 1 : ℕ) : ℝ) (Q2 F 0 ((L' : ℝ) + 1)) := by
    rintro ⟨ε, -, hx⟩
    rcases straight_count hx with h | h
    · exact (hns _).2 h
    · exact (hns _).1 h
  -- (2.4) the band far word
  have hseg : ∀ s : ℝ, 0 ≤ s → s ≤ ((k' + 1 : ℕ) : ℝ) →
      Q2 F (((0 : ℕ) : ℝ) + s) (((L' + 1 : ℕ) : ℝ) - ((0 : ℕ) : ℝ) - s)
        ∈ interior D.target.carrier := by
    intro s hs0 hs1
    push_cast at hs1 ⊢
    apply Q2_interior F FC (by linarith) (by linarith) (by linarith)
    have h1 : s * (cb e f - 1) ≤ ((k' : ℝ) + 1) * (cb e f - 1) :=
      mul_le_mul_of_nonneg_right hs1 (by linarith)
    nlinarith
  have hfar := far_word F L (L' + 1) 0 (k' + 1) (by omega) (by
      have : ((k' + 1 : ℕ) : ℝ) < f := by push_cast; nlinarith
      have : k' + 1 < f := by exact_mod_cast this
      omega) (by omega)
    (fun s hs0 hs1 => hseg s hs0.le hs1.le)
    (fun i t hi1 hi2 hit => hS.band2 i t (by omega) (by omega))
    (by
      have : Q2 F ((0 : ℕ) : ℝ) (((L' + 1 : ℕ) : ℝ) - ((0 : ℕ) : ℝ)) = Q2 F 0 ((L' : ℝ) + 1) := by
        push_cast; congr 1 <;> ring
      rw [this]; exact hYf)
    (by
      have : Q2 F (((0 : ℕ) : ℝ) + ((k' + 1 : ℕ) : ℝ))
          (((L' + 1 : ℕ) : ℝ) - ((0 : ℕ) : ℝ) - ((k' + 1 : ℕ) : ℝ))
          = Q2 F ((k' : ℝ) + 1) ((w0 : ℝ) + 1) := by
        push_cast; congr 1 <;> linarith
      rw [this]; exact hWf)
  -- (3.1)–(3.2) the corner's `AD_L` tile is `K + (L−1)P′`
  have hcol : ∀ j < L' + 1, Present D (Col F j) := fun j hj => by
    rw [Col_T2c]; exact hS.band2 0 j (by omega) (by omega)
  have hK0 : Present D (Kc F 0 L') := by
    rcases ad_first F L L' hXint (fun ε hε ℓ hℓ hE => hfar ε hε 0 ℓ hℓ le_rfl (by positivity) (by
        have e1 : Q2 F (((0 : ℕ) : ℝ) + 0) (((L' + 1 : ℕ) : ℝ) - ((0 : ℕ) : ℝ) - 0)
            = Q2 F 0 ((L' : ℝ) + 1) := by push_cast; congr 1 <;> ring
        have e2 : Q2 F (((0 : ℕ) : ℝ) + 0 + ℓ / ((e : ℝ) * f))
            (((L' + 1 : ℕ) : ℝ) - ((0 : ℕ) : ℝ) - 0 - ℓ / ((e : ℝ) * f))
            = Q2 F (ℓ / ((e : ℝ) * f)) ((L' : ℝ) + 1 - ℓ / ((e : ℝ) * f)) := by
          push_cast; congr 1 <;> ring
        rw [e1, e2]; exact hE))
      (hS.band2 0 L' (by omega) (by omega)) (hS.up3 L' 0 (by omega)) with h | h
    · exact h
    · exact absurd h (fun hN => pka_frame F L (L' + 1) (by omega) (by
        have : ((L' + 1 : ℕ) : ℝ) < f := by push_cast; nlinarith
        have : L' + 1 < f := by exact_mod_cast this
        omega) hcol hN)
  -- the march from `LP′`
  have key : ∀ n, ∀ i t, i = n → i ≤ k' → i + t = L' → Present D (Kc F i t) := by
    intro n
    induction n with
    | zero =>
      intro i t hi _ hit
      subst hi
      have : t = L' := by omega
      subst this; exact hK0
    | succ n ih =>
      intro i t hi hik hit
      obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨n, hi⟩
      have hitR : (i' : ℝ) + 1 + t = L' := by exact_mod_cast (show i' + 1 + t = L' by omega)
      have hXi : Q2 F ((i' : ℝ) + 1) ((t : ℝ) + 1) ∈ interior D.target.carrier := by
        have h := hseg ((i' : ℝ) + 1) (by positivity) (by
          have : ((i' + 1 : ℕ) : ℝ) ≤ ((k' + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : i' + 1 ≤ k' + 1)
          push_cast at this ⊢; linarith)
        have e : Q2 F (((0 : ℕ) : ℝ) + ((i' : ℝ) + 1)) (((L' + 1 : ℕ) : ℝ) - ((0 : ℕ) : ℝ) - ((i' : ℝ) + 1))
            = Q2 F ((i' : ℝ) + 1) ((t : ℝ) + 1) := by push_cast; congr 1 <;> linarith
        rw [e] at h; exact h
      have hq : (i' : ℝ) + 1 < ((k' + 1 : ℕ) : ℝ) := by
        have : ((i' + 1 : ℕ) : ℝ) < ((k' + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : i' + 1 < k' + 1)
        push_cast at this ⊢; linarith
      refine junction F L (L' + 1) i' t (by omega) hXi (fun ε hε ℓ hℓ hE => hfar ε hε ((i' : ℝ) + 1) ℓ hℓ
          (by positivity) hq ?_) (hS.band2 (i' + 1) t hik (by omega))
        (hS.bandK i' t (by omega) (by omega)) (Or.inr (ih i' (t + 1) (by omega) (by omega) (by omega)))
      have e1 : Q2 F (((0 : ℕ) : ℝ) + ((i' : ℝ) + 1)) (((L' + 1 : ℕ) : ℝ) - ((0 : ℕ) : ℝ) - ((i' : ℝ) + 1))
          = Q2 F ((i' : ℝ) + 1) ((t : ℝ) + 1) := by push_cast; congr 1 <;> linarith
      have e2 : Q2 F (((0 : ℕ) : ℝ) + ((i' : ℝ) + 1) + ℓ / ((e : ℝ) * f))
          (((L' + 1 : ℕ) : ℝ) - ((0 : ℕ) : ℝ) - ((i' : ℝ) + 1) - ℓ / ((e : ℝ) * f))
          = Q2 F ((i' : ℝ) + 1 + ℓ / ((e : ℝ) * f)) ((t : ℝ) + 1 - ℓ / ((e : ℝ) * f)) := by
        push_cast; congr 1 <;> linarith
      rw [e1, e2]; exact hE
  intro i t hi hit
  exact key i i t rfl hi hit

/-- **Terminal(k)** (proof_L3M.md, proof_H_empty.md §5.16): at a level `L = L' + 1` with
`kc + (L − k + 1)b > fb` (the exit level `L*`), `S(L)` is impossible: `l3m_band` makes
`K + (k−1)V + (L−k)P′` a tile, and its vertex `W_{L+1}` has depth `kc + (L−k+1)b > fb`. -/
theorem l3m_terminal (L : LFrame F) (k' L' : ℕ) (hkL : k' + 1 ≤ L') (hS : L3S F k' (L' + 1))
    (hexit : (f : ℝ) < ((L' : ℝ) - k' + 1) + ((k' : ℝ) + 1) * cb e f) : False := by
  have FC := L.FC
  obtain ⟨w0, hw0⟩ : ∃ w0, L' = k' + 1 + w0 := ⟨L' - (k' + 1), by omega⟩
  have hK := l3m_band F L k' L' hkL hS k' (w0 + 1) le_rfl (by omega)
  have hm : Q2 F ((k' : ℝ) + 1) ((w0 : ℝ) + 1 + 1) ∈ D.target.carrier := by
    apply mem_of_present hK; rw [D_eq F FC]; push_cast; exact mem3_3
  have hle := Q2_le F FC hm
  have : (L' : ℝ) = k' + 1 + w0 := by rw [hw0]; push_cast; ring
  linarith

set_option maxHeartbeats 4000000 in
/-- **Λ3M(k, L) — THE MARCH AFTER `L_b`, ONE LEVEL — PROVED** (proof_L3M.md §§2–4; corrected statement
§0.3): `S(L) ⇒ S(L+1)` for `k + 1 ≤ L ≤ f − 2` (in the tree, `L ≤ L* − 1 ≤ f − 2`). -/
theorem l3m_step (L : LFrame F) (k' L' : ℕ) (hkL : k' + 1 ≤ L') (hLf : L' + 3 ≤ f)
    (hS : L3S F k' (L' + 1)) : L3S F k' (L' + 2) := by
  classical
  have FC := L.FC
  obtain ⟨-, hb0, hc0, -, -⟩ := consts F
  obtain ⟨hcb0, hcb1⟩ := cb_pos F
  have hbc : (0 : ℝ) < ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) / (f : ℝ) ^ 2 := by positivity
  have hKb := l3m_band F L k' L' hkL hS
  have hcol : ∀ j < L' + 1, Present D (Col F j) := fun j hj => by
    rw [Col_T2c]; exact hS.band2 0 j (by omega) (by omega)
  -- CW(ℓ_j, m_k) at level `L` with `B_k`'s c-seed
  have hseedB : ∃ ε ∈ rsChain F (((k' + 1 : ℕ) : ℝ)),
      EdgeIs D ε (Q2 F ((k' + 1 : ℕ) : ℝ) 0) (Q2 F ((k' + 1 : ℕ) : ℝ) (cb e f)) := by
    obtain ⟨ε, hε, hE⟩ := seedB_of_Sw F FC _ _ hS.hB
    rw [zero_add] at hE; push_cast; exact ⟨ε, hε, hE⟩
  have hCW : ∀ j : ℕ, 1 ≤ j → j ≤ L' + 1 → L' + 2 ≤ k' + 1 + j → ∀ x : ℝ,
      x = ((L' + 1 : ℕ) : ℝ) - j → ∀ ε ∈ bandChain F (j : ℝ),
      EdgeIs D ε (Q2 F x j) (Q2 F (x + bcr e f) j) → False := by
    intro j hj1 hjL hjk x hx ε hε hE
    apply cw_frame F L j (k' + 1) (L' + 1) (L' + 1)
    refine ⟨hj1, by omega, hjL, le_rfl, by omega, by omega, ?_, hseedB, ?_⟩
    · rw [← hx]; exact ⟨ε, hε, hE⟩
    · intro i t hi ht hit
      refine ⟨hS.band2 i t (by omega) hit, ?_⟩
      rcases Nat.lt_or_ge (i + t + 2) (L' + 2) with h | h
      · exact hS.bandK i t (by omega) (by omega)
      · exact hKb i t (by omega) (by omega)
  -- (3.3) `G_L`, hence every row-`L` far tile is the half-turn
  have hGL : ¬ MirUp F L' 0 := fun h => by
    obtain ⟨ε, hε, hE⟩ := mirUp_seed F FC L' h
    exact hCW (L' + 1) (by omega) le_rfl (by omega) 0 (by simp) ε (by push_cast; exact hε)
      (by push_cast; rw [zero_add]; exact hE)
  obtain ⟨-, hrow2, hrow3⟩ := r8_row F L L' (by omega) (fun i t h => hS.up3 i t h)
    (fun i t h => hS.dn3 i t h) (hcol L' (by omega))
  have hROW : ∀ i t, i + t = L' → Present D (Dn F i t) := by
    intro i t hit
    rcases hrow2 i t hit with h | h
    · exact h
    · exact absurd (hrow3 i t hit h) hGL
  have hC3 : ∀ i t, i + t + 1 ≤ L' + 1 → Present D (Up F i t) ∧ Present D (Dn F i t) := by
    intro i t hit
    refine ⟨hS.up3 i t hit, ?_⟩
    rcases Nat.lt_or_ge (i + t + 2) (L' + 2) with h | h
    · exact hS.dn3 i t (by omega)
    · exact hROW i t (by omega)
  -- (3.4)–(3.5) the corner `LP′`
  have hXint : Q2 F 0 ((L' : ℝ) + 1) ∈ interior D.target.carrier := by
    apply Q2_interior F FC le_rfl (by positivity) (by positivity)
    rw [zero_mul, add_zero]
    have : (L' : ℝ) + 3 ≤ f := by exact_mod_cast hLf
    linarith
  obtain ⟨c2, c3⟩ := corner_fills F L L' hXint (hS.band2 0 L' (by omega) (by omega))
    (hS.up3 L' 0 (by omega)) (hKb 0 L' (by omega) (by omega)) (hROW L' 0 (by omega))
  have hT2P : Present D (T2c F 0 (L' + 1)) := by
    rcases c2 with h | h
    · exact h
    · exfalso
      obtain ⟨ε, hε, hE⟩ := seed_of_Sw F FC 0 ((L' : ℝ) + 1) h
      exact hCW (L' + 1) (by omega) le_rfl (by omega) 0 (by simp) ε (by push_cast; exact hε)
        (by push_cast; exact hE)
  have hT3P : Present D (Up F (L' + 1) 0) := by
    rcases c3 with h | h
    · exact h
    · exfalso
      obtain ⟨ε, hε, hE⟩ := seed_of_Xs F L _ _ h
      rw [zero_add] at hE
      apply rw_frame F L (L' + 1) (L' + 1) (by omega) le_rfl (by omega)
      refine ⟨fun i t hi ht => hC3 i t ht, ?_, ?_⟩
      · push_cast; exact start_of_edge F L _ _ hbc hε hE
      · push_cast
        exact ⟨ε, hε, 0, le_rfl, by simp, by rw [zero_add]; exact hE⟩
  refine ⟨hS.hB, ?_, ?_, ?_, ?_⟩
  · -- (4.4) the band up cells of level `L + 1`
    intro i t hi hit
    rcases Nat.lt_or_ge (i + t + 1) (L' + 2) with h | h
    · exact hS.band2 i t hi (by omega)
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · have : t = L' + 1 := by omega
      subst this; exact hT2P
    obtain ⟨a, rfl⟩ : ∃ a, i = a + 1 := ⟨i - 1, by omega⟩
    obtain ⟨b, rfl⟩ : ∃ b, t = b + 1 := ⟨t - 1, by omega⟩
    have hA := hS.bandK a b (by omega) (by omega)
    rcases slot2 F L a b (D_vertex_int F L hA) hA (hS.band2 a (b + 1) (by omega) (by omega))
        (hKb (a + 1) b hi (by omega)) (hS.band2 (a + 1) b hi (by omega))
        (hKb a (b + 1) (by omega) (by omega)) with h | hSw
    · exact h
    · exfalso
      obtain ⟨ε, hε, hE⟩ := seed_of_Sw F FC _ _ hSw
      exact hCW (b + 1) (by omega) (by omega) (by omega) ((a : ℝ) + 1) (by
          have : ((a + 1 + (b + 1) : ℕ) : ℝ) = ((L' + 1 : ℕ) : ℝ) := by
            rw [show a + 1 + (b + 1) = L' + 1 by omega]
          push_cast at this ⊢; linarith) ε (by push_cast; exact hε) (by push_cast; exact hE)
  · intro i t hi hit
    rcases Nat.lt_or_ge (i + t + 2) (L' + 2) with h | h
    · exact hS.bandK i t hi (by omega)
    · exact hKb i t hi (by omega)
  · -- (4.1)–(4.3) the Λ₃ up cells of level `L + 1`
    intro i t hit
    rcases Nat.lt_or_ge (i + t + 1) (L' + 2) with h | h
    · exact hS.up3 i t (by omega)
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · have : t = L' + 1 := by omega
      subst this
      exact slot_leg F L L' hLf (hS.up3 0 L' (by omega)) (hROW 0 L' (by omega))
    rcases Nat.eq_zero_or_pos t with rfl | ht0
    · have : i = L' + 1 := by omega
      subst this; exact hT3P
    obtain ⟨a, rfl⟩ : ∃ a, i = a + 1 := ⟨i - 1, by omega⟩
    obtain ⟨b, rfl⟩ : ∃ b, t = b + 1 := ⟨t - 1, by omega⟩
    rcases slot_int F L a b (by omega) (hS.dn3 a b (by omega)) (hS.up3 (a + 1) b (by omega))
        (hROW a (b + 1) (by omega)) (hS.up3 a (b + 1) (by omega)) (hROW (a + 1) b (by omega))
      with h | hXs
    · exact h
    · exfalso
      apply rw_frame F L (a + 1) (L' + 1) (by omega) (by omega) (by omega)
      refine ⟨fun i' t' hi' ht' => hC3 i' t' ht', ?_, ?_⟩
      · exact start_of_up F L (a + 1) (hS.up3 (a + 1) 0 (by omega))
      · obtain ⟨ε, hε, hE⟩ := seed_of_Xs F L _ _ hXs
        refine ⟨ε, by push_cast; exact hε, (b : ℝ) + 1, by positivity, ?_, by push_cast; exact hE⟩
        have : ((a + 1 + (b + 1) : ℕ) : ℝ) = ((L' + 1 : ℕ) : ℝ) := by
          rw [show a + 1 + (b + 1) = L' + 1 by omega]
        push_cast at this ⊢; linarith
  · intro i t hit
    rcases Nat.lt_or_ge (i + t + 2) (L' + 2) with h | h
    · exact hS.dn3 i t (by omega)
    · exact hROW i t (by omega)

/-! ## §3 Theorem L3M and Theorem H -/

set_option maxHeartbeats 1000000 in
/-- **The base `S(k+1)`** (proof_L3M.md, proof_H_empty.md §5.15): from `Π(k)` and `B_k`, S4(k) gives
`Π(k+1)` except the `α`-tile at `kV`, which is `B_k`.  (`B_k`'s vertex `kV + c·u_l` has depth
`(k+1)c ≤ fb`, so `kc < fb` and `k ≤ f − 2`.) -/
theorem l3m_base (L : LFrame F) (k' : ℕ) (hP : PiK F (k' + 1))
    (hB : Present D (Sw F ((k' : ℝ) + 1) 0)) : L3S F k' (k' + 2) := by
  have FC := L.FC
  obtain ⟨hcb0, hcb1⟩ := cb_pos F
  obtain ⟨-, hb0, hc0, -, -⟩ := consts F
  obtain ⟨hT2, hK2, hUp, hDn⟩ := hP
  have hm : Q2 F ((k' : ℝ) + 1) (0 + cb e f) ∈ D.target.carrier :=
    mem_of_present hB (by rw [Sw]; exact mem3_3)
  rw [zero_add] at hm
  have hle := Q2_le F FC hm
  have h2 : cb e f * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) = (f : ℝ) ^ 2 := by rw [cb]; field_simp
  have hle' : ((k' : ℝ) + 2) * cb e f ≤ f := by linarith
  have hKc : ((k' + 1 : ℕ) : ℝ) * (f : ℝ) ^ 2 < (f : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) := by
    have h3 : ((k' : ℝ) + 2) * cb e f * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)
        ≤ (f : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) := mul_le_mul_of_nonneg_right hle' hb0.le
    have h4 : ((k' : ℝ) + 2) * cb e f * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) = ((k' : ℝ) + 2) * (f : ℝ) ^ 2 := by
      rw [mul_assoc, h2]
    push_cast; linarith
  have hkf : k' + 3 ≤ f := by
    have : ((k' : ℝ) + 2) < f := by nlinarith
    have : k' + 2 < f := by exact_mod_cast this
    omega
  obtain ⟨hAD, hROW, hS2, hS3⟩ := s4_frame F L k' hkf hKc hT2 hK2 hUp hDn
  refine ⟨hB, fun i t hi hit => ?_, fun i t hi hit => ?_, fun i t hit => ?_, fun i t hit => ?_⟩
  · rcases Nat.lt_or_ge (i + t + 1) (k' + 2) with h | h
    · exact hT2 i t (by omega)
    · exact hS2 i t (by omega) hi
  · rcases Nat.lt_or_ge (i + t + 2) (k' + 2) with h | h
    · exact hK2 i t (by omega)
    · exact hAD i t (by omega)
  · rcases Nat.lt_or_ge (i + t + 1) (k' + 2) with h | h
    · exact hUp i t (by omega)
    · exact hS3 i t (by omega)
  · rcases Nat.lt_or_ge (i + t + 2) (k' + 2) with h | h
    · exact hDn i t (by omega)
    · exact hROW i t (by omega)

set_option maxHeartbeats 1000000 in
/-- **THEOREM L3M(k) — PROVED** (proof_H_empty.md §5.16): no dissection (in the apex frame) contains
`Π(k)` and `B_k` (`k = k' + 1`).  `S(k+1)` from the base; then, level by level, Terminal(k) at the exit
level `L*` or the step Λ3M(k, L); the levels are bounded by `f`. -/
theorem l3m_theorem (L : LFrame F) (k' : ℕ) (hP : PiK F (k' + 1))
    (hB : Present D (Sw F ((k' : ℝ) + 1) 0)) : False := by
  have FC := L.FC
  obtain ⟨hcb0, hcb1⟩ := cb_pos F
  have key : ∀ d, L3S F k' (k' + 2 + d) := by
    intro d
    induction d with
    | zero => exact l3m_base F L k' hP hB
    | succ d ih =>
      have ih' : L3S F k' (k' + 1 + d + 1) := by
        rw [show k' + 1 + d + 1 = k' + 2 + d by omega]; exact ih
      by_cases hexit : (f : ℝ) < (((k' + 1 + d : ℕ) : ℝ) - k' + 1) + ((k' : ℝ) + 1) * cb e f
      · exact (l3m_terminal F L k' (k' + 1 + d) (by omega) ih' hexit).elim
      · push Not at hexit
        have hLf : k' + 1 + d + 3 ≤ f := by
          push_cast at hexit
          have : ((k' + 1 + d : ℕ) : ℝ) + 2 < f := by push_cast; nlinarith
          have : k' + 1 + d + 2 < f := by exact_mod_cast this
          omega
        have := l3m_step F L k' (k' + 1 + d) (by omega) hLf ih'
        rwa [show k' + 1 + d + 2 = k' + 2 + (d + 1) by omega] at this
  have hK := (key f).bandK k' f le_rfl (by omega)
  have hm : Q2 F ((k' : ℝ) + 1) ((f : ℝ) + 1) ∈ D.target.carrier := by
    apply mem_of_present hK; rw [D_eq F FC]; exact mem3_3
  have hle := Q2_le F FC hm
  nlinarith

/-- **THEOREM H — (H) IS EMPTY, AND THERE IS NO `m = 1` DISSECTION AT COPRIME `2 ≤ e ≤ f − 2`,
frame form — PROVED (by composition).**  In the apex frame of a dissection with the target's cone
coordinates: the `L_c` phase (`lc_phase`: APX, S4 + R9, S5 + S5-M; (M) at level 1 is R2 = PK·a(1)
inside S4(1)) forces an `L_b` turn at some `kV`, `1 ≤ k ≤ n − 1`, with `Π(k)`; Theorem L3M(k)
(`l3m_theorem`) kills it. -/
theorem theorem_H_frame (L : LFrame F) : False := by
  obtain ⟨n', hnc, hnc1⟩ := chain_length F
  obtain ⟨k', -, hP, hB⟩ := lc_phase F L n' hnc hnc1
  exact l3m_theorem F L k' hP hB

/-- **COROLLARY H′ — NO REAL `m = 1` DISSECTION AT COPRIME `2 ≤ e ≤ f − 2` — PROVED (draft).**  No
congruent dissection of the `m = 1` base-β target by the base-β tile `(ef, f² − e², f²)` with its
angles `α, β, γ` (`M1Data`: coprime `2 ≤ e ≤ f − 2`, the model's side/angle data, the angle bundle,
the target's apex `3α`, base corners `β`, legs `f³`, base `e(3f² − e²)`) exists.  The frame is
`ApexLegWord.exists_hframe_coords_m1`; the rest is `theorem_H_frame`. -/
theorem theorem_H_real {kk : Fin 3} (h : ApexFrameReal.M1Data D e f α β γ kk) : False := by
  obtain ⟨F, FC⟩ := ApexLegWord.exists_hframe_coords_m1 D h.hco h.he h.hef h.hM h.hAng kk
    h.hcorner h.hβ1 h.hβ2 h.hleg1 h.hleg2 h.hbase
  exact theorem_H_frame F (lframe_real F h FC)

end Erdos634.Draft.RowWallReal

#print axioms Erdos634.Draft.RowWallReal.ad_first
#print axioms Erdos634.Draft.RowWallReal.corner_fills
#print axioms Erdos634.Draft.RowWallReal.lp_ns
#print axioms Erdos634.Draft.RowWallReal.l3m_band
#print axioms Erdos634.Draft.RowWallReal.l3m_terminal
#print axioms Erdos634.Draft.RowWallReal.l3m_step
#print axioms Erdos634.Draft.RowWallReal.l3m_base
#print axioms Erdos634.Draft.RowWallReal.l3m_theorem
#print axioms Erdos634.Draft.RowWallReal.theorem_H_frame
#print axioms Erdos634.Draft.RowWallReal.theorem_H_real
