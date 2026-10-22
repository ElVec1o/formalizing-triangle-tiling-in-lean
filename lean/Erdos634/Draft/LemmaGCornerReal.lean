-- Draft/LemmaGCornerReal.lean — R8 clause (4), the six fills of the free wedge at `KP′`
-- ((private working notes, not included) §5.8; review_S2B repair R1; review2_R8S4), for real `m = 1`
-- dissections in the apex frame, on top of `r8_ad` (Draft/LemmaGADReal.lean) and `r8_row`
-- (Draft/LemmaGRowReal.lean).  Imported directly by All.lean (stale "NOT imported" header corrected 2026-10-04).
--
-- Build (scratch oleans; never .lake): LemmaGADReal olean in $S, then
--   lake env bash -c 'LEAN_PATH=$S:$LEAN_PATH lean Erdos634/Draft/LemmaGCornerReal.lean'
import Erdos634.Draft.LemmaGADReal

namespace Erdos634.Draft.RowWallReal

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.Draft.HalfTurnR3R4
open Erdos634.Draft.HalfTurnR3R4Glue Erdos634.Draft.CornerAdjacency
open Erdos634.Draft.HalfTurnR3R4Order Erdos634.Draft.MirrorStripR2Real
open Erdos634.Draft.HalfTurnR4Real

variable {N : ℕ} {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ}
variable (F : HFrame D e f α β γ)

/-- The band swap `σ_b` at `Λ(x, 0)`: `α` there, `b` along `ℓ` (direction `V − A`), `c` along `m₀`. -/
noncomputable def Sb (F : HFrame D e f α β γ) (x : ℝ) : Set Plane :=
  {Lam F x 0, Lam F (x + ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) / (f : ℝ) ^ 2 * (1 + cb e f))
      (-(((f : ℝ) ^ 2 - (e : ℝ) ^ 2) / (f : ℝ) ^ 2)), Lam F (x + cb e f) 0}

include F in
theorem bc_cb : ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) / (f : ℝ) ^ 2 * cb e f = 1 := by
  obtain ⟨-, hb0, hc0, -, -⟩ := consts F
  have hf0 : (f : ℝ) ≠ 0 := (f_pos' F).ne'
  rw [cb]; field_simp

/-- **An `α`-tile across a `v`-flank** (flank positively along `v`, other flank on the far side of
`ℝv` from `v − w`) is the up cell `{X, X + w, X + v}` or the swap `Xs` (`c` along `w`, `b` along `v`). -/
theorem alpha_at_v (FC : ApexPlacement.FrameCoords F) {z : Fin N} {mz : Fin 3} {x y : ℝ}
    {U W : Plane} {S : ℝ} (hmz : (D.tile z).pts mz = Lam F x y)
    (hUW : IsFlankPair (D.tile z) mz (Lam F x y) U W) (hS : 0 < S) (hU0 : vec F 0 1 = S • U)
    (hside : cross (vec F 0 1) W * cross (vec F 0 1) (vec F (-1) 1) < 0)
    (hα : (D.tile z).localAngle (Lam F x y) = α) :
    Set.range (D.tile z).pts = {Lam F x y, Lam F (x + 1) y, Lam F x (y + 1)} ∨
      Set.range (D.tile z).pts = Xs F x y := by
  obtain ⟨ha0, hb0, hc0, hbc, hac⟩ := consts F
  have hK := K_ne F FC
  have hK2 : 0 < ((f : ℝ) ^ 2 * cross (w F) F.uL) * ((f : ℝ) ^ 2 * cross (w F) F.uL) :=
    mul_self_pos.mpr hK
  obtain ⟨hn, hopp⟩ := (corner_dataH F hmz hUW).2 hα
  have hL0 := norm_vec_01 F
  obtain ⟨hcb0, -⟩ := cb_pos F
  have hbc1 := bc_cb F
  rcases hn with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · -- `b` along `v`: the swap
    right
    have hq : (0 : ℝ) < ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) / (f : ℝ) ^ 2 := by positivity
    have hU : U = vec F 0 (((f : ℝ) ^ 2 - (e : ℝ) ^ 2) / (f : ℝ) ^ 2) := by
      rw [flank_eq hS hU0 h1 hL0 hc0, vec_smul, mul_zero, mul_one]
    have hs2 : cross (vec F 0 1) (vec F (cb e f) 0) * cross (vec F 0 1) (vec F (-1) 1) < 0 := by
      rw [cross_vec, cross_vec]; nlinarith
    have hUne : vec F 0 (((f : ℝ) ^ 2 - (e : ℝ) ^ 2) / (f : ℝ) ^ 2) ≠ 0 := by
      intro h; have := norm_vec_0q F hq.le; rw [h, norm_zero] at this
      have : 0 < ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) / (f : ℝ) ^ 2 * (f : ℝ) ^ 2 := by positivity
      linarith
    have hr := ident hmz hUW hU hUne
      (by have := side_of_across hS hU0 hside hs2; rwa [hU] at this)
      (by rw [h2, norm_vec_p0 F hcb0.le, cb, div_mul_cancel₀ _ hb0.ne'])
      (by rw [hopp, dist_add_vec, zero_sub, sub_zero,
          show vec F (-cb e f) (((f : ℝ) ^ 2 - (e : ℝ) ^ 2) / (f : ℝ) ^ 2)
            = - vec F (cb e f) (-(((f : ℝ) ^ 2 - (e : ℝ) ^ 2) / (f : ℝ) ^ 2)) by
            rw [vec_neg]; norm_num, norm_neg, cb, norm_vec_swap])
    rw [hr, Xs, Lam_add_eq F (add_zero x) rfl, Lam_add_eq F rfl (add_zero y), cb]
    ext p; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  · -- `c` along `v`: the up cell
    left
    have hU : U = vec F 0 1 := by rw [flank_eq hS hU0 h1 hL0 hc0, div_self hc0.ne', one_smul]
    have hs2 : cross (vec F 0 1) (vec F 1 0) * cross (vec F 0 1) (vec F (-1) 1) < 0 := by
      rw [cross_vec, cross_vec]; nlinarith
    have hr := ident hmz hUW hU (by intro h; rw [h, norm_zero] at hL0; linarith)
      (by have := side_of_across hS hU0 hside hs2; rwa [hU] at this)
      (by rw [h2, norm_vec_10]) (by rw [hopp, dist_add_vec, zero_sub, sub_zero,
        show vec F (-1) 1 = vec F (-1) 1 from rfl, norm_vec_m11])
    rw [hr, Lam_add_eq F (add_zero x) rfl, Lam_add_eq F rfl (add_zero y)]
    ext p; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto

/-- **An `α`-tile across a flank along `V − A`** (the line `ℓ` through a `Λ₂`… point; other flank on
the far side from `V − P′`) is `T₂ + X` (`c` along `V − A`, `b` along `w`) or the band swap `σ_b`. -/
theorem alpha_at_R (FC : ApexPlacement.FrameCoords F) {z : Fin N} {mz : Fin 3} {x : ℝ}
    {U W : Plane} {S : ℝ} (hmz : (D.tile z).pts mz = Lam F x 0)
    (hUW : IsFlankPair (D.tile z) mz (Lam F x 0) U W) (hS : 0 < S)
    (hU0 : vec F (1 + cb e f) (-1) = S • U)
    (hside : cross (vec F (1 + cb e f) (-1)) W * cross (vec F (1 + cb e f) (-1)) (vec F (cb e f) (-1))
      < 0)
    (hα : (D.tile z).localAngle (Lam F x 0) = α) :
    Set.range (D.tile z).pts = {Lam F x 0, Lam F (x + (1 + cb e f)) (-1), Lam F (x + 1) 0} ∨
      Set.range (D.tile z).pts = Sb F x := by
  obtain ⟨ha0, hb0, hc0, hbc, hac⟩ := consts F
  have hK := K_ne F FC
  have hK2 : 0 < ((f : ℝ) ^ 2 * cross (w F) F.uL) * ((f : ℝ) ^ 2 * cross (w F) F.uL) :=
    mul_self_pos.mpr hK
  obtain ⟨hn, hopp⟩ := (corner_dataH F hmz hUW).2 hα
  have hL0 := norm_V F
  obtain ⟨hcb0, -⟩ := cb_pos F
  have hbc1 := bc_cb F
  have hq : (0 : ℝ) < ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) / (f : ℝ) ^ 2 := by positivity
  rcases hn with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · -- `b` along `V − A`: the band swap `σ_b`
    right
    have hU : U = vec F (((f : ℝ) ^ 2 - (e : ℝ) ^ 2) / (f : ℝ) ^ 2 * (1 + cb e f))
        (-(((f : ℝ) ^ 2 - (e : ℝ) ^ 2) / (f : ℝ) ^ 2)) := by
      rw [flank_eq hS hU0 h1 hL0 hc0, vec_smul]; congr 1; ring
    have hs2 : cross (vec F (1 + cb e f) (-1)) (vec F (cb e f) 0) *
        cross (vec F (1 + cb e f) (-1)) (vec F (cb e f) (-1)) < 0 := by
      rw [cross_vec, cross_vec]; nlinarith
    have hUne : vec F (((f : ℝ) ^ 2 - (e : ℝ) ^ 2) / (f : ℝ) ^ 2 * (1 + cb e f))
        (-(((f : ℝ) ^ 2 - (e : ℝ) ^ 2) / (f : ℝ) ^ 2)) ≠ 0 := by
      intro h; rw [← vec_zero F] at h; have := (vec_inj F FC h).2; linarith
    have hr := ident hmz hUW hU hUne
      (by have := side_of_across hS hU0 hside hs2; rwa [hU] at this)
      (by rw [h2, norm_vec_p0 F hcb0.le, cb, div_mul_cancel₀ _ hb0.ne'])
      (by
        rw [hopp, dist_add_vec]
        apply (norm_of_sq ha0.le _ (norm_nonneg _)).symm
        rw [norm_vec_sq, cb]
        have hf0 : (f : ℝ) ≠ 0 := (f_pos' F).ne'
        field_simp; ring)
    rw [hr, Sb, Lam_add_eq F rfl (zero_add _), Lam_add_eq F rfl (add_zero (0 : ℝ))]
  · -- `c` along `V − A`: `T₂ + X`
    left
    have hU : U = vec F (1 + cb e f) (-1) := by
      rw [flank_eq hS hU0 h1 hL0 hc0, div_self hc0.ne', one_smul]
    have hs2 : cross (vec F (1 + cb e f) (-1)) (vec F 1 0) *
        cross (vec F (1 + cb e f) (-1)) (vec F (cb e f) (-1)) < 0 := by
      rw [cross_vec, cross_vec]; nlinarith
    have hr := ident hmz hUW hU (by intro h; rw [h, norm_zero] at hL0; linarith)
      (by have := side_of_across hS hU0 hside hs2; rwa [hU] at this)
      (by rw [h2, norm_vec_10]) (by rw [hopp, dist_add_vec,
        show 1 + cb e f - 1 = cb e f by ring, show (-1 : ℝ) - 0 = -1 by ring, norm_VP])
    rw [hr, Lam_add_eq F rfl (zero_add _), Lam_add_eq F rfl (add_zero (0 : ℝ))]

set_option maxHeartbeats 2000000 in
/-- **R8 CLAUSE (4): THE SIX FILLS AT `KP′` — PROVED** (level `K = K' + 1`; review_S2B repair R1).
Given `Π(K)` and `Kc < fb`, the free wedge `2α + 2β` at `KP′ = Λ(K, 0)` (left by the two `γ`'s of
`T₂ + (K−1)P′` and `T₃ + (K−1)P′`) is filled in exactly one of six ways:
* `K + (K−1)P′`, `Z₀ + (K−1)P′`, one of `{T₂ + KP′, σ_b}` and one of `{T₃ + KP′, σ_3}` (four fills;
  `σ_b` = `b` on `ℓ_K`, `c` on `m₀`; `σ_3 = Xs` = `c` on `m₀`, `b` down `L_K`);
* `N_K` and `Z₀ + (K−1)P′`;
* `K + (K−1)P′` and `G_K`.
(The two edge tiles are `r8_ad`/`r8_row` at the corner; two mirrors would put four `γ`'s at
`KP′`; with two half-turns the angle count leaves `2α`, whose tiles lie across the half-turns' free
flanks and are identified by `alpha_at_R`, `alpha_at_v`.) -/
theorem r8_corner (L : LFrame F) (K' : ℕ) (hKf : K' + 2 ≤ f)
    (hKc : ((K' + 1 : ℕ) : ℝ) * (f : ℝ) ^ 2 < (f : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2))
    (hT2 : ∀ i t, i + t + 1 ≤ K' + 1 → Present D (T2c F i t))
    (hK2 : ∀ i t, i + t + 2 ≤ K' + 1 → Present D (Kc F i t))
    (hUp : ∀ i t, i + t + 1 ≤ K' + 1 → Present D (Up F i t))
    (hDn : ∀ i t, i + t + 2 ≤ K' + 1 → Present D (Dn F i t)) :
    (Present D (Kc F 0 K') ∧ Present D (Dn F K' 0) ∧
        (Present D {Lam F ((K' : ℝ) + 1) 0, Lam F ((K' : ℝ) + 1 + (1 + cb e f)) (-1),
            Lam F ((K' : ℝ) + 1 + 1) 0} ∨ Present D (Sb F ((K' : ℝ) + 1))) ∧
        (Present D (Up F (K' + 1) 0) ∨ Present D (Xs F ((K' : ℝ) + 1) 0))) ∨
    (MirT2 F (K' + 1) 0 ∧ Present D (Dn F K' 0)) ∨
    (Present D (Kc F 0 K') ∧ MirUp F K' 0) := by
  classical
  have FC := L.FC
  obtain ⟨ha0, hb0, hc0, hbc, hac⟩ := consts F
  obtain ⟨hcb0, hcb1⟩ := cb_pos F
  have hK := K_ne F FC
  have hK2' : 0 < ((f : ℝ) ^ 2 * cross (w F) F.uL) * ((f : ℝ) ^ 2 * cross (w F) F.uL) :=
    mul_self_pos.mpr hK
  have hKR : (K' : ℝ) + 2 ≤ f := by exact_mod_cast hKf
  have hcol : Present D (Col F K') := by rw [Col_T2c F]; exact hT2 0 K' (by omega)
  obtain ⟨-, a2, -⟩ := r8_ad F L K' hKf hKc hT2 hK2 (hUp K' 0 (by omega))
  obtain ⟨-, r2, -⟩ := r8_row F L K' hKf hUp hDn hcol
  have hX : Lam F ((K' : ℝ) + 1) 0 ∈ interior D.target.carrier :=
    Lam_interior F FC (by positivity) le_rfl (by linarith)
  -- the two `γ`'s at `KP′`
  obtain ⟨iT, hrT⟩ := hT2 0 K' (by omega)
  have rT : Set.range (D.tile iT).pts = {Lam F ((K' : ℝ) + 1) 0, Lam F K' 0,
      Lam F ((K' : ℝ) + 1 + cb e f) (-1)} := by
    rw [hrT, ← Col_T2c F, Col_eq F FC]; ext p; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  have gT : (D.tile iT).localAngle (Lam F ((K' : ℝ) + 1) 0) = γ := by
    apply (angle_of_range F rT).2.2
    rw [dist_Lam, show (K' : ℝ) - ((K' : ℝ) + 1 + cb e f) = -(1 + cb e f) by ring,
      show (0 : ℝ) - -1 = 1 by ring,
      show vec F (-(1 + cb e f)) 1 = - vec F (1 + cb e f) (-1) by rw [vec_neg]; norm_num,
      norm_neg, norm_V]
  obtain ⟨iU, hrU⟩ := hUp K' 0 (by omega)
  have rU : Set.range (D.tile iU).pts = {Lam F ((K' : ℝ) + 1) 0, Lam F K' 0, Lam F K' 1} := by
    rw [hrU]; simp only [Up, Nat.cast_zero, zero_add]
    ext p; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  have gU : (D.tile iU).localAngle (Lam F ((K' : ℝ) + 1) 0) = γ := by
    have := (Up_angles F hrU).2.1; simp only [Nat.cast_zero] at this; exact this
  have hTU : iT ≠ iU := (ne_of_range rU rT (p := Lam F K' 1) mem3_3
    (not_mem3 F FC (Or.inr (by norm_num)) (Or.inr (by norm_num)) (Or.inr (by norm_num)))).symm
  obtain ⟨E1, E2⟩ := interior_card_eqs D F.hAng F.hM.hα' F.hM.hβ' F.hM.hγ' hX
  have cT := card_two hTU gT gU
  -- the edge tiles at `KP′`
  have eA := a2 0 K' (by omega)
  have eR := r2 K' 0 (by omega)
  -- facts on the four candidate edge tiles
  have hX0 : Lam F ((K' : ℝ) + 1) 0 = Lam F (((K' + 1 : ℕ) : ℝ) + ((0 : ℕ) : ℝ) * cb e f)
      (-((0 : ℕ) : ℝ)) := by push_cast; simp
  rcases eA with ⟨iK, hrK⟩ | ⟨M, hM, iM, hrM⟩ <;> rcases eR with ⟨iD, hrD⟩ | ⟨G, hG, iG, hrG⟩
  · -- two half-turns: the four `α`-fills
    left
    have rK := Kc_range F FC (by omega : 0 + K' + 1 = K' + 1) hrK
    push_cast at rK
    simp only [zero_mul, add_zero, zero_add, neg_zero, one_mul] at rK
    have rK' : Set.range (D.tile iK).pts = {Lam F ((K' : ℝ) + 1) 0,
        Lam F ((K' : ℝ) + 1 + cb e f) (-1), Lam F ((K' : ℝ) + 1 + 1 + cb e f) (-1)} := by
      rw [rK]; ext p; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
    have gK : (D.tile iK).localAngle (Lam F ((K' : ℝ) + 1) 0) = β := by
      have := (Kc_angles F FC (by omega : 0 + K' + 1 = K' + 1) hrK).2.1
      rw [hX0]; exact this
    have rD : Set.range (D.tile iD).pts = {Lam F ((K' : ℝ) + 1) 0, Lam F K' 1,
        Lam F ((K' : ℝ) + 1) 1} := by
      rw [hrD]; simp only [Dn, Nat.cast_zero, zero_add]
    have gD : (D.tile iD).localAngle (Lam F ((K' : ℝ) + 1) 0) = β := by
      have := (Dn_angles F hrD).1; simp only [Nat.cast_zero] at this; exact this
    have hKD : iK ≠ iD := ne_of_range rK' rD (p := Lam F ((K' : ℝ) + 1 + cb e f) (-1)) mem3_2
      (not_mem3 F FC (Or.inr (by norm_num)) (Or.inr (by norm_num)) (Or.inr (by norm_num)))
    have cB := card_two hKD gK gD
    have hns : ∀ z, (D.tile z).localAngle (Lam F ((K' : ℝ) + 1) 0) ≠ Real.pi ∧
        (D.tile z).localAngle (Lam F ((K' : ℝ) + 1) 0) ≠ 2 * Real.pi :=
      count_gg F hX hTU gT gU
    have cG2 : ({i | (D.tile i).localAngle (Lam F ((K' : ℝ) + 1) 0) = γ} : Finset (Fin N)).card
        ≤ 2 := by omega
    have cB2 : ({i | (D.tile i).localAngle (Lam F ((K' : ℝ) + 1) 0) = β} : Finset (Fin N)).card
        ≤ 2 := by omega
    refine ⟨⟨iK, hrK⟩, ⟨iD, hrD⟩, ?_, ?_⟩
    · -- across the `ℓ`-flank of `K + (K−1)P′`
      obtain ⟨mK, hmK, hflK⟩ := flank_of_range rK'
      rw [Lam_sub_eq F (by ring : ((K' : ℝ) + 1 + cb e f) - ((K' : ℝ) + 1) = cb e f)
          (by ring : (-1 : ℝ) - 0 = -1),
        Lam_sub_eq F (by ring : ((K' : ℝ) + 1 + 1 + cb e f) - ((K' : ℝ) + 1) = 1 + cb e f)
          (by ring : (-1 : ℝ) - 0 = -1)] at hflK
      have hflK' : IsFlankPair (D.tile iK) mK (Lam F ((K' : ℝ) + 1) 0) (vec F (1 + cb e f) (-1))
          (vec F (cb e f) (-1)) := by
        rcases hflK with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · right; exact ⟨h2, h1⟩
        · left; exact ⟨h2, h1⟩
      obtain ⟨z, hzK, -, hcz⟩ := flank_neighbour_dissection D.toDissection hX hmK hflK'
      rcases hcz with ⟨mz, hmz, U, W, hUW, S, hS, hU0, hside⟩ | ⟨m', hm0, hmpos, hcr, -⟩
      swap
      · exact (hedge_of_ns hns _ z m' hm0 hmpos hcr).elim
      have hang := localAngle_at_own_vertex_mem D α β γ F.hM.hα' F.hM.hβ' F.hM.hγ' z mz
      rw [hmz] at hang
      rcases hang with hz | hz | hz
      · rcases alpha_at_R F FC hmz hUW hS hU0 hside hz with h | h
        · left; exact ⟨z, h⟩
        · right; exact ⟨z, h⟩
      · exfalso
        rcases mem_of_card_two hKD gK gD cB2 hz with h | h
        · exact hzK h
        · exact ne_of_flank_lam F FC hmz hUW hS hU0 rD (d1 := -1) (e1 := 1) (d2 := 0) (e2 := 1)
            (by ring) (by ring) (by ring) (by ring) (fun S' hS' h1 h2 => by linarith)
            (fun S' hS' h1 h2 => by nlinarith) h
      · exfalso
        rcases mem_of_card_two hTU gT gU cG2 hz with h | h
        · exact ne_of_flank_lam F FC hmz hUW hS hU0 rT (d1 := -1) (e1 := 0) (d2 := cb e f)
            (e2 := -1) (by ring) (by ring) (by ring) (by ring) (fun S' hS' h1 h2 => by nlinarith)
            (fun S' hS' h1 h2 => by nlinarith) h
        · exact ne_of_flank_lam F FC hmz hUW hS hU0 rU (d1 := -1) (e1 := 0) (d2 := -1) (e2 := 1)
            (by ring) (by ring) (by ring) (by ring) (fun S' hS' h1 h2 => by nlinarith)
            (fun S' hS' h1 h2 => by nlinarith) h
    · -- across the `L_K`-flank of `Z₀ + (K−1)P′`
      have rD' : Set.range (D.tile iD).pts = {Lam F ((K' : ℝ) + 1) 0, Lam F ((K' : ℝ) + 1) 1,
          Lam F K' 1} := by
        rw [rD]; ext p; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
      obtain ⟨mD, hmD, hflD⟩ := flank_of_range rD'
      rw [Lam_sub_eq F (by ring : ((K' : ℝ) + 1) - ((K' : ℝ) + 1) = 0)
          (by ring : (1 : ℝ) - 0 = 1),
        Lam_sub_eq F (by ring : (K' : ℝ) - ((K' : ℝ) + 1) = -1) (by ring : (1 : ℝ) - 0 = 1)] at hflD
      obtain ⟨z, hzD, -, hcz⟩ := flank_neighbour_dissection D.toDissection hX hmD hflD
      rcases hcz with ⟨mz, hmz, U, W, hUW, S, hS, hU0, hside⟩ | ⟨m', hm0, hmpos, hcr, -⟩
      swap
      · exact (hedge_of_ns hns _ z m' hm0 hmpos hcr).elim
      have hang := localAngle_at_own_vertex_mem D α β γ F.hM.hα' F.hM.hβ' F.hM.hγ' z mz
      rw [hmz] at hang
      rcases hang with hz | hz | hz
      · rcases alpha_at_v F FC hmz hUW hS hU0 hside hz with h | h
        · left; refine ⟨z, ?_⟩; rw [h]; simp only [Up, Nat.cast_add, Nat.cast_one, Nat.cast_zero,
            zero_add]
        · right; exact ⟨z, h⟩
      · exfalso
        rcases mem_of_card_two hKD gK gD cB2 hz with h | h
        · exact ne_of_flank_lam F FC hmz hUW hS hU0 rK' (d1 := cb e f) (e1 := -1)
            (d2 := 1 + cb e f) (e2 := -1) (by ring) (by ring) (by ring) (by ring)
            (fun S' hS' h1 h2 => by nlinarith) (fun S' hS' h1 h2 => by nlinarith) h
        · exact hzD h
      · exfalso
        rcases mem_of_card_two hTU gT gU cG2 hz with h | h
        · exact ne_of_flank_lam F FC hmz hUW hS hU0 rT (d1 := -1) (e1 := 0) (d2 := cb e f)
            (e2 := -1) (by ring) (by ring) (by ring) (by ring) (fun S' hS' h1 h2 => by nlinarith)
            (fun S' hS' h1 h2 => by nlinarith) h
        · exact ne_of_flank_lam F FC hmz hUW hS hU0 rU (d1 := -1) (e1 := 0) (d2 := -1) (e2 := 1)
            (by ring) (by ring) (by ring) (by ring) (fun S' hS' h1 h2 => by nlinarith)
            (fun S' hS' h1 h2 => by nlinarith) h
  · -- `K + (K−1)P′` and `G_K`
    right; right; exact ⟨⟨iK, hrK⟩, ⟨G, hG, iG, hrG⟩⟩
  · -- `N_K` and `Z₀ + (K−1)P′`
    right; left; exact ⟨⟨M, hM, iM, hrM⟩, ⟨iD, hrD⟩⟩
  · -- two mirrors: four `γ`'s at `KP′`
    exfalso
    have gM : (D.tile iM).localAngle (Lam F ((K' : ℝ) + 1) 0) = γ := by
      have := (MirT2_angles F hM hrM).1; rw [hX0]; exact this
    have gG : (D.tile iG).localAngle (Lam F ((K' : ℝ) + 1) 0) = γ := by
      have := (MirUp_angles F hG hrG).1; simp only [Nat.cast_zero] at this; exact this
    have hTM : iT ≠ iM := ne_of_range rT hrM (p := Lam F K' 0) mem3_2 (by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      refine ⟨Lam_ne F FC (Or.inr (by push_cast; norm_num)),
        Lam_ne F FC (Or.inl (by push_cast; intro h; linarith)), fun h => hM.1 ?_⟩
      rw [← h]; congr 1 <;> push_cast <;> ring)
    have hUM : iU ≠ iM := ne_of_range rU hrM (p := Lam F K' 0) mem3_2 (by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      refine ⟨Lam_ne F FC (Or.inr (by push_cast; norm_num)),
        Lam_ne F FC (Or.inl (by push_cast; intro h; linarith)), fun h => hM.1 ?_⟩
      rw [← h]; congr 1 <;> push_cast <;> ring)
    obtain ⟨-, hγ3⟩ := count_ggg F hX hTU hTM hUM gT gU gM
    have hnotG : ∀ (j : Fin N) (S : Set Plane), Set.range (D.tile j).pts = S →
        Lam F K' 0 ∈ S → j ≠ iG := by
      intro j S hj hS h
      rw [h, hrG] at hj
      rw [← hj] at hS
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hS
      rcases hS with h1 | h1 | h1
      · have := Lam_inj F FC h1; push_cast at this; linarith [this.1]
      · have := Lam_inj F FC h1; push_cast at this; linarith [this.2]
      · exact hG.1 (by rw [← h1]; push_cast; rfl)
    rcases hγ3 iG gG with h | h | h
    · exact hnotG iT _ rT mem3_2 h.symm
    · exact hnotG iU _ rU mem3_2 h.symm
    · -- `X₁ ∈ N_K` would be `G_K`'s mirror point: distances `a` and `b` to `KP′`
      have h1 : Lam F (((K' + 1 : ℕ) : ℝ) + (((0 : ℕ) : ℝ) + 1) * cb e f) (-(((0 : ℕ) : ℝ) + 1))
          ∈ Set.range (D.tile iM).pts := by rw [hrM]; exact mem3_1
      rw [← h, hrG] at h1
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1
      rcases h1 with h1 | h1 | h1
      · have := Lam_inj F FC h1; push_cast at this; linarith [this.2]
      · have := Lam_inj F FC h1; push_cast at this; linarith [this.2]
      · have hb := hG.2.1
        rw [← h1, dist_Lam, dist_Lam] at hb
        push_cast at hb
        rw [show (K' : ℝ) + 1 + (0 + 1) * cb e f - ((K' : ℝ) + 1) = cb e f by ring,
          show -((0 : ℝ) + 1) - 0 = -1 by ring, norm_VP,
          show (K' : ℝ) - ((K' : ℝ) + 1) = -1 by ring, sub_self, norm_vec_m10] at hb
        obtain ⟨hab, -, -⟩ := sides_distinct F.hco F.he (by have := F.hef; omega)
        exact hab hb

/-- **R8 AT LEVEL `K = K' + 1` — ALL FOUR CLAUSES — FOR EVERY APEX FRAME OF A REAL `m = 1`
DISSECTION — PROVED.**  Given `Π(K) = K·T₂ ∪ K·T₃` and `Kc < fb`: (2)–(3) on `AD_K` and on row `K`
(`r8_real`: half-turn or mirror across each `a`-edge; a mirror forces `N_K`, resp. `G_K`, at `KP′`;
clause (1), the far words `a^K`, is inside `r8_ad`/`r8_row`), and (4) the six fills at `KP′`
(`r8_corner`). -/
theorem r8_real_full {k : Fin 3} (h : ApexFrameReal.M1Data D e f α β γ k)
    (FC : ApexPlacement.FrameCoords F) (K' : ℕ) (hKf : K' + 2 ≤ f)
    (hKc : ((K' + 1 : ℕ) : ℝ) * (f : ℝ) ^ 2 < (f : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2))
    (hT2 : ∀ i t, i + t + 1 ≤ K' + 1 → Present D (T2c F i t))
    (hK2 : ∀ i t, i + t + 2 ≤ K' + 1 → Present D (Kc F i t))
    (hUp : ∀ i t, i + t + 1 ≤ K' + 1 → Present D (Up F i t))
    (hDn : ∀ i t, i + t + 2 ≤ K' + 1 → Present D (Dn F i t)) :
    (((∀ s t, s + t + 1 = K' + 1 → Present D (Kc F s t) ∨ MirT2 F (K' + 1) s) ∧
      (∀ s t, s + t + 1 = K' + 1 → MirT2 F (K' + 1) s → MirT2 F (K' + 1) 0)) ∧
    ((∀ i t, i + t = K' → Present D (Dn F i t) ∨ MirUp F i t) ∧
      (∀ i t, i + t = K' → MirUp F i t → MirUp F K' 0))) ∧
    ((Present D (Kc F 0 K') ∧ Present D (Dn F K' 0) ∧
        (Present D {Lam F ((K' : ℝ) + 1) 0, Lam F ((K' : ℝ) + 1 + (1 + cb e f)) (-1),
            Lam F ((K' : ℝ) + 1 + 1) 0} ∨ Present D (Sb F ((K' : ℝ) + 1))) ∧
        (Present D (Up F (K' + 1) 0) ∨ Present D (Xs F ((K' : ℝ) + 1) 0))) ∨
      (MirT2 F (K' + 1) 0 ∧ Present D (Dn F K' 0)) ∨
      (Present D (Kc F 0 K') ∧ MirUp F K' 0)) :=
  ⟨r8_real F h FC K' hKf hKc hT2 hK2 hUp hDn,
    r8_corner F (lframe_real F h FC) K' hKf hKc hT2 hK2 hUp hDn⟩

end Erdos634.Draft.RowWallReal

#print axioms Erdos634.Draft.RowWallReal.alpha_at_v
#print axioms Erdos634.Draft.RowWallReal.alpha_at_R
#print axioms Erdos634.Draft.RowWallReal.r8_corner
#print axioms Erdos634.Draft.RowWallReal.r8_real_full
