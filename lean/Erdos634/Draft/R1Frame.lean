-- Draft/R1Frame.lean — the apex frame of a real congruent dissection of the m = 1 base-β target,
-- for EVERY coprime member 1 ≤ e < f (in particular the thick line e = f − 1, f ≥ 2, where R1 lives).
-- Imported into All.lean (header updated 2026-10-01).  Part of the R1 formalization (proof_R1_compressed.md, room W2).
--
-- WHY A PARALLEL FRAME.  `HalfTurnR3R4Glue.HFrame` carries the FIELD `hef : e + 2 ≤ f` (and
-- `he : 2 ≤ e`), so it cannot be built on R1's line e = f − 1 (nor at e = 1).  Its construction
-- `ApexPlacement.exists_hframe_coords` uses `e + 2 ≤ f` only to get `e < f`, `0 < e`, `1 < f` (checked
-- here by re-running it), and `ApexLegWord.legFlanksC_m1` uses `2 ≤ e` only through
-- `HalfTurnR3R4Glue.sides_distinct`.  This file is those two proofs, COPIED with the hypotheses
-- relaxed to `1 ≤ e < f` (`sides_distinct1` replaces `sides_distinct`), and `R1Frame` = `HFrame`'s
-- fields with `he : 1 ≤ e`, `hef : e < f`, plus the three `FrameCoords` facts the depth step needs.
-- REUSE LEDGER (cited, not re-derived): `ApexPlacement.apex_config`, `coeff_sum`, `cone_LR`,
-- `coord_LR`, `ApexLegWord.leg_no_b` (lem:sidenob + γ-trap on the real leg chain, every coprime
-- e < f), `flank_norms_bc`, `apex_three_tiles`.  Nothing here is new mathematics.
--
-- Build (scratch oleans; never .lake): ApexLegWord olean in $S, then lean_guard.sh.
import Erdos634.Draft.ApexLegWord

namespace Erdos634.Draft.R1Frame

open Erdos634.Geometry Erdos634.Placement Erdos634.TilePlacement Erdos634.WallEndpoints
  Erdos634.BridgeC Erdos634.BaseBetaWalkArith
open Erdos634.SideWall Erdos634.Draft.ApexPlacement Erdos634.Draft.CornerAdjacency
open Erdos634.Draft.ApexLegWord
open Erdos634.CertCoord Erdos634.Draft.NearBaseVertex

variable {N : ℕ}

/-- The base-β side values are pairwise distinct at every coprime member `1 ≤ e < f`
(`HalfTurnR3R4Glue.sides_distinct` needs `2 ≤ e`; at `e = 1`, `a = b` would be `f + 1 = f²`). -/
theorem sides_distinct1 {e f : ℕ} (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f) :
    ((e : ℝ) * f ≠ (f : ℝ) ^ 2 - (e : ℝ) ^ 2) ∧ ((e : ℝ) * f ≠ (f : ℝ) ^ 2) ∧
      ((f : ℝ) ^ 2 - (e : ℝ) ^ 2 ≠ (f : ℝ) ^ 2) := by
  have heR : (1 : ℝ) ≤ e := by exact_mod_cast he
  have hefR : (e : ℝ) < f := by exact_mod_cast hef
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · have hN : e * f + e ^ 2 = f ^ 2 := by
      have : ((e * f + e ^ 2 : ℕ) : ℝ) = ((f ^ 2 : ℕ) : ℝ) := by push_cast; linarith
      exact_mod_cast this
    have hdvd : e ∣ f ^ 2 := ⟨f + e, by rw [← hN]; ring⟩
    have he1 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right 2 hco) hdvd
    subst he1
    have hf2 : 2 ≤ f := by omega
    nlinarith
  · have hf : (0 : ℝ) < f := by linarith
    have : (e : ℝ) = f := by
      have h' : (e : ℝ) * f = f * f := by rw [h]; ring
      exact mul_right_cancel₀ hf.ne' h'
    linarith
  · have : (e : ℝ) ^ 2 = 0 := by linarith
    have : (e : ℝ) = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
    linarith

/-! ## Clause (2) at every coprime `1 ≤ e < f` (copy of `ApexLegWord`, `2 ≤ e` relaxed) -/

/-- **One leg: the apex flank along the side `k' → k'+1` (base corner → apex) is a `c`.** -/
theorem leg_flank_c_side1 (D : CongruentDissection N) {e f : ℕ} {α β γ : ℝ}
    (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f)
    (hM : HalfTurnR3R4Glue.ModelDataE D e f α β γ) (hAng : MarchSlots.AngleData α β γ)
    (k' : Fin 3)
    (hcornerbase : cornerAngle (D.target.pts (k' + 1)) (D.target.pts k')
      (D.target.pts (k' + 2)) = β)
    (hcornerapex : cornerAngle (D.target.pts (k' + 1 + 1)) (D.target.pts (k' + 1))
      (D.target.pts (k' + 1 + 2)) = 3 * α)
    (hLen : dist (D.target.pts k') (D.target.pts (k' + 1)) = (f : ℝ) ^ 3)
    {i : Fin N} {m : Fin 3} {U W : Plane} {S : ℝ}
    (hm : (D.tile i).pts m = D.target.pts (k' + 1))
    (hUW : IsFlankPair (D.tile i) m (D.target.pts (k' + 1)) U W)
    (hS : 0 < S) (hU : D.target.pts k' - D.target.pts (k' + 1) = S • U) :
    ‖U‖ = (f : ℝ) ^ 2 := by
  classical
  obtain ⟨hαβ, hαγ, hαπ, hα0, hβγ, hβπ, hβ0, hγπ, hγ0, -, -, -⟩ := angle_facts hAng
  have hN : 0 < N := Fin.pos i
  obtain ⟨hab, hac, hbc⟩ := sides_distinct1 hco he hef
  have h01 : sideOpp D.model 0 ≠ sideOpp D.model 1 := by rw [hM.hs0, hM.hs1]; exact hab
  have h02 : sideOpp D.model 0 ≠ sideOpp D.model 2 := by rw [hM.hs0, hM.hs2]; exact hac
  have h12 : sideOpp D.model 1 ≠ sideOpp D.model 2 := by rw [hM.hs1, hM.hs2]; exact hbc
  have hscalene : ∀ j j' : Fin 3, j ≠ j' → sideOpp D.model j ≠ sideOpp D.model j' := by
    intro j j' hjj'
    fin_cases j <;> fin_cases j' <;> first | exact absurd rfl hjj' | exact h01 | exact h02 | exact h12 | exact h01.symm | exact h02.symm | exact h12.symm
  have hee : e * e ≤ f * f := Nat.mul_le_mul hef.le hef.le
  have hthirdD : ∀ p ∈ Erdos634.BaseChain.wallList D.toDissection (wallFun D.target k') 0,
      wallFun D.target k' ((D.tile p.1).pts (p.2 + 2)) < 0 :=
    hthird_general D.toDissection (wallFun D.target k') 0 (wallFun_linear_ne_zero D.target k')
      (fun y hy => by simpa using wallFun_le D.target k' hy)
  have hnob := leg_no_b D α β γ hαβ hαγ hαπ hα0 hβγ hβπ hβ0 hγπ hγ0 Real.pi_ne_zero hAng.hγdef
    hAng.hrel hAng.hirr hscalene hM.hα' hM.hβ' hM.hγ' k' (dirFun D.target k').linear
    (hker_wallFun D.target k') (hdirab_dirFun D.target k') hthirdD hcornerbase hcornerapex
    (hiso_wallFun' D.target k') hN e f (f * f - e * e) hef hco (Nat.sub_add_cancel hee)
    hM.hs0 (by rw [hM.hs1]; push_cast [Nat.cast_sub hee]; ring) hM.hs2 hLen
  -- the flank edge lies on the side
  set A := D.target.pts (k' + 1) with hAdef
  have hS' : 0 < S⁻¹ := inv_pos.mpr hS
  have hUe : A + U = A + S⁻¹ • (D.target.pts k' - A) := by
    rw [hU, smul_smul, inv_mul_cancel₀ hS.ne', one_smul]
  have hgA : wallFun D.target k' A = 0 := by
    simp only [wallFun, AffineMap.coe_neg, Pi.neg_apply, neg_eq_zero]
    exact Erdos634.Draft.NearBaseVertex.coord_other D.target
      (show k' + 2 ≠ k' + 1 by fin_cases k' <;> decide)
  have hgU : wallFun D.target k' (A + U) = 0 := by
    rw [hUe]
    simp only [wallFun, AffineMap.coe_neg, Pi.neg_apply, neg_eq_zero]
    exact coord_line_zero D.target (show k' + 2 ≠ k' + 1 by fin_cases k' <;> decide)
      (show k' + 2 ≠ k' by fin_cases k' <;> decide) _
  obtain ⟨j, hj⟩ := flank_edge hm hUW
  have hq : ((i, j) : Fin N × Fin 3) ∈
      Erdos634.BaseChain.wallList D.toDissection (wallFun D.target k') 0 := by
    rw [Erdos634.BaseChain.mem_wallList]
    rcases hj with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨by simp only; rw [h1]; exact hgA, by simp only; rw [h2]; exact hgU⟩
    · exact ⟨by simp only; rw [h1]; exact hgU, by simp only; rw [h2]; exact hgA⟩
  have hlen : dist ((D.tile i).pts j) ((D.tile i).pts (j + 1)) = ‖U‖ := by
    rcases hj with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2, dist_comm, dist_eq_norm, add_sub_cancel_left]
    · rw [h1, h2, dist_eq_norm, add_sub_cancel_left]
  have hnb := hnob (i, j) hq
  simp only at hnb
  rw [hlen] at hnb
  -- the flank is `b` or `c`
  obtain ⟨-, -, -, -, -, -, -, hAt⟩ :=
    apex_three_tiles D hAng hM.hα' hM.hβ' hM.hγ' (k' + 1) hcornerapex
  have hAmem : A ∈ (D.tile i).carrier := by
    rw [← hm]; exact subset_convexHull ℝ _ (Set.mem_range_self m)
  have hi := (hAt i hAmem).1
  have he0 : (0 : ℝ) < e := by exact_mod_cast (show 0 < e by omega)
  have hf0 : (0 : ℝ) < f := by exact_mod_cast (show 0 < f by omega)
  have ha0 : (e : ℝ) * f ≠ 0 := mul_ne_zero he0.ne' hf0.ne'
  rcases flank_norms_bc D hM.hs0 hM.hs1 hM.hs2 ha0
      hAng hM.hα' hM.hβ' hM.hγ' (k' + 1) hcornerapex hm hUW hi with ⟨h1, -⟩ | ⟨h1, -⟩
  · exact absurd (h1.trans hM.hs1.symm) hnb
  · exact h1

/-- **Clause (2) at `m = 1`, every coprime member `1 ≤ e < f`** (copy of `ApexLegWord.legFlanksC_m1`, whose only use of `2 ≤ e` is `sides_distinct`; here `sides_distinct1`).
In a real congruent dissection of the `m = 1` base-β target (legs `f³`, apex `3α`, base corners
`β`), every apex flank lying along a leg is a `c`. -/
theorem legFlanksC_m1' (D : CongruentDissection N) {e f : ℕ} {α β γ : ℝ}
    (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f)
    (hM : HalfTurnR3R4Glue.ModelDataE D e f α β γ) (hAng : MarchSlots.AngleData α β γ)
    (k : Fin 3)
    (hcorner : cornerAngle (D.target.pts (k + 1)) (D.target.pts k) (D.target.pts (k + 2))
      = 3 * α)
    (hβ1 : cornerAngle (D.target.pts (k + 2)) (D.target.pts (k + 1)) (D.target.pts k) = β)
    (hβ2 : cornerAngle (D.target.pts k) (D.target.pts (k + 2)) (D.target.pts (k + 1)) = β)
    (hleg1 : dist (D.target.pts k) (D.target.pts (k + 1)) = (f : ℝ) ^ 3)
    (hleg2 : dist (D.target.pts k) (D.target.pts (k + 2)) = (f : ℝ) ^ 3) :
    LegFlanksC D k ((f : ℝ) ^ 2) := by
  classical
  intro i m U W l S hm hUW hl hS hU
  have e1 : k + 2 + 1 = k := by fin_cases k <;> rfl
  have e2 : k + 2 + 2 = k + 1 := by fin_cases k <;> rfl
  have e3 : k + 2 + 1 + 1 = k + 1 := by fin_cases k <;> rfl
  have e4 : k + 2 + 1 + 2 = k + 2 := by fin_cases k <;> rfl
  have e5 : k + 1 + 1 = k + 2 := by fin_cases k <;> rfl
  have e6 : k + 1 + 2 = k := by fin_cases k <;> rfl
  have hl' : l = k + 1 ∨ l = k + 2 := by
    fin_cases k <;> fin_cases l <;> simp_all
  rcases hl' with rfl | rfl
  · -- the leg `k → k+1`: relabel the target by the transposition `(k, k+1)`
    let σ : Equiv.Perm (Fin 3) := Equiv.swap k (k + 1)
    let D' : CongruentDissection N :=
      { toDissection := Erdos634.NormalPosition.relabelTarget D.toDissection σ
        model := D.model
        tiles_congruent := D.tiles_congruent }
    have hp0 : D'.target.pts k = D.target.pts (k + 1) := by
      show D.target.pts (σ k) = _; simp [σ]
    have hp1 : D'.target.pts (k + 1) = D.target.pts k := by
      show D.target.pts (σ (k + 1)) = _; simp [σ]
    have hp2 : D'.target.pts (k + 2) = D.target.pts (k + 2) := by
      show D.target.pts (σ (k + 2)) = _
      rw [Equiv.swap_apply_of_ne_of_ne (by fin_cases k <;> decide) (by fin_cases k <;> decide)]
    have hM' : HalfTurnR3R4Glue.ModelDataE D' e f α β γ :=
      ⟨hM.hs0, hM.hs1, hM.hs2, hM.hα', hM.hβ', hM.hγ'⟩
    have hb' : cornerAngle (D'.target.pts (k + 1)) (D'.target.pts k) (D'.target.pts (k + 2))
        = β := by
      rw [hp0, hp1, hp2, cornerAngle, EuclideanGeometry.angle_comm]; exact hβ1
    have ha' : cornerAngle (D'.target.pts (k + 1 + 1)) (D'.target.pts (k + 1))
        (D'.target.pts (k + 1 + 2)) = 3 * α := by
      rw [e5, e6, hp1, hp2, hp0, cornerAngle, EuclideanGeometry.angle_comm]; exact hcorner
    have hL' : dist (D'.target.pts k) (D'.target.pts (k + 1)) = (f : ℝ) ^ 3 := by
      rw [hp0, hp1, dist_comm]; exact hleg1
    have hm' : (D'.tile i).pts m = D'.target.pts (k + 1) := by rw [hp1]; exact hm
    have hUW' : IsFlankPair (D'.tile i) m (D'.target.pts (k + 1)) U W := by rw [hp1]; exact hUW
    have hU' : D'.target.pts k - D'.target.pts (k + 1) = S • U := by rw [hp0, hp1]; exact hU
    exact leg_flank_c_side1 D' hco he hef hM' hAng k hb' ha' hL' hm' hUW' hS hU'
  · -- the leg `k+2 → k`
    have hb' : cornerAngle (D.target.pts (k + 2 + 1)) (D.target.pts (k + 2))
        (D.target.pts (k + 2 + 2)) = β := by rw [e1, e2]; exact hβ2
    have ha' : cornerAngle (D.target.pts (k + 2 + 1 + 1)) (D.target.pts (k + 2 + 1))
        (D.target.pts (k + 2 + 1 + 2)) = 3 * α := by rw [e3, e1]; exact hcorner
    have hL' : dist (D.target.pts (k + 2)) (D.target.pts (k + 2 + 1)) = (f : ℝ) ^ 3 := by
      rw [e1, dist_comm]; exact hleg2
    have hm' : (D.tile i).pts m = D.target.pts (k + 2 + 1) := by rw [e1]; exact hm
    have hUW' : IsFlankPair (D.tile i) m (D.target.pts (k + 2 + 1)) U W := by rw [e1]; exact hUW
    have hU' : D.target.pts (k + 2) - D.target.pts (k + 2 + 1) = S • U := by rw [e1]; exact hU
    exact leg_flank_c_side1 D hco he hef hM hAng (k + 2) hb' ha' hL' hm' hUW' hS hU'



/-! ## The frame -/

/-- **The apex frame at a coprime member `1 ≤ e < f`, `m = 1`** — the fields of
`HalfTurnR3R4Glue.HFrame` (same names, same meaning) with `he : 1 ≤ e`, `hef : e < f` in place of
`2 ≤ e`, `e + 2 ≤ f`, plus the cone coordinates of `P′` and of `b·u_r` and the exterior of the
target beyond the base (`ApexPlacement.FrameCoords` clauses `hP`, `hV`, `hout`). -/
structure R1Frame (D : CongruentDissection N) (e f : ℕ) (α β γ : ℝ) where
  A : Plane
  V : Plane
  P : Plane
  R : Plane
  uL : Plane
  uR : Plane
  h : Plane →ₗ[ℝ] ℝ
  hco : Nat.Coprime e f
  he : 1 ≤ e
  hef : e < f
  hM : HalfTurnR3R4Glue.ModelDataE D e f α β γ
  hAng : MarchSlots.AngleData α β γ
  htarget : Set.range D.target.pts = {A, A + ((f : ℝ) ^ 3) • uL, R}
  hlegR : dist A R = (f : ℝ) ^ 3
  huL : ‖uL‖ = 1
  huR : ‖uR‖ = 1
  hV : V = A + ((f : ℝ) ^ 2) • uR
  hAP : dist A P = (f : ℝ) ^ 2 - (e : ℝ) ^ 2
  hVP : dist V P = (e : ℝ) * f
  hPJ1 : dist P (A + ((f : ℝ) ^ 2) • uL) = (e : ℝ) * f
  hh0 : h ≠ 0
  hhuR : h uR = 0
  hhP : h P < h A
  hhR : h A < h R
  hrbase : ∀ t : ℝ, 0 < t →
    A + ((f : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) + t) • uR ∉ D.target.carrier
  hrint : ∀ t : ℝ, 0 < t → t < (f : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) →
    A + t • uR ∈ interior D.target.carrier
  hPint : P ∈ interior D.target.carrier
  hT1 : HalfTurnR3R4Glue.Present D
    {A, A + ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) • uR, A + (1 / (f : ℝ)) • (R - A)}
  hT2 : HalfTurnR3R4Glue.Present D {A, V, P}
  hT3 : HalfTurnR3R4Glue.Present D {A, P, A + ((f : ℝ) ^ 2) • uL}
  hPc : ∃ s t : ℝ, 0 < s ∧ 0 < t ∧ P - A = s • (((f : ℝ) ^ 3) • uL) + t • (R - A) ∧
    s + t = 1 / (f : ℝ)
  hVc : ∃ s t : ℝ, 0 < s ∧ 0 < t ∧
    ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) • uR = s • (((f : ℝ) ^ 3) • uL) + t • (R - A) ∧
    s + t = 1 / (f : ℝ)
  hout : ∀ x y : ℝ, 1 < x + y →
    A + (x • (((f : ℝ) ^ 3) • uL) + y • (R - A)) ∉ D.target.carrier

set_option maxHeartbeats 1000000 in
/-- **THE FRAME FROM A REAL `m = 1` DISSECTION, every coprime `1 ≤ e < f` — PROVED.**  Copy of
`ApexPlacement.exists_hframe_coords` (whose `e + 2 ≤ f` is used only for `0 < e < f`, `1 < f`),
with clause (2) as a hypothesis (`LegFlanksC`, discharged by `legFlanksC_m1'`). -/
theorem exists_r1frame (D : CongruentDissection N) {e f : ℕ} {α β γ : ℝ}
    (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f)
    (hM : HalfTurnR3R4Glue.ModelDataE D e f α β γ) (hAng : MarchSlots.AngleData α β γ)
    (k : Fin 3)
    (hcorner : cornerAngle (D.target.pts (k + 1)) (D.target.pts k) (D.target.pts (k + 2))
      = 3 * α)
    (hleg1 : dist (D.target.pts k) (D.target.pts (k + 1)) = (f : ℝ) ^ 3)
    (hleg2 : dist (D.target.pts k) (D.target.pts (k + 2)) = (f : ℝ) ^ 3)
    (hbase : dist (D.target.pts (k + 1)) (D.target.pts (k + 2))
      = (e : ℝ) * (3 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2))
    (hlegc : LegFlanksC D k ((f : ℝ) ^ 2)) :
    Nonempty (R1Frame D e f α β γ) := by
  classical
  have heR : (1 : ℝ) ≤ e := by exact_mod_cast he
  have hlt : (e : ℝ) < f := by exact_mod_cast hef
  have he0 : (0 : ℝ) < e := by linarith
  have hf0 : (0 : ℝ) < f := by linarith
  have hf1 : (1 : ℝ) < f := by linarith
  set a : ℝ := (e : ℝ) * f with ha
  set b : ℝ := (f : ℝ) ^ 2 - (e : ℝ) ^ 2 with hb
  set c : ℝ := (f : ℝ) ^ 2 with hc
  have ha0 : a ≠ 0 := by rw [ha]; exact mul_ne_zero he0.ne' hf0.ne'
  have hb0 : 0 < b := by rw [hb]; nlinarith
  have hc0 : 0 < c := by positivity
  have hbc : b ≠ c := by rw [hb, hc]; intro h; nlinarith
  obtain ⟨L, R, G1, G3, hLR, cfg⟩ := apex_config D hM.hs0 hM.hs1 hM.hs2 ha0 hb0 hc0 hbc hAng
    hM.hα' hM.hβ' hM.hγ' k hcorner hlegc
  set A := D.target.pts k with hAdef
  have hC : ApexCone D.target A L R := cone_LR hLR
  have hLA : dist A L = (f : ℝ) ^ 3 := by
    rcases hLR with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hleg1
    · exact hleg2
  have hRA : dist A R = (f : ℝ) ^ 3 := by
    rcases hLR with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hleg2
    · exact hleg1
  have hLRd : dist L R = (e : ℝ) * (3 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) := by
    rcases hLR with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hbase
    · rw [dist_comm]; exact hbase
  have hLn : ‖L - A‖ = (f : ℝ) ^ 3 := by rw [← dist_eq_norm, dist_comm]; exact hLA
  have hRn : ‖R - A‖ = (f : ℝ) ^ 3 := by rw [← dist_eq_norm, dist_comm]; exact hRA
  have hcf : c / (f : ℝ) ^ 3 = 1 / (f : ℝ) := by rw [hc]; field_simp
  have hdistA : ∀ G : Plane, dist A (A + G) = ‖G‖ := fun G => by
    rw [dist_comm, dist_eq_norm, add_sub_cancel_left]
  -- the two rays leave the target at `1/f` of the cone
  obtain ⟨s1, t1, hs1, ht1, hG1⟩ := cfg.hG1cone
  obtain ⟨s3, t3, hs3, ht3, hG3⟩ := cfg.hG3cone
  have hc1 : s1 * (3 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) = f ∧ s1 + t1 = 1 / (f : ℝ) := by
    apply coeff_sum he0 hlt hs1 hLA hRA hLRd
    · rw [← hG1, hdistA, cfg.hG1]
    · rw [← hG1, ← hcf, ← hRn]; exact cfg.hT1a
  have hc3 : t3 * (3 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) = f ∧ t3 + s3 = 1 / (f : ℝ) := by
    apply coeff_sum he0 hlt ht3 hRA hLA (by rw [dist_comm]; exact hLRd)
    · rw [add_comm (t3 • _), ← hG3, hdistA, cfg.hG3]
    · rw [add_comm (t3 • _), ← hG3, ← hcf, ← hLn, dist_comm]; exact cfg.hT3a
  have hsum1 := hc1.2
  have hsum3 := hc3.2
  have hvL : ((f : ℝ) ^ 3) • ((1 / (f : ℝ) ^ 3) • (L - A)) = L - A := by
    rw [smul_smul, mul_one_div_cancel (by positivity), one_smul]
  -- the normal functional of `r`
  have hside := cfg.hside
  have hcr : cross G1 (R - A) ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hside; exact lt_irrefl _ hside
  set h : Plane →ₗ[ℝ] ℝ := (cross G1 (R - A)) • Erdos634.Geometry.crossL G1 with hhdef
  have happ : ∀ v, h v = cross G1 (R - A) * cross G1 v := fun v => by
    rw [hhdef, LinearMap.smul_apply, Erdos634.Geometry.crossL_apply, smul_eq_mul]
  have hG3neg : h G3 < 0 := by rw [happ, mul_comm]; exact hside
  have hRpos : 0 < h (R - A) := by
    rw [happ]; exact mul_self_pos.mpr hcr
  refine ⟨{
    A := A
    V := A + ((f : ℝ) ^ 2) • ((1 / b) • G1)
    P := A + G3
    R := R
    uL := (1 / (f : ℝ) ^ 3) • (L - A)
    uR := (1 / b) • G1
    h := h
    hco := hco
    he := he
    hef := hef
    hM := hM
    hAng := hAng
    htarget := ?_
    hlegR := hRA
    huL := ?_
    huR := ?_
    hV := rfl
    hAP := ?_
    hVP := ?_
    hPJ1 := ?_
    hh0 := ?_
    hhuR := ?_
    hhP := ?_
    hhR := ?_
    hrbase := ?_
    hrint := ?_
    hPint := ?_
    hT1 := ?_
    hT2 := ?_
    hT3 := ?_
    hPc := ?_
    hVc := ?_
    hout := ?_ }⟩
  · -- htarget
    have hL' : A + ((f : ℝ) ^ 3) • ((1 / (f : ℝ) ^ 3) • (L - A)) = L := by
      rw [smul_smul, mul_one_div_cancel (by positivity), one_smul]; abel
    rw [hL', range_pts_eq D.target k]
    rcases hLR with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Set.insert_comm _ _ _
    · ext y; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  · rw [norm_smul, hLn, Real.norm_of_nonneg (by positivity), one_div_mul_cancel (by positivity)]
  · rw [norm_smul, cfg.hG1, Real.norm_of_nonneg (by positivity), one_div_mul_cancel hb0.ne']
  · rw [hdistA, cfg.hG3]
  · rw [smul_smul, show (f : ℝ) ^ 2 * (1 / b) = c / b by rw [hc]; ring, dist_comm]
    exact cfg.hT2a
  · rw [smul_smul, show (f : ℝ) ^ 2 * (1 / (f : ℝ) ^ 3) = c / ‖L - A‖ by rw [hLn, hc]; ring,
      dist_comm]
    exact cfg.hT3a
  · intro h0
    have := congrArg (fun φ : Plane →ₗ[ℝ] ℝ => φ G3) h0
    simp only [LinearMap.zero_apply] at this
    rw [this] at hG3neg; exact lt_irrefl _ hG3neg
  · rw [happ, cross_smul_right, cross_self', mul_zero, mul_zero]
  · rw [map_add]; linarith
  · have : h R = h A + h (R - A) := by rw [← map_add]; congr 1; abel
    rw [this]; linarith
  · -- `r` leaves the target at `f·b`
    intro τ hτ hmem
    have hpt : A + ((f : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) + τ) • ((1 / b) • G1)
        = A + ((((f : ℝ) * b + τ) / b * s1) • (L - A) + (((f : ℝ) * b + τ) / b * t1) • (R - A)) := by
      rw [hG1, smul_smul, smul_add, smul_smul, smul_smul, ← hb]; congr 2 <;> ring_nf
    rw [hpt] at hmem
    have hco' := ((mem_carrier_iff _ _).mp hmem) k
    rw [coord_LR hLR] at hco'
    have hbne := hb0.ne'
    have hfne := hf0.ne'
    have hx : ((f : ℝ) * b + τ) / b * s1 + ((f : ℝ) * b + τ) / b * t1 = 1 + τ / (b * f) := by
      rw [← mul_add, hsum1]; field_simp
    have : 0 < τ / (b * f) := div_pos hτ (mul_pos hb0 hf0)
    linarith
  · -- and runs inside before that
    intro τ hτ hτ2
    have hpt : A + τ • ((1 / b) • G1) = A + (τ / b) • (s1 • (L - A) + t1 • (R - A)) := by
      rw [hG1, smul_smul]; ring_nf
    rw [hpt]
    apply hC.inter s1 t1 (τ / b) hs1 ht1 (div_pos hτ hb0)
    rw [hsum1, div_mul_div_comm, mul_one, div_lt_one (mul_pos hb0 hf0)]
    rw [← hb] at hτ2
    have : (f : ℝ) * b = b * f := mul_comm _ _
    linarith
  · -- `P′` is interior
    rw [hG3, add_comm (s3 • _)]
    have hC' : ApexCone D.target A R L := hC.swap
    have := hC'.inter t3 s3 1 ht3 hs3 one_pos (by
      rw [one_mul, hsum3, div_lt_one hf0]; linarith)
    rwa [one_smul] at this
  · -- `T₁`
    obtain ⟨i, hi⟩ := cfg.hT1
    refine ⟨i, ?_⟩
    rw [hi, smul_smul, ← hb, mul_one_div_cancel hb0.ne', one_smul, hRn, hcf]
  · -- `T₂`
    obtain ⟨i, hi⟩ := cfg.hT2
    refine ⟨i, ?_⟩
    rw [hi, smul_smul, show (f : ℝ) ^ 2 * (1 / b) = c / b by rw [hc]; ring]
    exact congrArg (insert A) (Set.pair_comm _ _)
  · -- `T₃`
    obtain ⟨i, hi⟩ := cfg.hT3
    refine ⟨i, ?_⟩
    rw [hi, smul_smul, show (f : ℝ) ^ 2 * (1 / (f : ℝ) ^ 3) = c / ‖L - A‖ by rw [hLn, hc]; ring]
    exact congrArg (insert A) (Set.pair_comm _ _)
  · -- `P′` in cone coordinates
    refine ⟨s3, t3, hs3, ht3, ?_, by linarith⟩
    show A + G3 - A = s3 • (((f : ℝ) ^ 3) • ((1 / (f : ℝ) ^ 3) • (L - A))) + t3 • (R - A)
    rw [hvL, add_sub_cancel_left]; exact hG3
  · -- `b·u_r` in cone coordinates
    refine ⟨s1, t1, hs1, ht1, ?_, hsum1⟩
    show ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) • ((1 / b) • G1)
        = s1 • (((f : ℝ) ^ 3) • ((1 / (f : ℝ) ^ 3) • (L - A))) + t1 • (R - A)
    rw [hvL, smul_smul, ← hb, mul_one_div_cancel hb0.ne', one_smul]; exact hG1
  · -- beyond the base
    intro x y hxy hmem
    change A + (x • (((f : ℝ) ^ 3) • ((1 / (f : ℝ) ^ 3) • (L - A))) + y • (R - A))
      ∈ D.target.carrier at hmem
    rw [hvL] at hmem
    have hco' := ((mem_carrier_iff _ _).mp hmem) k
    rw [coord_LR hLR] at hco'
    linarith

/-- **The frame, clause (2) discharged, every coprime `1 ≤ e < f`.** -/
theorem exists_r1frame_m1 (D : CongruentDissection N) {e f : ℕ} {α β γ : ℝ}
    (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f)
    (hM : HalfTurnR3R4Glue.ModelDataE D e f α β γ) (hAng : MarchSlots.AngleData α β γ)
    (k : Fin 3)
    (hcorner : cornerAngle (D.target.pts (k + 1)) (D.target.pts k) (D.target.pts (k + 2))
      = 3 * α)
    (hβ1 : cornerAngle (D.target.pts (k + 2)) (D.target.pts (k + 1)) (D.target.pts k) = β)
    (hβ2 : cornerAngle (D.target.pts k) (D.target.pts (k + 2)) (D.target.pts (k + 1)) = β)
    (hleg1 : dist (D.target.pts k) (D.target.pts (k + 1)) = (f : ℝ) ^ 3)
    (hleg2 : dist (D.target.pts k) (D.target.pts (k + 2)) = (f : ℝ) ^ 3)
    (hbase : dist (D.target.pts (k + 1)) (D.target.pts (k + 2))
      = (e : ℝ) * (3 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2)) :
    Nonempty (R1Frame D e f α β γ) :=
  exists_r1frame D hco he hef hM hAng k hcorner hleg1 hleg2 hbase
    (legFlanksC_m1' D hco he hef hM hAng k hcorner hβ1 hβ2 hleg1 hleg2)

end Erdos634.Draft.R1Frame

#print axioms Erdos634.Draft.R1Frame.sides_distinct1
#print axioms Erdos634.Draft.R1Frame.leg_flank_c_side1
#print axioms Erdos634.Draft.R1Frame.legFlanksC_m1'
#print axioms Erdos634.Draft.R1Frame.exists_r1frame
#print axioms Erdos634.Draft.R1Frame.exists_r1frame_m1
