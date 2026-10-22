-- Draft/Level2LemmaGReal.lean — R4 (d) ((private working notes, not included) Step 6): Lemma G at level 2 in
-- branch (H) after an `L_c` step, `HalfTurnR3R4Glue.level2_lemmaG`, for real dissections via the
-- apex frame.  Imported directly by All.lean (stale "NOT imported" header corrected 2026-10-04).
--
-- Build (scratch oleans; never .lake): HalfTurnR4Real olean in $S, then
--   lake env bash -c 'LEAN_PATH=$S:$LEAN_PATH lean Erdos634/Draft/Level2LemmaGReal.lean'
import Erdos634.Draft.HalfTurnR4Real

namespace Erdos634.Draft.Level2LemmaGReal

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.Draft.HalfTurnR3R4
open Erdos634.Draft.HalfTurnR3R4Glue Erdos634.Draft.CornerAdjacency
open Erdos634.Draft.HalfTurnR3R4Order Erdos634.Draft.MirrorStripR2Real
open Erdos634.Draft.HalfTurnR4Real

variable {N : ℕ} {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ}

/-- `P′ − A` is not along the leg `uL` (`P′` has a positive cone coordinate across the leg). -/
theorem cross_w_uL (F : HFrame D e f α β γ) (FC : ApexPlacement.FrameCoords F) :
    cross (F.P - F.A) F.uL ≠ 0 := by
  obtain ⟨s3, t3, -, ht3, hP, -, -⟩ := FC.hP
  have hdet := FC.hcone.det
  rw [show F.A + ((f : ℝ) ^ 3) • F.uL - F.A = ((f : ℝ) ^ 3) • F.uL by abel,
    cross_smul_left'] at hdet
  have hd : cross F.uL (F.R - F.A) ≠ 0 := fun h => hdet (by rw [h, mul_zero])
  rw [hP, cross_add_left', cross_smul_left', cross_smul_left', cross_smul_left', cross_self',
    mul_zero, mul_zero, zero_add, cross_anti]
  exact mul_ne_zero ht3.ne' (neg_ne_zero.mpr hd)

/-- **`Z₀` is a tile**: in (H), the tile across `T₃`'s `a`-edge `P′J₁` presents `β` at `P′`, with
flanks `J₁ − P′` and `c·uL` (it is `(P′, J₁, P′ + J₁ − A)`). -/
theorem Z0_tile (F : HFrame D e f α β γ) (FC : ApexPlacement.FrameCoords F)
    (hK : Present D F.K) :
    ∃ (z : Fin N) (mz : Fin 3), (D.tile z).pts mz = F.P ∧
      IsFlankPair (D.tile z) mz F.P (F.A + ((f : ℝ) ^ 2) • F.uL - F.P) (((f : ℝ) ^ 2) • F.uL) ∧
      (D.tile z).localAngle F.P = β := by
  classical
  obtain ⟨habd, hacd, hbcd⟩ := sides_distinct F.hco F.he (by have := F.hef; omega)
  have heR : (2 : ℝ) ≤ e := by exact_mod_cast F.he
  have hefR : (e : ℝ) + 2 ≤ f := by exact_mod_cast F.hef
  have hc0 : (0 : ℝ) < (f : ℝ) ^ 2 := by nlinarith
  have hJP : ‖F.A + ((f : ℝ) ^ 2) • F.uL - F.P‖ = (e : ℝ) * f := by
    rw [← dist_eq_norm, dist_comm]; exact F.hPJ1
  have hPJ : dist F.P (F.A + ((f : ℝ) ^ 2) • F.uL) = (e : ℝ) * f := F.hPJ1
  obtain ⟨-, z, -, -, mz, W'', hmz, hUWz, hsidez⟩ := pprime_across_J1_all F hK
  obtain ⟨-, -, hC2, -⟩ := r4_figure_at_pprime' F FC hK
  obtain ⟨i2, i3, h23, hr2, hr3, g2, g3⟩ := ApexFrameReal.two_gamma_at_pprime F
  have hflZ := flank_lengths F hmz hUWz
  rw [hJP] at hflZ
  have hZang := localAngle_at_own_vertex_mem D α β γ F.hM.hα' F.hM.hβ' F.hM.hγ' z mz
  rw [hmz] at hZang
  have hzβ : (D.tile z).localAngle F.P = β := by
    rcases hZang with h | h | h
    · rcases hflZ.2.2 h with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact absurd h1 habd
      · exact absurd h1 hacd
    · exact h
    · exfalso
      have hsub : ({i2, i3} : Finset (Fin N)) ⊆
          ({i | (D.tile i).localAngle F.P = γ} : Finset (Fin N)) := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact mem_filter_of g2
        · exact mem_filter_of g3
      have heq := Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_pair h23, hC2])
      have hzm : z ∈ ({i2, i3} : Finset (Fin N)) := by rw [heq]; exact mem_filter_of h
      simp only [Finset.mem_insert, Finset.mem_singleton] at hzm
      -- `z`'s vertex `P′ + W''` lies strictly across `P′J₁` from `A`
      have hW : F.P + W'' ∈ Set.range (D.tile z).pts := by
        rcases hUWz with ⟨-, h2⟩ | ⟨-, h2⟩
        · exact ⟨mz + 2, by rw [h2]; abel⟩
        · exact ⟨mz + 1, by rw [h2]; abel⟩
      rcases hzm with rfl | rfl
      · rw [hr2] at hW
        have hJz : F.A + ((f : ℝ) ^ 2) • F.uL ∈ Set.range (D.tile z).pts := by
          rcases hUWz with ⟨h1, -⟩ | ⟨h1, -⟩
          · exact ⟨mz + 1, sub_left_inj.mp h1.symm⟩
          · exact ⟨mz + 2, sub_left_inj.mp h1.symm⟩
        rw [hr2] at hJz
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hJz
        have hAJ : dist F.A (F.A + ((f : ℝ) ^ 2) • F.uL) = (f : ℝ) ^ 2 :=
          dist_self_add_unit F.huL hc0.le
        rcases hJz with h' | h' | h'
        · rw [h', dist_self] at hAJ; linarith
        · exact V_ne_J1 F h'.symm
        · rw [h', dist_self] at hPJ; nlinarith
      · rw [hr3] at hW
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hW
        rcases hW with h' | h' | h'
        · have : W'' = F.A - F.P := by rw [← h']; abel
          rw [this] at hsidez; nlinarith [sq_nonneg (cross (F.A + ((f : ℝ) ^ 2) • F.uL - F.P)
            (F.A - F.P))]
        · have : W'' = 0 := by have := h'; rw [add_eq_left] at this; exact this
          rw [this] at hsidez; simp at hsidez
        · have : W'' = F.A + ((f : ℝ) ^ 2) • F.uL - F.P := by rw [← h']; abel
          rw [this, cross_self'] at hsidez; simp at hsidez
  -- `Z = Z₀`: its third vertex is `P′ + J₁ − A`
  have hW''c : ‖W''‖ = (f : ℝ) ^ 2 := by
    rcases hflZ.2.1 hzβ with ⟨-, h2'⟩ | ⟨h1', -⟩
    · exact h2'
    · exact absurd h1' hacd
  have hrz : Set.range (D.tile z).pts = {F.P, F.A + ((f : ℝ) ^ 2) • F.uL, F.P + W''} := by
    rw [ApexPlacement.range_of_flank hmz hUWz]; congr 2; abel
  have hopp : dist (F.A + ((f : ℝ) ^ 2) • F.uL) (F.P + W'') = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 :=
    third_side D habd hacd hbcd F.hM.hs0 F.hM.hs1 F.hM.hs2 hrz (by rw [dist_comm]; exact hPJ)
      (by rw [dist_eq_norm, add_sub_cancel_left, hW''c])
  have hJPne : F.A + ((f : ℝ) ^ 2) • F.uL ≠ F.P := by
    intro h; rw [h, dist_self] at hPJ; nlinarith
  have hZ0 : F.P + W'' = F.P + ((F.A + ((f : ℝ) ^ 2) • F.uL) - F.A) := by
    apply third_vertex_cross (X := F.P) (Y := F.A + ((f : ℝ) ^ 2) • F.uL)
    · exact hJPne.symm
    · rw [add_sub_cancel_left, add_sub_cancel_left,
        show (F.A + ((f : ℝ) ^ 2) • F.uL) - F.A
          = (F.A + ((f : ℝ) ^ 2) • F.uL - F.P) - (F.A - F.P) by abel,
        cross_sub_right', cross_self', zero_sub, mul_neg]
      linarith
    · have e1 : dist F.P (F.P + W'') = (f : ℝ) ^ 2 := by
        rw [dist_comm, dist_eq_norm, add_sub_cancel_left, hW''c]
      have e2 : dist F.P (F.P + ((F.A + ((f : ℝ) ^ 2) • F.uL) - F.A)) = (f : ℝ) ^ 2 := by
        rw [dist_comm, dist_eq_norm, add_sub_cancel_left, add_sub_cancel_left, norm_smul,
          F.huL, mul_one, Real.norm_of_nonneg hc0.le]
      rw [e1, e2]
    · rw [hopp, dist_comm, dist_eq_norm,
        show F.P + ((F.A + ((f : ℝ) ^ 2) • F.uL) - F.A) - (F.A + ((f : ℝ) ^ 2) • F.uL)
          = F.P - F.A by abel, ← dist_eq_norm, dist_comm, F.hAP]
  have hW0 : W'' = ((f : ℝ) ^ 2) • F.uL := by
    have := add_left_cancel hZ0; rw [this]; abel
  rw [hW0] at hUWz
  exact ⟨z, mz, hmz, hUWz, hzβ⟩


/-- A point in the relative interior of two edges of one triangle: the edges coincide. -/
theorem same_edge (T : Tri) {x : Plane} {a1 a2 : Fin 3}
    (h1 : x ∈ openSegment ℝ (T.pts a1) (T.pts (a1 + 1)))
    (h2 : x ∈ openSegment ℝ (T.pts a2) (T.pts (a2 + 1))) : a1 = a2 := by
  obtain ⟨c1, p1, q1⟩ := openSeg_coords T a1 h1
  obtain ⟨c2, p2, q2⟩ := openSeg_coords T a2 h2
  by_contra hne
  rcases fin3_cases3 a1 (a2 + 2) with h | h | h
  · rw [h] at c2; linarith
  · rw [h] at c2; linarith
  · exact hne (add_right_cancel h).symm

/-- A tile with a point in an open edge presents `π` or `2π` there. -/
theorem straight_of_openSeg (T : Tri) {x : Plane} {a : Fin 3}
    (hx : x ∈ openSegment ℝ (T.pts a) (T.pts (a + 1))) :
    x ∈ T.carrier ∧ (T.localAngle x = 2 * Real.pi ∨ T.localAngle x = Real.pi) := by
  obtain ⟨hc2, hc0, hc1⟩ := openSeg_coords T a hx
  have hxb : x ∈ T.carrier := by
    rw [NearBaseVertex.mem_carrier_iff]; intro l
    rcases fin3_cases3 a l with rfl | rfl | rfl
    · exact hc0.le
    · exact hc1.le
    · exact hc2.ge
  refine ⟨hxb, localAngle_mem_pi_of_mem T hxb (fun q hq => ?_)⟩
  refine NearBaseVertex.vertex_not_edge T q hq (a + 2) (fun l hl => ?_)
  rcases fin3_cases3 a l with rfl | rfl | rfl
  · exact hc0
  · exact hc1
  · exact absurd rfl hl

/-- **The second `α`-tile at `P′`**: the tile across `T₂ + P′`'s `b`-flank `P′ → 2P′ − A` is an
`α`-tile with a flank positively along `P′ − A` (it is none of `T₂, T₃, K, Z₀, T₂ + P′`). -/
theorem alpha2_tile (F : HFrame D e f α β γ) (FC : ApexPlacement.FrameCoords F)
    (hK : Present D F.K) :
    ∃ (j z : Fin N) (mz : Fin 3) (U W : Plane) (S : ℝ), Set.range (D.tile j).pts = F.T2P ∧
      z ≠ j ∧ (D.tile z).pts mz = F.P ∧ IsFlankPair (D.tile z) mz F.P U W ∧ 0 < S ∧
      F.P - F.A = S • U ∧ (D.tile z).localAngle F.P = α := by
  classical
  obtain ⟨habd, hacd, hbcd⟩ := sides_distinct F.hco F.he (by have := F.hef; omega)
  have heR : (2 : ℝ) ≤ e := by exact_mod_cast F.he
  have hefR : (e : ℝ) + 2 ≤ f := by exact_mod_cast F.hef
  have hc0 : (0 : ℝ) < (f : ℝ) ^ 2 := by nlinarith
  have hb0 : (0 : ℝ) < (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by nlinarith
  have hloc := fun {i : Fin N} {P Q R : Plane} (hr : Set.range (D.tile i).pts = {P, Q, R}) =>
    localAngle_of_rangeE D habd hacd hbcd F.hM.hs0 F.hM.hs1 F.hM.hs2 F.hM.hα' F.hM.hβ' F.hM.hγ' hr
  obtain ⟨j, hj, -⟩ := t2pprime_forced' F FC hK
  have hj' : Set.range (D.tile j).pts = {F.P, F.V + F.P - F.A, F.P + F.P - F.A} := hj
  obtain ⟨mj, hmj⟩ := MarchInduction.mem_range_of_eq hj' (Set.mem_insert _ _)
  have hflj : IsFlankPair (D.tile j) mj F.P (F.P + F.P - F.A - F.P) (F.V + F.P - F.A - F.P) := by
    rcases MarchInduction.vertex_data_of_range hj' hmj with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · right; exact ⟨by rw [h2], by rw [h1]⟩
    · left; exact ⟨by rw [h1], by rw [h2]⟩
  obtain ⟨z, hzj, hPz, hcase⟩ := flank_neighbour_dissection D.toDissection F.hPint hmj hflj
  rcases hcase with ⟨mz, hmz, U, W, hUW, S, hS, hU, hside⟩ | ⟨m', -, hmpos, -, -⟩
  swap
  · exfalso
    obtain ⟨m'', hm''⟩ := pprime_vertex_of_mem F hK z hPz
    exact NearBaseVertex.vertex_not_edge (D.tile z) m'' hm'' m' hmpos
  have hw : F.P + F.P - F.A - F.P = F.P - F.A := by abel
  rw [hw] at hU
  refine ⟨j, z, mz, U, W, S, hj, hzj, hmz, hUW, hS, hU, ?_⟩
  -- `P′ − A` is along none of the flanks of `T₂, T₃, K, Z₀`
  have hbad : ∀ v, cross (F.P - F.A) v ≠ 0 → U ≠ v := by
    intro v hv hUv
    rw [hUv] at hU
    have := congrArg (cross (F.P - F.A)) hU
    rw [cross_smul_right, cross_self'] at this
    rcases mul_eq_zero.mp this.symm with h | h
    · linarith
    · exact hv h
  have hwn : ‖F.P - F.A‖ = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := F.hw_norm
  have hbadA : U ≠ F.A - F.P := by
    intro hUv
    rw [hUv, show F.A - F.P = (-1 : ℝ) • (F.P - F.A) by module, smul_smul] at hU
    have h1 : (1 + S) • (F.P - F.A) = 0 := by
      rw [add_smul, one_smul]; nth_rewrite 1 [hU]; rw [← add_smul]; simp
    rcases smul_eq_zero.mp h1 with h | h
    · linarith
    · rw [h, norm_zero] at hwn; linarith
  have hcuR : cross (F.P - F.A) F.uR ≠ 0 := F.cross_w_uR
  have hcuL : cross (F.P - F.A) F.uL ≠ 0 := cross_w_uL F FC
  have hVP : cross (F.P - F.A) (F.V - F.P) ≠ 0 := by
    rw [show F.V - F.P = ((f : ℝ) ^ 2) • F.uR - (F.P - F.A) by rw [F.hV]; abel,
      cross_sub_right', cross_smul_right, cross_self', sub_zero]
    exact mul_ne_zero hc0.ne' hcuR
  have hJP : cross (F.P - F.A) (F.A + ((f : ℝ) ^ 2) • F.uL - F.P) ≠ 0 := by
    rw [show F.A + ((f : ℝ) ^ 2) • F.uL - F.P = ((f : ℝ) ^ 2) • F.uL - (F.P - F.A) by abel,
      cross_sub_right', cross_smul_right, cross_self', sub_zero]
    exact mul_ne_zero hc0.ne' hcuL
  have hQP : cross (F.P - F.A) (F.V + F.P - F.A - F.P) ≠ 0 := by
    rw [show F.V + F.P - F.A - F.P = ((f : ℝ) ^ 2) • F.uR by rw [F.hV]; abel, cross_smul_right]
    exact mul_ne_zero hc0.ne' hcuR
  have hcL : cross (F.P - F.A) (((f : ℝ) ^ 2) • F.uL) ≠ 0 := by
    rw [cross_smul_right]; exact mul_ne_zero hc0.ne' hcuL
  -- a tile with a known flank pair at `P′` is not `z`
  have hnot : ∀ (t : Fin N) (mt : Fin 3) (U1 W1 : Plane), (D.tile t).pts mt = F.P →
      IsFlankPair (D.tile t) mt F.P U1 W1 → U ≠ U1 → U ≠ W1 → z ≠ t := by
    intro t mt U1 W1 hmt hfl h1 h2 hzt
    subst hzt
    have hmm : mt = mz := (D.tile z).indep.injective (hmt.trans hmz.symm)
    subst hmm
    rcases ApexPlacement.flank_cases hfl hUW with ⟨h, -⟩ | ⟨h, -⟩
    · exact h1 h
    · exact h2 h
  have flank_of : ∀ (t : Fin N) {Q R : Plane}, Set.range (D.tile t).pts = {F.P, Q, R} →
      ∃ mt, (D.tile t).pts mt = F.P ∧ IsFlankPair (D.tile t) mt F.P (Q - F.P) (R - F.P) := by
    intro t Q R hr
    obtain ⟨mt, hmt⟩ := MarchInduction.mem_range_of_eq hr (Set.mem_insert _ _)
    refine ⟨mt, hmt, ?_⟩
    rcases MarchInduction.vertex_data_of_range hr hmt with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left; exact ⟨by rw [h1], by rw [h2]⟩
    · right; exact ⟨by rw [h2], by rw [h1]⟩
  -- the known tiles
  obtain ⟨i2, i3, h23, hr2, hr3, g2, g3⟩ := ApexFrameReal.two_gamma_at_pprime F
  have hr2' : Set.range (D.tile i2).pts = {F.P, F.A, F.V} := by
    rw [hr2, Set.pair_comm F.V F.P, Set.insert_comm F.A F.P]
  have hr3' : Set.range (D.tile i3).pts = {F.P, F.A, F.A + ((f : ℝ) ^ 2) • F.uL} := by
    rw [hr3, Set.insert_comm F.A F.P]
  obtain ⟨k, hk⟩ := hK
  have hk' : Set.range (D.tile k).pts = {F.P, F.V, F.V + F.P - F.A} := by
    rw [hk]; unfold HFrame.K; rw [Set.insert_comm F.V F.P]
  obtain ⟨z0, mz0, hmz0, hfl0, g0⟩ := Z0_tile F FC ⟨k, hk⟩
  have hVQ : dist F.V (F.V + F.P - F.A) = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
    rw [← F.hAP, dist_comm F.V, dist_comm F.A F.P, dist_eq_norm, dist_eq_norm]
    congr 1; abel
  have gk : (D.tile k).localAngle F.P = β := (hloc hk').2.1 hVQ
  have hz2 : z ≠ i2 := by
    obtain ⟨mt, hmt, hfl⟩ := flank_of i2 hr2'
    exact hnot i2 mt _ _ hmt hfl hbadA (hbad _ hVP)
  have hz3 : z ≠ i3 := by
    obtain ⟨mt, hmt, hfl⟩ := flank_of i3 hr3'
    exact hnot i3 mt _ _ hmt hfl hbadA (hbad _ hJP)
  have hzk : z ≠ k := by
    obtain ⟨mt, hmt, hfl⟩ := flank_of k hk'
    exact hnot k mt _ _ hmt hfl (hbad _ hVP) (hbad _ hQP)
  have hzz0 : z ≠ z0 := hnot z0 mz0 _ _ hmz0 hfl0 (hbad _ hJP) (hbad _ hcL)
  -- `k ≠ z₀` (`J₁` is a vertex of `Z₀`, not of `K`)
  have hkz0 : k ≠ z0 := by
    intro hkz
    have hJ : F.A + ((f : ℝ) ^ 2) • F.uL ∈ Set.range (D.tile z0).pts := by
      rcases hfl0 with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact ⟨mz0 + 1, sub_left_inj.mp h1.symm⟩
      · exact ⟨mz0 + 2, sub_left_inj.mp h1.symm⟩
    rw [← hkz, hk'] at hJ
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hJ
    have hPJ : dist F.P (F.A + ((f : ℝ) ^ 2) • F.uL) = (e : ℝ) * f := F.hPJ1
    have hAV : dist F.A F.V = (f : ℝ) ^ 2 := by
      rw [F.hV]; exact dist_self_add_unit F.huR hc0.le
    rcases hJ with h | h | h
    · rw [h, dist_self] at hPJ; nlinarith
    · exact V_ne_J1 F h.symm
    · have : dist F.P (F.A + ((f : ℝ) ^ 2) • F.uL) = (f : ℝ) ^ 2 := by
        rw [h, dist_eq_norm, show F.P - (F.V + F.P - F.A) = F.A - F.V by abel, ← dist_eq_norm,
          hAV]
      rw [hPJ] at this; exact hacd this
  obtain ⟨-, hB2, hC2, -⟩ := r4_figure_at_pprime' F FC ⟨k, hk⟩
  have hang := localAngle_at_own_vertex_mem D α β γ F.hM.hα' F.hM.hβ' F.hM.hγ' z mz
  rw [hmz] at hang
  rcases hang with h | h | h
  · exact h
  · exfalso
    have hsub : ({k, z0} : Finset (Fin N)) ⊆
        ({i | (D.tile i).localAngle F.P = β} : Finset (Fin N)) := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact mem_filter_of gk
      · exact mem_filter_of g0
    have heq := Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_pair hkz0, hB2])
    have hzm : z ∈ ({k, z0} : Finset (Fin N)) := by rw [heq]; exact mem_filter_of h
    simp only [Finset.mem_insert, Finset.mem_singleton] at hzm
    rcases hzm with h' | h'
    · exact hzk h'
    · exact hzz0 h'
  · exfalso
    have hsub : ({i2, i3} : Finset (Fin N)) ⊆
        ({i | (D.tile i).localAngle F.P = γ} : Finset (Fin N)) := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact mem_filter_of g2
      · exact mem_filter_of g3
    have heq := Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_pair h23, hC2])
    have hzm : z ∈ ({i2, i3} : Finset (Fin N)) := by rw [heq]; exact mem_filter_of h
    simp only [Finset.mem_insert, Finset.mem_singleton] at hzm
    rcases hzm with h' | h'
    · exact hz2 h'
    · exact hz3 h'


/-- Two distinct straight (`π` or `2π`) tiles at a point. -/
theorem two_straight {D : CongruentDissection N} {x : Plane} {i z : Fin N} (hiz : i ≠ z)
    (hi : (D.tile i).localAngle x = 2 * Real.pi ∨ (D.tile i).localAngle x = Real.pi)
    (hz : (D.tile z).localAngle x = 2 * Real.pi ∨ (D.tile z).localAngle x = Real.pi) :
    2 ≤ ({i | (D.tile i).localAngle x = Real.pi} : Finset (Fin N)).card
      + ({i | (D.tile i).localAngle x = 2 * Real.pi} : Finset (Fin N)).card := by
  classical
  rcases hi with hi | hi <;> rcases hz with hz | hz
  · have hsub : ({i, z} : Finset (Fin N)) ⊆
        ({i | (D.tile i).localAngle x = 2 * Real.pi} : Finset (Fin N)) := by
      intro y hy; simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl
      · exact mem_filter_of hi
      · exact mem_filter_of hz
    have := Finset.card_le_card hsub; rw [Finset.card_pair hiz] at this; omega
  · have h1 := Finset.card_pos.mpr ⟨i, mem_filter_of hi⟩
    have h2 := Finset.card_pos.mpr ⟨z, mem_filter_of hz⟩
    omega
  · have h1 := Finset.card_pos.mpr ⟨i, mem_filter_of hi⟩
    have h2 := Finset.card_pos.mpr ⟨z, mem_filter_of hz⟩
    omega
  · have hsub : ({i, z} : Finset (Fin N)) ⊆
        ({i | (D.tile i).localAngle x = Real.pi} : Finset (Fin N)) := by
      intro y hy; simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl
      · exact mem_filter_of hi
      · exact mem_filter_of hz
    have := Finset.card_le_card hsub; rw [Finset.card_pair hiz] at this; omega

theorem one_straight {D : CongruentDissection N} {x : Plane} {i : Fin N}
    (hi : (D.tile i).localAngle x = 2 * Real.pi ∨ (D.tile i).localAngle x = Real.pi) :
    1 ≤ ({i | (D.tile i).localAngle x = Real.pi} : Finset (Fin N)).card
      + ({i | (D.tile i).localAngle x = 2 * Real.pi} : Finset (Fin N)).card := by
  classical
  rcases hi with hi | hi
  · have := Finset.card_pos.mpr ⟨i, mem_filter_of hi⟩; omega
  · have := Finset.card_pos.mpr ⟨i, mem_filter_of hi⟩; omega

/-- `2P′ − A` is interior to the target. -/
theorem Z_interior (F : HFrame D e f α β γ) (FC : ApexPlacement.FrameCoords F) :
    F.P + F.P - F.A ∈ interior D.target.carrier := by
  obtain ⟨s3, t3, hs3, ht3, hP, -, hsum3⟩ := FC.hP
  have hefR : (e : ℝ) + 2 ≤ f := by exact_mod_cast F.hef
  have heR : (2 : ℝ) ≤ e := by exact_mod_cast F.he
  have hf0 : (0 : ℝ) < f := by linarith
  have h1 := FC.hcone.inter (2 * s3) (2 * t3) 1 (by positivity) (by positivity) one_pos (by
    rw [one_mul, show 2 * s3 + 2 * t3 = 2 * (s3 + t3) by ring, hsum3,
      show (2 : ℝ) * (1 / f) = 2 / f by ring, div_lt_one hf0]
    linarith)
  rw [show F.A + ((f : ℝ) ^ 3) • F.uL - F.A = ((f : ℝ) ^ 3) • F.uL by abel, one_smul] at h1
  have hP' : F.P = F.A + (s3 • (((f : ℝ) ^ 3) • F.uL) + t3 • (F.R - F.A)) := by rw [← hP]; abel
  have : F.P + F.P - F.A
      = F.A + ((2 * s3) • (((f : ℝ) ^ 3) • F.uL) + (2 * t3) • (F.R - F.A)) := by
    rw [hP']; module
  rw [this]; exact h1

/-- **`2P′ − A` is rigid for the anti-diagonal**: no tile edge parallel to `P′ − V` has `2P′ − A`
in its relative interior.  (`T₂ + P′` presents `γ` there; the second `α`-tile at `P′` lays `b` along
`P′ − A` — a second `γ` at `2P′ − A` — or `c` — a straight angle along `P′ − A`.  Either way a further
straight angle overfills `2π`.) -/
theorem Z_rigid (F : HFrame D e f α β γ) (FC : ApexPlacement.FrameCoords F)
    (hK : Present D F.K) {i : Fin N} {m : Fin 3}
    (hZ : F.P + F.P - F.A ∈ openSegment ℝ ((D.tile i).pts m) ((D.tile i).pts (m + 1)))
    (hpar : cross ((D.tile i).pts (m + 1) - (D.tile i).pts m) (F.P - F.V) = 0) : False := by
  classical
  obtain ⟨habd, hacd, hbcd⟩ := sides_distinct F.hco F.he (by have := F.hef; omega)
  have heR : (2 : ℝ) ≤ e := by exact_mod_cast F.he
  have hefR : (e : ℝ) + 2 ≤ f := by exact_mod_cast F.hef
  have hc0 : (0 : ℝ) < (f : ℝ) ^ 2 := by nlinarith
  have hb0 : (0 : ℝ) < (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by nlinarith
  have hbc : (f : ℝ) ^ 2 - (e : ℝ) ^ 2 < (f : ℝ) ^ 2 := by nlinarith
  have hloc := fun {i : Fin N} {P Q R : Plane} (hr : Set.range (D.tile i).pts = {P, Q, R}) =>
    localAngle_of_rangeE D habd hacd hbcd F.hM.hs0 F.hM.hs1 F.hM.hs2 F.hM.hα' F.hM.hβ' F.hM.hγ' hr
  have hZint := Z_interior F FC
  obtain ⟨j, z, mz, U, W, S, hj, hzj, hmz, hUW, hS, hU, hzα⟩ := alpha2_tile F FC hK
  have hj' : Set.range (D.tile j).pts = {F.P + F.P - F.A, F.P, F.V + F.P - F.A} := by
    rw [hj]; unfold HFrame.T2P
    rw [Set.pair_comm (F.V + F.P - F.A), Set.insert_comm F.P]
  have gj : (D.tile j).localAngle (F.P + F.P - F.A) = γ := by
    apply (hloc hj').2.2
    rw [dist_eq_norm, show F.P - (F.V + F.P - F.A) = F.A - F.V by abel, ← dist_eq_norm, F.hV]
    exact dist_self_add_unit F.huR hc0.le
  obtain ⟨E1, E2⟩ := interior_card_eqs D F.hAng F.hM.hα' F.hM.hβ' F.hM.hγ' hZint
  obtain ⟨-, hiang⟩ := straight_of_openSeg (D.tile i) hZ
  have cC1 : 1 ≤ ({i | (D.tile i).localAngle (F.P + F.P - F.A) = γ} : Finset (Fin N)).card :=
    Finset.card_pos.mpr ⟨j, mem_filter_of gj⟩
  obtain ⟨hn, hopp⟩ := (corner_dataH F hmz hUW).2 hzα
  have hSU : S * ‖U‖ = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
    rw [← F.hw_norm, hU, norm_smul, Real.norm_of_nonneg hS.le]
  rcases hn with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · -- `b` along `P′ − A`: `z` has a vertex at `2P′ − A`, presenting `γ` there
    have hS1 : S = 1 := by
      rw [h1] at hSU
      have : S * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) = 1 * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) := by
        rw [hSU, one_mul]
      exact mul_right_cancel₀ hb0.ne' this
    have hUw : U = F.P - F.A := by rw [hU, hS1, one_smul]
    have hUe : F.P + U = F.P + F.P - F.A := by rw [hUw]; abel
    have hzr : Set.range (D.tile z).pts = {F.P + F.P - F.A, F.P, F.P + W} := by
      rw [ApexPlacement.range_of_flank hmz hUW, hUe, Set.insert_comm]
    have gz : (D.tile z).localAngle (F.P + F.P - F.A) = γ := by
      apply (hloc hzr).2.2
      rw [dist_comm, dist_eq_norm, add_sub_cancel_left, h2]
    have hsub : ({j, z} : Finset (Fin N)) ⊆
        ({i | (D.tile i).localAngle (F.P + F.P - F.A) = γ} : Finset (Fin N)) := by
      intro y hy; simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl
      · exact mem_filter_of gj
      · exact mem_filter_of gz
    have hC2 := Finset.card_le_card hsub
    rw [Finset.card_pair (Ne.symm hzj)] at hC2
    have := one_straight hiang
    omega
  · -- `c` along `P′ − A`: `z` has `2P′ − A` inside its edge along `P′ − A`
    have hS1 : S < 1 := by
      rw [h1] at hSU
      by_contra hc; push Not at hc; nlinarith
    have hZseg : F.P + F.P - F.A ∈ openSegment ℝ F.P (F.P + U) := by
      refine ⟨1 - S, S, by linarith, hS, by ring, ?_⟩
      rw [show F.P + F.P - F.A = F.P + (F.P - F.A) by abel, hU]; module
    obtain ⟨a, ha⟩ : ∃ a : Fin 3,
        F.P + F.P - F.A ∈ openSegment ℝ ((D.tile z).pts a) ((D.tile z).pts (a + 1)) ∧
        ((D.tile z).pts (a + 1) - (D.tile z).pts a = U ∨
          (D.tile z).pts (a + 1) - (D.tile z).pts a = -U) := by
      rcases hUW with ⟨h1', -⟩ | ⟨h1', -⟩
      · refine ⟨mz, ?_, Or.inl ?_⟩
        · rw [hmz, show (D.tile z).pts (mz + 1) = F.P + U by rw [h1']; abel]; exact hZseg
        · rw [hmz, h1']
      · refine ⟨mz + 2, ?_, Or.inr ?_⟩
        · rw [fin3_add_two_add_one, hmz, show (D.tile z).pts (mz + 2) = F.P + U by rw [h1']; abel,
            openSegment_symm]
          exact hZseg
        · rw [fin3_add_two_add_one, hmz, h1']; abel
    obtain ⟨hZz, ha'⟩ := ha
    obtain ⟨-, hzang⟩ := straight_of_openSeg (D.tile z) hZz
    by_cases hiz : i = z
    · subst hiz
      have hma : m = a := same_edge (D.tile i) hZ hZz
      subst hma
      have hcU : cross U (F.P - F.V) = 0 := by
        rcases ha' with h | h <;> rw [h] at hpar
        · exact hpar
        · rw [cross_neg_left] at hpar; linarith
      have hcw : cross (F.P - F.A) (F.P - F.V) = 0 := by
        rw [hU, cross_smul_left', hcU, mul_zero]
      rw [show F.P - F.V = (F.P - F.A) - ((f : ℝ) ^ 2) • F.uR by rw [F.hV]; abel,
        cross_sub_right', cross_self', zero_sub, cross_smul_right, neg_eq_zero] at hcw
      exact mul_ne_zero hc0.ne' F.cross_w_uR hcw
    · have := two_straight hiz hiang hzang
      omega

/-- **`2V − A` is rigid for the anti-diagonal**: no tile edge parallel to `P′ − V` has `2V − A` in
its relative interior (`2V − A` is pierced along `r`, and `L` presents `β` there). -/
theorem X_rigid (F : HFrame D e f α β γ) (hL : Present D F.L)
    {i : Fin N} {m : Fin 3}
    (hX : F.V + F.V - F.A ∈ openSegment ℝ ((D.tile i).pts m) ((D.tile i).pts (m + 1)))
    (hpar : cross ((D.tile i).pts (m + 1) - (D.tile i).pts m) (F.P - F.V) = 0) : False := by
  classical
  obtain ⟨habd, hacd, hbcd⟩ := sides_distinct F.hco F.he (by have := F.hef; omega)
  have heR : (2 : ℝ) ≤ e := by exact_mod_cast F.he
  have hefR : (e : ℝ) + 2 ≤ f := by exact_mod_cast F.hef
  have hc0 : (0 : ℝ) < (f : ℝ) ^ 2 := by nlinarith
  have hloc := fun {i : Fin N} {P Q R : Plane} (hr : Set.range (D.tile i).pts = {P, Q, R}) =>
    localAngle_of_rangeE D habd hacd hbcd F.hM.hs0 F.hM.hs1 F.hM.hs2 F.hM.hα' F.hM.hβ' F.hM.hγ' hr
  have e2 : F.Vk (1 + 1) = F.V + F.V - F.A := by
    rw [HFrame.Vk, F.hV]; push_cast; module
  have hQ1 : F.Qk 1 = F.V + F.P - F.A := by
    simp only [HFrame.Qk, Nat.cast_one, one_mul]; rw [F.hV]; abel
  obtain ⟨l, hl⟩ := hL
  have hL1 : Present D (F.Lc 1) := ⟨l, by rw [hl, HFrame.Lc, F.Vk_one, e2, hQ1]; rfl⟩
  have hL0 : Present D (F.Lc 0) := by
    obtain ⟨i2, h2⟩ := F.hT2
    exact ⟨i2, by rw [h2, HFrame.Lc, F.Vk_zero, F.Vk_one, F.Qk_zero]⟩
  have hLs : ∀ i ≤ 1, Present D (F.Lc i) := fun i hi => by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hi with rfl | rfl
    · exact hL0
    · exact hL1
  have hmem : F.Vk (1 + 1) ∈ D.target.carrier := mem_of_present hL1 (by simp [HFrame.Lc])
  obtain ⟨ε, hεf, hstr⟩ := pierced_of F 1 hLs hmem
  have hXint := Vk_interior F (1 + 1) (by norm_num) hmem
  rw [e2] at hstr hXint
  -- `L` presents `β` at `2V − A`
  have hl' : Set.range (D.tile l).pts = {F.V + F.V - F.A, F.V, F.V + F.P - F.A} := by
    rw [hl]; unfold HFrame.L; rw [Set.insert_comm F.V]
  have gl : (D.tile l).localAngle (F.V + F.V - F.A) = β := by
    apply (hloc hl').2.1
    rw [dist_comm, dist_eq_norm, show F.V + F.P - F.A - F.V = F.P - F.A by abel]
    exact F.hw_norm
  obtain ⟨E1, E2⟩ := interior_card_eqs D F.hAng F.hM.hα' F.hM.hβ' F.hM.hγ' hXint
  have cB1 : 1 ≤ ({i | (D.tile i).localAngle (F.V + F.V - F.A) = β} : Finset (Fin N)).card :=
    Finset.card_pos.mpr ⟨l, mem_filter_of gl⟩
  obtain ⟨-, hiang⟩ := straight_of_openSeg (D.tile i) hX
  obtain ⟨-, hbang⟩ := straight_of_openSeg (D.tile ε.1) hstr
  by_cases hib : i = ε.1
  · subst hib
    have hm : m = ε.2 := same_edge (D.tile ε.1) hX hstr
    subst hm
    have hε' : ε ∈ D.toDissection.lineChain (-F.h) (-(F.h F.A)) := hεf
    obtain ⟨h0, h1, -⟩ := Dissection.mem_lineChain.mp hε'
    rw [LinearMap.neg_apply] at h0 h1
    have hne' : ∀ x : Fin 3, x ≠ x + 1 := by decide
    have hd0 := sub_ne_zero.mpr (pts_ne (D.tile ε.1) (hne' ε.2)).symm
    have hgd : F.h ((D.tile ε.1).pts (ε.2 + 1) - (D.tile ε.1).pts ε.2) = 0 := by
      rw [map_sub]; linarith
    have hgd' : F.h (F.P - F.V) ≠ 0 := by
      rw [map_sub, F.hV, map_add, map_smul, F.hhuR, smul_zero, add_zero]
      exact (sub_neg.mpr F.hhP).ne
    exact cross_ne_of_g F.h hd0 hgd hgd' hpar
  · have := two_straight hib hiang hbang
    omega


theorem cross_sub_left'' (u v w : Plane) : cross (u - v) w = cross u w - cross v w := by
  simp only [NearBaseVertex.cross_apply, PiLp.sub_apply]; ring

/-- The two other sides of a tile with an `a`-side `XY` are `{b, c}`. -/
theorem sides_of_a (D : CongruentDissection N) {a b c : ℝ} (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) (hs0 : sideOpp D.model 0 = a) (hs1 : sideOpp D.model 1 = b)
    (hs2 : sideOpp D.model 2 = c) {i : Fin N} {x Y Z : Plane}
    (hr : Set.range (D.tile i).pts = {x, Y, Z}) (hY : dist Y x = a) :
    (dist Z x = b ∧ dist Y Z = c) ∨ (dist Z x = c ∧ dist Y Z = b) := by
  obtain ⟨m, hm⟩ := MarchInduction.mem_range_of_eq hr (Set.mem_insert _ _)
  have hP := NearBaseBridge.tile_triple (D.tiles_congruent i) hs0 hs1 hs2 m
  rw [hm] at hP
  unfold NearBaseBridge.Perm3 at hP
  rcases MarchInduction.vertex_data_of_range hr hm with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    rw [h1, h2] at hP
  · rw [hY] at hP
    rcases hP with ⟨p1, p2, p3⟩ | ⟨p1, p2, p3⟩ | ⟨p1, p2, p3⟩ | ⟨p1, p2, p3⟩ | ⟨p1, p2, p3⟩ |
      ⟨p1, p2, p3⟩ <;>
    first
      | exact Or.inl ⟨p2, p3⟩
      | exact Or.inr ⟨p2, p3⟩
      | exact absurd p1 hab
      | exact absurd p1 hac
  · rw [hY, dist_comm Z Y] at hP
    rcases hP with ⟨p1, p2, p3⟩ | ⟨p1, p2, p3⟩ | ⟨p1, p2, p3⟩ | ⟨p1, p2, p3⟩ | ⟨p1, p2, p3⟩ |
      ⟨p1, p2, p3⟩ <;>
    first
      | exact Or.inl ⟨p1, p3⟩
      | exact Or.inr ⟨p1, p3⟩
      | exact absurd p2 hab
      | exact absurd p2 hac

set_option maxHeartbeats 1000000 in
/-- **R4 (d), `HalfTurnR3R4Glue.level2_lemmaG`, PROVED.**  In branch (H) after an `L_c` step
(`L = T₂ + V` a tile), the tile across `L`'s `a`-edge `[2V − A, V + P′ − A]` is `K + V` or the
mirror of `L` across that edge.  The anti-diagonal `[2V − A, 2P′ − A]` is the union of the `a`-edges of
`L` and `T₂ + P′` (`t2pprime_forced'`); its far side is covered by whole edges (`wall_sum`; both ends
rigid: `X_rigid`, `Z_rigid`) totalling `2a`, hence all `a` (`Inflation.a_side_no_b`,
`a_side_rigid`, `f ≥ 3`); two `a`-edges overlapping at `Q₁` would share an interval (`meet`), so
`Q₁` is a far junction and the first far edge is exactly `[2V − A, Q₁]`; its tile is identified by
its two other sides `{b, c}` (`third_vertex_cross`). -/
theorem level2_lemmaG' (F : HFrame D e f α β γ) (FC : ApexPlacement.FrameCoords F)
    (hK : Present D F.K) (hL : Present D F.L) :
    Present D F.KV ∨ ∃ M : Plane,
      IsMirror F.V (F.V + F.V - F.A) (F.V + F.P - F.A) M ∧
        Present D {F.V + F.V - F.A, F.V + F.P - F.A, M} := by
  classical
  obtain ⟨habd, hacd, hbcd⟩ := sides_distinct F.hco F.he (by have := F.hef; omega)
  have heR : (2 : ℝ) ≤ e := by exact_mod_cast F.he
  have hefR : (e : ℝ) + 2 ≤ f := by exact_mod_cast F.hef
  have hc0 : (0 : ℝ) < (f : ℝ) ^ 2 := by nlinarith
  have hb0 : (0 : ℝ) < (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by nlinarith
  have ha0 : (0 : ℝ) < (e : ℝ) * f := by nlinarith
  set X := F.V + F.V - F.A with hXdef
  set Y := F.V + F.P - F.A with hYdef
  set Z := F.P + F.P - F.A with hZdef
  set dd := F.P - F.V with hdd
  have hdn : ‖dd‖ = (e : ℝ) * f := by rw [hdd, ← dist_eq_norm, dist_comm]; exact F.hVP
  have hdw : dd = (F.P - F.A) - ((f : ℝ) ^ 2) • F.uR := by rw [hdd, F.hV]; abel
  set u : Plane := (1 / ((e : ℝ) * f)) • dd with hudef
  have hu1 : ‖u‖ = 1 := by
    rw [hudef, norm_smul, hdn, Real.norm_of_nonneg (by positivity), one_div_mul_cancel ha0.ne']
  have hu0 : u ≠ 0 := TraceCovering.ne_zero_of_norm hu1
  have hdu : ((e : ℝ) * f) • u = dd := by
    rw [hudef, smul_smul, mul_one_div_cancel ha0.ne', one_smul]
  have hX0 : X + (0 : ℝ) • u = X := by rw [zero_smul, add_zero]
  have hXY : X + ((e : ℝ) * f) • u = Y := by rw [hdu, hdd, hXdef, hYdef]; abel
  have hXZ : X + (2 * ((e : ℝ) * f)) • u = Z := by
    rw [mul_smul, hdu, hdd, hXdef, hZdef]; module
  -- the side functional of the anti-diagonal: `A` on `{g > g X}`
  set ε0 := cross dd (F.A - X) with hε0def
  have hAX : F.A - X = (-(2 * (f : ℝ) ^ 2)) • F.uR := by rw [hXdef, F.hV]; module
  have hVX : F.V - X = (-((f : ℝ) ^ 2)) • F.uR := by rw [hXdef, F.hV]; module
  have hcross_d_uR : cross dd F.uR = cross (F.P - F.A) F.uR := by
    rw [hdw, cross_sub_left'', cross_smul_left', cross_self', mul_zero, sub_zero]
  have hε0v : ε0 = -(2 * (f : ℝ) ^ 2) * cross (F.P - F.A) F.uR := by
    rw [hε0def, hAX, cross_smul_right, hcross_d_uR]
  have hε0 : ε0 ≠ 0 := by
    rw [hε0v]; exact mul_ne_zero (by nlinarith) F.cross_w_uR
  set g : Plane →ₗ[ℝ] ℝ := ε0 • crossL dd with hgdef
  have happ : ∀ y, g y = ε0 * cross dd y := fun y => by
    rw [hgdef, LinearMap.smul_apply, crossL_apply, smul_eq_mul]
  have hgu : g u = 0 := by rw [happ, hudef, cross_smul_right, cross_self', mul_zero, mul_zero]
  have hgsub : ∀ y z, g y - g z = ε0 * cross dd (y - z) := fun y z => by
    rw [happ, happ, ← mul_sub, cross_sub_right']
  have hg0 : g ≠ 0 := by
    intro h
    have := hgsub F.A X
    rw [h, LinearMap.zero_apply, LinearMap.zero_apply, sub_zero, ← hε0def] at this
    exact hε0 (mul_self_eq_zero.mp this.symm)
  -- the tiles: `L`, `T₂ + P′`
  obtain ⟨j, hj, -⟩ := t2pprime_forced' F FC hK
  have hL' := hL
  obtain ⟨l, hl⟩ := hL'
  -- interior of the anti-diagonal
  have e2 : F.Vk (1 + 1) = X := by rw [hXdef, HFrame.Vk, F.hV]; push_cast; module
  have hXmem : X ∈ D.target.carrier :=
    mem_of_present hL (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  have hXint : X ∈ interior D.target.carrier := by
    rw [← e2]; exact Vk_interior F (1 + 1) (by norm_num) (by rw [e2]; exact hXmem)
  have hZint : Z ∈ interior D.target.carrier := Z_interior F FC
  have hint : ∀ x ∈ Set.Ioo 0 (2 * ((e : ℝ) * f)), X + x • u ∈ interior D.target.carrier := by
    intro x hx
    have hpos : (0 : ℝ) < 2 * ((e : ℝ) * f) := by positivity
    have h := D.target.convex.interior hXint hZint
      (a := 1 - x / (2 * ((e : ℝ) * f))) (b := x / (2 * ((e : ℝ) * f)))
      (by rw [sub_nonneg, div_le_one hpos]; exact hx.2.le) (div_nonneg hx.1.le hpos.le) (by ring)
    have : (1 - x / (2 * ((e : ℝ) * f))) • X + (x / (2 * ((e : ℝ) * f))) • Z = X + x • u := by
      rw [← hXZ, smul_add, smul_smul, div_mul_cancel₀ _ hpos.ne']; module
    rwa [this] at h
  -- the wall: `L`'s `a`-edge `[X, Y]` and `T₂ + P′`'s `a`-edge `[Y, Z]`
  have edge_of : ∀ (t : Fin N) (S : Set Plane) (p q : Plane), Set.range (D.tile t).pts = S →
      p ∈ S → q ∈ S → p ≠ q → ∃ m, (D.tile t).edge m = segment ℝ p q := by
    intro t S p q hr hp hq hpq
    obtain ⟨k0, hk0⟩ := MarchInduction.mem_range_of_eq hr hp
    obtain ⟨k1, hk1⟩ := MarchInduction.mem_range_of_eq hr hq
    have hkne : k0 ≠ k1 := by rintro rfl; exact hpq (hk0.symm.trans hk1)
    obtain ⟨m, hm⟩ := (D.tile t).pair_eq_edge hkne
    exact ⟨m, by rw [← hm, hk0, hk1]⟩
  have hXYne : X ≠ Y := by
    intro h
    have : Y - X = dd := by rw [hXdef, hYdef, hdd]; abel
    rw [← h, sub_self] at this
    rw [← this, norm_zero] at hdn; linarith
  have hYZne : Y ≠ Z := by
    intro h
    have : Z - Y = dd := by rw [hZdef, hYdef, hdd]; abel
    rw [← h, sub_self] at this
    rw [← this, norm_zero] at hdn; linarith
  obtain ⟨mL, hmL⟩ := edge_of l _ X Y hl (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
    (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))) hXYne
  obtain ⟨mT, hmT⟩ := edge_of j _ Y Z hj (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
    (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))) hYZne
  have hwall : ∀ x ∈ Set.Ioo 0 (2 * ((e : ℝ) * f)), ∀ i,
      X + x • u ∉ interior (D.tile i).carrier := by
    intro x hx i
    rcases le_or_gt x ((e : ℝ) * f) with hle | hgt
    · have hmem : X + x • u ∈ (D.tile l).edge mL := by
        rw [hmL, show segment ℝ X Y = segment ℝ (X + (0 : ℝ) • u) (X + ((e : ℝ) * f) • u) by
          rw [hX0, hXY], TraceCovering.segment_param, min_eq_left ha0.le, max_eq_right ha0.le]
        exact ⟨x, ⟨hx.1.le, hle⟩, rfl⟩
      exact D.toDissection.edge_point_not_interior hmem i
    · have hmem : X + x • u ∈ (D.tile j).edge mT := by
        rw [hmT, show segment ℝ Y Z = segment ℝ (X + ((e : ℝ) * f) • u)
            (X + (2 * ((e : ℝ) * f)) • u) by rw [hXY, hXZ], TraceCovering.segment_param,
          min_eq_left (by linarith), max_eq_right (by linarith)]
        exact ⟨x, ⟨hgt.le, hx.2.le⟩, rfl⟩
      exact D.toDissection.edge_point_not_interior hmem i
  -- the ends are rigid
  have hline : ∀ ε ∈ D.toDissection.lineChain g (g X),
      cross ((D.tile ε.1).pts (ε.2 + 1) - (D.tile ε.1).pts ε.2) dd = 0 := by
    intro ε hε
    obtain ⟨h0, h1, -⟩ := Dissection.mem_lineChain.mp hε
    have := hgsub ((D.tile ε.1).pts (ε.2 + 1)) ((D.tile ε.1).pts ε.2)
    rw [h0, h1, sub_self] at this
    have h' : cross dd ((D.tile ε.1).pts (ε.2 + 1) - (D.tile ε.1).pts ε.2) = 0 := by
      rcases mul_eq_zero.mp this.symm with h | h
      · exact absurd h hε0
      · exact h
    rw [cross_anti, h', neg_zero]
  have hs : ¬ TraceCovering.Straddled D.toDissection g (g X) (X + (0 : ℝ) • u) := by
    rintro ⟨ε, hε, hstr⟩
    rw [hX0] at hstr
    exact X_rigid F hL hstr (hline ε hε)
  have ht : ¬ TraceCovering.Straddled D.toDissection g (g X)
      (X + (2 * ((e : ℝ) * f)) • u) := by
    rintro ⟨ε, hε, hstr⟩
    rw [hXZ] at hstr
    exact Z_rigid F FC hK hstr (hline ε hε)
  have hsum := TraceCovering.wall_sum (D := D.toDissection) (f := g) (c := g X) hg0
    (fun _ => Iff.rfl) hg0 rfl hgu hu1 (by positivity) hint hwall hs ht
  set s := (D.toDissection.lineChain g (g X)).filter
    (fun ε => (D.tile ε.1).edge ε.2 ⊆ segment ℝ (X + (0 : ℝ) • u)
      (X + (2 * ((e : ℝ) * f)) • u)) with hs_def
  have hee : e ^ 2 ≤ f ^ 2 := Nat.pow_le_pow_left (by have := F.hef; omega) 2
  have hlen := fun ε : Fin N × Fin 3 =>
    MirrorStripR2Glue.edge_len_mem D F.hM.hs0 F.hM.hs1 F.hM.hs2 ε.1 ε.2
  -- 2a = a + a only: every far edge on the anti-diagonal is an `a`
  have all_a : ∀ ε ∈ s,
      dist ((D.tile ε.1).pts ε.2) ((D.tile ε.1).pts (ε.2 + 1)) = (e : ℝ) * f := by
    intro ε hεs
    have hsum' := hsum
    rw [← Finset.add_sum_erase s _ hεs] at hsum'
    obtain ⟨P', Q', R', hPQR, -⟩ := sum_three_values (s.erase ε)
      (fun ε => dist ((D.tile ε.1).pts ε.2) ((D.tile ε.1).pts (ε.2 + 1)))
      ((e : ℝ) * f) ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ((f : ℝ) ^ 2) (fun ε _ => hlen ε)
    rcases hlen ε with h | h | h
    · exact h
    · exfalso
      rw [h] at hsum'
      have hreal : ((P' * (e * f) + (Q' + 1) * (f ^ 2 - e ^ 2) + R' * f ^ 2 : ℕ) : ℝ)
          = ((2 * (e * f) : ℕ) : ℝ) := by
        push_cast [Nat.cast_sub hee]; linarith
      have hnat : P' * (e * f) + (Q' + 1) * (f ^ 2 - e ^ 2) + R' * f ^ 2 = 2 * (e * f) := by
        exact_mod_cast hreal
      have := Inflation.a_side_no_b e f (f ^ 2 - e ^ 2) 2 P' (Q' + 1) R'
        (by have := F.he; omega) (by have := F.hef; omega) F.hco (Nat.sub_add_cancel hee)
        (by have := F.hef; omega) hnat
      omega
    · exfalso
      rw [h] at hsum'
      have hreal : ((P' * (e * f) + Q' * (f ^ 2 - e ^ 2) + (R' + 1) * f ^ 2 : ℕ) : ℝ)
          = ((2 * (e * f) : ℕ) : ℝ) := by
        push_cast [Nat.cast_sub hee]; linarith
      have hnat : P' * (e * f) + Q' * (f ^ 2 - e ^ 2) + (R' + 1) * f ^ 2 = 2 * (e * f) := by
        exact_mod_cast hreal
      have hQ := Inflation.a_side_no_b e f (f ^ 2 - e ^ 2) 2 P' Q' (R' + 1)
        (by have := F.he; omega) (by have := F.hef; omega) F.hco (Nat.sub_add_cancel hee)
        (by have := F.hef; omega) hnat
      subst hQ
      have := Inflation.a_side_rigid e f 2 P' (R' + 1) (by have := F.he; omega)
        (by have := F.hef; omega) F.hco (by have := F.hef; have := F.he; omega)
        (by rw [zero_mul, add_zero] at hnat; exact hnat)
      omega
  have sum_a : ∀ t : Finset (Fin N × Fin 3), t ⊆ s →
      ∑ ε ∈ t, dist ((D.tile ε.1).pts ε.2) ((D.tile ε.1).pts (ε.2 + 1))
        = (t.card : ℝ) * ((e : ℝ) * f) := by
    intro t hts
    rw [Finset.sum_congr rfl (fun ε hε => all_a ε (hts hε)), Finset.sum_const, nsmul_eq_mul]
  -- the parametrization of chain edges along the anti-diagonal
  have hgd : ∀ y, g y = g X ↔ g y = g X := fun _ => Iff.rfl
  have hpar_len : ∀ ε ∈ D.toDissection.lineChain g (g X),
      dist ((D.tile ε.1).pts ε.2) ((D.tile ε.1).pts (ε.2 + 1))
        = TraceCovering.hi D.toDissection X u ε - TraceCovering.lo D.toDissection X u ε := by
    intro ε hε
    obtain ⟨h0, h1⟩ := TraceCovering.onLine hgd hε
    exact (TraceCovering.edge_data hg0 rfl hgu hu0 h0 h1).2.2.2 hu1
  have hlohi : ∀ ε ∈ D.toDissection.lineChain g (g X),
      TraceCovering.lo D.toDissection X u ε < TraceCovering.hi D.toDissection X u ε := by
    intro ε hε
    obtain ⟨h0, h1⟩ := TraceCovering.onLine hgd hε
    exact (TraceCovering.edge_data hg0 rfl hgu hu0 h0 h1).1
  have hs' := (TraceCovering.str_iff hgd hg0 rfl hgu hu0 0).not.mp hs
  have ht' := (TraceCovering.str_iff hgd hg0 rfl hgu hu0 _).not.mp ht
  -- `Q₁ = Y` is a far junction
  have hY : ¬ TraceCovering.Straddled D.toDissection g (g X) (X + ((e : ℝ) * f) • u) := by
    intro hstr
    obtain ⟨E1, hE1, hlo1, hhi1⟩ := (TraceCovering.str_iff hgd hg0 rfl hgu hu0 _).mp hstr
    have hlo0 : 0 ≤ TraceCovering.lo D.toDissection X u E1 := by
      by_contra hc; push Not at hc
      exact hs' ⟨E1, hE1, hc, by linarith⟩
    have hhi2 : TraceCovering.hi D.toDissection X u E1 ≤ 2 * ((e : ℝ) * f) := by
      by_contra hc; push Not at hc
      exact ht' ⟨E1, hE1, by linarith, hc⟩
    have hE1s : E1 ∈ s := Finset.mem_filter.mpr ⟨hE1,
      (TraceCovering.inside_iff hgd hg0 rfl hgu hu0 hE1 (by positivity)).mpr ⟨hlo0, hhi2⟩⟩
    have hl1 := (hpar_len E1 hE1).symm.trans (all_a E1 hE1s)
    -- the rest of the covering is a single `a`-edge
    have hsum' := hsum
    rw [← Finset.add_sum_erase s _ hE1s, all_a E1 hE1s,
      sum_a _ (Finset.erase_subset _ _)] at hsum'
    have hcard : ((s.erase E1).card : ℝ) = 1 := by
      have : ((s.erase E1).card : ℝ) * ((e : ℝ) * f) = 1 * ((e : ℝ) * f) := by linarith
      exact mul_right_cancel₀ ha0.ne' this
    obtain ⟨E2, hE2⟩ := Finset.card_eq_one.mp (by exact_mod_cast hcard)
    have hE2m : E2 ∈ s.erase E1 := by rw [hE2]; exact Finset.mem_singleton_self _
    have hE21 : E2 ≠ E1 := (Finset.mem_erase.mp hE2m).1
    have hE2s : E2 ∈ s := (Finset.mem_erase.mp hE2m).2
    have hE2c := (Finset.mem_filter.mp hE2s)
    obtain ⟨hlo2, hhi2'⟩ := (TraceCovering.inside_iff hgd hg0 rfl hgu hu0 hE2c.1
      (by positivity)).mp hE2c.2
    have hl2 := (hpar_len E2 hE2c.1).symm.trans (all_a E2 hE2s)
    have hsub := TraceCovering.meet hg0 hgd hg0 rfl hgu hu0 E1 hE1 E2 hE2c.1 hE21.symm
    set l1 := TraceCovering.lo D.toDissection X u E1
    set h1' := TraceCovering.hi D.toDissection X u E1
    set l2 := TraceCovering.lo D.toDissection X u E2
    set h2' := TraceCovering.hi D.toDissection X u E2
    have hlt1 := hlohi E1 hE1
    have hlt2 := hlohi E2 hE2c.1
    have m1 : max l1 l2 ∈ Set.Icc l1 h1' ∩ Set.Icc l2 h2' :=
      ⟨⟨le_max_left _ _, max_le (by linarith) (by linarith)⟩,
        ⟨le_max_right _ _, max_le (by linarith) (by linarith)⟩⟩
    have m2 : min h1' h2' ∈ Set.Icc l1 h1' ∩ Set.Icc l2 h2' :=
      ⟨⟨le_min (by linarith) (by linarith), min_le_left _ _⟩,
        ⟨le_min (by linarith) (by linarith), min_le_right _ _⟩⟩
    have hlt : max l1 l2 < min h1' h2' :=
      max_lt (lt_min (by linarith) (by linarith)) (lt_min (by linarith) (by linarith))
    exact (ne_of_lt hlt) (hsub m1 m2)
  -- the far covering of `[X, Y]`: one `a`-edge, exactly `[X, Y]`
  have hint1 : ∀ x ∈ Set.Ioo 0 ((e : ℝ) * f), X + x • u ∈ interior D.target.carrier :=
    fun x hx => hint x ⟨hx.1, by linarith [hx.2]⟩
  have hwall1 : ∀ x ∈ Set.Ioo 0 ((e : ℝ) * f), ∀ i, X + x • u ∉ interior (D.tile i).carrier :=
    fun x hx => hwall x ⟨hx.1, by linarith [hx.2]⟩
  have hsum1 := TraceCovering.wall_sum (D := D.toDissection) (f := g) (c := g X) hg0
    (fun _ => Iff.rfl) hg0 rfl hgu hu1 ha0.le hint1 hwall1 hs hY
  set s1 := (D.toDissection.lineChain g (g X)).filter
    (fun ε => (D.tile ε.1).edge ε.2 ⊆ segment ℝ (X + (0 : ℝ) • u) (X + ((e : ℝ) * f) • u))
    with hs1_def
  have hs1s : s1 ⊆ s := by
    intro ε hε
    obtain ⟨hεc, hεi⟩ := Finset.mem_filter.mp hε
    obtain ⟨hlo, hhi⟩ := (TraceCovering.inside_iff hgd hg0 rfl hgu hu0 hεc ha0.le).mp hεi
    exact Finset.mem_filter.mpr ⟨hεc, (TraceCovering.inside_iff hgd hg0 rfl hgu hu0 hεc
      (by positivity)).mpr ⟨hlo, by linarith⟩⟩
  rw [sum_a s1 hs1s] at hsum1
  have hcard1 : (s1.card : ℝ) = 1 := by
    have : (s1.card : ℝ) * ((e : ℝ) * f) = 1 * ((e : ℝ) * f) := by linarith
    exact mul_right_cancel₀ ha0.ne' this
  obtain ⟨E, hE⟩ := Finset.card_eq_one.mp (by exact_mod_cast hcard1)
  have hEs1 : E ∈ s1 := by rw [hE]; exact Finset.mem_singleton_self _
  obtain ⟨hEc, hEi⟩ := Finset.mem_filter.mp hEs1
  obtain ⟨hlo, hhi⟩ := (TraceCovering.inside_iff hgd hg0 rfl hgu hu0 hEc ha0.le).mp hEi
  have hlE := (hpar_len E hEc).symm.trans (all_a E (hs1s hEs1))
  have hlo0 : TraceCovering.lo D.toDissection X u E = 0 := by linarith
  have hhia : TraceCovering.hi D.toDissection X u E = (e : ℝ) * f := by linarith
  -- its endpoints are `X` and `Y`
  obtain ⟨h0E, h1E⟩ := TraceCovering.onLine hgd hEc
  have hp0 := TraceCovering.par_spec (TraceCovering.exists_param hg0 rfl hgu hu0 h0E)
  have hp1 := TraceCovering.par_spec (TraceCovering.exists_param hg0 rfl hgu hu0 h1E)
  simp only [TraceCovering.lo, TraceCovering.hi] at hlo0 hhia
  have hends : ((D.tile E.1).pts E.2 = X ∧ (D.tile E.1).pts (E.2 + 1) = Y) ∨
      ((D.tile E.1).pts E.2 = Y ∧ (D.tile E.1).pts (E.2 + 1) = X) := by
    rcases le_total (TraceCovering.par X u ((D.tile E.1).pts E.2))
      (TraceCovering.par X u ((D.tile E.1).pts (E.2 + 1))) with hle | hle
    · rw [min_eq_left hle] at hlo0; rw [max_eq_right hle] at hhia
      left; exact ⟨by rw [hp0, hlo0, hX0], by rw [hp1, hhia, hXY]⟩
    · rw [min_eq_right hle] at hlo0; rw [max_eq_left hle] at hhia
      right; exact ⟨by rw [hp0, hhia, hXY], by rw [hp1, hlo0, hX0]⟩
  -- the third vertex `W` lies strictly on the far side
  set W := (D.tile E.1).pts (E.2 + 2) with hWdef
  have hfar := (Dissection.mem_lineChain.mp hEc).2.2 (E.2 + 2)
  have hWne : cross dd (W - X) ≠ 0 := by
    have hfl : IsFlankPair (D.tile E.1) E.2 ((D.tile E.1).pts E.2)
        ((D.tile E.1).pts (E.2 + 1) - (D.tile E.1).pts E.2)
        ((D.tile E.1).pts (E.2 + 2) - (D.tile E.1).pts E.2) := Or.inl ⟨rfl, rfl⟩
    have hc := ApexPlacement.flank_cross_ne rfl hfl
    rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2, show Y - X = dd by rw [hXdef, hYdef, hdd]; abel] at hc
      exact hc
    · rw [h1, h2, show X - Y = -dd by rw [hXdef, hYdef, hdd]; abel, cross_neg_left,
        show W - Y = (W - X) - dd by rw [hXdef, hYdef, hdd]; abel, cross_sub_right',
        cross_self', sub_zero, neg_ne_zero] at hc
      exact hc
  have hgW : ε0 * cross dd (W - X) < 0 := by
    rw [← hgsub]
    have : g W - g X ≠ 0 := by rw [hgsub]; exact mul_ne_zero hε0 hWne
    have hle : g W ≤ g X := hfar
    rcases lt_or_eq_of_le hle with h | h
    · linarith
    · exact absurd (by rw [h, sub_self]) this
  have hrE : Set.range (D.tile E.1).pts = {X, Y, W} := by
    rw [TilePlacement.range_pts_eq (D.tile E.1) E.2]
    rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2, Set.insert_comm]
    · rw [h1, h2]
  have hXYd : dist Y X = (e : ℝ) * f := by
    rw [dist_eq_norm, show Y - X = dd by rw [hXdef, hYdef, hdd]; abel, hdn]
  have hcw : cross dd (F.P - F.A) = (f : ℝ) ^ 2 * cross (F.P - F.A) F.uR := by
    rw [hdw, cross_sub_left'', cross_smul_left', cross_self', zero_sub,
      cross_anti (F.P - F.A) F.uR]
    ring
  set q := cross (F.P - F.A) F.uR with hqdef
  have hqq : 0 < q * q := mul_self_pos.mpr F.cross_w_uR
  have hqp : 0 < q * cross dd (W - X) := by
    have h' : ε0 * cross dd (W - X) = -(2 * (f : ℝ) ^ 2) * (q * cross dd (W - X)) := by
      rw [hε0v]; ring
    rw [h'] at hgW
    by_contra hc; push Not at hc
    have : 0 ≤ -(2 * (f : ℝ) ^ 2) * (q * cross dd (W - X)) :=
      mul_nonneg_of_nonpos_of_nonpos (by linarith) hc
    linarith
  rcases sides_of_a D habd hacd hbcd F.hM.hs0 F.hM.hs1 F.hM.hs2 hrE hXYd with
    ⟨hWX, hYW⟩ | ⟨hWX, hYW⟩
  · -- `b` at `X`, `c` at `Y`: the tile is `K + V`
    left
    have hQ2 : W = X + (F.P - F.A) := by
      apply third_vertex_cross (X := X) (Y := Y)
      · exact hXYne
      · rw [show Y - X = dd by rw [hXdef, hYdef, hdd]; abel, add_sub_cancel_left, hcw]
        have : cross dd (W - X) * ((f : ℝ) ^ 2 * q) = (f : ℝ) ^ 2 * (q * cross dd (W - X)) := by
          ring
        rw [this]; exact mul_pos hc0 hqp
      · rw [dist_comm, hWX, dist_comm, dist_eq_norm, add_sub_cancel_left]; exact F.hw_norm.symm
      · rw [hYW, dist_comm, dist_eq_norm,
          show X + (F.P - F.A) - Y = ((f : ℝ) ^ 2) • F.uR by rw [hXdef, hYdef, F.hV]; abel,
          F.c_normR]
    refine ⟨E.1, ?_⟩
    rw [hrE, hQ2]
    unfold HFrame.KV
    congr 2
    rw [hXdef]; abel
  · -- `c` at `X`, `b` at `Y`: the tile is the mirror of `L`
    right
    refine ⟨W, ⟨?_, ?_, ?_⟩, E.1, hrE⟩
    · intro hWV
      have hgV : ε0 * cross dd (F.V - X) = 2 * (f : ℝ) ^ 2 * (f : ℝ) ^ 2 * (q * q) := by
        rw [hVX, cross_smul_right, hcross_d_uR, hε0v]; ring
      rw [hWV, hgV] at hgW
      have : 0 < 2 * (f : ℝ) ^ 2 * (f : ℝ) ^ 2 * (q * q) :=
        mul_pos (mul_pos (mul_pos two_pos hc0) hc0) hqq
      linarith
    · rw [hWX, dist_eq_norm, hVX, norm_smul, F.huR, mul_one, Real.norm_eq_abs, abs_neg,
        abs_of_pos hc0]
    · rw [dist_comm, hYW, dist_comm, dist_eq_norm,
        show Y - F.V = F.P - F.A by rw [hYdef]; abel]
      exact F.hw_norm.symm

/-- **R4 (d) for EVERY real `m = 1` dissection**: in the apex frame, if `L = T₂ + V` is a tile then
the tile across its `a`-edge is `K + V` or the mirror of `L`. -/
theorem level2_lemmaG_real {k : Fin 3} (h : ApexFrameReal.M1Data D e f α β γ k) :
    ∃ F : HFrame D e f α β γ, Present D F.K ∧ (Present D F.L →
      Present D F.KV ∨ ∃ M : Plane,
        IsMirror F.V (F.V + F.V - F.A) (F.V + F.P - F.A) M ∧
          Present D {F.V + F.V - F.A, F.V + F.P - F.A, M}) := by
  obtain ⟨F, FC, hK⟩ := K_present_real h
  exact ⟨F, hK, fun hL => level2_lemmaG' F FC hK hL⟩

end Erdos634.Draft.Level2LemmaGReal

#print axioms Erdos634.Draft.Level2LemmaGReal.cross_w_uL
#print axioms Erdos634.Draft.Level2LemmaGReal.Z0_tile
#print axioms Erdos634.Draft.Level2LemmaGReal.same_edge
#print axioms Erdos634.Draft.Level2LemmaGReal.alpha2_tile
#print axioms Erdos634.Draft.Level2LemmaGReal.Z_rigid
#print axioms Erdos634.Draft.Level2LemmaGReal.X_rigid
#print axioms Erdos634.Draft.Level2LemmaGReal.level2_lemmaG'
#print axioms Erdos634.Draft.Level2LemmaGReal.level2_lemmaG_real
