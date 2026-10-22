-- Draft/LaczFormalIVcRatB2.lean -- Laczkovich DCG 48 (2012), Sect. 8.3 (Subcase IVc, rational branch), BLUEPRINT Part B, item B2.
--   `polygon_angle_cnt` : the corner count form of `polygon_angle_pi3` (same proof, the counts are exported): P.angle(k+1) = (2 cnt_beta + cnt_gamma) pi/3 < pi at P.v(k+1).
--   `ivc_rat_all_c_hexagon` : second branch of B1 (every tile edge of the side walks has length c) with gamma = pi/3, {alpha, beta} = {pi/6, pi/2},
--      a, b commensurable, c not commensurable with a  ==>  Concl9 (hexagon, all angles 2pi/3).
--   Proof: at a corner V the first walk edge is a tile edge of length c from V, so the tile corner at V is an alpha- or beta-corner (a,b-edges are at gamma);
--   regularity gives both, hence the corner angle is >= alpha+beta = 2pi/3 and (< pi) equal to 2pi/3; angle sum gives M = 6; RationalPoly by Lemma 4.7.
--   DEVIATION: hypotheses are exactly those named (no M >= 5 needed). Witness: the Part B P6 hexagon (sides 2b,b,2b,b,2b,b; 6 tiles) satisfies them; NOT built here.
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Lemma 4.7, Sect. 8.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIVcRatB1
import Erdos634.Draft.LaczFormalRG4Comm
import Erdos634.Draft.LaczFormalRG4AngleSum
import Erdos634.Draft.LaczFormalBZ7

open scoped Classical Fin.NatCast Fin.CommRing
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ} [NeZero M]

set_option maxHeartbeats 3200000 in
theorem polygon_angle_cnt (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v) (hγ : D.model.angleAt 2 = Real.pi / 3)
    (hαβ : D.model.angleAt 0 + D.model.angleAt 1 = 2 * Real.pi / 3) (hregc : ∀ X, cnt D idx X 0 = cnt D idx X 1) (k : Fin M) :
    P.angle (k + 1) = ((2 * cnt D idx (P.v (k + 1)) 1 + cnt D idx (P.v (k + 1)) 2 : ℕ) : ℝ) * (Real.pi / 3) ∧
      2 * cnt D idx (P.v (k + 1)) 1 + cnt D idx (P.v (k + 1)) 2 < 3 := by
  classical
  set V := P.v (k + 1) with hVdef
  have hvert : ∃ j k', (D.tile j).pts k' = V := poly_vertex_is_tile_vertex D.toRegionDissection P hreg (k + 1)
  obtain ⟨pT, qT, F, hpd, hqd, hcr, h1, h2, h3, h4, h5⟩ := fan_vertex_poly D.toRegionDissection P hreg k hvert
  have hqT : qT ≠ 0 := by intro h; rw [h] at hcr; unfold crs at hcr; simp at hcr
  have hpT : pT ≠ 0 := hpd.ne_left
  obtain ⟨i0, k0, hk0⟩ := hvert
  have hmem0 : V ∈ (D.tile i0).carrier := hk0 ▸ subset_convexHull ℝ _ ⟨k0, rfl⟩
  have hAt : 0 < Fintype.card (AtV D.toRegionDissection V) := Fintype.card_pos_iff.mpr ⟨⟨i0, hmem0⟩⟩
  obtain ⟨c, hc1, hcn, hadj, hsurjc, hinjc⟩ := corner_chain F hcr h1 h2 h3 h4 h5 hAt
  set n := Fintype.card (AtV D.toRegionDissection V) with hn
  have hsumT := corner_tile_sum D.toRegionDissection F hcr h1 h2 h3 h4
  have hwlt := wd_lt_pi_of_crs_pos hcr
  have hwpos := wd_pos (Or.inl hcr : SecOK pT qT)
  have hnostr : ∀ x : AtV D.toRegionDissection V, ∃ k, (D.tile x.1).pts k = V := by
    intro x
    rcases F.hspec x with ⟨k, hk, -⟩ | ⟨hnv, m', -, -, hq, -⟩
    · exact ⟨k, hk⟩
    · exfalso
      have hw : wd (F.p x) (F.q x) = Real.pi := by rw [hq]; exact wd_straight (F.hok x).ne_p
      have hle : wd (F.p x) (F.q x) ≤ ∑ y : AtV D.toRegionDissection V, wd (F.p y) (F.q y) :=
        Finset.single_le_sum (f := fun y => wd (F.p y) (F.q y)) (fun y _ => (wd_pos (F.hok y)).le) (Finset.mem_univ x)
      linarith
  have hcrall : ∀ x : AtV D.toRegionDissection V, 0 < crs (F.p x) (F.q x) :=
    fun x => crs_pos_of_corner (F.hok x) (F.hspec x) (hnostr x)
  have hStrn : Strn D.toRegionDissection V = ∅ := by
    ext j
    simp only [Strn, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false, not_and, not_forall, not_not]
    intro hj
    exact hnostr ⟨j, hj⟩
  have hang := head_angle_sum_gen D idx hidxA F
  have hvirt : ∑ j : Bool, wd (F.pe j) (F.qe j) = Real.pi + (Real.pi - wd pT qT) := by
    rw [Fintype.sum_bool, h1, h2, h3, h4, wd_straight hqT, wd_neg_left hcr]; ring
  rw [hStrn, hvirt] at hang
  simp only [Finset.card_empty, Nat.cast_zero, mul_zero, add_zero] at hang
  rw [Fin.sum_univ_three] at hang
  have hsum' : ((cnt D idx V 0 : ℕ) : ℝ) * D.model.angleAt 0 + (cnt D idx V 1 : ℕ) * D.model.angleAt 1 + (cnt D idx V 2 : ℕ) * D.model.angleAt 2 = wd pT qT := by
    linarith
  -- the polygon angle
  have hθ : P.angle (k + 1) = wd pT qT := by
    obtain ⟨ρ, hρ, hiff⟩ := P.vertex_local_T P.three_le k
    have hN : 0 < N := Fin.pos i0
    have hT1 : (P.locTri P.three_le k).pts 1 = V := rfl
    have hiffD : ∀ y, dist y ((P.locTri P.three_le k).pts 1) < ρ → (y ∈ D.region ↔ y ∈ (P.locTri P.three_le k).carrier) := by
      intro y hy; rw [hreg]; exact hiff y hy
    have hs := sum_localAngle_tri D.toRegionDissection hN (P.locTri P.three_le k) hρ hiffD
    have hwdt := tiles_angle_sum D.toRegionDissection V F.p F.q F.hwd
    have hwdT : wd pT qT = (P.locTri P.three_le k).localAngle V := by
      rw [← hsumT, hwdt]; exact hs
    have hloc : (P.locTri P.three_le k).localAngle V = P.angle (k + 1) := by
      have := Tri.localAngle_vertex (P.locTri P.three_le k) 1
      rw [hT1] at this
      rw [this]
      unfold ConvPoly.angle cornerAngle
      have e1 : k + 1 - 1 = k := by simp
      have e2 : k + 1 + 1 = k + 2 := (ConvPoly.fin_facts P.three_le k).2.2.2.2.2
      rw [e1, e2, EuclideanGeometry.angle_comm (P.v k)]
      rfl
    rw [← hloc, hwdT]
  -- counts
  have hpi := Real.pi_pos
  have hr : ((cnt D idx V 0 : ℕ) : ℝ) = (cnt D idx V 1 : ℕ) := by exact_mod_cast hregc V
  have hN2 : ((2 * cnt D idx V 1 + cnt D idx V 2 : ℕ) : ℝ) * (Real.pi / 3) = wd pT qT := by
    rw [← hsum', hr, hγ]
    have := hαβ
    push_cast
    nlinarith [this]
  have hN2pos : 0 < 2 * cnt D idx V 1 + cnt D idx V 2 := by
    by_contra hz
    have : 2 * cnt D idx V 1 + cnt D idx V 2 = 0 := by omega
    rw [this] at hN2
    simp at hN2; linarith
  have hN2lt : 2 * cnt D idx V 1 + cnt D idx V 2 < 3 := by
    by_contra hz
    push Not at hz
    have : (3 : ℝ) ≤ ((2 * cnt D idx V 1 + cnt D idx V 2 : ℕ) : ℝ) := by exact_mod_cast hz
    nlinarith
  have hang3 : P.angle (k + 1) = ((2 * cnt D idx V 1 + cnt D idx V 2 : ℕ) : ℝ) * (Real.pi / 3) := by rw [hθ, hN2]
  exact ⟨hang3, hN2lt⟩

theorem fin3_add2_ne : ∀ kk : Fin 3, kk + 2 ≠ kk := by decide
theorem fin3_add1_ne : ∀ kk : Fin 3, kk + 1 ≠ kk := by decide

/-- A tile edge of length `c` (distinct from `a`, `b`) starting at a tile corner leaves from an `α`- or `β`-corner. -/
theorem corner_edge_c_idx (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    {j : Fin N} {d : V2} {U U' : Plane} (hS : TriStep (D.tile j) d U U') (hc : dist U U' = slen D 2)
    (hne0 : slen D 0 ≠ slen D 2) (hne1 : slen D 1 ≠ slen D 2) :
    ∃ kk, (D.tile j).pts kk = U ∧ (idx j kk = 0 ∨ idx j kk = 1) := by
  obtain ⟨kk, f, g, hk, hf, hfk, -⟩ := hS
  refine ⟨kk, hk, ?_⟩
  by_contra hn
  push Not at hn
  have h2 : idx j kk = 2 := by
    generalize idx j kk = z at hn
    revert z; decide
  rw [← hk, ← hf] at hc
  rcases fin3_arm kk f hfk with h | h
  · subst h
    rw [side_len_01 D idx hidx] at hc
    have hne : idx j (kk + 2) ≠ idx j kk := fun e => fin3_add2_ne kk ((idx j).injective e)
    rw [h2] at hne
    generalize idx j (kk + 2) = t at hc hne
    fin_cases t
    · exact hne0 hc
    · exact hne1 hc
    · exact hne rfl
  · subst h
    rw [side_len_02 D idx hidx] at hc
    have hne : idx j (kk + 1) ≠ idx j kk := fun e => fin3_add1_ne kk ((idx j).injective e)
    rw [h2] at hne
    generalize idx j (kk + 1) = t at hc hne
    fin_cases t
    · exact hne0 hc
    · exact hne1 hc
    · exact hne rfl

/-- **B2.**  Second branch of B1: if every tile edge of the side walks has length `c`, then (with `γ = π/3`, `{α,β} = {π/6, π/2}`, `a, b` commensurable,
`c` not commensurable with `a`) the polygon is a rational hexagon with all angles `2π/3`: `Concl9`. -/
theorem ivc_rat_all_c_hexagon {N M : ℕ} [NeZero M] (T : PolyTiling N M) (hreg : RegularPQ T.C)
    (hγ : angleAt T.C.model 2 = Real.pi / 3)
    (hαβ : (angleAt T.C.model 0 = Real.pi / 6 ∧ angleAt T.C.model 1 = Real.pi / 2) ∨ (angleAt T.C.model 0 = Real.pi / 2 ∧ angleAt T.C.model 1 = Real.pi / 6))
    (hab : Comm (slen T.C 0) (slen T.C 1)) (hac : ¬ Comm (slen T.C 0) (slen T.C 2))
    (L : Fin M → List (Fin N × Plane × Plane))
    (hW : ∀ i, WalkT T.C.toRegionDissection (toV2 (T.P.e i)) (T.P.v i) (T.P.v (i + 1)) (L i)) (hLne : ∀ i, L i ≠ [])
    (hc : ∀ i, ∀ e ∈ L i, dist e.2.1 e.2.2 = slen T.C 2) : Concl9 T.C T.P := by
  classical
  have hRat := polytiling_rational T hreg hab hac
  obtain ⟨idx, hA, hcnt⟩ := hreg
  haveI : HasFansC T.C.toRegionDissection := hasFansC_poly _ T.P T.region_eq
  have hidx := idx_dist_of_angle T.C idx hA
  have hcnt' : ∀ X, cnt T.C idx X 0 = cnt T.C idx X 1 := fun X => hcnt X
  have hpi := Real.pi_pos
  have hsum2 : T.C.model.angleAt 0 + T.C.model.angleAt 1 = 2 * Real.pi / 3 := by
    show angleAt T.C.model 0 + angleAt T.C.model 1 = _
    rcases hαβ with ⟨h0, h1⟩ | ⟨h0, h1⟩ <;> rw [h0, h1] <;> ring
  have hγ' : T.C.model.angleAt 2 = Real.pi / 3 := hγ
  have hne0 : slen T.C 0 ≠ slen T.C 2 := fun e => hac ⟨1, 1, one_pos, one_pos, by simpa using e⟩
  have hne1 : slen T.C 1 ≠ slen T.C 2 := fun e => hac (RG.comm_trans' hab ⟨1, 1, one_pos, one_pos, by simpa using e⟩)
  have hall : ∀ i : Fin M, T.P.angle i = 2 * Real.pi / 3 := by
    intro i
    have hk : i - 1 + 1 = i := sub_add_cancel i 1
    obtain ⟨hang, hlt⟩ := polygon_angle_cnt T.C T.P T.region_eq idx hA hγ' hsum2 hcnt' (i - 1)
    rw [hk] at hang hlt
    obtain ⟨e, L', hL⟩ : ∃ e L', L i = e :: L' := by
      cases h : L i with
      | nil => exact absurd h (hLne i)
      | cons e L' => exact ⟨e, L', rfl⟩
    have hhead := walkT_head (hL ▸ hW i)
    have hce : dist e.2.1 e.2.2 = slen T.C 2 := hc i e (by rw [hL]; exact List.mem_cons_self)
    obtain ⟨kk, hkk, hid⟩ := corner_edge_c_idx T.C idx hidx hhead.2 hce hne0 hne1
    rw [hhead.1] at hkk
    have h1 : 1 ≤ cnt T.C idx (T.P.v i) 1 := by
      rcases hid with h | h
      · have := cnt_one T.C idx 0 hkk h
        have := hcnt' (T.P.v i)
        omega
      · exact cnt_one T.C idx 1 hkk h
    rw [hang]
    have : 2 * cnt T.C idx (T.P.v i) 1 + cnt T.C idx (T.P.v i) 2 = 2 := by omega
    rw [this]; push_cast; ring
  have hsum := poly_angle_sum T.P
  have hM3 : 3 ≤ M := T.P.three_le
  have hM6 : M = 6 := by
    have e1 : ∑ i, T.P.angle i = ∑ _i : Fin M, 2 * Real.pi / 3 := Finset.sum_congr rfl (fun i _ => hall i)
    rw [hsum] at e1
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at e1
    rw [Nat.cast_sub (by omega)] at e1
    push_cast at e1
    have : (M : ℝ) = 6 := by nlinarith
    exact_mod_cast this
  subst hM6
  exact ⟨rfl, hRat, hall, hγ, hαβ⟩

/-- Non-vacuity control of the hypotheses: `Concl9` needs `γ = π/3`; with `γ = π/3` and `α, β = π/6, π/2` the angle sum hypothesis used above holds. -/
theorem ivc_rat_all_c_angle_sum : Real.pi / 6 + Real.pi / 2 = 2 * Real.pi / 3 := by ring

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.polygon_angle_cnt
#print axioms Erdos634.Draft.LaczFormal.RG.ivc_rat_all_c_hexagon
