-- Draft/LaczFormalIIcWN87.lean -- Laczkovich (DCG 48 (2012), Sect. 6.2, Fig. 5), the FAN LEMMA `StraightAt <-> turn 0`.
-- (a) `gkite_straight_bwd`: if `Z - Y = Y - X` for consecutive Gamma_kite edges then a straight line of tile sides passes through `Y` (`StraightAt D Y`): the two tiles of `XY` flank the ray `YX`, the tile of `YZ` starts along `Y - X`.
-- (b) `gkite_straight_iff`: `StraightAt D Y <-> toC Z - toC Y = toC Y - toC X` (with the forward half WN86).
-- (c) `gkite_cycle_straight_iff`: for a closed injective Gamma_kite chain `C`, `StraightAt D (C k) <-> extAng (toC o C) k = 0`.
-- NOTE, UNAUDITED.  Hypotheses: the Case IIc block + `AngGen`.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.2, Fig. 5), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcWN86
import Erdos634.Draft.LaczFormalIIcWN70

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ}

theorem toV2_inj {a b : Plane} (h : toV2 a = toV2 b) : a = b := by
  have h0 : a 0 = b 0 := congrArg Prod.fst h
  have h1 : a 1 = b 1 := congrArg Prod.snd h
  ext i; fin_cases i
  · exact h0
  · exact h1

theorem toV2_eq_iff_toC (A B C' D' : Plane) :
    toV2 (A - B) = toV2 (C' - D') ↔
      Erdos634.Draft.LaczFormal.WN.toC A - Erdos634.Draft.LaczFormal.WN.toC B = Erdos634.Draft.LaczFormal.WN.toC C' - Erdos634.Draft.LaczFormal.WN.toC D' := by
  constructor
  · intro h
    have := toV2_inj h
    rw [← toC_sub A B, ← toC_sub C' D', this]
  · intro h
    rw [← toC_sub A B, ← toC_sub C' D'] at h
    rw [Erdos634.Draft.LaczFormal.WN.toC.injective h]

theorem gkite_straight_bwd (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) {X Y Z : Plane}
    (hXY : GKite D idx X Y) (hYZ : GKite D idx Y Z) (h : toV2 (Z - Y) = toV2 (Y - X)) : StraightAt D Y := by
  obtain ⟨i, j, d, kk, f, kk', f', hij, hSi, hSj, -⟩ := hXY
  obtain ⟨i', j', d', kk2, f2, kk2', f2', hij2, hSi2, hSj2, -⟩ := hYZ
  have hYX : Par (toV2 (Y - X)) d := by
    obtain ⟨-, -, -, -, -, -, -, -, hp, -⟩ := hSi; exact hp
  have hZ : Par (toV2 (Z - Y)) d' := by
    obtain ⟨-, -, -, -, -, -, -, -, hp, -⟩ := hSi2; exact hp
  rw [h] at hZ
  have hdd : Par d d' := hYX.symm.trans hZ
  exact ⟨d, X, X, Z, i, j, i', hSi, hSj, TriStep.of_par hdd hSi2⟩

set_option maxHeartbeats 6400000 in
theorem gkite_straight_iff [NeZero M] (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hC : CaseC D idx) (h1 : D.model.angleAt 2 < Real.pi / 2) (h3 : D.model.angleAt 2 ≠ Real.pi / 3)
    (G : AngGen (fun l => D.model.angleAt l)) {X Y Z : Plane} (hXY : GKite D idx X Y) (hYZ : GKite D idx Y Z) :
    StraightAt D Y ↔ Erdos634.Draft.LaczFormal.WN.toC Z - Erdos634.Draft.LaczFormal.WN.toC Y =
      Erdos634.Draft.LaczFormal.WN.toC Y - Erdos634.Draft.LaczFormal.WN.toC X := by
  rw [← toV2_eq_iff_toC]
  exact ⟨gkite_straight_fwd D P hreg idx hC h1 h3 G hXY hYZ, gkite_straight_bwd D idx hXY hYZ⟩

set_option maxHeartbeats 6400000 in
/-- **Fan lemma**: along a closed injective Gamma_kite chain, a vertex has a straight line of tile sides iff the polygon has turn `0` there. -/
theorem gkite_cycle_straight_iff [NeZero N] [NeZero M] (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hC : CaseC D idx) (h1 : D.model.angleAt 2 < Real.pi / 2) (h3 : D.model.angleAt 2 ≠ Real.pi / 3)
    (G : AngGen (fun l => D.model.angleAt l)) {m : ℕ} [NeZero m] (C : Fin m → Plane) (hCy : ∀ k : Fin m, GKite D idx (C k) (C (k + 1)))
    (k : Fin m) :
    StraightAt D (C k) ↔ Erdos634.Draft.LaczFormal.WN.extAng (fun k => Erdos634.Draft.LaczFormal.WN.toC (C k)) k = 0 := by
  have hXY : GKite D idx (C (k - 1)) (C k) := by simpa using hCy (k - 1)
  have hYZ := hCy k
  rw [gkite_straight_iff D P hreg idx hC h1 h3 G hXY hYZ]
  obtain ⟨t, ht, hr⟩ := gkite_ratio D P hreg idx hC h1 h3 G hXY hYZ
  have hne : Erdos634.Draft.LaczFormal.WN.toC (C k) - Erdos634.Draft.LaczFormal.WN.toC (C (k - 1)) ≠ 0 := by
    intro h
    have := Erdos634.Draft.LaczFormal.WN.toC.injective (sub_eq_zero.1 h)
    exact gkite_ne D idx hXY this.symm
  have hγ0 : 0 < D.model.angleAt 2 := G.pos 2
  have hpi := Real.pi_pos
  have hext : Erdos634.Draft.LaczFormal.WN.extAng (fun k => Erdos634.Draft.LaczFormal.WN.toC (C k)) k = ((t : ℝ) - 1) * D.model.angleAt 2 := by
    unfold Erdos634.Draft.LaczFormal.WN.extAng
    simp only
    rw [hr]
    apply arg_exp_real_mul_I
    have ht' : (t : ℝ) ≤ 2 := by exact_mod_cast ht
    have ht0 : (0 : ℝ) ≤ t := Nat.cast_nonneg t
    constructor <;> nlinarith
  rw [hext]
  constructor
  · intro h
    have h' : (Erdos634.Draft.LaczFormal.WN.toC (C (k + 1)) - Erdos634.Draft.LaczFormal.WN.toC (C k)) /
        (Erdos634.Draft.LaczFormal.WN.toC (C k) - Erdos634.Draft.LaczFormal.WN.toC (C (k - 1))) = 1 := by
      rw [h]; exact div_self hne
    rw [hr] at h'
    have : ((t : ℝ) - 1) * D.model.angleAt 2 = 0 := by
      have e := congrArg Complex.arg h'
      rw [Complex.arg_one] at e
      have ht' : (t : ℝ) ≤ 2 := by exact_mod_cast ht
      have ht0 : (0 : ℝ) ≤ t := Nat.cast_nonneg t
      rw [arg_exp_real_mul_I (by constructor <;> nlinarith)] at e
      exact e
    exact this
  · intro h
    have hx : ((t : ℝ) - 1) = 0 := by
      rcases mul_eq_zero.1 h with h | h
      · exact h
      · exact absurd h hγ0.ne'
    have h' : (Erdos634.Draft.LaczFormal.WN.toC (C (k + 1)) - Erdos634.Draft.LaczFormal.WN.toC (C k)) /
        (Erdos634.Draft.LaczFormal.WN.toC (C k) - Erdos634.Draft.LaczFormal.WN.toC (C (k - 1))) = 1 := by
      rw [hr, hx]; simp
    exact (div_eq_one_iff_eq hne).1 h'

#print axioms gkite_straight_iff
#print axioms gkite_cycle_straight_iff

end Erdos634.Draft.LaczFormal.RG
