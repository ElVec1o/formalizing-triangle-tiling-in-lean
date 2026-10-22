-- Draft/LaczFormalIIcWN70.lean -- Laczkovich (DCG 48 (2012), Sect. 6.3), Lemma 6.2, item (T1): the TURN of every vertex of a closed Gamma_kite chain.
-- For a closed injective chain `C` of Gamma_kite (cycle of the graph) the polygon `toC o C` has `extAng k in {gamma, 0, -gamma}` at every vertex (`gamma` = model angle 2), and
-- `sigma * extAng k in {gamma, -gamma, 0}` for `sigma = +-1`: exactly the field `turn` of `KiteLayer` (WN67).  Pure export of `hk` inside `gkite_cycle_count` (WN29) using `gkite_ratio` (WN29, `gkite_turn` WN28).
-- NOTE, UNAUDITED.  Hypotheses: Case IIc block + AngGen + a closed injective Gamma_kite chain (NOT witnessed).  Credit: Laczkovich (DCG 48 (2012), Sect. 6.2/6.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcWN29

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ}

/-- **T1**: every vertex of a closed injective Gamma_kite chain turns by `gamma`, `0` or `-gamma`. -/
theorem gkite_cycle_turn [NeZero N] [NeZero M] (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hC : CaseC D idx)
    (h1 : D.model.angleAt 2 < Real.pi / 2) (h3 : D.model.angleAt 2 ≠ Real.pi / 3) (G : AngGen (fun l => D.model.angleAt l))
    {m : ℕ} [NeZero m] (C : Fin m → Plane) (hCy : ∀ k : Fin m, GKite D idx (C k) (C (k + 1))) (hinj : Function.Injective C) :
    ∀ k : Fin m, Erdos634.Draft.LaczFormal.WN.extAng (fun k => Erdos634.Draft.LaczFormal.WN.toC (C k)) k = D.model.angleAt 2 ∨
      Erdos634.Draft.LaczFormal.WN.extAng (fun k => Erdos634.Draft.LaczFormal.WN.toC (C k)) k = 0 ∨
      Erdos634.Draft.LaczFormal.WN.extAng (fun k => Erdos634.Draft.LaczFormal.WN.toC (C k)) k = -D.model.angleAt 2 := by
  intro k
  have hXY : GKite D idx (C (k - 1)) (C k) := by simpa using hCy (k - 1)
  obtain ⟨t, ht, hr⟩ := gkite_ratio D P hreg idx hC h1 h3 G hXY (hCy k)
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
  have : t = 0 ∨ t = 1 ∨ t = 2 := by omega
  rcases this with rfl | rfl | rfl
  · right; right; norm_num
  · right; left; norm_num
  · left; norm_num

/-- The form used by `KiteLayer.turn`: for a sign `sigma = +-1`, `sigma * extAng in {gamma, -gamma, 0}`. -/
theorem gkite_cycle_turn_sigma [NeZero N] [NeZero M] (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hC : CaseC D idx)
    (h1 : D.model.angleAt 2 < Real.pi / 2) (h3 : D.model.angleAt 2 ≠ Real.pi / 3) (G : AngGen (fun l => D.model.angleAt l))
    {m : ℕ} [NeZero m] (C : Fin m → Plane) (hCy : ∀ k : Fin m, GKite D idx (C k) (C (k + 1))) (hinj : Function.Injective C)
    {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (k : Fin m) :
    σ * Erdos634.Draft.LaczFormal.WN.extAng (fun k => Erdos634.Draft.LaczFormal.WN.toC (C k)) k = D.model.angleAt 2 ∨
      σ * Erdos634.Draft.LaczFormal.WN.extAng (fun k => Erdos634.Draft.LaczFormal.WN.toC (C k)) k = -D.model.angleAt 2 ∨
      σ * Erdos634.Draft.LaczFormal.WN.extAng (fun k => Erdos634.Draft.LaczFormal.WN.toC (C k)) k = 0 := by
  rcases gkite_cycle_turn D P hreg idx hC h1 h3 G C hCy hinj k with h | h | h <;> rcases hσ with rfl | rfl <;> rw [h] <;> simp

#print axioms gkite_cycle_turn
#print axioms gkite_cycle_turn_sigma

end Erdos634.Draft.LaczFormal.RG
