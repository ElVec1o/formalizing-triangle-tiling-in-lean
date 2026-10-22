-- Draft/LaczFormalIIcWN75.lean -- Laczkovich (DCG 48 (2012), Sect. 6.3), Lemma 6.2, item (6)(a): CYCLE EXISTENCE.
-- Every edge `X Y` of Gamma_kite lies on a CLOSED INJECTIVE chain `C : Fin m -> Plane` of Gamma_kite edges (`GKite (C k) (C (k+1))`, `C 0 = X`): the successor map on the finite set of tails is
-- injective (`gkite_pred_le_one`) with `GKite X (f X)` (`gkite_succ_unique`), hence every point is periodic; `C k = f^[k] X`, `m` the minimal period.
-- Printed: "Therefore, Gamma_kite is the union of disjoint cycles" (Laczkovich p. 357).  `3 <= m` and simplicity then follow from `gkite_cycle_simple` (WN18).
-- NOTE, UNAUDITED.  Hypotheses: Case IIc block (not witnessed).  Credit: Laczkovich (DCG 48 (2012), Sect. 6.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalRG12GKiteEx
import Erdos634.Draft.LaczFormalIIcWN18

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ}

theorem fin_succ_val {m : ℕ} [NeZero m] (k : Fin m) (h : k.val + 1 < m) : (k + 1 : Fin m).val = k.val + 1 := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by have := NeZero.pos m; omega⟩
  exact Fin.val_add_one_of_lt (by rw [Fin.lt_iff_val_lt_val]; simpa using h)

theorem fin_succ_wrap {m : ℕ} [NeZero m] (k : Fin m) (h : k.val + 1 = m) : (k + 1 : Fin m) = 0 := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by have := NeZero.pos m; omega⟩
  have : k = Fin.last m' := Fin.ext (by simpa using (by omega : k.val = m'))
  rw [this]
  exact Fin.last_add_one m'

theorem gkite_cycle_exists [NeZero M] (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hC : CaseC D idx) (hab : Comm (slen D 0) (slen D 1)) (hac : ¬ Comm (slen D 0) (slen D 2))
    (h1 : D.model.angleAt 2 < Real.pi / 2) (h3 : D.model.angleAt 2 ≠ Real.pi / 3) {X Y : Plane} (h : GKite D idx X Y) :
    ∃ (m : ℕ) (_ : NeZero m) (C : Fin m → Plane), C 0 = X ∧ Function.Injective C ∧ ∀ k : Fin m, GKite D idx (C k) (C (k + 1)) := by
  classical
  set K : Set Plane := {X : Plane | ∃ Y, GKite D idx X Y} with hK
  haveI : Finite K := (gkite_tails_finite D idx).to_subtype
  have hex : ∀ X : K, ∃ Y : K, GKite D idx X.1 Y.1 := fun X => by
    obtain ⟨Y, hY⟩ := X.2
    obtain ⟨Z, hZ⟩ := gkite_succ_exists D P hreg idx hC hab hac h1 h3 hY
    exact ⟨⟨Y, Z, hZ⟩, hY⟩
  choose f hf using hex
  have hinj : Function.Injective f := fun a b e => by
    apply Subtype.ext
    have h1' := hf a
    have h2' := hf b
    rw [e] at h1'
    exact gkite_pred_le_one D P hreg idx hC.hidxA hC.hregc h1 h3 h1' h2'
  set x0 : K := ⟨X, Y, h⟩ with hx0
  have hper : x0 ∈ Function.periodicPts f := hinj.mem_periodicPts x0
  set m := Function.minimalPeriod f x0 with hm
  have hmpos : 0 < m := Function.minimalPeriod_pos_of_mem_periodicPts hper
  haveI : NeZero m := ⟨hmpos.ne'⟩
  refine ⟨m, inferInstance, fun k => (f^[k.val] x0).1, rfl, ?_, ?_⟩
  · intro a b hab'
    have h1' : f^[a.val] x0 = f^[b.val] x0 := Subtype.ext hab'
    have := Function.iterate_injOn_Iio_minimalPeriod (f := f) (x := x0) (show a.val ∈ Set.Iio m from a.isLt) (show b.val ∈ Set.Iio m from b.isLt) h1'
    exact Fin.ext this
  · intro k
    by_cases hk : k.val + 1 < m
    · have e := fin_succ_val k hk
      simp only [e, Function.iterate_succ_apply']
      exact hf _
    · have h' : k.val + 1 = m := by have := k.isLt; omega
      have e := fin_succ_wrap k h'
      rw [e]
      have hp : f^[m] x0 = x0 := Function.isPeriodicPt_minimalPeriod f x0
      have := hf (f^[k.val] x0)
      rw [← Function.iterate_succ_apply' f k.val x0] at this
      have e2 : f^[k.val.succ] x0 = x0 := by rw [Nat.succ_eq_add_one, h']; exact hp
      rw [e2] at this
      simpa using this

#print axioms gkite_cycle_exists

end Erdos634.Draft.LaczFormal.RG
