-- Draft/LaczFormalIIcSpoke5.lean -- Laczkovich (DCG 48 (2012)), Sect. 6.3, step 3: `spokes_angle`.
-- Case IIc with every corner of type (1,1,0) (P = N), every exceptional vertex interior (the conclusion of S7 `gexc_exc_interior_exact`), and an edge `GExc (P.v j) (W j)` at every corner.  Then there are labels {a, b} = {0, 1} such that for ALL k
--   angle (v_{k+2}) (v_{k+1}) (W_{k+1}) = model angle a  (alpha at the START of a side)   and   angle (v_k) (v_{k+1}) (W_{k+1}) = model angle b  (beta at the END of a side),
-- the same (a, b) at every corner (no swapping from corner to corner).
-- Route: item (c) `gexc_spoke_angles` gives the labels of the two boundary tiles at each corner; `corner_out_c` makes the outgoing boundary step a c-step, so the head label of the first tile of the side is the other of {0,1};
-- `side_labels_propagate` (the body of `edge_multiple_c`, needs normal interior vertices, which follow from interiority of the exceptional vertices) carries (a at the tail, b at the head) to the last tile of the side, which is the incoming
-- tile of the next corner; there the two labels differ and are not gamma, so the outgoing label of the next corner equals a.
-- NOTE, UNAUDITED.  The global hypothesis block is that of `gexc_matching` (Case IIc, P = N); satisfiability is witnessed by GenWitK (204-tile octagon, genTiling_thm21) and IsoWitM (WITNESS_IIC_2026-10-22.md).  Credit: Laczkovich (DCG 48 (2012), Sect. 6.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcSpoke4

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ}

theorem fin3_lab_triple : ∀ x y z : Fin 3, x ≠ 2 → y ≠ 2 → z ≠ 2 → x ≠ y → z ≠ y → z = x := by decide
theorem fin3_lab_pair : ∀ x y : Fin 3, x ≠ 2 → y ≠ 2 → x ≠ y → (x = 0 ∧ y = 1) ∨ (x = 1 ∧ y = 0) := by decide
theorem fin3_lab_other : ∀ a x : Fin 3, a ≠ 2 → x ≠ 2 → x ≠ a → x = (if a = 0 then 1 else 0) := by decide

set_option maxHeartbeats 6400000 in
/-- **`spokes_angle`** (Lemma 6.3, step 3). -/
theorem spokes_angle [NeZero M] (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hC : CaseC D idx) (h1 : D.model.angleAt 2 < Real.pi / 2) (h3 : D.model.angleAt 2 ≠ Real.pi / 3)
    (hcor : ∀ j : Fin M, cnt D idx (P.v j) 0 = 1 ∧ cnt D idx (P.v j) 1 = 1 ∧ cnt D idx (P.v j) 2 = 0)
    (hint : ∀ E ∈ excVerts2 D idx P, E ∈ interior D.region) (W : Fin M → Plane) (hW : ∀ j, GExc D idx (P.v j) (W j)) :
    ∃ a b : Fin 3, ((a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0)) ∧ ∀ k : Fin M,
      EuclideanGeometry.angle (P.v (k + 1 + 1)) (P.v (k + 1)) (W (k + 1)) = D.model.angleAt a ∧
      EuclideanGeometry.angle (P.v k) (P.v (k + 1)) (W (k + 1)) = D.model.angleAt b := by
  classical
  have hdat := fun k : Fin M => gexc_spoke_angles D P hreg idx hC k (hcor (k + 1)).1 (hcor (k + 1)).2.1 (hcor (k + 1)).2.2 (hW (k + 1))
  choose jx jy kx ky Uo Ui hSo hSi hkx hky hlx hly hne hWne hax hay using hdat
  have hnorm : ∀ i : Fin M, NormSide D idx P i := by
    intro i
    apply normSide_of_good D P hreg idx hC h1 h3 i
    rintro ⟨X, hX, t, ht0, ht1, hXt⟩
    have := hint X hX
    rw [hreg, hXt] at this
    exact not_interior_of_c_zero P (c_on_edge P i t) this
  choose L e0 el hWk hh hl hs1 hs2 hT0 hT1 using edge_data D P hreg
  have hout := corner_out_c D P hreg idx hC h1 h3 hcor
  -- label chain: the outgoing label of corner k+1 is the outgoing label of corner k+2, and the incoming label of corner k+2 is the head label
  have key : ∀ k : Fin M, idx (jx (k + 1)) (kx (k + 1)) = idx (jx k) (kx k) ∧ idx (jy (k + 1)) (ky (k + 1)) ≠ idx (jx k) (kx k) := by
    intro k
    have hSo0 : TriStep (D.tile (e0 (k + 1)).1) (toV2 (P.e (k + 1))) (P.v (k + 1)) (e0 (k + 1)).2.2 := by
      rw [← hs1 (k + 1)]; exact hT0 (k + 1)
    obtain ⟨hj, hU⟩ := left_step_unique D.toRegionDissection hSo0 (hSo k)
    -- the head label of the first tile
    obtain ⟨kk, f, g, hk0, hf0, hfk, hgk, hgf, -⟩ := id (hSo k)
    have hkk : kk = kx k := (D.tile (jx k)).indep.injective (hk0.trans (hkx k).symm)
    subst hkk
    have hdist := hout (k + 1) (jx k) (Uo k) (hSo k)
    have hbne : idx (jx k) f ≠ 2 := by
      intro e
      apply step_dist_ne_c D idx hC (p := kx k) (q := f) (Ne.symm hfk) (Or.inr e)
      rw [hk0, hf0]; exact hdist
    have hab := fin3_lab_pair _ _ (hlx k) hbne (fun e => hfk ((idx (jx k)).injective e).symm)
    have h0 : TyAt D idx (e0 (k + 1)).1 (e0 (k + 1)).2.1 (idx (jx k) (kx k)) ∧ TyAt D idx (e0 (k + 1)).1 (e0 (k + 1)).2.2 (idx (jx k) f) := by
      constructor
      · intro kk' hkk'
        rw [hj] at hkk' ⊢
        rw [hs1] at hkk'
        have : kk' = kx k := (D.tile (jx k)).indep.injective (hkk'.trans (hkx k).symm)
        rw [this]
      · intro kk' hkk'
        rw [hj] at hkk' ⊢
        rw [hU] at hkk'
        have : kk' = f := (D.tile (jx k)).indep.injective (hkk'.trans hf0.symm)
        rw [this]
    have hall := side_labels_propagate D P hreg idx hC (k + 1) (hnorm (k + 1)) (hWk (k + 1)) (hh (k + 1)) hab h0 (el (k + 1)) (List.mem_of_getLast? (hl (k + 1)))
    -- the last tile of the side is the incoming tile of the corner k+2
    have hSi1 : TriStep (D.tile (jy (k + 1))) (neg2 (neg2 (toV2 (P.e (k + 1))))) (Ui (k + 1)) (P.v (k + 1 + 1)) := by
      rw [neg2_neg2']; exact hSi (k + 1)
    have hTl : TriStep (D.tile (el (k + 1)).1) (neg2 (neg2 (toV2 (P.e (k + 1))))) (el (k + 1)).2.1 (P.v (k + 1 + 1)) := by
      rw [neg2_neg2', ← hs2 (k + 1)]; exact hT1 (k + 1)
    obtain ⟨hj2, -⟩ := right_step_unique D.toRegionDissection hTl hSi1
    have hlb : idx (jy (k + 1)) (ky (k + 1)) = idx (jx k) f := by
      have := hall.2 (ky (k + 1))
      rw [hj2] at this
      rw [hs2 (k + 1)] at this
      exact this (hky (k + 1))
    refine ⟨?_, ?_⟩
    · exact fin3_lab_triple _ _ _ (hlx k) hbne (hlx (k + 1)) (fun e => hfk ((idx (jx k)).injective e).symm) (by rw [← hlb]; exact hne (k + 1))
    · rw [hlb]; exact fun e => hfk ((idx (jx k)).injective e)
  have hconst : ∀ n : ℕ, idx (jx (n : Fin M)) (kx (n : Fin M)) = idx (jx 0) (kx 0) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [Nat.cast_succ]; exact (key _).1.trans ih
  have ha2 := hlx 0
  have hk : ∀ k : Fin M, idx (jx k) (kx k) = idx (jx 0) (kx 0) := by
    intro k
    have := hconst k.val
    rwa [Fin.cast_val_eq_self] at this
  have hab' : ∀ a : Fin 3, a ≠ 2 → (a = 0 ∧ (if a = 0 then (1 : Fin 3) else 0) = 1) ∨ (a = 1 ∧ (if a = 0 then (1 : Fin 3) else 0) = 0) := by decide
  refine ⟨idx (jx 0) (kx 0), if idx (jx 0) (kx 0) = 0 then 1 else 0, hab' _ ha2, fun k => ⟨?_, ?_⟩⟩
  · rw [hax k, hk k]
  · rw [hay k]
    congr 1
    apply fin3_lab_other _ _ ha2 (hly k)
    intro e
    exact hne k (by rw [hk k]; exact e.symm)

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.spokes_angle
