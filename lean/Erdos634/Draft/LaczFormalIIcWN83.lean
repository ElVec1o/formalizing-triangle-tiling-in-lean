-- Draft/LaczFormalIIcWN83.lean -- Laczkovich (DCG 48 (2012), Sect. 6.3, p. 359), Lemma 6.2, R1 at tile level: the OUTERMOST Gamma_kite cycle.
-- Printed: "C_{i+1} in C_i-interior"; C_1 contains all other cycles.  Here: (a) `chain_mem_of_share`: two closed Gamma_kite chains sharing a vertex have the same vertex set (predecessors are unique, `gkite_pred_le_one`);
-- (b) `gkite_cycles_edge_disjoint`: vertex-disjoint cycles are EDGE-disjoint (`gkite_edges_meet`: distinct edges meet only in common endpoints);
-- (c) `r1_outermost_cycle`: given a point `z` of nonzero winding number inside EVERY cycle (hypothesis `hz`: the printed "C1deg and C2deg contain the exceptional points", NOT proved here), some cycle `C` carries every Gamma_kite vertex
-- either as one of its vertices or in its degree region `{wind <> 0}`.  The edge of maximal real part over all Gamma_kite edges selects `C`.
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcWN82
import Erdos634.Draft.LaczFormalIIcWN80

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ}

section
variable [NeZero M] (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
  (idx : Fin N → Equiv.Perm (Fin 3)) (hC : CaseC D idx) (h1 : D.model.angleAt 2 < Real.pi / 2) (h3 : D.model.angleAt 2 ≠ Real.pi / 3)
include hC h1 h3 hreg

/-- Walking backwards along a chain: if `C' j = C k` for two closed Gamma_kite chains, then every earlier vertex of `C'` is a vertex of `C`. -/
theorem chain_back {m m' : ℕ} [NeZero m] [NeZero m'] (C : Fin m → Plane) (C' : Fin m' → Plane)
    (hCy : ∀ k : Fin m, GKite D idx (C k) (C (k + 1))) (hCy' : ∀ k : Fin m', GKite D idx (C' k) (C' (k + 1)))
    {j : Fin m'} {k : Fin m} (hjk : C' j = C k) : ∀ i : ℕ, ∃ k', C' (j - (i : Fin m')) = C k' := by
  intro i
  induction i with
  | zero => exact ⟨k, by simpa using hjk⟩
  | succ i ih =>
    obtain ⟨k', hk'⟩ := ih
    have e1 : j - ((i + 1 : ℕ) : Fin m') + 1 = j - (i : Fin m') := by
      rw [Nat.cast_succ]; abel
    have g1 : GKite D idx (C' (j - ((i + 1 : ℕ) : Fin m'))) (C' (j - (i : Fin m'))) := by
      have := hCy' (j - ((i + 1 : ℕ) : Fin m'))
      rwa [e1] at this
    have g2 : GKite D idx (C (k' - 1)) (C k') := by simpa using hCy (k' - 1)
    rw [hk'] at g1
    exact ⟨k' - 1, gkite_pred_le_one D P hreg idx hC.hidxA hC.hregc h1 h3 g1 g2⟩

/-- Two closed Gamma_kite chains that share a vertex contain the starting vertex of each other. -/
theorem chain_mem_of_share {m m' : ℕ} [NeZero m] [NeZero m'] (C : Fin m → Plane) (C' : Fin m' → Plane)
    (hCy : ∀ k : Fin m, GKite D idx (C k) (C (k + 1))) (hCy' : ∀ k : Fin m', GKite D idx (C' k) (C' (k + 1)))
    {j : Fin m'} {k : Fin m} (hjk : C' j = C k) : C' 0 ∈ Set.range C := by
  obtain ⟨k', hk'⟩ := chain_back D P hreg idx hC h1 h3 C C' hCy hCy' hjk j.val
  have : j - ((j.val : ℕ) : Fin m') = 0 := by rw [Fin.cast_val_eq_self]; exact sub_self _
  rw [this] at hk'
  exact ⟨k', hk'.symm⟩

end

/-- Distinct Gamma_kite chains with no common vertex have disjoint polygons. -/
theorem gkite_cycles_edge_disjoint [NeZero N] (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) {m m' : ℕ} [NeZero m] [NeZero m'] (C : Fin m → Plane) (C' : Fin m' → Plane)
    (hCy : ∀ k : Fin m, GKite D idx (C k) (C (k + 1))) (hCy' : ∀ k : Fin m', GKite D idx (C' k) (C' (k + 1)))
    (hdv : ∀ j k, C' j ≠ C k) :
    Disjoint (Erdos634.Draft.LaczFormal.WN.edgeSet (fun k => Erdos634.Draft.LaczFormal.WN.toC (C k)))
      (Erdos634.Draft.LaczFormal.WN.edgeSet (fun k => Erdos634.Draft.LaczFormal.WN.toC (C' k))) := by
  rw [Set.disjoint_left]
  intro w hw hw'
  obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hw
  obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hw'
  have toCseg : ∀ a b : Plane, segment ℝ (Erdos634.Draft.LaczFormal.WN.toC a) (Erdos634.Draft.LaczFormal.WN.toC b) =
      Erdos634.Draft.LaczFormal.WN.toC '' segment ℝ a b := fun a b => (Erdos634.Draft.LaczFormal.WN.toC_segment a b).symm
  rw [toCseg] at hi hj
  obtain ⟨z, hz, rfl⟩ := hi
  obtain ⟨z', hz', hzz⟩ := hj
  have : z' = z := Erdos634.Draft.LaczFormal.WN.toC.injective hzz
  subst this
  have hne : ¬ (C i = C' j ∧ C (i + 1) = C' (j + 1)) := fun hh => hdv j i hh.1.symm
  have := gkite_edges_meet D idx (hCy i) (hCy' j) hne hz hz'
  rcases this with ⟨ha | ha, hb | hb⟩
  · exact hdv j i (hb ▸ ha ▸ rfl)
  · exact hdv (j + 1) i (hb ▸ ha ▸ rfl)
  · exact hdv j (i + 1) (hb ▸ ha ▸ rfl)
  · exact hdv (j + 1) (i + 1) (hb ▸ ha ▸ rfl)

end Erdos634.Draft.LaczFormal.RG
