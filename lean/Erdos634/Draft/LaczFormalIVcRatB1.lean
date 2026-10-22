-- Draft/LaczFormalIVcRatB1.lean -- Laczkovich DCG 48 (2012), Sect. 8.3 (Subcase IVc, rational branch), BLUEPRINT Part B, item B1.
--   Printed gap P1 (l.1990 ignores tiles whose c-side lies on bd A).  Repair, at EDGE level (not only side lengths):
--   `ivc_rat_boundary_c_dichotomy`: for a regular polygon tiling with a, b commensurable and c not commensurable with a, there is a decomposition
--   of every side of A into tile edges (a `WalkT`, nonempty) such that EITHER no tile edge on bd A has length c, OR every tile edge on bd A has length c.
--   This is the walk form of Lemma 4.7 (`polygon_sides_alike`, same proof, the edge statuses are exported instead of being summed to lengths).
--   DEVIATION from the blueprint text: stated for tile edges of the side walks (what B2, B6 and the bridge consume), and with NO hypothesis on gamma, alpha,
--   M (the argument does not use them; the blueprint's list of IVc hypotheses is a superset).  Hypotheses are those of `polytiling_rational`.
--   `ivc_rat_boundary_c_dichotomy_lengths` : the length form (all sides positive multiples of c, or all sides n_a a + n_b b), as a corollary.
--   Witness: the hypotheses (regular, Comm a b, not Comm a c) are the ones of `ivc_rat_witness`/`ivc_final_ge5`; the hexagon of Part B P6 satisfies them (not rebuilt here).
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Lemma 4.7, Sect. 8.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalRG5GammaC

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ} [NeZero M]

theorem sides_edge_dichotomy (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (idx : Fin N → Equiv.Perm (Fin 3)) (h : CaseC D idx)
    (P : ConvPoly M) (hreg : D.region = P.carrier) :
    ∃ L : Fin M → List (Fin N × Plane × Plane),
      (∀ i, WalkT D.toRegionDissection (toV2 (P.e i)) (P.v i) (P.v (i + 1)) (L i)) ∧ (∀ i, L i ≠ []) ∧
      ((∀ i, ∀ e ∈ L i, dist e.2.1 e.2.2 = slen D 2) ∨ (∀ i, ∀ e ∈ L i, dist e.2.1 e.2.2 ≠ slen D 2)) := by
  classical
  have hG := h.caseG
  set D' := relabelC D with hD'
  set idx' := relabelCIdx idx with hidx'
  haveI : HasFansC D'.toRegionDissection := (inferInstance : HasFansC D.toRegionDissection)
  have hD'0 : slen D' 0 = slen D 2 := relabelC_slen0 D
  have hed := edge_data D P hreg
  choose L e0 el hW hh hl hs1 hs2 hT0 hT1 using hed
  have hU : ∀ i, ∃ s : ℝ, 0 ≤ s ∧ toV2 (P.v i - P.v i) = (s * (toV2 (P.e i)).1, s * (toV2 (P.e i)).2) :=
    fun i => ⟨0, le_rfl, by unfold toV2; ext <;> simp⟩
  have hchain : ∀ i, ∀ e ∈ L i, (dist e.2.1 e.2.2 = slen D 2 ↔ dist (e0 i).2.1 (e0 i).2.2 = slen D 2) := by
    intro i e he
    have := walk_status_chain D' idx' hG P hreg i rfl (hW i) (hU i) (e0 i) (hh i) e he
    rwa [hD'0] at this
  have hlast : ∀ i, (dist (el i).2.1 (el i).2.2 = slen D 2 ↔ dist (e0 i).2.1 (e0 i).2.2 = slen D 2) := by
    intro i
    exact hchain i (el i) (List.mem_of_getLast? (hl i))
  have hstep : ∀ k : Fin M, (dist (e0 (k + 1)).2.1 (e0 (k + 1)).2.2 = slen D 2 ↔ dist (e0 k).2.1 (e0 k).2.2 = slen D 2) := by
    intro k
    have hSo : TriStep (D.tile (e0 (k + 1)).1) (toV2 (P.e (k + 1))) (P.v (k + 1)) (e0 (k + 1)).2.2 := by
      have := hT0 (k + 1); rwa [hs1 (k + 1)] at this
    have hSi : TriStep (D.tile (el k).1) (toV2 (P.e k)) (el k).2.1 (P.v (k + 1)) := by
      have := hT1 k; rwa [hs2 k] at this
    have := corner_c_status D idx h P hreg k _ _ _ _ hSo hSi
    have hA : dist (e0 (k + 1)).2.1 (e0 (k + 1)).2.2 = dist (P.v (k + 1)) (e0 (k + 1)).2.2 := by rw [hs1]
    have hB : dist (el k).2.1 (el k).2.2 = dist (el k).2.1 (P.v (k + 1)) := by rw [hs2]
    rw [hA]
    exact this.trans (by rw [← hB]; exact hlast k)
  have hall : ∀ n : ℕ, (dist (e0 (n : Fin M)).2.1 (e0 (n : Fin M)).2.2 = slen D 2 ↔ dist (e0 0).2.1 (e0 0).2.2 = slen D 2) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have := hstep (n : Fin M)
      rw [Nat.cast_succ]
      exact this.trans ih
  have hall' : ∀ i : Fin M, (dist (e0 i).2.1 (e0 i).2.2 = slen D 2 ↔ dist (e0 0).2.1 (e0 0).2.2 = slen D 2) := by
    intro i
    have := hall i.val
    rwa [Fin.cast_val_eq_self] at this
  refine ⟨L, hW, fun i hL0 => ?_, ?_⟩
  · have := hh i
    rw [hL0] at this; simp at this
  · by_cases hc0 : dist (e0 0).2.1 (e0 0).2.2 = slen D 2
    · left
      intro i e he
      exact (hchain i e he).mpr ((hall' i).mpr hc0)
    · right
      intro i e he hh'
      exact hc0 ((hall' i).mp ((hchain i e he).mp hh'))

/-- **B1 (printed gap P1).** For a regular polygon tiling with `a, b` commensurable and `c` not commensurable with `a`: the sides of `A` are tile-edge walks that
either carry no `c`-edge at all or consist of `c`-edges only (for all sides simultaneously). -/
theorem ivc_rat_boundary_c_dichotomy {N M : ℕ} [NeZero M] (T : PolyTiling N M) (hreg : RegularPQ T.C) (hab : Comm (slen T.C 0) (slen T.C 1))
    (hac : ¬ Comm (slen T.C 0) (slen T.C 2)) :
    ∃ L : Fin M → List (Fin N × Plane × Plane),
      (∀ i, WalkT T.C.toRegionDissection (toV2 (T.P.e i)) (T.P.v i) (T.P.v (i + 1)) (L i)) ∧ (∀ i, L i ≠ []) ∧
      ((∀ i, ∀ e ∈ L i, dist e.2.1 e.2.2 = slen T.C 2) ∨ (∀ i, ∀ e ∈ L i, dist e.2.1 e.2.2 ≠ slen T.C 2)) := by
  classical
  obtain ⟨idx, hA, hcnt⟩ := hreg
  haveI : HasFansC T.C.toRegionDissection := hasFansC_poly _ T.P T.region_eq
  have hC : CaseC T.C idx := ⟨idx_dist_of_angle T.C idx hA, hA, fun X => hcnt X, notComb_c_of_comm (slen_pos T.C 2) hab hac⟩
  exact sides_edge_dichotomy T.C idx hC T.P T.region_eq

/-- Length form of B1 (this is `polygon_sides_alike` for polygon tilings; reproduction of Lemma 4.7). -/
theorem ivc_rat_boundary_c_dichotomy_lengths {N M : ℕ} [NeZero M] (T : PolyTiling N M) (hreg : RegularPQ T.C) (hab : Comm (slen T.C 0) (slen T.C 1))
    (hac : ¬ Comm (slen T.C 0) (slen T.C 2)) :
    (∀ i : Fin M, ∃ m : ℕ, 0 < m ∧ T.P.side i = m * slen T.C 2) ∨
    (∀ i : Fin M, ∃ na nb : ℕ, 0 < na + nb ∧ T.P.side i = na * slen T.C 0 + nb * slen T.C 1) := by
  classical
  obtain ⟨idx, hA, hcnt⟩ := hreg
  haveI : HasFansC T.C.toRegionDissection := hasFansC_poly _ T.P T.region_eq
  have hC : CaseC T.C idx := ⟨idx_dist_of_angle T.C idx hA, hA, fun X => hcnt X, notComb_c_of_comm (slen_pos T.C 2) hab hac⟩
  exact polygon_sides_alike T.C idx hC T.P T.region_eq

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.ivc_rat_boundary_c_dichotomy
#print axioms Erdos634.Draft.LaczFormal.RG.ivc_rat_boundary_c_dichotomy_lengths
