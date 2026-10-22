-- Draft/LaczFormalIIcWN126.lean -- Laczkovich (DCG 48 (2012), Sect. 6.3, p. 358-359), Lemma 6.2: `ExcInsideAll` PROVED, hence `iicNoKites : IIcNoKites`.
-- Printed: "Our next aim is to show that for every cycle C of Gamma_kite, C-degree contains all exceptional points. In order to prove this we may assume that C-degree does not contain any vertex of Gamma_kite.
-- Indeed, if C-degree meets Gamma_kite, then we take a cycle C1 of Gamma_kite belonging to C-degree and having minimal area. Then C1-degree does not contain any vertex of Gamma_kite, and if C1-degree contains all exceptional points then so does C-degree."
-- Here "minimal area" is replaced by induction on the finite number of Gamma_kite vertices strictly inside (`KIn`): a vertex `v` inside `C` lies on a cycle `C'` vertex- and edge-disjoint from `C` (`chain_mem_of_share`, `gkite_cycles_edge_disjoint`),
-- the degree region of `C'` lies in that of `C` (`nest_contain`, WN119, no Jordan theorem), so `KIn C'` is a proper subset of `KIn C` (it misses `v`); the base case is `exc_inside_of_innermost` (WN125).
-- NOTE, UNAUDITED.  Hypotheses: the Case IIc block + AngGen (the hypothesis block of `IIcNoKites`).  Credit: Laczkovich (DCG 48 (2012), Sect. 6.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcWN125
import Erdos634.Draft.LaczFormalIIcWN119
import Erdos634.Draft.LaczFormalIIcWN118

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG
open Erdos634.Draft.LaczFormal.WN (edgeSet wind extAng OrientOK)

local notation "tc" => Erdos634.Draft.LaczFormal.WN.toC

variable {N M : ℕ}

/-- The Gamma_kite vertices strictly inside the polygon of the chain `C`. -/
def KIn (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) {m : ℕ} [NeZero m] (C : Fin m → Plane) : Set Plane :=
  {v | (∃ Y, GKite D idx v Y) ∧ tc v ∉ edgeSet (cyc C) ∧ wind (cyc C) (tc v) ≠ 0}

theorem kin_finite (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) {m : ℕ} [NeZero m] (C : Fin m → Plane) :
    (KIn D idx C).Finite :=
  (gkite_tails_finite D idx).subset (fun v hv => hv.1)

/-- A Gamma_kite vertex `v` inside `C` lies on a closed chain `C'` whose degree region lies in that of `C`. -/
theorem kin_step [NeZero N] [NeZero M] (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hC : CaseC D idx) (hab : Comm (slen D 0) (slen D 1)) (hac : ¬ Comm (slen D 0) (slen D 2))
    (h1 : D.model.angleAt 2 < Real.pi / 2) (h3 : D.model.angleAt 2 ≠ Real.pi / 3)
    {m : ℕ} [NeZero m] (C : Fin m → Plane) (hCy : ∀ k : Fin m, GKite D idx (C k) (C (k + 1))) {v : Plane} (hv : v ∈ KIn D idx C) :
    ∃ (m' : ℕ) (_ : NeZero m') (C' : Fin m' → Plane), (∀ k : Fin m', GKite D idx (C' k) (C' (k + 1))) ∧ Function.Injective C' ∧ tc v ∈ edgeSet (cyc C') ∧
      ∀ z : ℂ, z ∉ edgeSet (cyc C') → wind (cyc C') z ≠ 0 → z ∉ edgeSet (cyc C) ∧ wind (cyc C) z ≠ 0 := by
  obtain ⟨⟨Y, hvY⟩, hvoff, hvw⟩ := hv
  obtain ⟨m', hm', C', hC'0, hC'inj, hC'y⟩ := gkite_cycle_exists D P hreg idx hC hab hac h1 h3 hvY
  have hsh : ∀ j k, C' j ≠ C k := by
    intro j k hjk
    have := chain_mem_of_share D P hreg idx hC h1 h3 C C' hCy hC'y hjk
    rw [hC'0] at this
    obtain ⟨k', hk'⟩ := this
    apply hvoff
    rw [← hk']
    exact Erdos634.Draft.LaczFormal.WN.vertex_mem_edgeSet (cyc C) k'
  have hd := gkite_cycles_edge_disjoint D idx C C' hCy hC'y hsh
  have hv' : tc v ∈ edgeSet (cyc C') := by
    have := Erdos634.Draft.LaczFormal.WN.vertex_mem_edgeSet (cyc C') 0
    simpa [cyc, hC'0] using this
  exact ⟨m', hm', C', hC'y, hC'inj, hv', fun z hz hwz =>
    Erdos634.Draft.LaczFormal.WN.nest_contain (cyc C) (cyc C') hd ⟨tc v, hv', hvw⟩ hz hwz⟩

set_option maxHeartbeats 6400000 in
/-- **`ExcInsideAll` (Laczkovich, Lemma 6.2, p. 358-359).** -/
theorem excInsideAll_proved [NeZero M] (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hC : CaseC D idx) (hab : Comm (slen D 0) (slen D 1)) (hac : ¬ Comm (slen D 0) (slen D 2))
    (h1 : D.model.angleAt 2 < Real.pi / 2) (h3 : D.model.angleAt 2 ≠ Real.pi / 3) (G : AngGen (fun l => D.model.angleAt l))
    (hcor : ∀ j : Fin M, cnt D idx (P.v j) 0 = 1 ∧ cnt D idx (P.v j) 1 = 1 ∧ cnt D idx (P.v j) 2 = 0) :
    ExcInsideAll D idx P := by
  have H : ∀ n : ℕ, ∀ (m : ℕ) [NeZero m] (C : Fin m → Plane), (∀ k : Fin m, GKite D idx (C k) (C (k + 1))) → Function.Injective C →
      (KIn D idx C).ncard = n → ∀ E ∈ excVerts2 D idx P, tc E ∉ edgeSet (cyc C) ∧ wind (cyc C) (tc E) ≠ 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro m hm C hCy hinj hn
      haveI : NeZero N := ⟨by obtain ⟨i, -⟩ := hCy 0; exact (Fin.pos i).ne'⟩
      by_cases hne : (KIn D idx C).Nonempty
      · obtain ⟨v, hv⟩ := hne
        obtain ⟨m', hm', C', hC'y, hC'inj, hv', hcont⟩ := kin_step D P hreg idx hC hab hac h1 h3 C hCy hv
        have hsubset : KIn D idx C' ⊆ KIn D idx C := by
          intro v' hv''
          obtain ⟨hY, h0, h2⟩ := hv''
          have := hcont (tc v') h0 h2
          exact ⟨hY, this.1, this.2⟩
        have hsub : KIn D idx C' ⊂ KIn D idx C :=
          ⟨hsubset, fun h => (h hv).2.1 hv'⟩
        have hlt : (KIn D idx C').ncard < n := hn ▸ Set.ncard_lt_ncard hsub (kin_finite D idx C)
        have := ih _ hlt m' C' hC'y hC'inj rfl
        intro E hE
        exact hcont (tc E) (this E hE).1 (this E hE).2
      · rw [Set.not_nonempty_iff_eq_empty] at hne
        apply exc_inside_of_innermost D P hreg idx hC hab hac h1 h3 G hcor C hCy hinj
        intro v Y hvY
        by_contra hcon
        push Not at hcon
        have hmem : v ∈ KIn D idx C := ⟨⟨Y, hvY⟩, hcon.1, hcon.2⟩
        rw [hne] at hmem
        exact hmem
  intro m hm C hCy hinj
  exact H _ m C hCy hinj rfl

#print axioms excInsideAll_proved

end Erdos634.Draft.LaczFormal.RG
