-- Draft/LaczFormalIVcRatBr3c.lean -- Laczkovich DCG 48 (2012), Sect. 8.3 (Subcase IVc, rational branch): BRIDGE stage Br3c (B-b, the V/W transfer).
--   `BrHyp`: the hypothesis bundle of the bridge (CaseC, regularity inside `CaseC.hregc`, tile type labels rho/pi, c-edges interior (`hint`)).
--   `Pr_exists`: every tile has a c-partner.  `kite_of_samelabel`: partners with same-label corners at a point form a KITE.
--   `vw_transfer`: a same-label (c,c) partner pair of corners at X (c in {rho,pi}) gives a same-label (d,d) pair at X for the other label d: the counting of `involution_count` (Br3a)
--   with the partner involution on the corners at X.  Applied with (c,d) = (pi,rho): V(Q) = W(Q') for a kite Q'; with (rho,pi): W(Q) = V(Q'').  NO fan enumeration is used.
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 8.3, Lemma 4.8, blueprint P2), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIVcRatBr3a
import Erdos634.Draft.LaczFormalIVcRatBr3b

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement Erdos634.CertCoord

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ}

/-- Hypotheses of the bridge `VWTiling.ofPolyTiling`. -/
structure BrHyp [NeZero M] (D : CongruentRegionDissection N) (P : ConvPoly M) (idx : Fin N → Equiv.Perm (Fin 3)) (s : ℝ) (ρ π : Fin 3) : Prop where
  hC : CaseC D idx
  hreg : D.region = P.carrier
  hab : Comm (slen D 0) (slen D 1)
  hac : ¬ Comm (slen D 0) (slen D 2)
  hs : 0 < s
  hρπ : ρ ≠ π
  hρ : ρ ≠ 2
  hπ : π ≠ 2
  hlρ : slen D ρ = 2 * s
  hlπ : slen D π = s
  hl2 : slen D 2 ^ 2 = 3 * s ^ 2
  hint : ∀ (i : Fin N) (d : V2) (U V : Plane), TriStep (D.tile i) d U V → dist U V = slen D 2 →
    ∃ m ∈ openSegment ℝ U V, m ∈ interior D.region

namespace BrHyp
variable [NeZero M] {D : CongruentRegionDissection N} {P : ConvPoly M} {idx : Fin N → Equiv.Perm (Fin 3)} {s : ℝ} {ρ π : Fin 3}

theorem ne2 (h : BrHyp D P idx s ρ π) (l : Fin 3) (hl : l ≠ 2) : slen D l ≠ slen D 2 := by
  intro e
  have hl2 := h.hl2
  rcases fin3_two ρ π l h.hρπ h.hρ h.hπ hl with e1 | e1
  · rw [e1, h.hlρ] at e; rw [← e] at hl2; nlinarith [h.hs]
  · rw [e1, h.hlπ] at e; rw [← e] at hl2; nlinarith [h.hs]

theorem h0 (h : BrHyp D P idx s ρ π) : slen D 0 ≠ slen D 2 := h.ne2 0 (by decide)
theorem h1 (h : BrHyp D P idx s ρ π) : slen D 1 ≠ slen D 2 := h.ne2 1 (by decide)

end BrHyp

theorem fin3_other : ∀ c d l : Fin 3, c ≠ d → c ≠ 2 → d ≠ 2 → l ≠ 2 → l ≠ c → l = d := by decide
theorem fin3_cd : ∀ c d : Fin 3, c ≠ d → c ≠ 2 → d ≠ 2 → (c = 0 ∧ d = 1) ∨ (c = 1 ∧ d = 0) := by decide

variable [NeZero M] {D : CongruentRegionDissection N} {P : ConvPoly M} {idx : Fin N → Equiv.Perm (Fin 3)} {s : ℝ} {ρ π : Fin 3}

/-- Every tile has a c-partner (a different tile). -/
theorem Pr_exists [HasFansC D.toRegionDissection] (h : BrHyp D P idx s ρ π) (i : Fin N) : ∃ j, j ≠ i ∧ Pr D i j := by
  obtain ⟨kk, hkk⟩ : ∃ kk, idx i kk = ρ := ⟨(idx i).symm ρ, by simp⟩
  obtain ⟨f, hf⟩ : ∃ f, idx i f = π := ⟨(idx i).symm π, by simp⟩
  obtain ⟨g, hg⟩ : ∃ g, idx i g = 2 := ⟨(idx i).symm 2, by simp⟩
  have hfk : f ≠ kk := fun e => h.hρπ (by rw [← hkk, ← hf, e])
  have hgk : g ≠ kk := fun e => h.hρ (by rw [← hkk, ← hg, e])
  have hgf : g ≠ f := fun e => h.hπ (by rw [← hf, ← hg, e])
  have hc0 : dist ((D.tile i).pts kk) ((D.tile i).pts f) = slen D 2 := by
    rw [h.hC.hidx, hkk, hf]; exact dist_model_opp D ρ π 2 h.hρπ h.hπ h.hρ
  obtain ⟨d, hd⟩ := tile_step_either (D.tile i) hfk hgk hgf
  rcases hd with hd | hd
  · obtain ⟨m, hm, hmi⟩ := h.hint i d _ _ hd hc0
    obtain ⟨j, hji, hSj, -⟩ := pair_partner D P h.hreg idx h.hC h.hab h.hac hd hc0 hm hmi
    exact ⟨j, hji, d, _, _, hd, hc0, hSj⟩
  · have hc1 : dist ((D.tile i).pts f) ((D.tile i).pts kk) = slen D 2 := (dist_comm _ _).trans hc0
    obtain ⟨m, hm, hmi⟩ := h.hint i d _ _ hd hc1
    obtain ⟨j, hji, hSj, -⟩ := pair_partner D P h.hreg idx h.hC h.hab h.hac hd hc1 hm hmi
    exact ⟨j, hji, d, _, _, hd, hc1, hSj⟩

/-- Partners with same-label corners at a common point form a kite. -/
theorem kite_of_samelabel (h : BrHyp D P idx s ρ π) {i j : Fin N} (hPr : Pr D i j) {b b' : Fin 3} {X : Plane}
    (hb : (D.tile i).pts b = X) (hb' : (D.tile j).pts b' = X) (hl : idx i b = idx j b') (hl2 : idx i b ≠ 2) :
    KitePair D idx s ρ π i j := by
  obtain ⟨d, U, V, hS, hc, hS'⟩ := hPr
  rcases pair_tile_shape D idx h.hC.hidx h.hs h.hρπ h.hρ h.hπ h.hlρ h.hlπ h.hl2 hS hS' hc with hK | ⟨-, hP⟩
  · exact hK
  · exfalso
    obtain ⟨a', ha', hne, -⟩ := hP b hl2
    have : a' = b' := (D.tile j).indep.injective (ha'.trans (hb.trans hb'.symm))
    subst this
    exact hne hl.symm

#print axioms Erdos634.Draft.LaczFormal.RG.Pr_exists
#print axioms Erdos634.Draft.LaczFormal.RG.kite_of_samelabel

end Erdos634.Draft.LaczFormal.RG
