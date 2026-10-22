-- Draft/LaczFormalIVcRatBr3b.lean -- Laczkovich DCG 48 (2012), Sect. 8.3 (Subcase IVc, rational branch): BRIDGE stage Br3b: the PARTNER relation of tiles across their c-edge.
--   `Pr D i j` : tile i has a c-edge U -> V (left step) and tile j the same edge V -> U.  `Pr.symm`; `same_cedge` (a tile has ONE oriented c-edge: two left steps of length slen 2 of the same tile coincide);
--   `Pr.unique` (the partner is unique, via `same_side_tile_eq`).
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 8.3, Lemma 4.8), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIVcRatBr2b
import Erdos634.Draft.LaczFormalRG12GKiteEx

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement Erdos634.CertCoord

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ}

theorem neg2_neg2 (d : V2) : neg2 (neg2 d) = d := by
  unfold neg2; ext <;> simp

/-- `i, j` are partners across a c-edge. -/
def Pr (D : CongruentRegionDissection N) (i j : Fin N) : Prop :=
  ∃ (d : V2) (U V : Plane), TriStep (D.tile i) d U V ∧ dist U V = slen D 2 ∧ TriStep (D.tile j) (neg2 d) V U

theorem Pr.symm {D : CongruentRegionDissection N} {i j : Fin N} (h : Pr D i j) : Pr D j i := by
  obtain ⟨d, U, V, hS, hc, hS'⟩ := h
  refine ⟨neg2 d, V, U, hS', (dist_comm V U).trans hc, ?_⟩
  rw [neg2_neg2]; exact hS

theorem edge_third (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    (h0 : slen D 0 ≠ slen D 2) (h1 : slen D 1 ≠ slen D 2) (i : Fin N) {kk f g : Fin 3} (hfk : f ≠ kk) (hgk : g ≠ kk) (hgf : g ≠ f)
    (hd : dist ((D.tile i).pts kk) ((D.tile i).pts f) = slen D 2) : idx i g = 2 := by
  have e : dist ((D.tile i).pts kk) ((D.tile i).pts f) = slen D (idx i g) := by
    rw [hidx]; exact dist_model_opp D _ _ _ ((idx i).injective.ne hfk.symm) ((idx i).injective.ne hgf.symm) ((idx i).injective.ne hgk.symm)
  exact opp_eq_two D h0 h1 _ (e.symm.trans hd)

theorem fin3_edge : ∀ g kk f kk₂ f₂ : Fin 3, f ≠ kk → g ≠ kk → g ≠ f → f₂ ≠ kk₂ → g ≠ kk₂ → g ≠ f₂ →
    (kk₂ = kk ∧ f₂ = f) ∨ (kk₂ = f ∧ f₂ = kk) := by decide

set_option maxHeartbeats 800000 in
/-- A tile has only one oriented c-edge with the tile on its left. -/
theorem same_cedge (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    (h0 : slen D 0 ≠ slen D 2) (h1 : slen D 1 ≠ slen D 2) (i : Fin N) {d d₂ : V2} {U V U₂ V₂ : Plane}
    (hS : TriStep (D.tile i) d U V) (hS₂ : TriStep (D.tile i) d₂ U₂ V₂) (hc : dist U V = slen D 2) (hc₂ : dist U₂ V₂ = slen D 2) :
    U₂ = U ∧ V₂ = V := by
  obtain ⟨kk, f, g, hk, hf, hfk, hgk, hgf, hpar, hleft⟩ := hS
  obtain ⟨kk₂, f₂, g₂, hk₂, hf₂, hfk₂, hgk₂, hgf₂, hpar₂, hleft₂⟩ := hS₂
  subst hk hf hk₂ hf₂
  have hg := edge_third D idx hidx h0 h1 i hfk hgk hgf hc
  have hg₂ := edge_third D idx hidx h0 h1 i hfk₂ hgk₂ hgf₂ hc₂
  have hgg : g₂ = g := (idx i).injective (hg₂.trans hg.symm)
  subst hgg
  rcases fin3_edge g₂ kk f kk₂ f₂ hfk hgk hgf hfk₂ hgk₂ hgf₂ with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · exact ⟨by rw [e1], by rw [e2]⟩
  · exfalso
    rw [e1, e2] at hpar₂
    rw [e1] at hleft₂
    obtain ⟨c, hc0, hcd⟩ := hpar.smul
    obtain ⟨c₂, hc₂0, hcd₂⟩ := hpar₂.smul
    have b1 : (D.tile i).pts f 0 - (D.tile i).pts kk 0 = c * d.1 := by have := congrArg Prod.fst hcd; simp only [toV2] at this; simpa using this
    have b2 : (D.tile i).pts f 1 - (D.tile i).pts kk 1 = c * d.2 := by have := congrArg Prod.snd hcd; simpa [toV2] using this
    have a1 : (D.tile i).pts kk 0 - (D.tile i).pts f 0 = c₂ * d₂.1 := by have := congrArg Prod.fst hcd₂; simpa [toV2] using this
    have a2 : (D.tile i).pts kk 1 - (D.tile i).pts f 1 = c₂ * d₂.2 := by have := congrArg Prod.snd hcd₂; simpa [toV2] using this
    unfold crs at hleft hleft₂
    simp only [toV2, PiLp.sub_apply] at hleft hleft₂
    have key : c₂ * (d₂.1 * ((D.tile i).pts g₂ 1 - (D.tile i).pts f 1) - d₂.2 * ((D.tile i).pts g₂ 0 - (D.tile i).pts f 0)) +
        c * (d.1 * ((D.tile i).pts g₂ 1 - (D.tile i).pts kk 1) - d.2 * ((D.tile i).pts g₂ 0 - (D.tile i).pts kk 0)) = 0 := by
      linear_combination (-(((D.tile i).pts g₂ 1 - (D.tile i).pts f 1))) * a1 + ((D.tile i).pts g₂ 0 - (D.tile i).pts f 0) * a2
        - ((D.tile i).pts g₂ 1 - (D.tile i).pts kk 1) * b1 + ((D.tile i).pts g₂ 0 - (D.tile i).pts kk 0) * b2
    nlinarith [mul_pos hc₂0 hleft₂, mul_pos hc0 hleft]

/-- The partner across the c-edge is unique. -/
theorem Pr.unique (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    (h0 : slen D 0 ≠ slen D 2) (h1 : slen D 1 ≠ slen D 2) {i j k : Fin N} (hj : Pr D i j) (hk : Pr D i k) : j = k := by
  obtain ⟨d, U, V, hS, hc, hS'⟩ := hj
  obtain ⟨d₂, U₂, V₂, hS₂, hc₂, hS₂'⟩ := hk
  obtain ⟨hU, hV⟩ := same_cedge D idx hidx h0 h1 i hS hS₂ hc hc₂
  subst hU hV
  exact same_side_tile_eq D hS' hS₂'

#print axioms Erdos634.Draft.LaczFormal.RG.Pr.unique

end Erdos634.Draft.LaczFormal.RG
