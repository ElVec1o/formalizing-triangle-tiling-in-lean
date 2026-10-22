-- Draft/LaczFormalIVcRatBr2b.lean -- Laczkovich DCG 48 (2012), Sect. 8.3 (Subcase IVc, rational branch): BRIDGE stage Br2b: `pair_tile_shape`.
--   A c-pair of tiles (the `TriStep` data of `pair_shape_tiles`) of a congruent region dissection whose tile is of type (labels rho, pi, 2; slen rho = 2s, slen pi = s, slen 2 ^ 2 = 3 s^2)
--   is a `KitePair` (a KiteData piece = union of the two tiles) or a `ParPair` (two rhombi = union of the two tiles), with the label correspondence of the corners (Br2).
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 8.3, Lemma 4.8), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIVcRatBr2

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement Erdos634.CertCoord

namespace Erdos634.Draft.LaczFormal.RG

variable {N : ℕ}

set_option maxHeartbeats 1600000 in
theorem pair_tile_shape (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    {s : ℝ} (hs : 0 < s) {ρ π : Fin 3} (hρπ : ρ ≠ π) (hρ : ρ ≠ 2) (hπ : π ≠ 2)
    (hlρ : slen D ρ = 2 * s) (hlπ : slen D π = s) (hl2 : slen D 2 ^ 2 = 3 * s ^ 2)
    {i j : Fin N} {d : V2} {U V : Plane} (hS : TriStep (D.tile i) d U V) (hS' : TriStep (D.tile j) (neg2 d) V U)
    (hc : dist U V = slen D 2) :
    KitePair D idx s ρ π i j ∨ ParPair D idx s i j := by
  have hl2' : slen D 2 ≠ 0 := by intro h; rw [h] at hl2; nlinarith
  have hne : ∀ l : Fin 3, l ≠ 2 → slen D l ≠ slen D 2 := by
    intro l hl h
    rcases fin3_two ρ π l hρπ hρ hπ hl with e | e
    · rw [e, hlρ] at h; rw [← h] at hl2; nlinarith
    · rw [e, hlπ] at h; rw [← h] at hl2; nlinarith
  have h0 : slen D 0 ≠ slen D 2 := hne 0 (by decide)
  have h1 : slen D 1 ≠ slen D 2 := hne 1 (by decide)
  obtain ⟨kk, f, g, kk', f', g', hk, hf, hk', hf', hg, hg', hcase⟩ := pair_shape_tiles D idx hidx h0 h1 hS hS' hc
  have hUV : U ≠ V := by intro e; rw [e, dist_self] at hc; exact hl2' hc.symm
  have hkf : kk ≠ f := by rintro rfl; exact hUV (hk.symm.trans hf)
  have hdi : dist ((D.tile i).pts kk) ((D.tile i).pts f) = slen D 2 := by rw [hk, hf]; exact hc
  obtain ⟨hgk, hgf⟩ := third_label D idx hidx h0 h1 i hkf hdi hg
  have hkf' : kk' ≠ f' := by rintro rfl; exact hUV (hf'.symm.trans hk')
  have hdj : dist ((D.tile j).pts kk') ((D.tile j).pts f') = slen D 2 := by rw [hk', hf', dist_comm]; exact hc
  obtain ⟨hgk', hgf'⟩ := third_label D idx hidx h0 h1 j hkf' hdj hg'
  have hlU2 : idx i kk ≠ 2 := fun e => hgk ((idx i).injective (hg.trans e.symm))
  have hlV2 : idx i f ≠ 2 := fun e => hgf ((idx i).injective (hg.trans e.symm))
  have hlUV : idx i kk ≠ idx i f := (idx i).injective.ne hkf
  have dWU := tile_dsq D idx hidx i (a := g) (b := kk) (c := f) hgk hgf hkf
  have dWV := tile_dsq D idx hidx i (a := g) (b := f) (c := kk) hgf hgk hkf.symm
  have dVU := tile_dsq D idx hidx i (a := f) (b := kk) (c := g) hkf.symm hgf.symm hgk.symm
  rw [hk] at dWU dVU
  rw [hf] at dWV dVU
  rw [hg, hl2] at dVU
  rcases fin3_lab ρ π _ _ hρπ hρ hπ hlU2 hlV2 hlUV with ⟨hlU, hlV⟩ | ⟨hlU, hlV⟩
  · rw [hlV, hlπ] at dWU
    rw [hlU, hlρ] at dWV
    rcases hcase with ⟨⟨hf0, hf1⟩, hjf, hjk⟩ | ⟨⟨hW0, hW1⟩, hjf, hjk⟩
    · left
      obtain ⟨hm0, hm1⟩ := kite_foot_U hs U V ((D.tile i).pts g) ((D.tile j).pts g') dVU dWU dWV hf0 hf1
      refine core_kite D idx hidx hs (rv := kk) (pv := f) (g := g) (rv' := f') (pv' := kk') (g' := g') hkf hgk.symm hgf.symm hkf'.symm hgf'.symm hgk'.symm
        hlU hlV hg (by rw [hjf]; exact hlU) (by rw [hjk, hlV]) hg' hlρ hlπ hl2 (hf'.trans hk.symm) (hk'.trans hf.symm) ?_ ?_
      · rw [hk]; exact hm0
      · rw [hk]; exact hm1
    · right
      refine core_par D idx hidx hs (rv := kk) (pv := f) (g := g) (a1 := f') (a2 := kk') (g' := g') hkf hgk.symm hgf.symm hkf'.symm hgf'.symm hgk'.symm
        hlU hlV hρπ hρ hπ (by rw [hjf, hlV]) (by rw [hjk, hlU]) hlρ hlπ hl2 (hf'.trans hk.symm) (hk'.trans hf.symm) hg ?_ ?_
      · rw [hk, hf]; exact hW0
      · rw [hk, hf]; exact hW1
  · rw [hlV, hlρ] at dWU
    rw [hlU, hlπ] at dWV
    rcases hcase with ⟨⟨hf0, hf1⟩, hjf, hjk⟩ | ⟨⟨hW0, hW1⟩, hjf, hjk⟩
    · left
      obtain ⟨hm0, hm1⟩ := kite_foot_V hs U V ((D.tile i).pts g) ((D.tile j).pts g') dVU dWV dWU hf0 hf1
      refine core_kite D idx hidx hs (rv := f) (pv := kk) (g := g) (rv' := kk') (pv' := f') (g' := g') hkf.symm hgf.symm hgk.symm hkf' hgk'.symm hgf'.symm
        hlV hlU hg (by rw [hjk, hlV]) (by rw [hjf]; exact hlU) hg' hlρ hlπ hl2 (hk'.trans hf.symm) (hf'.trans hk.symm) ?_ ?_
      · rw [hf]; exact hm0
      · rw [hf]; exact hm1
    · right
      refine core_par D idx hidx hs (rv := f) (pv := kk) (g := g) (a1 := kk') (a2 := f') (g' := g') hkf.symm hgf.symm hgk.symm hkf' hgk'.symm hgf'.symm
        hlV hlU hρπ hρ hπ (by rw [hjk, hlU]) (by rw [hjf, hlV]) hlρ hlπ hl2 (hk'.trans hf.symm) (hf'.trans hk.symm) hg ?_ ?_
      · rw [hk, hf]; rw [hW0]; ring
      · rw [hk, hf]; rw [hW1]; ring

#print axioms Erdos634.Draft.LaczFormal.RG.pair_tile_shape

end Erdos634.Draft.LaczFormal.RG
