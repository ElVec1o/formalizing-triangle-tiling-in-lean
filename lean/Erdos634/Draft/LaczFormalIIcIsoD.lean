-- Draft/LaczFormalIIcIsoD.lean -- Laczkovich (DCG 48 (2012)), Sect. 6.2, Case IIc with alpha = beta: the interface `AngGenI` and the fan lemma `fan222_tile_iso`.
-- `AngGenI omega` = `AngGen' omega` (positive, sum pi, gamma differs from alpha, beta, none right) + `omega 0 = omega 1`.  All the iso copies of the Lemma 6.3 chain (LaczFormalIIcIso*.lean) take `(G : AngGenI ..)` where the
-- originals take `(G : AngGen ..)`, so call sites are unchanged.  `fan222_tile_iso` is `fan222_tile` verbatim (it uses only `G.sum`).  The originals are NOT edited.
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012)), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalRG12Fan222Tile
import Erdos634.Draft.LaczFormalIIcIsoB

open scoped Classical
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21

namespace Erdos634.Draft.LaczFormal.RG

variable {N : ℕ}

/-- `AngGen'` together with `alpha = beta` (isosceles model). -/
structure AngGenI (ω : Fin 3 → ℝ) : Prop extends AngGen' ω where
  eq01 : ω 0 = ω 1

set_option maxHeartbeats 3200000 in
/-- **The six sectors at an interior (2,2,2) vertex form a `Fan6`.** -/
theorem fan222_tile_iso (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (idx : Fin N → Equiv.Perm (Fin 3))
    (hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v) {Y : Plane} (hint : Y ∈ interior D.region)
    (h0 : cnt D idx Y 0 = 2) (h1 : cnt D idx Y 1 = 2) (h2 : cnt D idx Y 2 = 2) (G : AngGenI (fun l => D.model.angleAt l)) :
    ∃ (F : ExtFan D.toRegionDissection Y Empty) (s : ℕ → AtV D.toRegionDissection Y) (ℓ : ℕ → Fin 3),
      Fan6 (fun l => D.model.angleAt l) (fun j => F.p (s j)) (fun j => F.q (s j)) ℓ ∧
      (∀ j, ∃ k, (D.tile (s j).1).pts k = Y ∧ idx (s j).1 k = ℓ j) ∧ (∀ x : AtV D.toRegionDissection Y, ∃ j < 6, s j = x) ∧
      (∀ n, s (n + 6) = s n) := by
  classical
  have hvert : ∃ i k, (D.tile i).pts k = Y := by
    have : 0 < cnt D idx Y 0 := by rw [h0]; norm_num
    unfold cnt at this
    obtain ⟨⟨i, k⟩, hik⟩ := Finset.card_pos.mp this
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hik
    exact ⟨i, k, hik.1⟩
  obtain ⟨F⟩ := extFan_interior D.toRegionDissection Y hvert hint
  have hang := head_angle_sum D idx hidxA F inferInstance
  rw [Fin.sum_univ_three, h0, h1, h2] at hang
  have hStr : (Strn D.toRegionDissection Y).card = 0 := by
    have hs := G.sum
    have hp := Real.pi_pos
    have : Real.pi * ((Strn D.toRegionDissection Y).card : ℝ) = 0 := by push_cast at hang; simp only at hs; nlinarith
    have h0' := (mul_eq_zero.mp this).resolve_left hp.ne'
    exact_mod_cast h0'
  have hcorner : ∀ x : AtV D.toRegionDissection Y, ∃ k, (D.tile x.1).pts k = Y := by
    intro x
    by_contra hno
    push Not at hno
    have : x.1 ∈ Strn D.toRegionDissection Y := by
      simp only [Strn, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨x.2, hno⟩
    have := Finset.card_pos.mpr ⟨x.1, this⟩
    omega
  choose kk hkk using hcorner
  set lab : AtV D.toRegionDissection Y → Fin 3 := fun x => idx x.1 (kk x) with hlab
  have hwdl : ∀ x, wd (F.p x) (F.q x) = D.model.angleAt (lab x) := by
    intro x
    rw [F.hwd x, hlab]
    simp only
    rw [hidxA]
    calc (D.tile x.1).localAngle Y = (D.tile x.1).localAngle ((D.tile x.1).pts (kk x)) := by rw [hkk x]
      _ = _ := Tri.localAngle_vertex (D.tile x.1) (kk x)
  -- label counts
  have hlabcnt : ∀ l, (Finset.univ.filter (fun x : AtV D.toRegionDissection Y => lab x = l)).card = cnt D idx Y l := by
    intro l
    unfold cnt
    refine Finset.card_bij (fun x _ => (x.1, kk x)) ?_ ?_ ?_
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      exact ⟨hkk x, hx⟩
    · intro x _ x' _ h
      exact Subtype.ext (congrArg Prod.fst h)
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
      obtain ⟨hpk, hpl⟩ := hp
      have hmem : Y ∈ (D.tile p.1).carrier := hpk ▸ subset_convexHull ℝ _ ⟨p.2, rfl⟩
      refine ⟨⟨p.1, hmem⟩, ?_, ?_⟩
      · have : kk ⟨p.1, hmem⟩ = p.2 := (D.tile p.1).indep.injective ((hkk ⟨p.1, hmem⟩).trans hpk.symm)
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, hlab]
        simp only [this]; exact hpl
      · have : kk ⟨p.1, hmem⟩ = p.2 := (D.tile p.1).indep.injective ((hkk ⟨p.1, hmem⟩).trans hpk.symm)
        ext <;> simp [this]
  have hcard6 : Fintype.card (AtV D.toRegionDissection Y) = 6 := by
    have := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset (AtV D.toRegionDissection Y))) (t := (Finset.univ : Finset (Fin 3)))
      (f := lab) (fun _ _ => Finset.mem_univ _)
    rw [Finset.card_univ] at this
    rw [this, Fin.sum_univ_three, hlabcnt, hlabcnt, hlabcnt, h0, h1, h2]
  have hLc : Fintype.card (AtV D.toRegionDissection Y ⊕ Empty) = 6 := by simp [hcard6]
  -- the sector sequence
  set sN : ℕ → AtV D.toRegionDissection Y := fun n => Sum.elim id (fun e : Empty => e.elim) (F.e n) with hsN
  have heN : ∀ n, F.e n = Sum.inl (sN n) := by
    intro n
    rcases hn : F.e n with x | e
    · simp [hsN, hn]
    · exact e.elim
  refine ⟨F, sN, fun j => lab (sN j), ⟨?_, ?_, ?_, ?_⟩, fun j => ⟨kk (sN j), hkk _, rfl⟩, ?_, ?_⟩
  · intro j; exact (F.hok _).ne_p
  · intro j
    have := F.hP j
    rw [heN (j + 1), heN j] at this
    exact this
  · intro j; exact hwdl _
  · intro j l
    have hc2 : ∀ l, cnt D idx Y l = 2 := by
      intro l; fin_cases l
      exacts [h0, h1, h2]
    rw [← hc2 l, ← hlabcnt l]
    refine Finset.card_bij (fun i _ => sN (j + i)) ?_ ?_ ?_
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_univ, true_and] at hi ⊢
      exact hi.2
    · intro i hi i' hi' h
      simp only [Finset.mem_filter, Finset.mem_range] at hi hi'
      have h' : sN (j + i) = sN (j + i') := h
      have : F.e (j + i) = F.e (j + i') := by rw [heN, heN, h']
      exact e_inj_shift F j (by rw [hLc]; exact hi.1) (by rw [hLc]; exact hi'.1) this
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      obtain ⟨m, hm, hem⟩ := e_surj_shift F j (Sum.inl x)
      rw [heN] at hem
      have hx' : sN (j + m) = x := by simpa using hem
      refine ⟨m, ?_, hx'⟩
      simp only [Finset.mem_filter, Finset.mem_range]
      exact ⟨by rw [hLc] at hm; exact hm, by rw [hx']; exact hx⟩
  · intro x
    obtain ⟨m, hm, hem⟩ := e_surj_shift F 0 (Sum.inl x)
    refine ⟨m, by omega, ?_⟩
    rw [heN] at hem
    simpa using hem
  · intro n
    have h1 : F.e (n + 6) = F.e n := by simpa [hLc] using F.hper n
    have h2 : (Sum.inl (sN (n + 6)) : AtV D.toRegionDissection Y ⊕ Empty) = Sum.inl (sN n) := by rw [← heN, ← heN]; exact h1
    exact Sum.inl_injective h2

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.fan222_tile_iso
