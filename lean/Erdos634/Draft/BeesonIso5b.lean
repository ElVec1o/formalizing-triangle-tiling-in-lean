import Erdos634.Draft.BeesonIso5a

/-!
# Beeson, "Tilings of an isosceles triangle" (arXiv 1206.1974 v7), Lemma 11.10, "at least four": step lengths and the corner `B`

NOTE, UNAUDITED.  Credit: Michael Beeson (arXiv 1206.1974 v7, Lemma 11.10), Laczkovich (DCG 48 (2012)), Beeson-Zhang, Herdt, Zhang.
Formalization debt, not progress on the /goal outcomes.

* `bstep_dist`: a step whose tile has NO beta corner (label 1) at either end has length `b` (`BeesonIso2b.side_has_b_step` gives one on a side with two `alpha` corners).
* `step_ne_a`: a step with an `alpha` corner (label 0) at one end does not have length `a` (the sides at an `alpha` vertex are `b`, `c`).
* `corner_B_counts`: at a polygon vertex of angle `pi - 2 alpha` (`alpha + beta`) there is exactly one beta corner and no gamma corner.
* `tile_B_arm_a`: the (unique) beta corner at such a vertex has exactly one arm of length `a`: two steps of length `a` ending/starting at the vertex `B` along DIFFERENT sides belong to
  two different tiles, but there is only one beta corner: contradiction (`two_a_steps_at_B`).
Witness: the lemma shapes are those of the 1125-tiling's boundary; `wit_fin3` records the label facts (finite check).
-/

open scoped Classical
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ} [NeZero M]

theorem fin3_not_one : ∀ a b c : Fin 3, a ≠ b → a ≠ c → b ≠ c → a ≠ 1 → b ≠ 1 → c = 1 := by
  intro a b c; fin_cases a <;> fin_cases b <;> fin_cases c <;> simp

theorem fin3_ne_zero_cases : ∀ x : Fin 3, x ≠ 0 → x = 1 ∨ x = 2 := by
  intro x; fin_cases x <;> simp

theorem bstep_dist (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    {j : Fin N} {d : V2} {U U' : Plane} (hS : TriStep (D.tile j) d U U')
    (hno : ∀ k, ((D.tile j).pts k = U ∨ (D.tile j).pts k = U') → idx j k ≠ 1) : dist U U' = slen D 1 := by
  obtain ⟨kk, f, g, hk, hf, hfk, hgk, hgf, hd⟩ := step_third D idx hidx hS
  rw [hd]
  have h1 : idx j kk ≠ 1 := hno kk (Or.inl hk)
  have h2 : idx j f ≠ 1 := hno f (Or.inr hf)
  have := fin3_not_one (idx j kk) (idx j f) (idx j g) (fun h => hfk ((idx j).injective h).symm) (fun h => hgk ((idx j).injective h).symm)
    (fun h => hgf ((idx j).injective h).symm) h1 h2
  rw [this]

theorem step_ne_a (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    (hab : slen D 0 ≠ slen D 1) (hac : slen D 0 ≠ slen D 2)
    {j : Fin N} {d : V2} {U U' : Plane} (hS : TriStep (D.tile j) d U U')
    (h0 : ∃ k, ((D.tile j).pts k = U ∨ (D.tile j).pts k = U') ∧ idx j k = 0) : dist U U' ≠ slen D 0 := by
  obtain ⟨kk, f, g, hk, hf, hfk, hgk, hgf, hd⟩ := step_third D idx hidx hS
  rw [hd]
  obtain ⟨k0, hk0, hl0⟩ := h0
  have hg0 : idx j g ≠ 0 := by
    intro hg
    rcases hk0 with h | h
    · have : k0 = kk := (D.tile j).indep.injective (h.trans hk.symm)
      subst this
      exact hgk ((idx j).injective (hg.trans hl0.symm))
    · have : k0 = f := (D.tile j).indep.injective (h.trans hf.symm)
      subst this
      exact hgf ((idx j).injective (hg.trans hl0.symm))
  intro h
  rcases fin3_ne_zero_cases _ hg0 with h1 | h1
  · rw [h1] at h; exact hab h.symm
  · rw [h1] at h; exact hac h.symm

/-- At a polygon vertex of angle `pi - 2 alpha`: exactly one beta corner and no gamma corner. -/
theorem corner_B_counts (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v)
    (hβ : D.model.angleAt 1 = Real.pi - 3 * D.model.angleAt 0) (hγ : D.model.angleAt 2 = 2 * D.model.angleAt 0)
    (hα : ¬ ∃ r : ℚ, D.model.angleAt 0 = (r : ℝ) * Real.pi) (kB : Fin M) (hkB : P.angle (kB + 1) = Real.pi - 2 * D.model.angleAt 0) :
    cnt D idx (P.v (kB + 1)) 1 = 1 ∧ cnt D idx (P.v (kB + 1)) 2 = 0 := by
  have hv0 : ∃ j k, (D.tile j).pts k = P.v (kB + 1) := poly_vertex_is_tile_vertex D.toRegionDissection P hreg (kB + 1)
  have hcA := corner_A D P hreg idx hidxA kB hv0
  have hAexp : Asum D idx (P.v (kB + 1)) = (cnt D idx (P.v (kB + 1)) 0 : ℝ) * D.model.angleAt 0 + (cnt D idx (P.v (kB + 1)) 1 : ℝ) * D.model.angleAt 1
      + (cnt D idx (P.v (kB + 1)) 2 : ℝ) * (2 * D.model.angleAt 0) := by
    unfold Asum; rw [Fin.sum_univ_three, hγ]
  have := vtype_arith (α := D.model.angleAt 0) (β := D.model.angleAt 1) hβ hα _ _ _ (-2) 1 (by rw [← hAexp, hcA, hkB]; push_cast; ring)
  omega

/-- Two steps of length `a` that end/start at the same polygon vertex `B` of angle `pi - 2 alpha` along DIFFERENT sides are impossible: the two tiles would both
carry the (unique) beta corner at `B`, so they coincide, and then the tile has two distinct arms of length `a` at `B`. -/
theorem two_a_steps_at_B (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    (hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v)
    (hβ : D.model.angleAt 1 = Real.pi - 3 * D.model.angleAt 0) (hγ : D.model.angleAt 2 = 2 * D.model.angleAt 0)
    (hα : ¬ ∃ r : ℚ, D.model.angleAt 0 = (r : ℝ) * Real.pi) (kB : Fin M) (hkB : P.angle (kB + 1) = Real.pi - 2 * D.model.angleAt 0)
    (hab : slen D 0 ≠ slen D 1) (hac : slen D 0 ≠ slen D 2)
    {j1 j2 : Fin N} {d1 d2 : V2} {Z1 Z2 : Plane}
    (hS1 : TriStep (D.tile j1) d1 Z1 (P.v (kB + 1))) (hS2 : TriStep (D.tile j2) d2 (P.v (kB + 1)) Z2)
    (hZ : Z1 ≠ Z2) (hd1 : dist Z1 (P.v (kB + 1)) = slen D 0) (hd2 : dist (P.v (kB + 1)) Z2 = slen D 0) : False := by
  obtain ⟨hn1, hn2⟩ := corner_B_counts D P hreg idx hidxA hβ hγ hα kB hkB
  obtain ⟨ka, fa, ga, hka, hfa, hfka, hgka, hgfa, hda⟩ := step_third D idx hidx hS1
  obtain ⟨kb, fb, gb, hkb, hfb, hfkb, hgkb, hgfb, hdb⟩ := step_third D idx hidx hS2
  -- step 1 ends at B with the vertex fa; step 2 starts at B with kb.  The third vertices have label 0.
  have ha0 : idx j1 ga = 0 := by
    rw [hd1] at hda
    have : slen D (idx j1 ga) = slen D 0 := hda.symm
    have hne : ∀ x : Fin 3, slen D x = slen D 0 → x = 0 := by
      intro x hx
      fin_cases x
      · rfl
      · exact absurd hx.symm hab
      · exact absurd hx.symm hac
    exact hne _ this
  have hb0 : idx j2 gb = 0 := by
    rw [hd2] at hdb
    have : slen D (idx j2 gb) = slen D 0 := hdb.symm
    have hne : ∀ x : Fin 3, slen D x = slen D 0 → x = 0 := by
      intro x hx
      fin_cases x
      · rfl
      · exact absurd hx.symm hab
      · exact absurd hx.symm hac
    exact hne _ this
  -- B has no gamma corner, so the corners fa, kb are beta: the label of fa is 1 or 2, not 2
  have hfa1 : idx j1 fa = 1 := by
    have h2 : idx j1 fa ≠ 2 := by
      intro h
      have := cnt_pos_of_corner_h1 D idx hfa h
      omega
    have hne0 : idx j1 fa ≠ 0 := fun h => hgfa ((idx j1).injective (ha0.trans h.symm))
    rcases fin3_ne_zero_cases _ hne0 with h | h
    · exact h
    · exact absurd h h2
  have hkb1 : idx j2 kb = 1 := by
    have h2 : idx j2 kb ≠ 2 := by
      intro h
      have := cnt_pos_of_corner_h1 D idx hkb h
      omega
    have hne0 : idx j2 kb ≠ 0 := fun h => hgkb ((idx j2).injective (hb0.trans h.symm))
    rcases fin3_ne_zero_cases _ hne0 with h | h
    · exact h
    · exact absurd h h2
  -- the two tiles coincide (one beta corner at B)
  have hj : j1 = j2 := corner_eq_of_cnt_le_one_h1 D idx (l := 1) (by omega) hfa hfa1 hkb hkb1
  subst hj
  have hBB : fa = kb := (D.tile j1).indep.injective (hfa.trans hkb.symm)
  have hg : ga = gb := (idx j1).injective (ha0.trans hb0.symm)
  have hX : ∀ x y a b : Fin 3, x ≠ a → x ≠ b → y ≠ a → y ≠ b → a ≠ b → x = y := by
    intro x y a b; fin_cases x <;> fin_cases y <;> fin_cases a <;> fin_cases b <;> simp
  have hkf : ka = fb := hX ka fb fa ga (Ne.symm hfka) (Ne.symm hgka) (by rw [hBB]; exact hfkb) (by rw [hg]; exact Ne.symm hgfb) (Ne.symm hgfa)
  apply hZ
  rw [← hka, ← hfb, hkf]

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.corner_B_counts
#print axioms Erdos634.Draft.LaczFormal.RG.two_a_steps_at_B
