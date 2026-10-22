import Erdos634.Draft.LaczFormalJunctionThm1

/-!
# Band junction rules I and Im (Theorem 2): the interior pair

Erdős #634, base-`β` band.  `PROOF_C1.md` Theorem 2.  Credit: AI assistant (band lemma / item-3 proposal),
Beeson–Roșu, Beeson, Laczkovich, Paliy.

The corner tile `cBA` now sits at an interior base point `Q` (not at a target corner), so its top
vertex `G` is interior to the target.  The hand proof's input is that `G` lies in the **relative
interior of an edge of the `α`-tile `U`** adjacent to `cBA`'s `a`-edge `QG` (an `α`-tile has sides
`b,c > a` there); then the line `PG` enters `U` immediately beyond `G` and no far-side edge of the
chord `PG` can pass through `G`, so the far side is a single `b`-edge from `P` to `G`, as in
Theorem 1, and the same boundary-figure contradiction at `P` follows.

`band_interior_pair_impossible` proves everything after that input.  The input itself is the
hypothesis `hUa/hUb`: a tile `U` has vertices `G + l₁(G−Q)`, `G + l₂(G−Q)` (`Q` the third vertex of
the tile `T₁` with edge `PG`) with `l₁ < 0 < l₂`, i.e. an edge along the line `QG` with `G`
strictly between its ends.  That input is derived in `LaczFormalJunctionAdj2.exists_alpha_edge`, and
the two are assembled in `LaczFormalJunctionRuleI.band_rule_I`.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.LaczJunction

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.Draft.TraceCovering

variable {N : ℕ}

/-- **Theorem 2 (interior band pair), conditional on the edge `hU` of the adjacent `α`-tile.** -/
theorem band_interior_pair_impossible (D : CongruentDissection N) (e f : ℕ) (he : 1 ≤ e)
    (hef : e < f) (hcop : Nat.Coprime e f) (α β γ : ℝ)
    (hγdef : γ = 2 * α + β) (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hα0 : 0 < α) (hβ0 : 0 < β)
    (hα' : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hβ' : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hγ' : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    (hsa : sideOpp D.model 0 = (ta e f : ℝ)) (hsb : sideOpp D.model 1 = (tb e f : ℝ))
    (hsc : sideOpp D.model 2 = (tc e f : ℝ))
    {P G : Plane}
    {p q r : Fin 3} (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (hP : P ∈ openSegment ℝ (D.target.pts p) (D.target.pts q))
    (hGc : G ∈ D.target.carrier) (hGr : 0 < D.target.basis.coord r G)
    (hPG : dist P G = (tb e f : ℝ))
    (i1 : Fin N) (j1 : Fin 3) (hPv : (D.tile i1).pts j1 = P) (hGv : (D.tile i1).pts (j1+1) = G)
    (iU : Fin N) (l1 l2 : ℝ) (hl1 : l1 < 0) (hl2 : 0 < l2)
    (hUa : ∃ ka, (D.tile iU).pts ka = G + l1 • (G - (D.tile i1).pts (j1+2)))
    (hUb : ∃ kb, (D.tile iU).pts kb = G + l2 • (G - (D.tile i1).pts (j1+2)))
    (i2 : Fin N) (j2 : Fin 3) (hγ2 : (D.tile i2).localAngle P = γ)
    (hb2 : dist ((D.tile i2).pts j2) ((D.tile i2).pts (j2+1)) = (tb e f : ℝ))
    (hb2a : D.target.basis.coord r ((D.tile i2).pts j2) = 0)
    (hb2b : D.target.basis.coord r ((D.tile i2).pts (j2+1)) = 0) : False := by
  classical
  have hB : 0 < tb e f := b_pos e f he hef
  have hBr : (0:ℝ) < (tb e f : ℝ) := by exact_mod_cast hB
  have hne : P ≠ G := by
    intro h; rw [h, dist_self] at hPG; linarith
  obtain ⟨hint, hbef⟩ := chord_geometry_int D.target hpq hpr hqr hP hGc hGr
  obtain ⟨hfront, hnv⟩ := side_frontier D.target hpq hpr hqr hP
  set Q := (D.tile i1).pts (j1+2) with hQ
  have hfar := far_edge_gen D.toDissection (ta e f) (tb e f) (tc e f)
    (fun x y z h => cover_unique e f x y z he hef hcop h)
    (fun i k => by
      rcases edge_length_mem D i k with h | h | h
      · exact Or.inr (Or.inr (by rw [h, hsc]))
      · exact Or.inr (Or.inl (by rw [h, hsb]))
      · exact Or.inl (by rw [h, hsa]))
    hint hbef hPG hB i1 j1 hPv hGv
    (fun f' c hf0 hfP hfG hfV => by
      obtain ⟨ka, hka⟩ := hUa
      obtain ⟨kb, hkb⟩ := hUb
      have hw : G ∈ segment ℝ ((D.tile iU).pts ka) ((D.tile iU).pts kb) := by
        have hden : 0 < l2 - l1 := by linarith
        refine ⟨l2 / (l2 - l1), -l1 / (l2 - l1), div_nonneg hl2.le hden.le,
          div_nonneg (by linarith) hden.le, ?_, ?_⟩
        · field_simp; ring
        · rw [hka, hkb]
          have hab : l2 / (l2 - l1) * l1 + -l1 / (l2 - l1) * l2 = 0 := by field_simp; ring
          have key : (l2 / (l2 - l1)) • (G + l1 • (G - Q)) + (-l1 / (l2 - l1)) • (G + l2 • (G - Q))
              = (l2 / (l2 - l1) + -l1 / (l2 - l1)) • G
                + (l2 / (l2 - l1) * l1 + -l1 / (l2 - l1) * l2) • (G - Q) := by module
          rw [key, hab, zero_smul, add_zero]
          have : l2 / (l2 - l1) + -l1 / (l2 - l1) = 1 := by field_simp; ring
          rw [this, one_smul]
      have hu1 : (D.tile iU).pts ka ∈ (D.tile iU).carrier :=
        subset_convexHull ℝ _ ⟨ka, rfl⟩
      have hu2 : (D.tile iU).pts kb ∈ (D.tile iU).carrier :=
        subset_convexHull ℝ _ ⟨kb, rfl⟩
      have hGU : G ∈ (D.tile iU).carrier := (D.tile iU).convex.segment_subset hu1 hu2 hw
      refine nstr_end_across D.toDissection hne f' c hf0 hfP hfG iU hGU hu1 hu2 ?_ ?_
      · rw [hka, map_add, map_smul, map_sub, hfG, smul_eq_mul]
        nlinarith
      · rw [hkb, map_add, map_smul, map_sub, hfG, smul_eq_mul]
        nlinarith)
  exact corner_core D e f he hef hcop α β γ hγdef hrel hirr hα0 hβ0 hα' hβ' hγ' hsa hsb hsc
    hfront hnv hGr hPG i1 j1 hPv hGv hfar i2 j2 hγ2 hb2 hb2a hb2b

#print axioms band_interior_pair_impossible

end Erdos634.LaczJunction
