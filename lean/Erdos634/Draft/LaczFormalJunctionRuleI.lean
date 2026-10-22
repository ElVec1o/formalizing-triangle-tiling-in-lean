import Erdos634.Draft.LaczFormalJunctionAdj2

/-!
# Band junction rule I (and its mirror Im), for a real `CongruentDissection`

Erdős #634, base-`β` band.  `PROOF_C1.md` Theorem 2, from real geometry.  Credit: AI assistant (band lemma
/ item-3 proposal, C1/C2/C3 observations), Beeson–Roșu, Beeson, Laczkovich, Paliy.

`band_rule_I`: no `CongruentDissection` has the configuration `X, cBA, bGA` at consecutive positions
of a side word with `cBA` at an interior base point `Q` and `X ∈ {cAB, bAG}`, where

* `P`, `Q` lie strictly inside the side `[A_p,A_q]` (the base);
* `T₁ = cBA` has vertices `P` (corner `α`), `G`, `Q` (corner `β`) with `|PG| = b`;
* `X` is a tile different from `T₁` with a vertex at `Q`, presenting `β` (`cAB`) or `γ` (`bAG`), and
  an edge from `Q` along the base away from `P` (so it lies to the left of `Q`);
* `T₂ = bGA` presents `γ` at `P` and has a `b`-edge on the base line;
* the band inequality `a < b` (`LaczFormalJunctionArith.band_a_lt_b`).

The proof is the hand proof: the figure at `Q` makes the tile `U` next to `cBA`'s `a`-edge an
`α`-corner (`exists_alpha_edge`), whose edge along `QG` has length `b` or `c`, so the far side of the
chord `PG` is a single `b`-edge (`band_interior_pair_impossible`), against the figure at `P`.

The mirror rule Im is the same statement applied to the reflected labelling of the target (the
hypotheses are symmetric in the two base directions).

Axiom-clean; no `sorry`.
-/

namespace Erdos634.LaczJunction

open Erdos634.Geometry Erdos634.TilePlacement

variable {N : ℕ}

theorem band_rule_I (D : CongruentDissection N) (e f : ℕ) (he : 1 ≤ e) (hef : e < f)
    (hcop : Nat.Coprime e f) (hband : ta e f < tb e f) (α β γ : ℝ)
    (hγdef : γ = 2 * α + β) (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hα0 : 0 < α) (hβ0 : 0 < β)
    (hα' : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hβ' : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hγ' : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    (hsa : sideOpp D.model 0 = (ta e f : ℝ)) (hsb : sideOpp D.model 1 = (tb e f : ℝ))
    (hsc : sideOpp D.model 2 = (tc e f : ℝ))
    {p q r : Fin 3} (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    {P Q G : Plane}
    (hP : P ∈ openSegment ℝ (D.target.pts p) (D.target.pts q))
    (hQ : Q ∈ openSegment ℝ (D.target.pts p) (D.target.pts q))
    (hPG : dist P G = (tb e f : ℝ))
    (i1 : Fin N) (j1 : Fin 3) (hPv : (D.tile i1).pts j1 = P) (hGv : (D.tile i1).pts (j1+1) = G)
    (hQv : (D.tile i1).pts (j1+2) = Q)
    (hα1 : (D.tile i1).localAngle P = α) (hβ1 : (D.tile i1).localAngle Q = β)
    (iX : Fin N) (kX mX : Fin 3) (Y : Plane) (hXQ : (D.tile iX).pts kX = Q)
    (hXY : (D.tile iX).pts mX = Y) (hmk : mX ≠ kX) (s : ℝ) (hs : 0 < s)
    (hYQ : Y - Q = (-s) • (P - Q))
    (hXne : iX ≠ i1) (hXang : (D.tile iX).localAngle Q = β ∨ (D.tile iX).localAngle Q = γ)
    (i2 : Fin N) (j2 : Fin 3) (hγ2 : (D.tile i2).localAngle P = γ)
    (hb2 : dist ((D.tile i2).pts j2) ((D.tile i2).pts (j2+1)) = (tb e f : ℝ))
    (hb2a : D.target.basis.coord r ((D.tile i2).pts j2) = 0)
    (hb2b : D.target.basis.coord r ((D.tile i2).pts (j2+1)) = 0) : False := by
  classical
  obtain ⟨sP, hsP0, hsP1, hP0, hP1, hP2⟩ := coords_side D.target hpq hpr hqr hP
  obtain ⟨sQ, hsQ0, hsQ1, hQ0, hQ1, hQ2⟩ := coords_side D.target hpq hpr hqr hQ
  have hGc : G ∈ D.target.carrier :=
    tile_subset_target D.toDissection i1 (subset_convexHull ℝ _ ⟨j1+1, hGv⟩)
  have hGnn : 0 ≤ D.target.basis.coord r G := by
    have := hGc
    rw [D.target.carrier_eq_nonneg_coord] at this
    exact this r
  have hGr : 0 < D.target.basis.coord r G := by
    rcases hGnn.lt_or_eq with h | h
    · exact h
    · exfalso
      refine tile_vertex_off_side D.target (D.tile i1) r j1 ?_ ?_ ?_
      · rw [hPv]; exact hP2
      · rw [hGv]; exact h.symm
      · rw [hQv]; exact hQ2
  obtain ⟨iU, l1, l2, hl1, hl2, hUa, hUb⟩ := exists_alpha_edge D e f he hef hcop hband α β γ
    hγdef hrel hirr hα0 hβ0 hα' hβ' hγ' hsa hsb hsc hpq hpr hqr hP hQ hGr i1 j1 hPv hGv hQv hα1
    hβ1 iX kX mX Y hXQ hXY hmk s hs hYQ hXne hXang
  rw [← hQv] at hUa hUb
  exact band_interior_pair_impossible D e f he hef hcop α β γ hγdef hrel hirr hα0 hβ0 hα' hβ' hγ'
    hsa hsb hsc hpq hpr hqr hP hGc hGr hPG i1 j1 hPv hGv iU l1 l2 hl1 hl2 hUa hUb i2 j2 hγ2 hb2
    hb2a hb2b

#print axioms band_rule_I

end Erdos634.LaczJunction
