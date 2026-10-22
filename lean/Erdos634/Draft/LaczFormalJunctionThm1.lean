import Erdos634.Draft.LaczFormalJunctionArith
import Erdos634.Draft.LaczFormalJunctionAngle
import Erdos634.Draft.LaczFormalJunctionChord
import Erdos634.Draft.LaczFormalJunctionTile
import Erdos634.Draft.LaczFormalJunctionWall
import Erdos634.CertCoord

/-!
# Band junction rule S (Theorem 1), proved for a real `CongruentDissection`

Erdős #634, base-`β` band.  Formalizes (private working notes, not included) Theorem 1 from
real geometry.  Credit: AI assistant (band lemma / item-3 proposal, C1/C2/C3 observations), Beeson–Roșu
(tiles, band grammar), Beeson, Laczkovich, Paliy.

## What is proved
`band_corner_pair_impossible`: let `D` be a `CongruentDissection` of a triangle whose tile has
sides `(a,b,c) = (ef, f²−e², f²)` (`1 ≤ e < f`, coprime) with corner angles `α,β,γ`,
`3α+2β = π`, `γ = 2α+β`, `α ∉ ℚπ`.  Suppose

* `P` lies strictly inside the side `[A₀,A₁]` and `G` strictly inside the side `[A₀,A₂]` of the
  target (for the band word `cBA, bGA` at the left corner `A₀`: `P` is the junction on the base,
  `G` the top vertex of the corner tile, interior of the left side because `L > a`);
* a tile `T₁` has the edge `[P,G]` of length `b` (the `b`-edge of the corner tile `cBA`);
* a tile `T₂` presents `γ` at `P` and has a `b`-edge on the base line (the tile `bGA`).

Then `False`.  The proof is the hand proof: the far side of the chord `PG` is a single `b`-edge
(`far_edge_exists`, using `TraceCovering.wall_sum` and `cover_unique`); its tile `T'` presents `α`
or `γ` at `P` (`bedge_both_ends`); the boundary figure at `P` is `{α,β,γ}`, one tile each
(`congruentDissection_boundary_figure_cases_at_vertex`), and `T₁, T', T₂` are three distinct tiles
among which two would have to share a corner of the same type.

The wedge fillings (L-b) of the hand proof are not needed: the figure classification at `P`
replaces them.  No `sorry`, no hypothesis beyond those listed.

## What is not proved here
That the word `cBA, bGA` supplies the hypotheses (`P`, `G` interior to the two target sides, the
`b`-edge `PG` of `cBA`, `bGA` presenting `γ` at `P` with its `b`-edge on the base) is the
word-to-geometry step: the corner tile's `c`-edge on the base and `a`-edge on the left side give
`P` and `G` by distances `c` and `a` from the corner, interior to the sides when `c < base` and
`a < L`.  It is stated as hypotheses.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.LaczJunction

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.Geometry.Dissection

variable {N : ℕ}

/-- A point strictly inside side `[A_p,A_q]` is on the frontier of the target and is not a vertex. -/
theorem side_frontier (T : Tri) {p q r : Fin 3} (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    {P : Plane} (hP : P ∈ openSegment ℝ (T.pts p) (T.pts q)) :
    P ∈ frontier T.carrier ∧ P ∉ Set.range T.pts := by
  obtain ⟨s, hs0, hs1, p0, p1, p2⟩ := coords_side T hpq hpr hqr hP
  have hmem : P ∈ T.carrier := by
    rw [T.carrier_eq_nonneg_coord]
    intro j
    rcases fin3_cover p q r j hpq hpr hqr with rfl | rfl | rfl
    · rw [p0]; linarith
    · rw [p1]; linarith
    · rw [p2]
  refine ⟨?_, ?_⟩
  · refine ⟨subset_closure hmem, ?_⟩
    rw [T.mem_interior_iff_coord_pos]
    intro h; have := h r; rw [p2] at this; exact lt_irrefl _ this
  · rintro ⟨j, hj⟩
    have h0 := coord_vertex T p j
    have h1 := coord_vertex T q j
    have h2 := coord_vertex T r j
    rw [hj, p0] at h0
    rw [hj, p1] at h1
    rw [hj, p2] at h2
    rcases fin3_cover p q r j hpq hpr hqr with rfl | rfl | rfl
    · simp [hpq.symm] at h1; linarith
    · simp [hpq] at h0; linarith
    · simp [hpr, hqr] at h2

/-- **Corner core.**  The angle-and-distinctness half of Theorems 1 and 2: given the far-side
`b`-edge `[P,G]` of another tile `T'`, the boundary figure at `P` forces a contradiction. -/
theorem corner_core (D : CongruentDissection N) (e f : ℕ) (he : 1 ≤ e)
    (hef : e < f) (hcop : Nat.Coprime e f) (α β γ : ℝ)
    (hγdef : γ = 2 * α + β) (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hα0 : 0 < α) (hβ0 : 0 < β)
    (hα' : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hβ' : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hγ' : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    (hsa : sideOpp D.model 0 = (ta e f : ℝ)) (hsb : sideOpp D.model 1 = (tb e f : ℝ))
    (hsc : sideOpp D.model 2 = (tc e f : ℝ))
    {P G : Plane} {r : Fin 3}
    (hfront : P ∈ frontier D.target.carrier) (hnv : P ∉ Set.range D.target.pts)
    (hGr : 0 < D.target.basis.coord r G)
    (hPG : dist P G = (tb e f : ℝ))
    (i1 : Fin N) (j1 : Fin 3) (hPv : (D.tile i1).pts j1 = P) (hGv : (D.tile i1).pts (j1+1) = G)
    (hfar : ∃ (i' : Fin N) (k : Fin 3), i' ≠ i1 ∧
      dist ((D.tile i').pts k) ((D.tile i').pts (k+1)) = (tb e f : ℝ) ∧
      (((D.tile i').pts k = P ∧ (D.tile i').pts (k+1) = G) ∨
       ((D.tile i').pts k = G ∧ (D.tile i').pts (k+1) = P)))
    (i2 : Fin N) (j2 : Fin 3) (hγ2 : (D.tile i2).localAngle P = γ)
    (hb2 : dist ((D.tile i2).pts j2) ((D.tile i2).pts (j2+1)) = (tb e f : ℝ))
    (hb2a : D.target.basis.coord r ((D.tile i2).pts j2) = 0)
    (hb2b : D.target.basis.coord r ((D.tile i2).pts (j2+1)) = 0) : False := by
  classical
  -- arithmetic facts about the three side lengths
  have hneab : sideOpp D.model 0 ≠ sideOpp D.model 1 := by
    rw [hsa, hsb]; intro h
    have h' : ta e f = tb e f := by exact_mod_cast h
    exact a_not_dvd_b e f he hef hcop (h' ▸ dvd_refl _)
  have hnebc : sideOpp D.model 1 ≠ sideOpp D.model 2 := by
    rw [hsb, hsc]; intro h
    have h' : tb e f = tc e f := by exact_mod_cast h
    have := b_lt_c e f he hef; omega
  have hB : 0 < tb e f := b_pos e f he hef
  obtain ⟨i', k, hi'1, hbk, hends⟩ := hfar
  -- no tile with a `b`-edge ending at `G` is `T₂`
  have hne2 : ∀ (i : Fin N) (k : Fin 3),
      dist ((D.tile i).pts k) ((D.tile i).pts (k+1)) = sideOpp D.model 1 →
      ((D.tile i).pts k = G ∨ (D.tile i).pts (k+1) = G) → i ≠ i2 := by
    intro i k hk hG' hi
    subst hi
    have hkj := two_bedges D hneab hnebc i k j2 hk (by rw [hsb]; exact hb2)
    subst hkj
    rcases hG' with h | h
    · rw [h] at hb2a; exact absurd hb2a hGr.ne'
    · rw [h] at hb2b; exact absurd hb2b hGr.ne'
  have hb1 : dist ((D.tile i1).pts j1) ((D.tile i1).pts (j1+1)) = sideOpp D.model 1 := by
    rw [hPv, hGv, hPG, hsb]
  have hbk' : dist ((D.tile i').pts k) ((D.tile i').pts (k+1)) = sideOpp D.model 1 := by
    rw [hbk, hsb]
  have hi1 : i1 ≠ i2 := hne2 i1 j1 hb1 (Or.inr hGv)
  have hi' : i' ≠ i2 := hne2 i' k hbk' (by
    rcases hends with ⟨_, h⟩ | ⟨h, _⟩
    · exact Or.inr h
    · exact Or.inl h)
  -- boundary figure at `P`
  have hαβ : α ≠ β := by
    intro h
    apply hirr
    refine ⟨1/5, ?_⟩
    have : α = Real.pi / 5 := by rw [← h] at hrel; linarith
    rw [this]; push_cast; ring
  have hfig := congruentDissection_boundary_figure_cases_at_vertex D α β γ hαβ
    (by rw [hγdef]; intro h; linarith) (by intro h; linarith) hα0.ne'
    (by rw [hγdef]; intro h; linarith) (by intro h; linarith) hβ0.ne'
    (by intro h; linarith) (by intro h; linarith) Real.pi_ne_zero hγdef hrel hirr hα' hβ' hγ'
    hfront hnv i2 (Or.inr (Or.inr hγ2))
  have hmemγ : i2 ∈ ({i | (D.tile i).localAngle P = γ} : Finset (Fin N)) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]; exact hγ2
  rcases hfig with ⟨_, _, hg0⟩ | ⟨hαc, _, hγc⟩
  · rw [Finset.card_eq_zero.mp hg0] at hmemγ; simp at hmemγ
  · obtain ⟨x2, hx2⟩ := Finset.card_eq_one.mp hγc
    obtain ⟨y, hy⟩ := Finset.card_eq_one.mp hαc
    have hγmem : ∀ i, (D.tile i).localAngle P = γ → i = i2 := by
      intro i hi
      have h1 : i ∈ ({i | (D.tile i).localAngle P = γ} : Finset (Fin N)) := by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]; exact hi
      rw [hx2] at h1 hmemγ
      simp at h1 hmemγ
      rw [h1, hmemγ]
    have hαmem : ∀ i, (D.tile i).localAngle P = α → i = y := by
      intro i hi
      have h1 : i ∈ ({i | (D.tile i).localAngle P = α} : Finset (Fin N)) := by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]; exact hi
      rw [hy] at h1; simpa using h1
    -- `T₁` presents `α` at `P`
    have hT1 : (D.tile i1).localAngle P = α := by
      have := (bedge_both_ends D α β γ hα' hβ' hγ' hneab hnebc i1 j1 hb1).1
      rw [hPv] at this
      rcases this with h | h
      · exact h
      · exact absurd (hγmem i1 h) hi1
    -- `T'` presents `α` at `P`
    have hT' : (D.tile i').localAngle P = α := by
      have hboth := bedge_both_ends D α β γ hα' hβ' hγ' hneab hnebc i' k hbk'
      rcases hends with ⟨h1, _⟩ | ⟨_, h2⟩
      · have := hboth.1; rw [h1] at this
        rcases this with h | h
        · exact h
        · exact absurd (hγmem i' h) hi'
      · have := hboth.2; rw [h2] at this
        rcases this with h | h
        · exact h
        · exact absurd (hγmem i' h) hi'
    exact hi'1 ((hαmem _ hT').trans (hαmem _ hT1).symm)

/-- **Theorem 1 (band corner pair), for a real `CongruentDissection`.** -/
theorem band_corner_pair_impossible (D : CongruentDissection N) (e f : ℕ) (he : 1 ≤ e)
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
    (hG : G ∈ openSegment ℝ (D.target.pts p) (D.target.pts r))
    (hPG : dist P G = (tb e f : ℝ))
    (i1 : Fin N) (j1 : Fin 3) (hPv : (D.tile i1).pts j1 = P) (hGv : (D.tile i1).pts (j1+1) = G)
    (i2 : Fin N) (j2 : Fin 3) (hγ2 : (D.tile i2).localAngle P = γ)
    (hb2 : dist ((D.tile i2).pts j2) ((D.tile i2).pts (j2+1)) = (tb e f : ℝ))
    (hb2a : D.target.basis.coord r ((D.tile i2).pts j2) = 0)
    (hb2b : D.target.basis.coord r ((D.tile i2).pts (j2+1)) = 0) : False := by
  have hsb' : sideOpp D.model 1 = (tb e f : ℝ) := hsb
  have hB : 0 < tb e f := b_pos e f he hef
  obtain ⟨t, ht0, ht1, g0, g2, g1⟩ := coords_side D.target hpr hpq hqr.symm hG
  have hfar := far_edge_exists D.toDissection hpq hpr hqr (ta e f) (tb e f) (tc e f)
    (fun x y z h => cover_unique e f x y z he hef hcop h)
    (fun i k => by
      rcases edge_length_mem D i k with h | h | h
      · exact Or.inr (Or.inr (by rw [h, hsc]))
      · exact Or.inr (Or.inl (by rw [h, hsb]))
      · exact Or.inl (by rw [h, hsa]))
    hP hG hPG hB i1 j1 hPv hGv
  obtain ⟨hfront, hnv⟩ := side_frontier D.target hpq hpr hqr hP
  exact corner_core D e f he hef hcop α β γ hγdef hrel hirr hα0 hβ0 hα' hβ' hγ' hsa hsb hsc
    hfront hnv (by rw [g2]; exact ht0) hPG i1 j1 hPv hGv hfar i2 j2 hγ2 hb2 hb2a hb2b

/-! ## Non-vacuity of the geometric hypotheses

`band_corner_pair_impossible` is a no-tiling statement: its hypotheses together describe a
configuration inside a tiling of a band target, so the full conjunction cannot be satisfied (that is
the theorem).  Each *ingredient* is satisfiable: the angle and irrationality hypotheses by the real
tile `(e,f) = (2,3)` (`model_hyps_23`, `(a,b,c) = (6,5,9)`), and the chord geometry by a concrete
triangle (below). -/

open Erdos634.CertCoord in
/-- The chord hypotheses of `far_edge_exists` hold for `T = (0,0),(2,0),(0,2)`, `P = (1,0)`,
`G = (0,1)`; the conclusions of `chord_geometry` are then instances of the general theorem. -/
theorem chord_geometry_witness :
    ∃ (T : Tri) (P G : Plane),
      P ∈ openSegment ℝ (T.pts 0) (T.pts 1) ∧ G ∈ openSegment ℝ (T.pts 0) (T.pts 2) ∧
      (∀ t : ℝ, 0 < t → t < 1 → AffineMap.lineMap P G t ∈ interior T.carrier) ∧
      (∀ t : ℝ, t < 0 → AffineMap.lineMap P G t ∉ T.carrier) ∧
      (∀ t : ℝ, 1 < t → AffineMap.lineMap P G t ∉ T.carrier) := by
  have hdet : det3 0 0 2 0 0 2 ≠ 0 := by simp [det3]
  refine ⟨mkTri 0 0 2 0 0 2 hdet, mkPt 1 0, mkPt 0 1, ?_, ?_, ?_⟩
  · refine ⟨1/2, 1/2, by norm_num, by norm_num, by norm_num, ?_⟩
    ext i; fin_cases i <;> simp [mkPt, EuclideanSpace.equiv] <;> norm_num
  · refine ⟨1/2, 1/2, by norm_num, by norm_num, by norm_num, ?_⟩
    ext i; fin_cases i <;> simp [mkPt, EuclideanSpace.equiv] <;> norm_num
  · refine chord_geometry (mkTri 0 0 2 0 0 2 hdet) (p := 0) (q := 1) (r := 2) (by decide)
      (by decide) (by decide) ?_ ?_
    · refine ⟨1/2, 1/2, by norm_num, by norm_num, by norm_num, ?_⟩
      ext i; fin_cases i <;> simp [mkPt, EuclideanSpace.equiv] <;> norm_num
    · refine ⟨1/2, 1/2, by norm_num, by norm_num, by norm_num, ?_⟩
      ext i; fin_cases i <;> simp [mkPt, EuclideanSpace.equiv] <;> norm_num

#print axioms band_corner_pair_impossible

end Erdos634.LaczJunction
