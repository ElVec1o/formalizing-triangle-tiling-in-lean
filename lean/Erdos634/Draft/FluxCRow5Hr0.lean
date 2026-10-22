-- Draft/FluxCRow5Hr0.lean — Theorem E, π/3 branch, E7b at edge level: discharges the `hr0`
-- hypothesis of `Row5.sixty_forces_not_gt_three` (FluxCRow5Complete.lean) for a REAL
-- `CongruentDissection`, and assembles the π/3 half of Theorem E end to end.  NOT imported into
-- All.lean.  Formalization debt on a paper-level PROVED result ((private working notes, not included)
-- §4); not progress on the three /goal outcomes.
--
-- SURVEY / REDISCOVERY NOTE.  Every geometric ingredient already existed before this file:
-- * `Dissection.eDir_of_side` (Draft/FluxBoundary.lean): a tile edge contained in target side `j`
--   has left-unit direction EQUAL to the target's `leftUnit j` (orientation included).  This is
--   AUDIT.md's (L3) "a tile edge on a side points along the side", with the tile-on-the-left
--   orientation that P123 listed as 3 of 4 cases missing.  P121/P123 re-derived weaker forms.
-- * `Dissection.side_len_sum` (same file): the edges in `sideEdges j` sum to the side length.
-- * `Tri.flux_eq_edgeSign` (Draft/FluxCBoundary.lean): for EVERY edge `k` of a tile,
--   `C_F(T) = χ(π − φ_{k+2})·F(e_k)·K(T)` — the per-edge sign class of AUDIT.md E3/E7b step 2.
-- New here is only the assembly: uniform sign of the tile fluxes at prime `N > 3`, hence every
-- edge sign is `−1`, hence an edge on side `01` (weight `+1`) has `χ(π − φ) = −1`, so its opposite
-- angle is not `π/3`, so it is not a `c`-edge.
import Erdos634.Draft.FluxCRow5Complete

open scoped Classical
open Finset

namespace Erdos634.Geometry

namespace Row5Hr0

variable {N : ℕ}

/-- The `w₁` character anchored at target side `01`. -/
noncomputable abbrev G1 (D : CongruentDissection N) (α : ℝ)
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) : GridChar ℝ :=
  wAt α hα 0 (D.target.leftUnit 0).angle

theorem g1_sq (D : CongruentDissection N) {α : ℝ} (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) :
    ∀ l ∈ (G1 D α hα).L, (G1 D α hα).chi l * (G1 D α hα).chi l = 1 :=
  wAt_sq _ _ _ _

/-- Every tile's angles lie in the grid. -/
theorem tile_angles_mem (D : CongruentDissection N) {α a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (h : D.model.SixtyData α a b c) (i : Fin N) :
    ∀ k, (((D.tile i).angleAt k : ℝ) : Real.Angle) ∈ (G1 D α hα).L := by
  obtain ⟨σ, hσ⟩ := (D.tiles_congruent i).exists_perm
  intro k
  rw [(hσ k).1]
  exact D.model.sixty_angles_mem hα h 0 _ _

/-- `χ(π − π/3) = +1`, `χ(π − α) = −1`, `χ(π − (2π/3 − α)) = −1` for `w₁`. -/
theorem chi_c (α : ℝ) (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (anc : Real.Angle) :
    (wAt α hα 0 anc).chi ((Real.pi - Real.pi / 3 : ℝ) : Real.Angle) = 1 := by
  rw [show Real.pi - Real.pi / 3 = ((2 : ℤ) : ℝ) * (Real.pi / 3) + ((0 : ℤ) : ℝ) * α by
    push_cast; ring, wAt_chi, if_pos (by decide)]

theorem chi_a (α : ℝ) (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (anc : Real.Angle) :
    (wAt α hα 0 anc).chi ((Real.pi - α : ℝ) : Real.Angle) = -1 := by
  rw [show Real.pi - α = ((3 : ℤ) : ℝ) * (Real.pi / 3) + ((-1 : ℤ) : ℝ) * α by
    push_cast; ring, wAt_chi, if_neg (by decide)]

theorem chi_b (α : ℝ) (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (anc : Real.Angle) :
    (wAt α hα 0 anc).chi ((Real.pi - (2 * Real.pi / 3 - α) : ℝ) : Real.Angle) = -1 := by
  rw [show Real.pi - (2 * Real.pi / 3 - α) = ((1 : ℤ) : ℝ) * (Real.pi / 3) + ((1 : ℤ) : ℝ) * α by
    push_cast; ring, wAt_chi, if_neg (by decide)]

/-- **E4, flux form.**  The target's `w₁`-flux, anchored at side `01`, is `3·S`. -/
theorem target_flux (D : CongruentDissection N) {α a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (h : D.model.SixtyData α a b c)
    (hP : ∀ k, D.target.angleAt k = Real.pi / 3) :
    D.target.flux (G1 D α hα).weight = 3 * D.target.oppLen 0 := by
  set G := G1 D α hα
  have e3 : Real.pi / 3 = ((1 : ℤ) : ℝ) * (Real.pi / 3) + ((0 : ℤ) : ℝ) * α := by push_cast; ring
  have htarget : ∀ k, ((D.target.angleAt k : ℝ) : Real.Angle) ∈ G.L := by
    intro k; rw [hP k, e3]; exact wAt_mem _ _ _ _ _ _
  have hchi : G.chi ((Real.pi / 3 : ℝ) : Real.Angle) = -1 := by
    rw [e3, wAt_chi, if_neg (by decide)]
  obtain ⟨e1, e2, -⟩ := Row5.equilateral_boundary D hα 0
    (fun k => D.model.sixty_angles_mem hα h 0 _ k) hP
  have hPK : G.paperK D.target = 3 * D.target.oppLen 0 := by
    unfold GridChar.paperK
    rw [Fin.sum_univ_three, hP 0, hP 1, hP 2, hchi, e1, e2]
    ring
  rw [D.target.flux_eq_of_anchor G (g1_sq D hα) htarget 0 rfl,
    show (0 : Fin 3) + 2 = 2 from rfl, hP 2, hchi, hPK]
  ring

/-- **E7b step 1 (uniform sign), at the level of each tile.**  At prime `N > 3`, every tile's
`w₁`-flux is `+(a + b − c)`. -/
theorem tile_flux_eq (D : CongruentDissection N) {α a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (h : D.model.SixtyData α a b c)
    (hP : ∀ k, D.target.angleAt k = Real.pi / 3) (hNp : N.Prime) (hN3 : 3 < N) :
    ∀ i, (D.tile i).flux (G1 D α hα).weight = a + b - c := by
  set G := G1 D α hα
  set M := a + b - c with hMdef
  obtain ⟨m₁, m₂, -, -, -, -, -, -, hSeq1, -, -, -, -, hpin⟩ := Row5.theoremE_sixty D hα h hP
  obtain ⟨hm1, -⟩ := hpin hNp hN3
  subst hm1
  have hNM : (N : ℝ) * M = 3 * D.target.oppLen 0 := by exact_mod_cast hSeq1
  have hS0 : 0 < D.target.oppLen 0 := D.target.oppLen_pos 0
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hNp.pos
  have hM0 : 0 < M := by
    by_contra hc; push Not at hc
    have : (N : ℝ) * M ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hN0.le hc
    linarith
  have hK : G.tileValue D.model = -M := sixty_tileValue_one D.model hα h
  have hpm : ∀ i, (D.tile i).flux G.weight = M ∨ (D.tile i).flux G.weight = -M := by
    intro i
    have := (D.tile i).flux_grid_pm G (g1_sq D hα) (tile_angles_mem D hα h i)
    rw [G.tileValue_congr (D.tiles_congruent i), hK, neg_neg] at this
    exact this.symm
  let ε : Fin N → ℤ := fun i => if (D.tile i).flux G.weight = M then 1 else -1
  have hε : ∀ i, ε i = 1 ∨ ε i = -1 := by
    intro i; by_cases hi : (D.tile i).flux G.weight = M
    · left; exact if_pos hi
    · right; exact if_neg hi
  have hεv : ∀ i, (D.tile i).flux G.weight = (ε i : ℝ) * M := by
    intro i; by_cases hi : (D.tile i).flux G.weight = M
    · rw [show ε i = 1 from if_pos hi]; push_cast; rw [one_mul, hi]
    · rw [show ε i = -1 from if_neg hi]; push_cast
      rcases hpm i with h1 | h1
      · exact absurd h1 hi
      · rw [h1, neg_one_mul]
  have hsum : (∑ i, (ε i : ℝ)) * M = (N : ℝ) * M := by
    rw [Finset.sum_mul, ← Finset.sum_congr rfl fun i _ => hεv i,
      D.flux_cancel G.weight G.weight_odd, target_flux D hα h hP, hNM]
  have hsumR : (∑ i, (ε i : ℝ)) = (N : ℝ) := mul_right_cancel₀ hM0.ne' hsum
  have hsumZ : ∑ i, ε i = (N : ℤ) := by exact_mod_cast hsumR
  have hall := uniform_sign_pos ε hε hsumZ
  intro i
  rw [hεv i, hall i]; push_cast; ring

/-- **E7b step 2 (sign class), edge level.**  At prime `N > 3`, every edge sign of every tile is
`−1`. -/
theorem edgeSign_eq_neg_one (D : CongruentDissection N) {α a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (h : D.model.SixtyData α a b c)
    (hP : ∀ k, D.target.angleAt k = Real.pi / 3) (hNp : N.Prime) (hN3 : 3 < N)
    (i : Fin N) (k : Fin 3) : (G1 D α hα).edgeSign (D.tile i) k = -1 := by
  set G := G1 D α hα
  have hf := (D.tile i).flux_eq_edgeSign G (g1_sq D hα) (tile_angles_mem D hα h i) k
  have hK : G.tileValue D.model = -(a + b - c) := sixty_tileValue_one D.model hα h
  rw [G.tileValue_congr (D.tiles_congruent i), hK,
    tile_flux_eq D hα h hP hNp hN3 i] at hf
  obtain ⟨m₁, m₂, -, -, -, -, -, -, hSeq1, -, -, -, -, hpin⟩ := Row5.theoremE_sixty D hα h hP
  obtain ⟨hm1, -⟩ := hpin hNp hN3
  subst hm1
  have hS0 : 0 < D.target.oppLen 0 := D.target.oppLen_pos 0
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hNp.pos
  have hNM : (N : ℝ) * (a + b - c) = 3 * D.target.oppLen 0 := by exact_mod_cast hSeq1
  have hM0 : a + b - c ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hNM; linarith
  have : (G.edgeSign (D.tile i) k + 1) * (a + b - c) = 0 := by linear_combination hf
  rcases mul_eq_zero.mp this with h1 | h1
  · linarith
  · exact absurd h1 hM0

/-- **E7b steps 3–4: no `c`-edge on side `01`.**  Every tile edge lying on target side `01` has
length `a` or `b`. -/
theorem side_edge_len (D : CongruentDissection N) {α a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (h : D.model.SixtyData α a b c)
    (hP : ∀ k, D.target.angleAt k = Real.pi / 3) (hNp : N.Prime) (hN3 : 3 < N)
    (e : Fin N × Fin 3) (he : e ∈ D.toDissection.sideEdges 0) :
    D.toDissection.eLen e = a ∨ D.toDissection.eLen e = b := by
  set G := G1 D α hα
  have hsub : D.toDissection.eSet e ⊆ D.target.edge 0 := (Finset.mem_filter.mp he).2
  have hdir := D.toDissection.eDir_of_side hsub
  have hw : G.weight ((D.tile e.1).leftUnit e.2) = 1 := by
    have : (D.tile e.1).leftUnit e.2 = D.target.leftUnit 0 := hdir
    unfold GridChar.weight; rw [this]; exact G.val_anchor
  have hs := edgeSign_eq_neg_one D hα h hP hNp hN3 e.1 e.2
  unfold GridChar.edgeSign at hs
  rw [hw, mul_one] at hs
  -- the opposite vertex `v = e.2 + 2` and the model vertex it corresponds to
  obtain ⟨σ, hσ⟩ := (D.tiles_congruent e.1).exists_perm
  obtain ⟨τ, h0, o0, h1, o1, h2, o2⟩ := h
  have hlen : D.toDissection.eLen e = (D.tile e.1).oppLen (e.2 + 2) := by
    unfold Dissection.eLen Tri.oppLen
    have k1 : ∀ k : Fin 3, k + 2 + 1 = k := by decide
    have k2 : ∀ k : Fin 3, k + 2 + 2 = k + 1 := by decide
    rw [k1, k2]
  obtain ⟨m, hm⟩ := τ.surjective (σ (e.2 + 2))
  rw [hlen, (hσ _).2, ← hm]
  rw [(hσ _).1, ← hm] at hs
  have hm3 : m = 0 ∨ m = 1 ∨ m = 2 := by fin_cases m <;> simp
  rcases hm3 with rfl | rfl | rfl
  · exact Or.inl o0
  · exact Or.inr o1
  · rw [h2, chi_c] at hs; norm_num at hs

/-- **E8 with E7b: side `01` is `p·a + q·b`, no `c`-term (`r = 0`).** -/
theorem side_decomposition_r0 (D : CongruentDissection N) {α a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (h : D.model.SixtyData α a b c)
    (hP : ∀ k, D.target.angleAt k = Real.pi / 3) (hNp : N.Prime) (hN3 : 3 < N) :
    ∃ p q : ℕ, dist (D.target.pts 0) (D.target.pts 1) = (p : ℝ) * a + (q : ℝ) * b := by
  set s := D.toDissection.sideEdges 0
  set len := D.toDissection.eLen
  have hsum := D.toDissection.side_len_sum 0
  rw [show (0 : Fin 3) + 1 = 1 from rfl] at hsum
  refine ⟨(s.filter fun e => len e = a).card, (s.filter fun e => ¬ len e = a).card, ?_⟩
  rw [← hsum, ← Finset.sum_filter_add_sum_filter_not s (fun e => len e = a)]
  have hA : ∑ e ∈ s.filter (fun e => len e = a), len e
      = ((s.filter fun e => len e = a).card : ℝ) * a := by
    rw [Finset.sum_congr rfl (fun e he => (Finset.mem_filter.mp he).2),
      Finset.sum_const, nsmul_eq_mul]
  have hB : ∑ e ∈ s.filter (fun e => ¬ len e = a), len e
      = ((s.filter fun e => ¬ len e = a).card : ℝ) * b := by
    rw [Finset.sum_congr rfl (fun e he => ?_), Finset.sum_const, nsmul_eq_mul]
    have hm := Finset.mem_filter.mp he
    exact (side_edge_len D hα h hP hNp hN3 e hm.1).resolve_left hm.2
  rw [hA, hB]

/-- **Theorem E, `π/3` branch, end to end, with `hr0` DISCHARGED.**  An equilateral target
`N`-tiled by congruent copies of a `(α, 2π/3 − α, π/3)` tile with `α/π ∉ ℚ` (reflections allowed,
not edge-to-edge) has `N` not a prime `> 3`. -/
theorem Row5.theoremE_sixty_full (D : CongruentDissection N) {α a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (h : D.model.SixtyData α a b c)
    (hP : ∀ k, D.target.angleAt k = Real.pi / 3) : ¬ (N.Prime ∧ 3 < N) := by
  rintro ⟨hNp, hN3⟩
  obtain ⟨hab2, -, hfin2⟩ := Row5.sixty_closedForms D hα h hP hNp hN3
  obtain ⟨p, q, hpq⟩ := side_decomposition_r0 D hα h hP hNp hN3
  obtain ⟨-, e2, -⟩ := Row5.equilateral_boundary D hα 0
    (fun k => D.model.sixty_angles_mem hα h 0 _ k) hP
  have hd : dist (D.target.pts 0) (D.target.pts 1) = D.target.oppLen 0 := by
    rw [← e2]; unfold Tri.oppLen; rfl
  rw [hd] at hpq
  exact Row5.sixty_forces_not_gt_three hNp hN3 hab2 hfin2 (D.target.oppLen_pos 0)
    (p : ℤ) (q : ℤ) 0 (by positivity) (by positivity) (by rw [hpq]; push_cast; ring) rfl

/-! ## Non-vacuity checks on the pieces that are not dissection-bound.
The three `χ` values that drive the edge-level exclusion are genuinely different (the `c`-edge
value is `+1`, the other two `−1`), so the exclusion in `side_edge_len` is not trivial. -/

example (α : ℝ) (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (anc : Real.Angle) :
    (wAt α hα 0 anc).chi ((Real.pi - Real.pi / 3 : ℝ) : Real.Angle)
      ≠ (wAt α hα 0 anc).chi ((Real.pi - α : ℝ) : Real.Angle) := by
  rw [chi_c, chi_a]; norm_num

-- The hypotheses `D.model.SixtyData α a b c` (with `α/π ∉ ℚ`) and `hP` are each satisfiable in
-- Lean (`Draft/FluxCRow5Witness.lean`: `data387`, the `(3,8,7)` tile; the equilateral `E2`).  A
-- JOINT witness (a Lean `CongruentDissection` of an equilateral triangle by that tile) does not
-- exist in the corpus; real ones exist on paper at composite `N` (e.g. Herdt `N = 1944`).  At prime
-- `N > 3` the main theorem says the joint bundle is unsatisfiable — that is its content.

end Row5Hr0

end Erdos634.Geometry

#print axioms Erdos634.Geometry.Row5Hr0.target_flux
#print axioms Erdos634.Geometry.Row5Hr0.tile_flux_eq
#print axioms Erdos634.Geometry.Row5Hr0.edgeSign_eq_neg_one
#print axioms Erdos634.Geometry.Row5Hr0.side_edge_len
#print axioms Erdos634.Geometry.Row5Hr0.side_decomposition_r0
#print axioms Erdos634.Geometry.Row5Hr0.Row5.theoremE_sixty_full
