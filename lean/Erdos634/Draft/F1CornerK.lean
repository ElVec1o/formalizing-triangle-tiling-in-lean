-- Draft/F1CornerK.lean — K₁ counting: at V₁ of an F₁ target, the filling is (1,0,0,0).
--
-- Proves:
--   `f1_corner_single_tile` (algebraic):  if Σ localAngles = α with terms ∈ {α,π/3−α,2π/3,π,0},
--                                         counts are (1,0,0,0).
--   `f1_v1_tile_unique` (geometric):      exactly one tile covers V₁ of an F₁ target (IrrPi α).
--
-- NOT proved in THIS file (blockers recorded at the time of writing; STALE as of 2026-10-01 — the final
-- statement `F1FreeProof.f1_free_statement` is proved, so these are discharged downstream; see
-- F1CornerAlign / F1EdgeAlign (K1: edges at V₁ run along the sides) and F1BoundaryK2 / F1K2Core (K2:
-- γ-vertex segment-intersection)):
--   BLOCKER-K1: "T₁'s edges at V₁ run along the sides" — needs AngleWedge / ray-alignment for F₁.
--   BLOCKER-K2: "γ-vertex X ∈ V₁V₂ ∩ (V₂V₃ ∪ V₃V₁) = {V₁,V₂}" — segment-intersection lemma.
--
-- ZERO sorry.

import Erdos634.Draft.F1Bridge
import Erdos634.TileAt

open scoped Classical
open Erdos634.Draft.TheoremPConditional

namespace Erdos634.Geometry

open Erdos634.TilePlacement (corner_multiplicities)
open Erdos634.Geometry.Dissection (congruentDissection_localAngle_mem)

/-! ## Distinctness lemmas derived from IrrPi -/

lemma irrPi_ne_zero {α : ℝ} (h : IrrPi α) : α ≠ 0 :=
  fun hα => h ⟨0, by simp [hα]⟩

lemma irrPi_ne_pi {α : ℝ} (h : IrrPi α) : α ≠ Real.pi :=
  fun hα => h ⟨1, by simp [hα]⟩

-- α ≠ 2π/3
lemma irrPi_ne_twoThirdsPi {α : ℝ} (h : IrrPi α) : α ≠ 2 * Real.pi / 3 :=
  fun hα => h ⟨2/3, by push_cast; linarith⟩

-- α ≠ π/3 − α  (= α ≠ π/6)
lemma irrPi_ne_beta {α : ℝ} (h : IrrPi α) : α ≠ Real.pi / 3 - α :=
  fun hαβ => h ⟨1/6, by push_cast; linarith⟩

-- π/3 − α ≠ 0  (= α ≠ π/3)
lemma irrPi_beta_ne_zero {α : ℝ} (h : IrrPi α) : Real.pi / 3 - α ≠ 0 :=
  fun hb => h ⟨1/3, by push_cast; linarith⟩

-- π/3 − α ≠ π  (= α ≠ −2π/3)
lemma irrPi_beta_ne_pi {α : ℝ} (h : IrrPi α) : Real.pi / 3 - α ≠ Real.pi :=
  fun hb => h ⟨-2/3, by push_cast; linarith⟩

-- π/3 − α ≠ 2π/3  (= α ≠ −π/3)
lemma irrPi_beta_ne_gamma {α : ℝ} (h : IrrPi α) : Real.pi / 3 - α ≠ 2 * Real.pi / 3 :=
  fun hb => h ⟨-1/3, by push_cast; linarith⟩

lemma twoThirdsPi_ne_pi : (2 * Real.pi / 3 : ℝ) ≠ Real.pi := by
  intro h; linarith [Real.pi_pos]

lemma twoThirdsPi_ne_zero : (2 * Real.pi / 3 : ℝ) ≠ 0 := by
  intro h; linarith [Real.pi_pos]

/-! ## Algebraic counting: the V₁ filling is (1,0,0,0) -/

/-- **F₁ corner counting (algebraic).**  If nonneg integers (p,q,r,s) satisfy
  p·α + q·(π/3−α) + r·(2π/3) + s·π = α  with α/π ∉ ℚ,
then (p,q,r,s) = (1,0,0,0).

This is K₁ Step 2 of `prop:F1free`. -/
theorem f1_corner_single_tile {α : ℝ} (hirr : IrrPi α) (p q r s : ℕ)
    (hsum : (p : ℝ) * α + (q : ℝ) * (Real.pi / 3 - α) +
            (r : ℝ) * (2 * Real.pi / 3) + (s : ℝ) * Real.pi = α) :
    p = 1 ∧ q = 0 ∧ r = 0 ∧ s = 0 := by
  -- Rearrange to 3(p−q−1)·α + (q+2r+3s)·π = 0, then apply angle_indep
  obtain ⟨hA, hB⟩ := angle_indep hirr
    (3 * ((p : ℤ) - q - 1)) ((q : ℤ) + 2 * r + 3 * s)
    (by push_cast; linarith [hsum, show (3 : ℝ) * (Real.pi / 3) = Real.pi from by ring])
  omega

/-! ## Membership of tile angles in {α, π/3−α, 2π/3, π, 0} -/

/-- For a 2π/3-model CongruentDissection, each tile's local angle at any target vertex
lies in {α, π/3−α, 2π/3, π, 0} (the model's three angles plus π and 0). -/
lemma f1_localAngle_mem {N : ℕ} (D : CongruentDissection N) {α a b c : ℝ}
    (hm : D.model.TwoPiThreeData α a b c) (k : Fin 3) (i : Fin N) :
    (D.tile i).localAngle (D.target.pts k) ∈
      ({α, Real.pi / 3 - α, 2 * Real.pi / 3, Real.pi, 0} : Finset ℝ) := by
  obtain ⟨σ, hσ0, -, hσ1, -, hσ2, -⟩ := hm
  -- Each fixed index m maps to one of the TwoPiThreeData angles via σ's surjectivity
  have hA_mem : ∀ m : Fin 3, D.model.angleAt m ∈
      ({α, Real.pi / 3 - α, 2 * Real.pi / 3} : Finset ℝ) := fun m => by
    obtain ⟨j, rfl⟩ := σ.surjective m
    fin_cases j <;> simp_all [Finset.mem_insert, Finset.mem_singleton]
  -- Use congruentDissection_localAngle_mem with the model's fixed corner angles
  have hmem := congruentDissection_localAngle_mem D
    (D.model.angleAt 0) (D.model.angleAt 1) (D.model.angleAt 2)
    (by simp [Tri.angleAt])
    (by simp [Tri.angleAt])
    (by simp [Tri.angleAt])
    k i
  -- Convert {angleAt 0, angleAt 1, angleAt 2, π, 0} → {α, π/3-α, 2π/3, π, 0}
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem ⊢
  rcases hmem with h | h | h | h | h
  · have h0 := hA_mem 0
    simp only [Finset.mem_insert, Finset.mem_singleton] at h0
    rcases h0 with h0 | h0 | h0 <;> simp [h, h0]
  · have h1 := hA_mem 1
    simp only [Finset.mem_insert, Finset.mem_singleton] at h1
    rcases h1 with h1 | h1 | h1 <;> simp [h, h1]
  · have h2 := hA_mem 2
    simp only [Finset.mem_insert, Finset.mem_singleton] at h2
    rcases h2 with h2 | h2 | h2 <;> simp [h, h2]
  · right; right; right; left; exact h
  · right; right; right; right; exact h

/-! ## Unique tile at V₁ -/

/-- **F₁ V₁-corner uniqueness (K₁ Step 2).**
At the α-corner of an F₁ CongruentDissection with 2π/3 model, exactly one tile covers V₁.

This is the counting half of Lemma K₁ (`prop:F1free`).  The edge-placement half (K₁ Steps 3–5:
T₁'s edges run along V₁V₂ and V₁V₃) requires BLOCKER-K1 (see file header). -/
theorem f1_v1_tile_unique {N : ℕ} (D : CongruentDissection N) {α a b c μ : ℝ}
    (hirr : IrrPi α) (hm : D.model.TwoPiThreeData α a b c)
    (hF1 : D.target.F1Data α a b c μ) :
    ∃ k : Fin 3,
      cornerAngle (D.target.pts (k + 1)) (D.target.pts k) (D.target.pts (k + 2)) = α ∧
      ∃! i : Fin N, D.target.pts k ∈ (D.tile i).carrier := by
  obtain ⟨-, hgrid⟩ := hF1
  obtain ⟨σ, ha, -, -, -, -, -⟩ := hgrid
  use σ 0
  -- Target's corner angle at σ 0 is α (from GridTriData: angleAt(σ 0) = 0*π/3 + 1*α)
  have hcorner : cornerAngle (D.target.pts (σ 0 + 1)) (D.target.pts (σ 0))
      (D.target.pts (σ 0 + 2)) = α := by
    show D.target.angleAt (σ 0) = α
    rw [ha]; push_cast; ring
  refine ⟨hcorner, ?_⟩
  -- Membership of each tile's local angle at σ 0
  have hvals : ∀ i, (D.tile i).localAngle (D.target.pts (σ 0)) ∈
      ({α, Real.pi / 3 - α, 2 * Real.pi / 3, Real.pi, 0} : Finset ℝ) :=
    fun i => f1_localAngle_mem D hm (σ 0) i
  -- Multiplicity equation: n_α·α + n_β·(π/3-α) + n_γ·(2π/3) + n_π·π = α
  have hmeq := corner_multiplicities D.toDissection
    α (Real.pi / 3 - α) (2 * Real.pi / 3)
    (irrPi_ne_beta hirr) (irrPi_ne_twoThirdsPi hirr) (irrPi_ne_pi hirr) (irrPi_ne_zero hirr)
    (irrPi_beta_ne_gamma hirr) (irrPi_beta_ne_pi hirr) (irrPi_beta_ne_zero hirr)
    twoThirdsPi_ne_pi twoThirdsPi_ne_zero Real.pi_ne_zero (σ 0) hvals
  rw [hcorner] at hmeq
  -- Counting: (n_α, n_β, n_γ, n_π) = (1, 0, 0, 0)
  obtain ⟨h1, h2, h3, h4⟩ := f1_corner_single_tile hirr
    ({i | (D.tile i).localAngle (D.target.pts (σ 0)) = α} : Finset (Fin N)).card
    ({i | (D.tile i).localAngle (D.target.pts (σ 0)) = Real.pi / 3 - α} : Finset (Fin N)).card
    ({i | (D.tile i).localAngle (D.target.pts (σ 0)) = 2 * Real.pi / 3} : Finset (Fin N)).card
    ({i | (D.tile i).localAngle (D.target.pts (σ 0)) = Real.pi} : Finset (Fin N)).card
    (by push_cast at hmeq ⊢; linarith)
  obtain ⟨i₀, hi₀⟩ := Finset.card_eq_one.mp h1
  -- Helper: any tile with nonzero local angle at σ 0 must be i₀
  have heq_of_ne : ∀ i : Fin N,
      (D.tile i).localAngle (D.target.pts (σ 0)) ≠ 0 → i = i₀ := by
    intro i hine
    have hmem := hvals i
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    have hiα : (D.tile i).localAngle (D.target.pts (σ 0)) = α := by
      rcases hmem with h | h | h | h | h
      · exact h
      · exfalso
        have := Finset.card_eq_zero.mp h2
        have hi : i ∈ ({j | (D.tile j).localAngle (D.target.pts (σ 0)) = Real.pi / 3 - α} : Finset (Fin N)) := by
          simpa using h
        simp [this] at hi
      · exfalso
        have := Finset.card_eq_zero.mp h3
        have hi : i ∈ ({j | (D.tile j).localAngle (D.target.pts (σ 0)) = 2 * Real.pi / 3} : Finset (Fin N)) := by
          simpa using h
        simp [this] at hi
      · exfalso
        have := Finset.card_eq_zero.mp h4
        have hi : i ∈ ({j | (D.tile j).localAngle (D.target.pts (σ 0)) = Real.pi} : Finset (Fin N)) := by
          simpa using h
        simp [this] at hi
      · exact absurd h hine
    have hmemi : i ∈ ({j | (D.tile j).localAngle (D.target.pts (σ 0)) = α} : Finset (Fin N)) := by
      simpa using hiα
    rw [hi₀] at hmemi; simpa using hmemi
  -- Existence: get a covering tile via exists_tile_mem, identify it as i₀
  obtain ⟨w, hw⟩ := D.toDissection.exists_tile_mem
    (subset_convexHull ℝ _ (Set.mem_range_self (σ 0)) : D.target.pts (σ 0) ∈ D.target.carrier)
  exact ⟨i₀,
    by rw [← heq_of_ne w (Erdos634.MarchFlank.localAngle_ne_zero_of_mem _ hw)]; exact hw,
    fun j hj => heq_of_ne j (Erdos634.MarchFlank.localAngle_ne_zero_of_mem _ hj)⟩

end Erdos634.Geometry
