-- Draft/FDCCevianAtom.lean -- FDC item 13: the Lean-expressible part of `prop:cevianatom`
-- (companion erdos-634-companion.tex:4649): the atom A_4 at the member (e,f) = (1,2) and its
-- ladder multiples A_{4k}.
--
-- At (e,f) = (1,2) the tile is (f, f^2-1, f^2) = (2,3,4), b = 3, and the atom A_m is the isosceles
-- triangle with legs f*b*m = 6m, base e*b*m = 3m (apex angle alpha), carrying b*m^2 = 3 m^2 tiles.
--   * `atomTiles m`: A_m is dissected into 3 m^2 copies of the tile (2,3,4)   [the paper's predicate]
--   * `atomTiles_four`: atomTiles 4   (from G3CAtomTilingBridge.dissection, 1/8 homothety)
--   * `atomTiles_four_mul`: atomTiles (4k) for every k >= 1   (the main paper's ladder, `Realizable.cut_scale`)
--   * `count_4k`: the counting identity m^2 N_1 = 2 (f m)^2 + b m^2 at (1,2), m = 4k
-- NOT here (and why): see (private working notes, not included) section 13.  The geometric cevian/wall cut
-- Delta_m = fm.T u fm.T u A_m (hence "Delta_4 has a second 176-tiling") needs a union dissection
-- with full straight interfaces and is not built; "A_1 does not tile" has no Lean statement about a
-- CongruentDissection (Primitives.atom_base_forced / corner_fill_unique are arithmetic residue facts).
-- STATEMENT MATCH recorded in (private working notes, not included)  UNAUDITED; promotes no label.
-- Imported via AllNew8.lean → All.lean:853 (stale "NOT imported" header corrected 2026-10-04).  No sorry, no native_decide.
import Erdos634.Draft.G3CAtomTilingBridge
import Erdos634.Draft.FDBBaseBetaE1
import Erdos634.Realizable
import Erdos634.Primitives

namespace Erdos634.Draft.FDCCevianAtom
open Erdos634.Z15Real Erdos634.Geometry Erdos634.G3CAtomTilingBridge
open Erdos634.Draft.FDBBaseBetaE1 (HasSides tau3)

/-! ## Exact sides of the certified atom tiling -/

/-- The model of `G3CAtomTilingBridge.dissection`, exactly: squared sides at the pairs `01, 12, 20`
are `1024, 256, 576` (lengths `32, 16, 24 = 8*(4,2,3)`). -/
theorem model_dists_exact :
    dist (dissection.model.pts 0) (dissection.model.pts 1) = 32 ∧
    dist (dissection.model.pts 1) (dissection.model.pts 2) = 16 ∧
    dist (dissection.model.pts 2) (dissection.model.pts 0) = 24 := by
  have e01 : G3CAtomTiling.dist2 (vertexOf G3CAtomTiling.tiles.headI 0) (vertexOf G3CAtomTiling.tiles.headI 1)
      = ((1024:ℤ),(0:ℤ)) := by decide
  have e12 : G3CAtomTiling.dist2 (vertexOf G3CAtomTiling.tiles.headI 1) (vertexOf G3CAtomTiling.tiles.headI 2)
      = ((256:ℤ),(0:ℤ)) := by decide
  have e20 : G3CAtomTiling.dist2 (vertexOf G3CAtomTiling.tiles.headI 2) (vertexOf G3CAtomTiling.tiles.headI 0)
      = ((576:ℤ),(0:ℤ)) := by decide
  have hm : dissection.model = pieceTri headI_mem_tiles := rfl
  refine ⟨?_, ?_, ?_⟩
  · refine (sq_eq_sq₀ dist_nonneg (by norm_num)).mp ?_
    rw [hm, pieceTri_dist_sq _ headI_mem_tiles 0 1, e01]; norm_num [toR]
  · refine (sq_eq_sq₀ dist_nonneg (by norm_num)).mp ?_
    rw [hm, pieceTri_dist_sq _ headI_mem_tiles 1 2, e12]; norm_num [toR]
  · refine (sq_eq_sq₀ dist_nonneg (by norm_num)).mp ?_
    rw [hm, pieceTri_dist_sq _ headI_mem_tiles 2 0, e20]; norm_num [toR]

/-- The target, exactly: base `96` (pair `01`), legs `192, 192` (pairs `12, 20`), i.e.
`8*(12, 24, 24)`: the isosceles atom A_4. -/
theorem target_dists_exact :
    dist (dissection.target.pts 0) (dissection.target.pts 1) = 96 ∧
    dist (dissection.target.pts 1) (dissection.target.pts 2) = 192 ∧
    dist (dissection.target.pts 2) (dissection.target.pts 0) = 192 := by
  obtain ⟨h1, h2, h3⟩ := targetTri_sides
  have ht : dissection.target = targetTri := rfl
  rw [ht]
  refine ⟨?_, ?_, ?_⟩
  · exact (sq_eq_sq₀ dist_nonneg (by norm_num)).mp (by rw [h1]; norm_num)
  · exact (sq_eq_sq₀ dist_nonneg (by norm_num)).mp (by rw [h2]; norm_num)
  · exact (sq_eq_sq₀ dist_nonneg (by norm_num)).mp (by rw [h3]; norm_num)

/-! ## The atom predicate and A_4 -/

/-- **`A_m` tiles** at `(e,f) = (1,2)`: the isosceles triangle with legs `6m`, base `3m`
(`f b m`, `e b m`, `b = 3`) is dissected into `3 m^2 = b m^2` copies of the tile `(2,3,4)`
(`HasSides`: sides in some vertex order; the apex angle `alpha` follows from the sides:
`cos = (6m)^2 + (6m)^2 - (3m)^2) / (2 (6m)^2) = 7/8`). -/
def atomTiles (m : ℕ) : Prop :=
  ∃ D : CongruentDissection (3 * m ^ 2),
    HasSides D.target (3 * (m : ℝ)) (6 * (m : ℝ)) (6 * (m : ℝ)) ∧ HasSides D.model 2 3 4

/-- The atom spectrum at `(1,2)`: positive `m` with `A_m` tiled. -/
def atomSpectrum12 : Set ℕ := {m | 0 < m ∧ atomTiles m}

theorem atomTiles_four_scaled :
    ∃ D : CongruentDissection G3CAtomTiling.tiles.length,
      HasSides D.target 12 24 24 ∧ HasSides D.model 2 3 4 := by
  have hr : (1 / 8 : ℝ) ≠ 0 := by norm_num
  obtain ⟨t01, t12, t20⟩ := target_dists_exact
  obtain ⟨m01, m12, m20⟩ := model_dists_exact
  refine ⟨Erdos634.Realizable.scaleDissection (0 : Plane) (1 / 8) hr dissection,
    ⟨tau3, ?_, ?_, ?_⟩, ⟨Equiv.refl _, ?_, ?_, ?_⟩⟩
  · have e1 : tau3 1 = 0 := rfl
    have e2 : tau3 2 = 1 := rfl
    rw [e1, e2, Erdos634.Realizable.scaleDissection_target_pts,
      Erdos634.Realizable.scaleDissection_target_pts, Erdos634.Realizable.homothetyEquiv_dist, t01]
    norm_num [abs_of_pos]
  · have e2 : tau3 2 = 1 := rfl
    have e0 : tau3 0 = 2 := rfl
    rw [e2, e0, Erdos634.Realizable.scaleDissection_target_pts,
      Erdos634.Realizable.scaleDissection_target_pts, Erdos634.Realizable.homothetyEquiv_dist, t12]
    norm_num [abs_of_pos]
  · have e0 : tau3 0 = 2 := rfl
    have e1 : tau3 1 = 0 := rfl
    rw [e0, e1, Erdos634.Realizable.scaleDissection_target_pts,
      Erdos634.Realizable.scaleDissection_target_pts, Erdos634.Realizable.homothetyEquiv_dist, t20]
    norm_num [abs_of_pos]
  · simp only [Equiv.refl_apply]
    rw [Erdos634.Realizable.scaleDissection_model_pts,
      Erdos634.Realizable.scaleDissection_model_pts, Erdos634.Realizable.homothetyEquiv_dist, m12]
    norm_num [abs_of_pos]
  · simp only [Equiv.refl_apply]
    rw [Erdos634.Realizable.scaleDissection_model_pts,
      Erdos634.Realizable.scaleDissection_model_pts, Erdos634.Realizable.homothetyEquiv_dist, m20]
    norm_num [abs_of_pos]
  · simp only [Equiv.refl_apply]
    rw [Erdos634.Realizable.scaleDissection_model_pts,
      Erdos634.Realizable.scaleDissection_model_pts, Erdos634.Realizable.homothetyEquiv_dist, m01]
    norm_num [abs_of_pos]

/-- Changing the numeral forms of the three side values / the count index of an atom tiling. -/
theorem atomTiles_of_scaled {m n : ℕ} (hn : n = 3 * m ^ 2) (D : CongruentDissection n)
    (h1 : HasSides D.target (3 * (m : ℝ)) (6 * (m : ℝ)) (6 * (m : ℝ))) (h2 : HasSides D.model 2 3 4) :
    atomTiles m := by
  subst hn
  exact ⟨D, h1, h2⟩

theorem hasSides_congr {T : Tri} {a b c a' b' c' : ℝ} (h : HasSides T a b c)
    (ha : a = a') (hb : b = b') (hc : c = c') : HasSides T a' b' c' := by
  subst ha hb hc; exact h

/-- **`A_4` is tiled by `48` copies of `(2,3,4)`** (paper: "`A_4`, the isosceles triangle with legs
`24` and base `12`, is tiled by `48 = b m^2` copies of `(2,3,4)`"). -/
theorem atomTiles_four : atomTiles 4 := by
  obtain ⟨D, h1, h2⟩ := atomTiles_four_scaled
  exact atomTiles_of_scaled (m := 4) (by rw [tiles_length_eq_48]; norm_num) D
    (hasSides_congr h1 (by norm_num) (by norm_num) (by norm_num)) h2

/-! ## The ladder: `A_{4k}` for every `k >= 1` -/

/-- The scale-`k` copy `Realizable.scaleN k` multiplies every side by `k`. -/
theorem hasSides_scaleN {T : Tri} {a b c : ℝ} (h : HasSides T a b c) (k : ℕ) (hk : 0 < k) :
    HasSides (Erdos634.Realizable.scaleN k hk T) (k * a) (k * b) (k * c) := by
  obtain ⟨τ, h1, h2, h3⟩ := h
  have hk0 : |(k : ℝ)| = k := abs_of_nonneg (Nat.cast_nonneg k)
  refine ⟨τ, ?_, ?_, ?_⟩
  · show dist (AffineMap.homothety (T.pts 0) (k : ℝ) (T.pts (τ 1)))
      (AffineMap.homothety (T.pts 0) (k : ℝ) (T.pts (τ 2))) = _
    rw [Erdos634.Realizable.dist_homothety, h1, hk0]
  · show dist (AffineMap.homothety (T.pts 0) (k : ℝ) (T.pts (τ 2)))
      (AffineMap.homothety (T.pts 0) (k : ℝ) (T.pts (τ 0))) = _
    rw [Erdos634.Realizable.dist_homothety, h2, hk0]
  · show dist (AffineMap.homothety (T.pts 0) (k : ℝ) (T.pts (τ 0)))
      (AffineMap.homothety (T.pts 0) (k : ℝ) (T.pts (τ 1))) = _
    rw [Erdos634.Realizable.dist_homothety, h3, hk0]

/-- **`A_{4k}` is tiled for every `k >= 1`** (paper: "by the scaling ladder of the main paper
`A_{4k}` tiles for every `k >= 1`"): `A_4` blown up by `Ladder.ladder` (`Realizable.cut_scale`);
`3 (4k)^2 = k^2 * 48` tiles, the same tile `(2,3,4)`. -/
theorem atomTiles_four_mul (k : ℕ) (hk : 0 < k) : atomTiles (4 * k) := by
  obtain ⟨D, h1, h2⟩ := atomTiles_four
  obtain ⟨E, hEt, hEm⟩ := Erdos634.Realizable.cut_scale (T := D.target) (t := D.model)
    ⟨D, rfl, rfl⟩ k hk
  refine atomTiles_of_scaled (m := 4 * k) (n := k * k * (3 * 4 ^ 2)) (by ring) E ?_ (hEm ▸ h2)
  rw [hEt]
  exact hasSides_congr (hasSides_scaleN h1 k hk) (by push_cast; ring) (by push_cast; ring)
    (by push_cast; ring)

/-- The atom spectrum at `(1,2)` contains `4 N` (all positive multiples of 4). -/
theorem four_mul_mem_atomSpectrum12 (k : ℕ) (hk : 0 < k) : 4 * k ∈ atomSpectrum12 :=
  ⟨by omega, atomTiles_four_mul k hk⟩

/-! ## The counting identity of the cevian reduction at `(1,2)`, `m = 4k` -/

/-- `m^2 N_1 = 2 (f m)^2 + b m^2` at `(e,f) = (1,2)`, `m = 4k` (`Primitives.two_tiles_plus_atom`),
and the numerals: `N_1 = 11`, `176 k^2 = 2 (8k)^2 + 48 k^2` (two scaled tiles of `(8k)^2` tiles
each, plus the atom `A_{4k}` of `48 k^2` tiles). -/
theorem count_identity_4k (k : ℤ) :
    (4 * k) ^ 2 * (3 * 2 ^ 2 - 1 ^ 2) = 2 * (2 * (4 * k)) ^ 2 + (2 ^ 2 - 1 ^ 2) * (4 * k) ^ 2 ∧
    (4 * k) ^ 2 * (3 * 2 ^ 2 - 1 ^ 2) = 176 * k ^ 2 ∧
    (176 : ℤ) * k ^ 2 = 2 * (8 * k) ^ 2 + 48 * k ^ 2 :=
  ⟨Erdos634.Primitives.two_tiles_plus_atom 1 2 (4 * k), by ring, by ring⟩

end Erdos634.Draft.FDCCevianAtom

#print axioms Erdos634.Draft.FDCCevianAtom.model_dists_exact
#print axioms Erdos634.Draft.FDCCevianAtom.target_dists_exact
#print axioms Erdos634.Draft.FDCCevianAtom.atomTiles_four
#print axioms Erdos634.Draft.FDCCevianAtom.atomTiles_four_mul
#print axioms Erdos634.Draft.FDCCevianAtom.four_mul_mem_atomSpectrum12
#print axioms Erdos634.Draft.FDCCevianAtom.count_identity_4k
