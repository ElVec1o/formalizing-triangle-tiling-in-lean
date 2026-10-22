/-
Draft/EqSemigroup.lean — **the equilateral semigroup of the `2π/3` tile `(3, 5, 7)`**: for every `m` in the numerical semigroup
`⟨4, 9⟩ = {4, 8, 9, 12, 13, 16, 17, 18, 20, 21, 22, 24, …}` the equilateral triangle of side `15 m` is cut into `15 m²`
copies of the tile `(3, 5, 7)`; hence `15 m²` is a tile count (`eq357_semigroup`).

Gluing lemma (`eq_glue`).  In the 60-degree skew frame `Φ_1` (Eisenstein coordinates `x + yω`, form `x² + y² + xy`) the
equilateral triangle of side `L` is `Φ_1 '' {x, y ≥ 0, x + y ≤ L}`.  If the sides `L₁ = p k`, `L₂ = q l` are tiled
(`{p, q} = {3, 5}`), the triangle of side `L₁ + L₂` is the union of
  * the corner triangle `x + y ≤ L₁`,
  * the translate of the `L₂`-triangle by `(L₁, 0)` (`x ≥ L₁`),
  * the parallelogram `(L₁, 0) + Λ ([0, k] × [0, l])`, `Λ = (a, b) ↦ a (-p, p) + b (0, q)`, a `k × l` grid of
    `p × q` parallelograms with a 60-degree angle, each cut along its long diagonal (length `p² + p q + q² = 49 = 7²`)
    into two tiles `(3, 5, 7)`.
Count: `N₁ + N₂ + 2 k l`.  The assembly is by `S2L.pack_exists` (pairwise interior-disjoint regions inside the target whose
total area is the target's; the covering is derived from the area identity), as in `Draft/F4All.lean`.

Seeds: side `60` (`m = 4`, 240 tiles) is `Draft.N240.equilateral_60_by_357` (D. Paliy's tiling, kernel-checked); side `135`
(`m = 9`, 1215 tiles) is `G3CEqui135Control.D` (the Herdt / Zhang tiling, scaled by `1/1890`).

PRIOR ART / HONESTY.  Zhang (arXiv:2512.22696) constructs all sides `15 m`, `m ≥ 9`, by hand and Paliy announces every `m ≥ 4`;
the *formal* statement for the semigroup `⟨4, 9⟩` is what is new here (`m ∈ {13, 17, 21, 22}` are outside Zhang's range).

UNAUDITED.  No sorry, no native_decide.
-/
import Erdos634.Draft.F4All
import Erdos634.Draft.N240
import Erdos634.Draft.G3CEqui135Control

open scoped Classical
set_option linter.unusedSectionVars false
open Erdos634.Geometry Erdos634.CertCoord
open Erdos634.Draft.CollarParam (Tset Rect RTiling.cast RTiling.castN interior_disj_fst)

namespace Erdos634.Draft.EqSemigroup
open Erdos634.Draft.WFrameF Erdos634.Draft.RegionTiling Erdos634.Draft.S2G Erdos634.Draft.S2AllTheta
open Erdos634.Draft.S2L (mem_hull3' tri_le tri_fst_ge tri_snd_ge pack_exists)
open Erdos634.Draft.WBrickF (interior_disj_lin)
open Erdos634.Draft.FDBBaseBetaE1 (HasSides congruent_of_hasSides hasSides_swap hasSides_rot hasSides_of_oppLen)
open Erdos634.Draft.TileCountFamilies (TileCount)
open Erdos634.Draft.F4All (hf1 f4_eq_of_sq)

theorem dPhi1 (x y : ℝ × ℝ) (r : ℝ) (hr : 0 ≤ r)
    (h : (x.1 - y.1) ^ 2 + (x.2 - y.2) ^ 2 + (x.1 - y.1) * (x.2 - y.2) / 1 = r ^ 2) :
    dist (Phi 1 x) (Phi 1 y) = r := by
  refine f4_eq_of_sq dist_nonneg hr ?_
  rw [sq_Phi' hf1]; exact h

/-! ### the target triangles and the model tile -/
/-- the equilateral triangle of side `L`: skew vertices `(0,0), (L,0), (0,L)`. -/
noncomputable def eqTri (L : ℕ) (hL : 0 < L) : Erdos634.Geometry.Tri :=
  triC 1 hf1 (0, 0) ((L : ℝ), 0) (0, (L : ℝ)) (by
    have h : (0 : ℝ) < L := by exact_mod_cast hL
    intro h'
    have h2 : (L : ℝ) * L = 0 := by simpa using h'
    have := mul_pos h h
    linarith)

/-- the tile `(3, 5, 7)`: `dist 12 = 3`, `dist 20 = 5`, `dist 01 = 7`. -/
noncomputable def Mod357 : Erdos634.Geometry.Tri := triC 1 hf1 (0, 0) (3, 5) (0, 5) (by norm_num)

theorem Mod_12 : dist (Mod357.pts 1) (Mod357.pts 2) = 3 := by
  simp only [Mod357, triC_pts]
  exact dPhi1 _ _ _ (by norm_num) (by norm_num)
theorem Mod_20 : dist (Mod357.pts 2) (Mod357.pts 0) = 5 := by
  simp only [Mod357, triC_pts]
  exact dPhi1 _ _ _ (by norm_num) (by norm_num)
theorem Mod_01 : dist (Mod357.pts 0) (Mod357.pts 1) = 7 := by
  simp only [Mod357, triC_pts]
  exact dPhi1 _ _ _ (by norm_num) (by norm_num)

theorem hull_Tset (L : ℝ) (hL : 0 < L) :
    convexHull ℝ ({((0 : ℝ), (0 : ℝ)), (L, 0), (0, L)} : Set (ℝ × ℝ)) = Tset L := by
  apply Set.Subset.antisymm
  · intro p hp
    refine ⟨tri_fst_ge (A := ((0 : ℝ), (0 : ℝ))) (B := (L, 0)) (C := (0, L)) 0 le_rfl hL.le le_rfl p hp,
      tri_snd_ge (A := ((0 : ℝ), (0 : ℝ))) (B := (L, 0)) (C := (0, L)) 0 le_rfl le_rfl hL.le p hp, ?_⟩
    have := tri_le (A := ((0 : ℝ), (0 : ℝ))) (B := (L, 0)) (C := (0, L)) 1 1 L
      (by show (1 : ℝ) * 0 + 1 * 0 ≤ L; linarith) (by show (1 : ℝ) * L + 1 * 0 ≤ L; linarith)
      (by show (1 : ℝ) * 0 + 1 * L ≤ L; linarith) p hp
    linarith
  · rintro p ⟨h1, h2, h3⟩
    exact mem_hull3' (A := ((0 : ℝ), (0 : ℝ))) (B := (L, 0)) (C := (0, L)) L (L - p.1 - p.2) p.1 p.2 hL
      (by linarith) h1 h2 (by ring) p
      (by show L * p.1 = (L - p.1 - p.2) * 0 + p.1 * L + p.2 * 0; ring)
      (by show L * p.2 = (L - p.1 - p.2) * 0 + p.1 * 0 + p.2 * L; ring)

theorem carrier_eqTri (L : ℕ) (hL : 0 < L) : (eqTri L hL).carrier = Phi 1 '' Tset (L : ℝ) := by
  unfold eqTri; rw [carrier_triC, hull_Tset _ (by exact_mod_cast hL)]

open MeasureTheory in
theorem vol_Mod357 : volume Mod357.carrier
    = ENNReal.ofReal (|sD 1 / (2 * 1)| * 15) * volume Erdos634.AreaDet.stdCarrier := by
  unfold Mod357
  rw [vol_triC]
  congr 2
  rw [abs_mul]
  congr 1
  norm_num

open MeasureTheory in
theorem vol_eqTri (L : ℕ) (hL : 0 < L) : volume (eqTri L hL).carrier
    = ENNReal.ofReal (|sD 1 / (2 * 1)| * (L : ℝ) ^ 2) * volume Erdos634.AreaDet.stdCarrier := by
  unfold eqTri
  rw [vol_triC]
  congr 2
  rw [abs_mul]
  congr 1
  simp [sq, abs_mul_self]

/-! ### `EqD L N`: the equilateral triangle of side `L` is cut into `N` copies of `(3,5,7)` -/
def EqD (L N : ℕ) : Prop :=
  15 * N = L * L ∧ ∃ hL : 0 < L, ∃ D : CongruentDissection N, D.model = Mod357 ∧ D.target = eqTri L hL

/-- any dissection of a triangle with sides `L, L, L` by tiles with sides `3, 5, 7` is an `EqD` (transport by an isometry). -/
theorem eqD_of_seed (L N : ℕ) (hL : 0 < L) (hN : 15 * N = L * L) (D : CongruentDissection N)
    (hT : HasSides D.target (L : ℝ) (L : ℝ) (L : ℝ)) (hM : HasSides D.model 3 5 7) : EqD L N := by
  refine ⟨hN, hL, ?_⟩
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  have hcT : D.target.Congruent (eqTri L hL) := by
    refine congruent_of_hasSides hT ?_ ?_ ?_ <;> simp only [eqTri, triC_pts]
    · exact dPhi1 _ _ _ hLr.le (by
        show ((L : ℝ) - 0) ^ 2 + (0 - (L : ℝ)) ^ 2 + ((L : ℝ) - 0) * (0 - (L : ℝ)) / 1 = (L : ℝ) ^ 2
        ring)
    · exact dPhi1 _ _ _ hLr.le (by
        show ((0 : ℝ) - 0) ^ 2 + ((L : ℝ) - 0) ^ 2 + ((0 : ℝ) - 0) * ((L : ℝ) - 0) / 1 = (L : ℝ) ^ 2
        ring)
    · exact dPhi1 _ _ _ hLr.le (by
        show ((0 : ℝ) - L) ^ 2 + ((0 : ℝ) - 0) ^ 2 + ((0 : ℝ) - L) * ((0 : ℝ) - 0) / 1 = (L : ℝ) ^ 2
        ring)
  have hcM : D.model.Congruent Mod357 := congruent_of_hasSides hM Mod_12 Mod_20 Mod_01
  obtain ⟨f, σ, hf⟩ := hcT
  have hcar : f '' D.target.carrier = (eqTri L hL).carrier :=
    Erdos634.CongruentArea.image_carrier_of_congruent hf
  let R : RTiling (eqTri L hL).carrier Mod357 N :=
    RegionTiling.remodel (RTiling.cast hcar (RegionTiling.map (RegionTiling.ofCD D) f)) hcM
  exact ⟨RegionTiling.toCD R, rfl, rfl⟩

/-! ### the cell: a `p × q` parallelogram with a 60-degree angle is two tiles -/
def uu (p : ℝ) : ℝ × ℝ := (-p, p)
def ww (q : ℝ) : ℝ × ℝ := (0, q)

theorem det_uw {p q : ℝ} (hp : 0 < p) (hq : 0 < q) : (uu p).1 * (ww q).2 - (uu p).2 * (ww q).1 ≠ 0 := by
  simp only [uu, ww]; intro h; nlinarith [mul_pos hp hq]

theorem hs_TL {p q : ℝ} (hp : 0 < p) (hq : 0 < q) (h49 : p ^ 2 + p * q + q ^ 2 = 7 ^ 2) (hd) :
    HasSides (TL hf1 (uu p) (ww q) hd) p q 7 := by
  refine ⟨Equiv.refl _, ?_, ?_, ?_⟩ <;> simp only [Equiv.refl_apply, TL, triC_pts]
  · exact dPhi1 _ _ _ hp.le (by
      simp only [uu, ww, Prod.fst_add, Prod.snd_add, Prod.fst_zero, Prod.snd_zero]; ring)
  · exact dPhi1 _ _ _ hq.le (by
      simp only [uu, ww, Prod.fst_add, Prod.snd_add, Prod.fst_zero, Prod.snd_zero]; ring)
  · exact dPhi1 _ _ _ (by norm_num) (by
      simp only [uu, ww, Prod.fst_add, Prod.snd_add, Prod.fst_zero, Prod.snd_zero]
      linear_combination h49)

theorem hs_TU {p q : ℝ} (hp : 0 < p) (hq : 0 < q) (h49 : p ^ 2 + p * q + q ^ 2 = 7 ^ 2) (hd) :
    HasSides (TU hf1 (uu p) (ww q) hd) p q 7 := by
  refine ⟨Equiv.refl _, ?_, ?_, ?_⟩ <;> simp only [Equiv.refl_apply, TU, triC_pts]
  · exact dPhi1 _ _ _ hp.le (by
      simp only [uu, ww, Prod.fst_add, Prod.snd_add, Prod.fst_zero, Prod.snd_zero]; ring)
  · exact dPhi1 _ _ _ hq.le (by
      simp only [uu, ww, Prod.fst_add, Prod.snd_add, Prod.fst_zero, Prod.snd_zero]; ring)
  · exact dPhi1 _ _ _ (by norm_num) (by
      simp only [uu, ww, Prod.fst_add, Prod.snd_add, Prod.fst_zero, Prod.snd_zero]
      linear_combination h49)

theorem cong_cells {p q : ℝ} (hp : 0 < p) (hq : 0 < q) (hpq : (p = 3 ∧ q = 5) ∨ (p = 5 ∧ q = 3)) (hd) :
    (TL hf1 (uu p) (ww q) hd).Congruent Mod357 ∧ (TU hf1 (uu p) (ww q) hd).Congruent Mod357 := by
  have h49 : p ^ 2 + p * q + q ^ 2 = 7 ^ 2 := by
    rcases hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> norm_num
  have h1 := hs_TL hp hq h49 hd
  have h2 := hs_TU hp hq h49 hd
  rcases hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨congruent_of_hasSides h1 Mod_12 Mod_20 Mod_01, congruent_of_hasSides h2 Mod_12 Mod_20 Mod_01⟩
  · exact ⟨congruent_of_hasSides (hasSides_swap h1) Mod_12 Mod_20 Mod_01,
      congruent_of_hasSides (hasSides_swap h2) Mod_12 Mod_20 Mod_01⟩

/-! ### the three regions -/
/-- the translate of the `L₂`-triangle by `(L₁, 0)`. -/
def Tr (L₁ L₂ : ℝ) : Set (ℝ × ℝ) := {z | L₁ ≤ z.1 ∧ 0 ≤ z.2 ∧ z.1 + z.2 ≤ L₁ + L₂}

/-- the parallelogram `(L₁, 0) + Λ ([0, k+1] × [0, l+1])`. -/
def Pset (p q L₁ : ℝ) (k l : ℕ) : Set (ℝ × ℝ) :=
  (fun z : ℝ × ℝ => z + (L₁, 0)) '' (Lam (uu p) (ww q) '' Rect 0 (1 * ((k : ℝ) + 1)) 0 (1 * ((l : ℝ) + 1)))

theorem shift_phi (v : ℝ × ℝ) (S : Set (ℝ × ℝ)) :
    (IsometryEquiv.addRight (Phi 1 v)) '' (Phi 1 '' S) = Phi 1 '' ((fun z : ℝ × ℝ => z + v) '' S) := by
  ext x
  constructor
  · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    refine ⟨z + v, ⟨z, hz, rfl⟩, ?_⟩
    show Phi 1 (z + v) = Phi 1 z + Phi 1 v
    rw [Phi_add]
  · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    refine ⟨Phi 1 z, ⟨z, hz, rfl⟩, ?_⟩
    show Phi 1 z + Phi 1 v = Phi 1 (z + v)
    rw [Phi_add]

theorem shift_Tset (L₁ L₂ : ℝ) (h : 0 ≤ L₁) : (fun z : ℝ × ℝ => z + (L₁, 0)) '' Tset L₂ = Tr L₁ L₂ := by
  ext x
  constructor
  · rintro ⟨z, ⟨h1, h2, h3⟩, rfl⟩
    refine ⟨?_, ?_, ?_⟩
    · show L₁ ≤ z.1 + L₁; linarith
    · show 0 ≤ z.2 + 0; linarith
    · show z.1 + L₁ + (z.2 + 0) ≤ L₁ + L₂; linarith
  · rintro ⟨h1, h2, h3⟩
    refine ⟨x - (L₁, 0), ⟨?_, ?_, ?_⟩, ?_⟩
    · show 0 ≤ x.1 - L₁; linarith
    · show 0 ≤ x.2 - 0; linarith
    · show x.1 - L₁ + (x.2 - 0) ≤ L₂; linarith
    · show x - (L₁, 0) + (L₁, 0) = x
      simp

theorem Pset_mem {p q L₁ L₂ : ℝ} (hp : 0 < p) (hq : 0 < q) {k l : ℕ} (hL₁ : p * ((k : ℝ) + 1) = L₁)
    (hL₂ : q * ((l : ℝ) + 1) = L₂) {x : ℝ × ℝ} (hx : x ∈ Pset p q L₁ k l) :
    0 ≤ x.1 ∧ x.1 ≤ L₁ ∧ 0 ≤ x.2 ∧ L₁ ≤ x.1 + x.2 ∧ x.1 + x.2 ≤ L₁ + L₂ := by
  rcases hx with ⟨_, ⟨z, ⟨h1, h2, h3, h4⟩, rfl⟩, rfl⟩
  simp only [Lam, uu, ww, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  have a1 := mul_nonneg hp.le h1
  have a2 := mul_le_mul_of_nonneg_left h2 hp.le
  have a3 := mul_nonneg hq.le h3
  have a4 := mul_le_mul_of_nonneg_left h4 hq.le
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> nlinarith

/-! ### the gluing -/
theorem glue_real {p q : ℝ} (hp : 0 < p) (hq : 0 < q) (hpq : (p = 3 ∧ q = 5) ∨ (p = 5 ∧ q = 3)) (k l : ℕ)
    {L₁ L₂ : ℝ} (hL₁ : p * ((k : ℝ) + 1) = L₁) (hL₂ : q * ((l : ℝ) + 1) = L₂)
    {N₁ N₂ : ℕ} (R1 : RTiling (Phi 1 '' Tset L₁) Mod357 N₁) (R2 : RTiling (Phi 1 '' Tset L₂) Mod357 N₂)
    (hN₁ : (N₁ : ℝ) * 15 = L₁ ^ 2) (hN₂ : (N₂ : ℝ) * 15 = L₂ ^ 2)
    (T : Erdos634.Geometry.Tri) (hT : T.carrier = Phi 1 '' Tset (L₁ + L₂))
    (hvT : MeasureTheory.volume T.carrier
      = ENNReal.ofReal (|sD 1 / (2 * 1)| * (L₁ + L₂) ^ 2) * MeasureTheory.volume Erdos634.AreaDet.stdCarrier) :
    ∃ D : CongruentDissection (N₁ + N₂ + 2 * (k + 1) * (l + 1)), D.model = Mod357 ∧ D.target = T := by
  have hL₁0 : 0 ≤ L₁ := by rw [← hL₁]; positivity
  have hL₂0 : 0 ≤ L₂ := by rw [← hL₂]; positivity
  have hd := det_uw hp hq
  obtain ⟨c1, c2⟩ := cong_cells hp hq hpq hd
  have G := gridT (ThH hf1 (uu p) (ww q) hd) (ThH_add hf1 (uu p) (ww q) hd) (A := 1) (B := 1) one_pos one_pos
    (cellRT hf1 (uu p) (ww q) hd Mod357 c1 c2) k l
  rw [ThH_image] at G
  have G' := RegionTiling.map G (IsometryEquiv.addRight (Phi 1 (L₁, 0)))
  rw [shift_phi] at G'
  have R2' := RegionTiling.map R2 (IsometryEquiv.addRight (Phi 1 (L₁, 0)))
  rw [shift_phi, shift_Tset L₁ L₂ hL₁0] at R2'
  -- bounds
  have P := fun {x : ℝ × ℝ} (hx : x ∈ Pset p q L₁ k l) => Pset_mem hp hq hL₁ hL₂ hx
  have d01 : Disjoint (interior (Phi 1 '' Tset L₁)) (interior (Phi 1 '' Tr L₁ L₂)) :=
    disjoint_image' hf1 (interior_disj_fst L₁ (fun z hz => by linarith [hz.1, hz.2.1, hz.2.2])
      (fun z hz => hz.1))
  have d02 : Disjoint (interior (Phi 1 '' Tset L₁)) (interior (Phi 1 '' Pset p q L₁ k l)) :=
    disjoint_image' hf1 (interior_disj_lin 1 1 L₁ one_ne_zero (fun z hz => by linarith [hz.2.2])
      (fun z hz => by linarith [(P hz).2.2.2.1]))
  have d21 : Disjoint (interior (Phi 1 '' Pset p q L₁ k l)) (interior (Phi 1 '' Tr L₁ L₂)) :=
    disjoint_image' hf1 (interior_disj_fst L₁ (fun z hz => (P hz).2.1) (fun z hz => hz.1))
  have hsub0 : Tset L₁ ⊆ Tset (L₁ + L₂) := fun z hz => ⟨hz.1, hz.2.1, by linarith [hz.2.2]⟩
  have hsub1 : Tr L₁ L₂ ⊆ Tset (L₁ + L₂) := fun z hz => ⟨by linarith [hz.1], hz.2.1, hz.2.2⟩
  have hsub2 : Pset p q L₁ k l ⊆ Tset (L₁ + L₂) := fun z hz =>
    ⟨(P hz).1, (P hz).2.2.1, (P hz).2.2.2.2⟩
  have hpq15 : p * q = 15 := by rcases hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> norm_num
  have hsum : ∑ a : Fin 3, (![N₁, N₂, 2 * (k + 1) * (l + 1)] : Fin 3 → ℕ) a
      = N₁ + N₂ + 2 * (k + 1) * (l + 1) := by
    simp [Fin.sum_univ_three]
  have hN : ((N₁ + N₂ + 2 * (k + 1) * (l + 1) : ℕ) : ℝ) * 15 = (L₁ + L₂) ^ 2 := by
    subst hL₁ hL₂
    push_cast
    linear_combination hN₁ + hN₂ + (-2 * ((k : ℝ) + 1) * ((l : ℝ) + 1)) * hpq15
  have key := pack_exists (M := Mod357) (T := T)
    (![Phi 1 '' Tset L₁, Phi 1 '' Tr L₁ L₂, Phi 1 '' Pset p q L₁ k l])
    (![N₁, N₂, 2 * (k + 1) * (l + 1)])
    (fun i => match i with
      | ⟨0, _⟩ => R1
      | ⟨1, _⟩ => R2'
      | ⟨2, _⟩ => G'
      | ⟨k + 3, h⟩ => absurd h (by omega))
    (by
      intro i j hij
      exact match i, j with
        | ⟨0, _⟩, ⟨0, _⟩ => absurd rfl hij
        | ⟨0, _⟩, ⟨1, _⟩ => d01
        | ⟨0, _⟩, ⟨2, _⟩ => d02
        | ⟨1, _⟩, ⟨0, _⟩ => d01.symm
        | ⟨1, _⟩, ⟨1, _⟩ => absurd rfl hij
        | ⟨1, _⟩, ⟨2, _⟩ => d21.symm
        | ⟨2, _⟩, ⟨0, _⟩ => d02.symm
        | ⟨2, _⟩, ⟨1, _⟩ => d21
        | ⟨2, _⟩, ⟨2, _⟩ => absurd rfl hij
        | ⟨k + 3, h⟩, _ => absurd h (by omega)
        | _, ⟨k + 3, h⟩ => absurd h (by omega))
    (by
      intro i
      rw [hT]
      exact match i with
        | ⟨0, _⟩ => Set.image_mono hsub0
        | ⟨1, _⟩ => Set.image_mono hsub1
        | ⟨2, _⟩ => Set.image_mono hsub2
        | ⟨k + 3, h⟩ => absurd h (by omega))
    (by
      rw [hsum, vol_Mod357, hvT, ← mul_assoc, ← ENNReal.ofReal_natCast,
        ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      congr 2
      rw [← hN]; ring)
  rw [hsum] at key
  exact key

theorem eq_glue (p q : ℕ) (hpq : (p = 3 ∧ q = 5) ∨ (p = 5 ∧ q = 3)) (k l : ℕ) (hk : 0 < k) (hl : 0 < l)
    {N₁ N₂ : ℕ} (h1 : EqD (p * k) N₁) (h2 : EqD (q * l) N₂) :
    EqD (p * k + q * l) (N₁ + N₂ + 2 * k * l) := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  obtain ⟨l', rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
  obtain ⟨hN1, hL1, D1, hm1, ht1⟩ := h1
  obtain ⟨hN2, hL2, D2, hm2, ht2⟩ := h2
  have hp : (0 : ℝ) < p := by rcases hpq with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> norm_num
  have hq : (0 : ℝ) < q := by rcases hpq with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> norm_num
  have hpqR : ((p : ℝ) = 3 ∧ (q : ℝ) = 5) ∨ ((p : ℝ) = 5 ∧ (q : ℝ) = 3) := by
    rcases hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · left; norm_num
    · right; norm_num
  have hLpos : 0 < p * (k' + 1) + q * (l' + 1) := by
    have : 0 < p * (k' + 1) := hL1
    omega
  refine ⟨by
      have : 15 * (N₁ + N₂ + 2 * (k' + 1) * (l' + 1))
          = 15 * N₁ + 15 * N₂ + 30 * (k' + 1) * (l' + 1) := by ring
      rw [this, hN1, hN2]
      rcases hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> ring, hLpos, ?_⟩
  have e1 : (((p * (k' + 1) : ℕ)) : ℝ) = (p : ℝ) * ((k' : ℝ) + 1) := by push_cast; ring
  have e2 : (((q * (l' + 1) : ℕ)) : ℝ) = (q : ℝ) * ((l' : ℝ) + 1) := by push_cast; ring
  have R1 : RTiling (Phi 1 '' Tset ((p : ℝ) * ((k' : ℝ) + 1))) Mod357 N₁ := by
    refine RegionTiling.remodel (RTiling.cast ?_ (RegionTiling.ofCD D1)) (by rw [hm1]; exact Tri.Congruent.refl _)
    rw [ht1, carrier_eqTri, e1]
  have R2 : RTiling (Phi 1 '' Tset ((q : ℝ) * ((l' : ℝ) + 1))) Mod357 N₂ := by
    refine RegionTiling.remodel (RTiling.cast ?_ (RegionTiling.ofCD D2)) (by rw [hm2]; exact Tri.Congruent.refl _)
    rw [ht2, carrier_eqTri, e2]
  have hN1R : (N₁ : ℝ) * 15 = ((p : ℝ) * ((k' : ℝ) + 1)) ^ 2 := by
    have : ((15 * N₁ : ℕ) : ℝ) = ((p * (k' + 1) * (p * (k' + 1)) : ℕ) : ℝ) := by rw [hN1]
    push_cast at this; nlinarith
  have hN2R : (N₂ : ℝ) * 15 = ((q : ℝ) * ((l' : ℝ) + 1)) ^ 2 := by
    have : ((15 * N₂ : ℕ) : ℝ) = ((q * (l' + 1) * (q * (l' + 1)) : ℕ) : ℝ) := by rw [hN2]
    push_cast at this; nlinarith
  have hcast : (((p * (k' + 1) + q * (l' + 1) : ℕ)) : ℝ)
      = (p : ℝ) * ((k' : ℝ) + 1) + (q : ℝ) * ((l' : ℝ) + 1) := by push_cast; ring
  obtain ⟨D, hD1, hD2⟩ := glue_real hp hq hpqR k' l' rfl rfl R1 R2 hN1R hN2R (eqTri _ hLpos)
    (by rw [carrier_eqTri, hcast])
    (by rw [vol_eqTri, hcast])
  exact ⟨D, hD1, hD2⟩

/-! ### the seeds -/
theorem eqD_60 : EqD 60 240 := by
  obtain ⟨D, hT, hM⟩ := Erdos634.Draft.N240.equilateral_60_by_357
  exact eqD_of_seed 60 240 (by norm_num) (by norm_num) D (by simpa using hT) hM

open Erdos634.Realizable in
/-- a seed given at scale `s` (target sides `s L`, tile sides `s·(3,7,5)` on `oppLen 0,1,2`) is an `EqD`. -/
theorem eqD_of_scaled {N : ℕ} (D : CongruentDissection N) (s : ℝ) (hs : 0 < s) (L : ℕ) (hL : 0 < L)
    (hN : 15 * N = L * L)
    (t0 : D.target.oppLen 0 = s * L) (t1 : D.target.oppLen 1 = s * L) (t2 : D.target.oppLen 2 = s * L)
    (m0 : D.model.oppLen 0 = s * 3) (m1 : D.model.oppLen 1 = s * 7) (m2 : D.model.oppLen 2 = s * 5) :
    EqD L N := by
  have hν : (0 : ℝ) < 1 / s := by positivity
  have hs' : s ≠ 0 := hs.ne'
  have hsc : ∀ T : Erdos634.Geometry.Tri, ∀ j k : Fin 3, dist ((homothetyEquiv (D.model.pts 0) (1 / s) hν.ne') (T.pts j))
      ((homothetyEquiv (D.model.pts 0) (1 / s) hν.ne') (T.pts k)) = 1 / s * dist (T.pts j) (T.pts k) := by
    intro T j k
    rw [homothetyEquiv_dist, abs_of_pos hν]
  have hT : HasSides (scaleDissection (D.model.pts 0) (1 / s) hν.ne' D).target (L : ℝ) (L : ℝ) (L : ℝ) := by
    refine hasSides_of_oppLen ?_ ?_ ?_
    · show dist (_) (_) = _
      rw [scaleDissection_target_pts, scaleDissection_target_pts, hsc]
      have := t0
      unfold Erdos634.Geometry.Tri.oppLen at this
      rw [this]; field_simp
    · show dist (_) (_) = _
      rw [scaleDissection_target_pts, scaleDissection_target_pts, hsc]
      have := t1
      unfold Erdos634.Geometry.Tri.oppLen at this
      rw [this]; field_simp
    · show dist (_) (_) = _
      rw [scaleDissection_target_pts, scaleDissection_target_pts, hsc]
      have := t2
      unfold Erdos634.Geometry.Tri.oppLen at this
      rw [this]; field_simp
  have hM : HasSides (scaleDissection (D.model.pts 0) (1 / s) hν.ne' D).model 3 7 5 := by
    refine hasSides_of_oppLen ?_ ?_ ?_
    · show dist (_) (_) = _
      rw [scaleDissection_model_pts, scaleDissection_model_pts, hsc]
      have := m0
      unfold Erdos634.Geometry.Tri.oppLen at this
      rw [this]; field_simp
    · show dist (_) (_) = _
      rw [scaleDissection_model_pts, scaleDissection_model_pts, hsc]
      have := m1
      unfold Erdos634.Geometry.Tri.oppLen at this
      rw [this]; field_simp
    · show dist (_) (_) = _
      rw [scaleDissection_model_pts, scaleDissection_model_pts, hsc]
      have := m2
      unfold Erdos634.Geometry.Tri.oppLen at this
      rw [this]; field_simp
  exact eqD_of_seed L N hL hN _ hT (hasSides_rot (hasSides_swap hM))

theorem eqD_135 : EqD 135 1215 := by
  have h : EqD 135 Erdos634.Draft.G3CEqui135.cert.leaves.length :=
    eqD_of_scaled Erdos634.Draft.G3CEqui135Control.D 1890 (by norm_num) 135 (by norm_num)
      (by rw [Erdos634.Draft.G3CEqui135.cert_len]) (by
        rw [Erdos634.Draft.G3CEqui135Control.t_opp0]; try norm_num)
      (by rw [Erdos634.Draft.G3CEqui135Control.t_opp1]; try norm_num)
      (by rw [Erdos634.Draft.G3CEqui135Control.t_opp2]; try norm_num)
      (by rw [Erdos634.Draft.G3CEqui135Control.m_opp0]; try norm_num)
      (by rw [Erdos634.Draft.G3CEqui135Control.m_opp1]; try norm_num)
      (by rw [Erdos634.Draft.G3CEqui135Control.m_opp2]; try norm_num)
  rw [Erdos634.Draft.G3CEqui135.cert_len] at h
  exact h

/-! ### the semigroup -/
theorem eqD_step (m₁ m₂ : ℕ) (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (h1 : EqD (15 * m₁) (15 * m₁ * m₁))
    (h2 : EqD (15 * m₂) (15 * m₂ * m₂)) : EqD (15 * (m₁ + m₂)) (15 * (m₁ + m₂) * (m₁ + m₂)) := by
  have h1' : EqD (3 * (5 * m₁)) (15 * m₁ * m₁) := by
    rwa [show 3 * (5 * m₁) = 15 * m₁ by ring]
  have h2' : EqD (5 * (3 * m₂)) (15 * m₂ * m₂) := by
    rwa [show 5 * (3 * m₂) = 15 * m₂ by ring]
  have := eq_glue 3 5 (Or.inl ⟨rfl, rfl⟩) (5 * m₁) (3 * m₂) (by omega) (by omega) h1' h2'
  have e3 : 3 * (5 * m₁) + 5 * (3 * m₂) = 15 * (m₁ + m₂) := by ring
  have e4 : 15 * m₁ * m₁ + 15 * m₂ * m₂ + 2 * (5 * m₁) * (3 * m₂) = 15 * (m₁ + m₂) * (m₁ + m₂) := by ring
  rw [e3, e4] at this
  exact this

theorem eqD_semigroup {m : ℕ} (hm : m ∈ AddSubmonoid.closure ({4, 9} : Set ℕ)) :
    m = 0 ∨ EqD (15 * m) (15 * m * m) := by
  induction hm using AddSubmonoid.closure_induction with
  | mem x hx =>
    right
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact eqD_60
    · exact eqD_135
  | zero => left; rfl
  | add x y hx hy ihx ihy =>
    rcases ihx with rfl | h1
    · simpa using ihy
    · rcases ihy with rfl | h2
      · right; simpa using h1
      · right
        exact eqD_step x y (by
          rcases Nat.eq_zero_or_pos x with h | h
          · subst h; simp [EqD] at h1
          · exact h) (by
          rcases Nat.eq_zero_or_pos y with h | h
          · subst h; simp [EqD] at h2
          · exact h) h1 h2

/-- **The equilateral semigroup of `(3,5,7)`**: `15 m²` is a tile count for every nonzero `m` in `⟨4, 9⟩`
(`m = 4, 8, 9, 12, 13, 16, 17, 18, 20, 21, 22, 24, …`). -/
theorem eq357_semigroup {m : ℕ} (hm : m ∈ AddSubmonoid.closure ({4, 9} : Set ℕ)) (hm0 : m ≠ 0) :
    TileCount (15 * m ^ 2) := by
  rcases eqD_semigroup hm with h | ⟨-, -, D, -, -⟩
  · exact absurd h hm0
  · exact ⟨by rw [show 15 * m ^ 2 = 15 * m * m by ring]; exact D⟩

/-- explicit form: `m = 4 i + 9 j`, `(i, j) ≠ (0, 0)`. -/
theorem eq357_semigroup_explicit (i j : ℕ) (h : i ≠ 0 ∨ j ≠ 0) : TileCount (15 * (4 * i + 9 * j) ^ 2) := by
  refine eq357_semigroup ?_ (by omega)
  have h1 : i • (4 : ℕ) ∈ AddSubmonoid.closure ({4, 9} : Set ℕ) :=
    nsmul_mem (AddSubmonoid.subset_closure (by simp)) i
  have h2 : j • (9 : ℕ) ∈ AddSubmonoid.closure ({4, 9} : Set ℕ) :=
    nsmul_mem (AddSubmonoid.subset_closure (by simp)) j
  have := add_mem h1 h2
  simpa [smul_eq_mul, mul_comm] using this

/-- sanity: `m = 13 = 4 + 9`, `15 · 169 = 2535`; `m = 17 = 8 + 9`, `m = 21 = 12 + 9`, `m = 22 = 4 + 18`. -/
example : TileCount 2535 := by simpa using eq357_semigroup_explicit 1 1 (Or.inl one_ne_zero)
example : TileCount (15 * 22 ^ 2) := by simpa using eq357_semigroup_explicit 1 2 (Or.inl one_ne_zero)

end Erdos634.Draft.EqSemigroup

#print axioms Erdos634.Draft.EqSemigroup.eq_glue
#print axioms Erdos634.Draft.EqSemigroup.eq357_semigroup
#print axioms Erdos634.Draft.EqSemigroup.eq357_semigroup_explicit
