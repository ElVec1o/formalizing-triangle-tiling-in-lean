import Erdos634.Draft.LaczFormalColumnStmt
import Erdos634.Draft.LaczFormalColumnGrid
import Erdos634.Draft.LaczFormalColumnC2

/-!
# Controls for C1: fault segments of the grid, positive witness and negative control

Erdős #634, base-`β` row, Column Lemma.  This file proves NOTHING new about #634.  Credit: AI assistant (Column Lemma proposal),
Beeson–Roșu, Beeson, Laczkovich.  UNAUDITED.  Axiom-clean; no `sorry`.

The grid `gridD` (`k²` copies of the tile of `(e,f)` in `kT`, a genuine `CongruentDissection`, `gridD_model`) has `c`-edges on
the lattice rows and `a`-edges on the lattice columns.  Every integer column line `x = j` and every integer row line `y = ρ`
is a WALL (no tile crosses it): `grid_vwall`, `grid_hwall`.  Hence

* `grid_row_faultSeg` : the row segment `[pt a0 ρ, pt (a0+n) ρ]` is a `FaultSeg` for the upper chain `lineChain (−e0)`; its ends
  are non-straddled because they lie on the column walls `x = a0`, `x = a0 + n` (`WallAt.not_straddled`: this is the
  hypothesis `hP`, `hG` of `C1_between_walls` discharged by walls, not assumed);
* `grid_col_faultSeg` : the column segment `[pt a0 y0, pt a0 (y0+m)]` is a `FaultSeg` for `lineChain v` (non-straddled
  because its ends lie on the row walls `y = y0`, `y = y0 + m`);
* `grid_C1_c` : `C1_c_row` instantiated: the row of length `n c`, `n < e`, has far chain `c^n` (POSITIVE witness: every
  hypothesis of `C1_c_row_md` is satisfied on a genuine dissection, `M = gridD_model`);
* `grid_C1_a` : `C1_a_row` instantiated on the column segment of length `m a`, `m < f`: far chain `a^m`;
* `grid_C1_c_fails_at_e` : NEGATIVE CONTROL.  The column segment of length `f a = e c` is a `FaultSeg` (the same
  hypotheses), but its far chain is NOT `c^e`: `¬ PureCover … e (tc e f)`.  So `C1_c_row` is false at `n = e` (the threshold
  of C1 is sharp: `e c = f a`, `MJ_ec_eq_fa`).
-/

namespace Erdos634.LaczCol

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.LaczJunction Erdos634.LaczJunction.Walk
  Erdos634.LaczJunction.Grammar Erdos634.Draft.TraceCovering Erdos634.LaczMJ Erdos634.LaczWall Erdos634.CertCoord Erdos634.Subdivision Set

section Grid

variable {e f : ℕ} (he : 1 ≤ e) (hef : e < f) {k : ℕ} (hk : 0 < k)

/-- A tile whose vertices all lie on one side of a level of a functional lies in that closed half-plane. -/
theorem side_of_vertices (T : Erdos634.Geometry.Tri) (φ : Plane →ₗ[ℝ] ℝ) (c : ℝ)
    (h : (∀ i, φ (T.pts i) ≤ c) ∨ (∀ i, c ≤ φ (T.pts i))) :
    T.carrier ⊆ {z | φ z ≤ c} ∨ T.carrier ⊆ {z | c ≤ φ z} := by
  rcases h with h | h
  · left
    intro y hy
    exact Tri.carrier_subset_halfplane T φ c h y hy
  · right
    intro y hy
    have := Tri.carrier_subset_halfplane T (-φ) (-c) (fun i => by simp only [LinearMap.neg_apply]; linarith [h i]) y hy
    simp only [LinearMap.neg_apply] at this
    simp only [Set.mem_setOf_eq]
    linarith

/-- Lattice coordinates of the vertices of a tile of the grid: `(x_m, y_m)`, `m = 0,1,2`, with `x_m ∈ {i, i+1}`,
`y_m ∈ {j, j+1}`. -/
theorem grid_tile_coords (n : Fin (k * k)) :
    ∃ (i j : ℕ), (∀ m : Fin 3, ∃ x y : ℝ, ((gridD he hef k hk).tile n).pts m = (gridL he hef).pt x y ∧
        (i : ℝ) ≤ x ∧ x ≤ (i : ℝ) + 1 ∧ (j : ℝ) ≤ y ∧ y ≤ (j : ℝ) + 1) := by
  rcases grid_tile_cases he hef hk n with ⟨i, j, -, hn⟩ | ⟨i, j, -, hn⟩
  · obtain ⟨h0, h1, h2⟩ := tile_up_pts he hef hk hn
    refine ⟨i, j, fun m => ?_⟩
    rcases Erdos634.LaczMJ.fin3_cases m with rfl | rfl | rfl
    · exact ⟨_, _, h0, le_rfl, by linarith, le_rfl, by linarith⟩
    · exact ⟨_, _, h1, by linarith, le_rfl, le_rfl, by linarith⟩
    · exact ⟨_, _, h2, le_rfl, by linarith, by linarith, le_rfl⟩
  · obtain ⟨h0, h1, h2⟩ := tile_down_pts he hef hk hn
    refine ⟨i, j, fun m => ?_⟩
    rcases Erdos634.LaczMJ.fin3_cases m with rfl | rfl | rfl
    · exact ⟨_, _, h0, by linarith, le_rfl, le_rfl, by linarith⟩
    · exact ⟨_, _, h1, le_rfl, by linarith, by linarith, le_rfl⟩
    · exact ⟨_, _, h2, by linarith, le_rfl, by linarith, le_rfl⟩

/-- **Every integer column line `x = j` is a wall of the grid.** -/
theorem grid_vwall (j : ℕ) (n : Fin (k * k)) :
    ((gridD he hef k hk).tile n).carrier ⊆
        {y | crossL (gridL he hef).v y ≤ cross (gridL he hef).v ((gridL he hef).pt (j : ℝ) 0)} ∨
    ((gridD he hef k hk).tile n).carrier ⊆
        {y | cross (gridL he hef).v ((gridL he hef).pt (j : ℝ) 0) ≤ crossL (gridL he hef).v y} := by
  set L := gridL he hef with hL
  have hκ : 0 < cross L.e0 L.v := L.hcr
  obtain ⟨i, j', hc⟩ := grid_tile_coords he hef hk n
  refine side_of_vertices _ _ _ ?_
  rcases le_or_gt j i with hji | hji
  · left
    intro m
    obtain ⟨x, y, hp, h1, h2, -, -⟩ := hc m
    rw [hp, crossL_apply, cross_v_pt, cross_v_pt]
    have : (j : ℝ) ≤ (i : ℝ) := by exact_mod_cast hji
    nlinarith
  · right
    intro m
    obtain ⟨x, y, hp, h1, h2, -, -⟩ := hc m
    rw [hp, crossL_apply, cross_v_pt, cross_v_pt]
    have : (i : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast hji
    nlinarith

/-- **Every integer row line `y = ρ` is a wall of the grid.** -/
theorem grid_hwall (ρ : ℕ) (n : Fin (k * k)) :
    ((gridD he hef k hk).tile n).carrier ⊆
        {y | crossL (gridL he hef).e0 y ≤ cross (gridL he hef).e0 ((gridL he hef).pt 0 (ρ : ℝ))} ∨
    ((gridD he hef k hk).tile n).carrier ⊆
        {y | cross (gridL he hef).e0 ((gridL he hef).pt 0 (ρ : ℝ)) ≤ crossL (gridL he hef).e0 y} := by
  set L := gridL he hef with hL
  have hκ : 0 < cross L.e0 L.v := L.hcr
  obtain ⟨i, j', hc⟩ := grid_tile_coords he hef hk n
  refine side_of_vertices _ _ _ ?_
  rcases le_or_gt (j' + 1) ρ with hjr | hjr
  · left
    intro m
    obtain ⟨x, y, hp, -, -, h1, h2⟩ := hc m
    rw [hp, crossL_apply, cross_e0_pt, cross_e0_pt]
    have : (j' : ℝ) + 1 ≤ (ρ : ℝ) := by exact_mod_cast hjr
    nlinarith
  · right
    intro m
    obtain ⟨x, y, hp, -, -, h1, h2⟩ := hc m
    rw [hp, crossL_apply, cross_e0_pt, cross_e0_pt]
    have : (ρ : ℝ) ≤ (j' : ℝ) := by exact_mod_cast (by omega : ρ ≤ j')
    nlinarith

theorem grid_wallAt_v (j : ℕ) {z : Plane}
    (hz : crossL (gridL he hef).v z = cross (gridL he hef).v ((gridL he hef).pt (j : ℝ) 0)) :
    WallAt (gridD he hef k hk).toDissection (crossL (gridL he hef).v)
      (cross (gridL he hef).v ((gridL he hef).pt (j : ℝ) 0)) z :=
  ⟨hz, fun i _ => grid_vwall he hef hk j i⟩

theorem grid_wallAt_h (ρ : ℕ) {z : Plane}
    (hz : crossL (gridL he hef).e0 z = cross (gridL he hef).e0 ((gridL he hef).pt 0 (ρ : ℝ))) :
    WallAt (gridD he hef k hk).toDissection (crossL (gridL he hef).e0)
      (cross (gridL he hef).e0 ((gridL he hef).pt 0 (ρ : ℝ))) z :=
  ⟨hz, fun i _ => grid_hwall he hef hk ρ i⟩

theorem BLat.pt_lineMap (L : BLat e f) (x1 y1 x2 y2 τ : ℝ) :
    AffineMap.lineMap (L.pt x1 y1) (L.pt x2 y2) τ = L.pt (x1 + τ * (x2 - x1)) (y1 + τ * (y2 - y1)) := by
  rw [AffineMap.lineMap_apply]
  simp only [BLat.pt, vsub_eq_sub, vadd_eq_add]
  module

theorem grid_e0_ne : (gridL he hef).e0 ≠ 0 := by
  intro h; have := (gridL he hef).hcr; rw [h] at this; simp [cross] at this

theorem grid_v_ne : (gridL he hef).v ≠ 0 := by
  intro h; have := (gridL he hef).hcr; rw [h] at this; simp [cross] at this

/-- **The row segment `[pt a0 ρ, pt (a0+n) ρ]` is a fault segment** (upper chain `lineChain (−e0)`), with its ends non-straddled
because they lie on the column walls `x = a0`, `x = a0 + n`. -/
theorem grid_row_faultSeg (a0 ρ n : ℕ) (hρ : 1 ≤ ρ) (hn : 1 ≤ n) (h : a0 + n + ρ + 1 ≤ k) :
    FaultSeg (gridD he hef k hk).toDissection ((gridL he hef).pt (a0 : ℝ) (ρ : ℝ))
      ((gridL he hef).pt ((a0 : ℝ) + n) (ρ : ℝ)) (crossL (-(gridL he hef).e0))
      (cross (-(gridL he hef).e0) ((gridL he hef).pt (a0 : ℝ) (ρ : ℝ))) := by
  set L := gridL he hef with hL
  have hκ : 0 < cross L.e0 L.v := L.hcr
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hρR : (1 : ℝ) ≤ ρ := by exact_mod_cast hρ
  have hkR : (a0 : ℝ) + n + ρ + 1 ≤ k := by exact_mod_cast h
  have hg0 : (crossL (-L.e0) : Plane →ₗ[ℝ] ℝ) ≠ 0 := by
    intro h0
    apply grid_e0_ne he hef
    have : -L.e0 = 0 := by
      apply eq_zero_of_cross_eq_zero
      intro w
      have := congrArg (fun g : Plane →ₗ[ℝ] ℝ => g w) h0
      simpa using this
    simpa using this
  have htrans : ∀ w, crossL L.v w = 0 → (crossL (-L.e0) : Plane →ₗ[ℝ] ℝ) w = 0 → w = 0 := by
    intro w h1 h2
    refine grid_trans he hef w h1 ?_
    simp only [crossL_apply, cross, PiLp.neg_apply] at h2 ⊢
    linarith
  have hnear : ∀ t : ℝ, 0 < t → t < 1 → ∃ (i : Fin (k * k)) (kk : Fin 3),
      AffineMap.lineMap (L.pt (a0 : ℝ) (ρ : ℝ)) (L.pt ((a0 : ℝ) + n) (ρ : ℝ)) t ∈
        ((gridD he hef k hk).tile i).edge kk := by
    intro t ht0 ht1
    have hq : ∀ τ : ℝ, L.pt ((a0 : ℝ) + τ) (ρ : ℝ) = L.pt (a0 : ℝ) (ρ : ℝ) + τ • L.e0 := by
      intro τ; simp only [BLat.pt]; module
    obtain ⟨i, kk, hik⟩ := chain_cover (gridD he hef k hk).toDissection (fun τ => L.pt ((a0 : ℝ) + τ) (ρ : ℝ))
      (L.pt (a0 : ℝ) (ρ : ℝ)) L.e0 hq n (by omega)
      (by
        intro t' ht'
        obtain ⟨i, hi⟩ := grid_up he hef hk (i := a0 + t') (j := ρ) (by omega)
        obtain ⟨kk, hkk⟩ := hi.edge_AB
        refine ⟨i, kk, ?_⟩
        rw [hkk]
        push_cast
        rw [add_assoc])
      (τ := (n : ℝ) * t) (by positivity) (by nlinarith)
    refine ⟨i, kk, ?_⟩
    have : AffineMap.lineMap (L.pt (a0 : ℝ) (ρ : ℝ)) (L.pt ((a0 : ℝ) + n) (ρ : ℝ)) t =
        L.pt ((a0 : ℝ) + (n : ℝ) * t) (ρ : ℝ) := by
      rw [BLat.pt_lineMap]; congr 1 <;> ring
    rw [this]; exact hik
  have hwallC : ∀ t : ℝ, 0 < t → t < 1 → ∀ i, AffineMap.lineMap (L.pt (a0 : ℝ) (ρ : ℝ))
      (L.pt ((a0 : ℝ) + n) (ρ : ℝ)) t ∉ interior ((gridD he hef k hk).tile i).carrier := by
    intro t ht0 ht1 i
    obtain ⟨j, kk, hmem⟩ := hnear t ht0 ht1
    exact (gridD he hef k hk).toDissection.edge_point_not_interior hmem i
  have hz0 : ∀ (j : ℕ) (y : ℝ), crossL L.v (L.pt (j : ℝ) y) = cross L.v (L.pt (j : ℝ) 0) := by
    intro j y; rw [crossL_apply, cross_v_pt, cross_v_pt]
  refine ⟨?_, hg0, rfl, ?_, ?_, hwallC, ?_, ?_⟩
  · intro hPG
    have h1 := L.pt_sub ((a0 : ℝ) + n) (ρ : ℝ) (a0 : ℝ) (ρ : ℝ)
    rw [← hPG, sub_self] at h1
    have h2 : (n : ℝ) • L.e0 = 0 := by
      have : ((a0 : ℝ) + n - a0) • L.e0 + ((ρ : ℝ) - ρ) • L.v = (n : ℝ) • L.e0 := by module
      rw [this] at h1; exact h1.symm
    rcases smul_eq_zero.mp h2 with h3 | h3
    · linarith
    · exact grid_e0_ne he hef h3
  · rw [crossL_apply, cross_neg_e0_pt L _ _ (ρ : ℝ), cross_neg_e0_pt L (a0 : ℝ) (ρ : ℝ) (ρ : ℝ)]
  · intro t ht0 ht1
    rw [BLat.pt_lineMap]
    have e1 : L.pt ((a0 : ℝ) + t * (((a0 : ℝ) + n) - a0)) ((ρ : ℝ) + t * ((ρ : ℝ) - ρ)) =
        ptA + ((a0 : ℝ) + t * n) • L.e0 + (ρ : ℝ) • L.v := by
      show ptA + _ • L.e0 + _ • L.v = _
      congr 2 <;> ring_nf
    rw [e1]
    exact grid_interior_pt he hef hk (by nlinarith) (by linarith) (by nlinarith)
  · have hz : crossL L.v (L.pt (a0 : ℝ) (ρ : ℝ)) = cross L.v (L.pt (a0 : ℝ) 0) := hz0 a0 ρ
    exact (grid_wallAt_v he hef hk a0 hz).not_straddled htrans
  · have hz : crossL L.v (L.pt ((a0 : ℝ) + n) (ρ : ℝ)) = cross L.v (L.pt ((a0 + n : ℕ) : ℝ) 0) := by
      have := hz0 (a0 + n) ρ
      push_cast at this ⊢
      exact this
    exact (grid_wallAt_v he hef hk (a0 + n) hz).not_straddled htrans

/-- **The column segment `[pt a0 y0, pt a0 (y0+m)]` is a fault segment** (chain `lineChain v`: the tiles to the right of the
wall `x = a0`), with its ends non-straddled because they lie on the row walls `y = y0`, `y = y0 + m`. -/
theorem grid_col_faultSeg (a0 y0 m : ℕ) (ha : 1 ≤ a0) (hy : 1 ≤ y0) (hm : 1 ≤ m) (h : a0 + y0 + m + 1 ≤ k) :
    FaultSeg (gridD he hef k hk).toDissection ((gridL he hef).pt (a0 : ℝ) (y0 : ℝ))
      ((gridL he hef).pt (a0 : ℝ) ((y0 : ℝ) + m)) (crossL (gridL he hef).v)
      (cross (gridL he hef).v ((gridL he hef).pt (a0 : ℝ) 0)) := by
  set L := gridL he hef with hL
  have hκ : 0 < cross L.e0 L.v := L.hcr
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hyR : (1 : ℝ) ≤ y0 := by exact_mod_cast hy
  have haR : (1 : ℝ) ≤ a0 := by exact_mod_cast ha
  have hkR : (a0 : ℝ) + y0 + m + 1 ≤ k := by exact_mod_cast h
  have hg0 : (crossL L.v : Plane →ₗ[ℝ] ℝ) ≠ 0 := by
    intro h0
    apply grid_v_ne he hef
    apply eq_zero_of_cross_eq_zero
    intro w
    have := congrArg (fun g : Plane →ₗ[ℝ] ℝ => g w) h0
    simpa using this
  have htrans : ∀ w, crossL L.e0 w = 0 → (crossL L.v : Plane →ₗ[ℝ] ℝ) w = 0 → w = 0 := by
    intro w h1 h2
    exact grid_trans he hef w h2 h1
  have hq : ∀ τ : ℝ, L.pt (a0 : ℝ) ((y0 : ℝ) + τ) = L.pt (a0 : ℝ) (y0 : ℝ) + τ • L.v := by
    intro τ; simp only [BLat.pt]; module
  have hnear : ∀ t : ℝ, 0 < t → t < 1 → ∃ (i : Fin (k * k)) (kk : Fin 3),
      AffineMap.lineMap (L.pt (a0 : ℝ) (y0 : ℝ)) (L.pt (a0 : ℝ) ((y0 : ℝ) + m)) t ∈
        ((gridD he hef k hk).tile i).edge kk := by
    intro t ht0 ht1
    obtain ⟨i, kk, hik⟩ := chain_cover (gridD he hef k hk).toDissection (fun τ => L.pt (a0 : ℝ) ((y0 : ℝ) + τ))
      (L.pt (a0 : ℝ) (y0 : ℝ)) L.v hq m (by omega)
      (by
        intro t' ht'
        obtain ⟨i, hi⟩ := grid_up he hef hk (i := a0) (j := y0 + t') (by omega)
        obtain ⟨kk, hkk⟩ := hi.edge_AC
        refine ⟨i, kk, ?_⟩
        rw [hkk]
        push_cast
        rw [add_assoc])
      (τ := (m : ℝ) * t) (by positivity) (by nlinarith)
    refine ⟨i, kk, ?_⟩
    have : AffineMap.lineMap (L.pt (a0 : ℝ) (y0 : ℝ)) (L.pt (a0 : ℝ) ((y0 : ℝ) + m)) t =
        L.pt (a0 : ℝ) ((y0 : ℝ) + (m : ℝ) * t) := by
      rw [BLat.pt_lineMap]; congr 1 <;> ring
    rw [this]; exact hik
  have hwallC : ∀ t : ℝ, 0 < t → t < 1 → ∀ i, AffineMap.lineMap (L.pt (a0 : ℝ) (y0 : ℝ))
      (L.pt (a0 : ℝ) ((y0 : ℝ) + m)) t ∉ interior ((gridD he hef k hk).tile i).carrier := by
    intro t ht0 ht1 i
    obtain ⟨j, kk, hmem⟩ := hnear t ht0 ht1
    exact (gridD he hef k hk).toDissection.edge_point_not_interior hmem i
  have hz0 : ∀ (y : ℝ), crossL L.v (L.pt (a0 : ℝ) y) = cross L.v (L.pt (a0 : ℝ) 0) := by
    intro y; rw [crossL_apply, cross_v_pt, cross_v_pt]
  have hh0 : ∀ (x : ℝ) (ρ : ℕ), crossL L.e0 (L.pt x (ρ : ℝ)) = cross L.e0 (L.pt 0 (ρ : ℝ)) + x * 0 := by
    intro x ρ
    rw [crossL_apply, cross_e0_pt, cross_e0_pt]; ring
  refine ⟨?_, hg0, hz0 _, ?_, ?_, hwallC, ?_, ?_⟩
  · intro hPG
    have h1 := L.pt_sub (a0 : ℝ) ((y0 : ℝ) + m) (a0 : ℝ) (y0 : ℝ)
    rw [← hPG, sub_self] at h1
    have h2 : (m : ℝ) • L.v = 0 := by
      have : ((a0 : ℝ) - a0) • L.e0 + (((y0 : ℝ) + m) - y0) • L.v = (m : ℝ) • L.v := by module
      rw [this] at h1; exact h1.symm
    rcases smul_eq_zero.mp h2 with h3 | h3
    · linarith
    · exact grid_v_ne he hef h3
  · exact hz0 _
  · intro t ht0 ht1
    rw [BLat.pt_lineMap]
    have e1 : L.pt ((a0 : ℝ) + t * ((a0 : ℝ) - a0)) ((y0 : ℝ) + t * (((y0 : ℝ) + m) - y0)) =
        ptA + (a0 : ℝ) • L.e0 + ((y0 : ℝ) + t * m) • L.v := by
      show ptA + _ • L.e0 + _ • L.v = _
      congr 2 <;> ring_nf
    rw [e1]
    exact grid_interior_pt he hef hk (by linarith) (by nlinarith) (by nlinarith)
  · have hz : crossL L.e0 (L.pt (a0 : ℝ) (y0 : ℝ)) = cross L.e0 (L.pt 0 (y0 : ℝ)) := by
      rw [crossL_apply, cross_e0_pt, cross_e0_pt]
    exact (grid_wallAt_h he hef hk y0 hz).not_straddled htrans
  · have hz : crossL L.e0 (L.pt (a0 : ℝ) ((y0 : ℝ) + m)) = cross L.e0 (L.pt 0 ((y0 + m : ℕ) : ℝ)) := by
      rw [crossL_apply, cross_e0_pt, cross_e0_pt]; push_cast; ring
    exact (grid_wallAt_h he hef hk (y0 + m) hz).not_straddled htrans

/-- The row has length `n c`. -/
theorem grid_row_dist (a0 ρ n : ℕ) :
    dist ((gridL he hef).pt (a0 : ℝ) (ρ : ℝ)) ((gridL he hef).pt ((a0 : ℝ) + n) (ρ : ℝ)) = (n : ℝ) * tc e f := by
  rw [BLat.dist_pt]
  have : ((a0 : ℝ) - ((a0 : ℝ) + n)) • (gridL he hef).e0 + ((ρ : ℝ) - ρ) • (gridL he hef).v =
      (-(n : ℝ)) • (gridL he hef).e0 := by module
  rw [this, norm_smul, (gridL he hef).he0]
  simp

/-- The column has length `m a`. -/
theorem grid_col_dist (a0 y0 m : ℕ) :
    dist ((gridL he hef).pt (a0 : ℝ) (y0 : ℝ)) ((gridL he hef).pt (a0 : ℝ) ((y0 : ℝ) + m)) = (m : ℝ) * ta e f := by
  rw [BLat.dist_pt]
  have : ((a0 : ℝ) - a0) • (gridL he hef).e0 + ((y0 : ℝ) - ((y0 : ℝ) + m)) • (gridL he hef).v =
      (-(m : ℝ)) • (gridL he hef).v := by module
  rw [this, norm_smul, (gridL he hef).hv]
  simp

/-- **POSITIVE witness for C1 (`c`-rows).**  On the genuine grid, `C1_c_row_md` applies to the row of length `n c`,
`1 ≤ n < e`, `a0 + n + ρ + 1 ≤ k`: every hypothesis (`FaultSeg`: interior, fault line, ends on walls; model data) is
satisfied, and the far chain is `c^n`. -/
theorem grid_C1_c (hcop : Nat.Coprime e f) (a0 ρ n : ℕ) (hρ : 1 ≤ ρ) (hn : 1 ≤ n) (hne : n < e)
    (h : a0 + n + ρ + 1 ≤ k) :
    PureCover (gridD he hef k hk).toDissection (crossL (-(gridL he hef).e0))
      (cross (-(gridL he hef).e0) ((gridL he hef).pt (a0 : ℝ) (ρ : ℝ)))
      ((gridL he hef).pt (a0 : ℝ) (ρ : ℝ)) ((gridL he hef).pt ((a0 : ℝ) + n) (ρ : ℝ)) n (tc e f) :=
  C1_c_row_md (gridD_model he hef hcop k hk) hcop (grid_row_faultSeg he hef hk a0 ρ n hρ hn h) hne
    (grid_row_dist he hef a0 ρ n)

/-- **POSITIVE witness for C1 (`a`-columns).**  The column segment of length `m a`, `1 ≤ m < f`, has far chain `a^m`. -/
theorem grid_C1_a (hcop : Nat.Coprime e f) (a0 y0 m : ℕ) (ha : 1 ≤ a0) (hy : 1 ≤ y0) (hm : 1 ≤ m) (hmf : m < f)
    (h : a0 + y0 + m + 1 ≤ k) :
    PureCover (gridD he hef k hk).toDissection (crossL (gridL he hef).v)
      (cross (gridL he hef).v ((gridL he hef).pt (a0 : ℝ) 0))
      ((gridL he hef).pt (a0 : ℝ) (y0 : ℝ)) ((gridL he hef).pt (a0 : ℝ) ((y0 : ℝ) + m)) m (ta e f) :=
  C1_a_row_md (gridD_model he hef hcop k hk) hcop (grid_col_faultSeg he hef hk a0 y0 m ha hy hm h) hmf
    (grid_col_dist he hef a0 y0 m)

/-- **NEGATIVE CONTROL for C1 at the threshold `e c = f a`.**  The column segment of length `f a = e c` satisfies every
hypothesis of `C1_c_row_md` except `n < e` (here `n = e`: `FaultSeg`, `dist P G = e · c`), and its far chain is NOT `c^e`:
the edges on the wall are `a`-edges.  So `C1_c_row` is false at `n = e`. -/
theorem grid_C1_c_fails_at_e (hcop : Nat.Coprime e f) (a0 y0 : ℕ) (ha : 1 ≤ a0) (hy : 1 ≤ y0)
    (h : a0 + y0 + f + 1 ≤ k) :
    FaultSeg (gridD he hef k hk).toDissection ((gridL he hef).pt (a0 : ℝ) (y0 : ℝ))
      ((gridL he hef).pt (a0 : ℝ) ((y0 : ℝ) + f)) (crossL (gridL he hef).v)
      (cross (gridL he hef).v ((gridL he hef).pt (a0 : ℝ) 0)) ∧
    dist ((gridL he hef).pt (a0 : ℝ) (y0 : ℝ)) ((gridL he hef).pt (a0 : ℝ) ((y0 : ℝ) + f)) = (e : ℝ) * tc e f ∧
    ¬ PureCover (gridD he hef k hk).toDissection (crossL (gridL he hef).v)
      (cross (gridL he hef).v ((gridL he hef).pt (a0 : ℝ) 0))
      ((gridL he hef).pt (a0 : ℝ) (y0 : ℝ)) ((gridL he hef).pt (a0 : ℝ) ((y0 : ℝ) + f)) e (tc e f) := by
  set L := gridL he hef with hL
  have hf1 : 1 ≤ f := by omega
  have hFS := grid_col_faultSeg he hef hk a0 y0 f ha hy hf1 h
  refine ⟨hFS, ?_, ?_⟩
  · rw [grid_col_dist he hef a0 y0 f]
    have := LaczColumn.ec_eq_fa' e f
    have h2 : (e : ℝ) * (tc e f : ℝ) = (f : ℝ) * (ta e f : ℝ) := by exact_mod_cast this
    rw [h2]
  · intro H
    obtain ⟨u, hu⟩ := gridDiss_tile_up ptA (gB e f) (gC e f) (gInd he hef) k hk (i := a0) (j := y0) (by omega)
    have hu' : (gridD he hef k hk).tile u = cellUp ptA (gB e f) (gC e f) (gInd he hef) a0 y0 := hu
    obtain ⟨p0, p1, p2⟩ := tile_up_pts he hef hk hu'
    have hκ : 0 < cross L.e0 L.v := L.hcr
    have hmem : ((u, (2 : Fin 3)) : Fin (k * k) × Fin 3) ∈ (gridD he hef k hk).toDissection.lineChain
        (crossL L.v) (cross L.v (L.pt (a0 : ℝ) 0)) := by
      rw [Dissection.mem_lineChain]
      have e3 : (2 : Fin 3) + 1 = 0 := rfl
      refine ⟨?_, ?_, ?_⟩
      · show crossL L.v (((gridD he hef k hk).tile u).pts 2) = _
        rw [p2, crossL_apply, cross_v_pt, cross_v_pt]
      · show crossL L.v (((gridD he hef k hk).tile u).pts (2 + 1)) = _
        rw [e3, p0, crossL_apply, cross_v_pt, cross_v_pt]
      · intro j
        rcases Erdos634.LaczMJ.fin3_cases j with rfl | rfl | rfl
        · show crossL L.v (((gridD he hef k hk).tile u).pts 0) ≤ _
          rw [p0, crossL_apply, cross_v_pt, cross_v_pt]
        · show crossL L.v (((gridD he hef k hk).tile u).pts 1) ≤ _
          rw [p1, crossL_apply, cross_v_pt, cross_v_pt]; nlinarith
        · show crossL L.v (((gridD he hef k hk).tile u).pts 2) ≤ _
          rw [p2, crossL_apply, cross_v_pt, cross_v_pt]
    have e3 : (2 : Fin 3) + 1 = 0 := rfl
    have hsub : ((gridD he hef k hk).tile u).edge 2 ⊆ segment ℝ (L.pt (a0 : ℝ) (y0 : ℝ))
        (L.pt (a0 : ℝ) ((y0 : ℝ) + f)) := by
      show segment ℝ (((gridD he hef k hk).tile u).pts 2) (((gridD he hef k hk).tile u).pts (2 + 1)) ⊆ _
      rw [e3, p2, p0]
      refine (convex_segment _ _).segment_subset ?_ ?_
      · have : L.pt (a0 : ℝ) ((y0 : ℝ) + 1) = AffineMap.lineMap (L.pt (a0 : ℝ) (y0 : ℝ))
            (L.pt (a0 : ℝ) ((y0 : ℝ) + f)) (1 / (f : ℝ)) := by
          rw [BLat.pt_lineMap]
          have hfR : (f : ℝ) ≠ 0 := by positivity
          congr 1 <;> field_simp <;> ring
        rw [this]
        rw [segment_eq_image_lineMap]
        exact ⟨1 / (f : ℝ), ⟨by positivity, by
          rw [div_le_one (by positivity)]; exact_mod_cast hf1⟩, rfl⟩
      · exact left_mem_segment _ _ _
    have := H.1 _ hmem hsub
    simp only at this
    rw [e3, p2, p0] at this
    have hd : dist (L.pt (a0 : ℝ) ((y0 : ℝ) + 1)) (L.pt (a0 : ℝ) (y0 : ℝ)) = (ta e f : ℝ) := by
      rw [dist_comm]; exact L.dist_pt_a _ _
    rw [hd] at this
    have hac : ta e f < tc e f := by
      unfold ta tc
      have : e * f < f * f := Nat.mul_lt_mul_of_pos_right hef (by omega)
      nlinarith
    have : (ta e f : ℝ) = tc e f := this
    have h3 : ta e f = tc e f := by exact_mod_cast this
    omega

#print axioms grid_C1_c
#print axioms grid_C1_a
#print axioms grid_C1_c_fails_at_e

/-- **The chord (hypotenuse) segment `[pt x0 y0, pt (x0−n) (y0+n)]` is a fault segment** (chain `lineChain (v − e0)`: the tiles
above the diagonal), with its ends non-straddled because they lie on the row walls `y = y0`, `y = y0 + n`. -/
theorem grid_chord_faultSeg (x0 y0 n : ℕ) (hy : 1 ≤ y0) (hn : 1 ≤ n) (hx : n ≤ x0) (h : x0 + y0 + 2 ≤ k) :
    FaultSeg (gridD he hef k hk).toDissection ((gridL he hef).pt (x0 : ℝ) (y0 : ℝ))
      ((gridL he hef).pt ((x0 : ℝ) - n) ((y0 : ℝ) + n)) (crossL ((gridL he hef).v - (gridL he hef).e0))
      (cross ((gridL he hef).v - (gridL he hef).e0) ((gridL he hef).pt (x0 : ℝ) (y0 : ℝ))) := by
  set L := gridL he hef with hL
  have hκ : 0 < cross L.e0 L.v := L.hcr
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hyR : (1 : ℝ) ≤ y0 := by exact_mod_cast hy
  have hxR : (n : ℝ) ≤ x0 := by exact_mod_cast hx
  have hkR : (x0 : ℝ) + y0 + 2 ≤ k := by exact_mod_cast h
  have hu0 : L.v - L.e0 ≠ 0 := by
    intro h0
    have : ‖L.v - L.e0‖ = 0 := by rw [h0, norm_zero]
    rw [L.hu] at this
    have hb : (0 : ℝ) < tb e f := by exact_mod_cast b_pos e f he hef
    linarith
  have hg0 : (crossL (L.v - L.e0) : Plane →ₗ[ℝ] ℝ) ≠ 0 := by
    intro h0
    apply hu0
    apply eq_zero_of_cross_eq_zero
    intro w
    have := congrArg (fun g : Plane →ₗ[ℝ] ℝ => g w) h0
    simpa using this
  have htrans : ∀ w, crossL L.e0 w = 0 → (crossL (L.v - L.e0) : Plane →ₗ[ℝ] ℝ) w = 0 → w = 0 := by
    intro w h1 h2
    refine grid_trans he hef w ?_ h1
    simp only [crossL_apply, cross, PiLp.sub_apply] at h1 h2 ⊢
    linarith
  have hq : ∀ τ : ℝ, L.pt ((x0 : ℝ) - τ) ((y0 : ℝ) + τ) = L.pt (x0 : ℝ) (y0 : ℝ) + τ • (L.v - L.e0) := by
    intro τ; simp only [BLat.pt]; module
  have hnear : ∀ t : ℝ, 0 < t → t < 1 → ∃ (i : Fin (k * k)) (kk : Fin 3),
      AffineMap.lineMap (L.pt (x0 : ℝ) (y0 : ℝ)) (L.pt ((x0 : ℝ) - n) ((y0 : ℝ) + n)) t ∈
        ((gridD he hef k hk).tile i).edge kk := by
    intro t ht0 ht1
    obtain ⟨i, kk, hik⟩ := chain_cover (gridD he hef k hk).toDissection
      (fun τ => L.pt ((x0 : ℝ) - τ) ((y0 : ℝ) + τ)) (L.pt (x0 : ℝ) (y0 : ℝ)) (L.v - L.e0) hq n (by omega)
      (by
        intro t' ht'
        obtain ⟨i, hi⟩ := grid_down he hef hk (i := x0 - 1 - t') (j := y0 + t') (by omega)
        obtain ⟨kk, hkk⟩ := hi.edge_AB
        refine ⟨i, kk, ?_⟩
        rw [hkk]
        have e1 : ((x0 - 1 - t' : ℕ) : ℝ) + 1 = (x0 : ℝ) - t' := by
          rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
        have e2 : ((x0 - 1 - t' : ℕ) : ℝ) = (x0 : ℝ) - ((t' : ℝ) + 1) := by
          rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
        have e3 : ((y0 + t' : ℕ) : ℝ) = (y0 : ℝ) + t' := by push_cast; ring
        rw [e1, e2, e3]
        push_cast
        rw [add_assoc (y0 : ℝ) (t' : ℝ) 1])
      (τ := (n : ℝ) * t) (by positivity) (by nlinarith)
    refine ⟨i, kk, ?_⟩
    have : AffineMap.lineMap (L.pt (x0 : ℝ) (y0 : ℝ)) (L.pt ((x0 : ℝ) - n) ((y0 : ℝ) + n)) t =
        L.pt ((x0 : ℝ) - (n : ℝ) * t) ((y0 : ℝ) + (n : ℝ) * t) := by
      rw [BLat.pt_lineMap]; congr 1 <;> ring
    rw [this]; exact hik
  have hwallC : ∀ t : ℝ, 0 < t → t < 1 → ∀ i, AffineMap.lineMap (L.pt (x0 : ℝ) (y0 : ℝ))
      (L.pt ((x0 : ℝ) - n) ((y0 : ℝ) + n)) t ∉ interior ((gridD he hef k hk).tile i).carrier := by
    intro t ht0 ht1 i
    obtain ⟨j, kk, hmem⟩ := hnear t ht0 ht1
    exact (gridD he hef k hk).toDissection.edge_point_not_interior hmem i
  refine ⟨?_, hg0, rfl, ?_, ?_, hwallC, ?_, ?_⟩
  · intro hPG
    have h1 := L.pt_sub (x0 : ℝ) (y0 : ℝ) ((x0 : ℝ) - n) ((y0 : ℝ) + n)
    rw [hPG, sub_self] at h1
    have h2 : (n : ℝ) • (L.e0 - L.v) = 0 := by
      have : ((x0 : ℝ) - ((x0 : ℝ) - n)) • L.e0 + ((y0 : ℝ) - ((y0 : ℝ) + n)) • L.v = (n : ℝ) • (L.e0 - L.v) := by
        module
      rw [this] at h1; exact h1.symm
    rcases smul_eq_zero.mp h2 with h3 | h3
    · linarith
    · apply hu0
      have : L.e0 - L.v = 0 := h3
      have h4 : L.v - L.e0 = -(L.e0 - L.v) := by abel
      rw [h4, this]; simp
  · rw [crossL_apply, cross_hyp_pt L ((x0 : ℝ) - n) ((y0 : ℝ) + n) (x0 : ℝ) (y0 : ℝ)]
    ring_nf
  · intro t ht0 ht1
    rw [BLat.pt_lineMap]
    have e1 : L.pt ((x0 : ℝ) + t * (((x0 : ℝ) - n) - x0)) ((y0 : ℝ) + t * (((y0 : ℝ) + n) - y0)) =
        ptA + ((x0 : ℝ) - t * n) • L.e0 + ((y0 : ℝ) + t * n) • L.v := by
      show ptA + _ • L.e0 + _ • L.v = _
      congr 2 <;> ring_nf
    rw [e1]
    exact grid_interior_pt he hef hk (by nlinarith) (by nlinarith) (by nlinarith)
  · have hz : crossL L.e0 (L.pt (x0 : ℝ) (y0 : ℝ)) = cross L.e0 (L.pt 0 (y0 : ℝ)) := by
      rw [crossL_apply, cross_e0_pt, cross_e0_pt]
    exact (grid_wallAt_h he hef hk y0 hz).not_straddled htrans
  · have hz : crossL L.e0 (L.pt ((x0 : ℝ) - n) ((y0 : ℝ) + n)) = cross L.e0 (L.pt 0 ((y0 + n : ℕ) : ℝ)) := by
      rw [crossL_apply, cross_e0_pt, cross_e0_pt]; push_cast; ring
    exact (grid_wallAt_h he hef hk (y0 + n) hz).not_straddled htrans

/-- The chord has length `n b`. -/
theorem grid_chord_dist (x0 y0 n : ℕ) :
    dist ((gridL he hef).pt (x0 : ℝ) (y0 : ℝ)) ((gridL he hef).pt ((x0 : ℝ) - n) ((y0 : ℝ) + n)) =
      (n : ℝ) * tb e f := by
  rw [BLat.dist_pt]
  have : ((x0 : ℝ) - ((x0 : ℝ) - n)) • (gridL he hef).e0 + ((y0 : ℝ) - ((y0 : ℝ) + n)) • (gridL he hef).v =
      (-(n : ℝ)) • ((gridL he hef).v - (gridL he hef).e0) := by module
  rw [this, norm_smul, (gridL he hef).hu]
  simp

/-- **POSITIVE witness for C3 (chords).**  The hypotenuse chord of length `n b`, `1 ≤ n < f`, has far chain `b^n`. -/
theorem grid_C3_b (hcop : Nat.Coprime e f) (x0 y0 n : ℕ) (hy : 1 ≤ y0) (hn : 1 ≤ n) (hx : n ≤ x0) (hnf : n < f)
    (h : x0 + y0 + 2 ≤ k) :
    PureCover (gridD he hef k hk).toDissection (crossL ((gridL he hef).v - (gridL he hef).e0))
      (cross ((gridL he hef).v - (gridL he hef).e0) ((gridL he hef).pt (x0 : ℝ) (y0 : ℝ)))
      ((gridL he hef).pt (x0 : ℝ) (y0 : ℝ)) ((gridL he hef).pt ((x0 : ℝ) - n) ((y0 : ℝ) + n)) n (tb e f) :=
  C3_b_row_md (gridD_model he hef hcop k hk) hcop (grid_chord_faultSeg he hef hk x0 y0 n hy hn hx h) hnf
    (grid_chord_dist he hef x0 y0 n)

#print axioms grid_C3_b

/-- **Witness for the hypotheses of `C4_bfree_counts`**: on the grid row of length `n c`, `n < e`, the segment is a fault
segment of length `n c` and every chain edge inside it is an `a`- or a `c`-edge (it is a `c`-edge by `grid_C1_c`). -/
theorem grid_C4_hyps (hcop : Nat.Coprime e f) (a0 ρ n : ℕ) (hρ : 1 ≤ ρ) (hn : 1 ≤ n) (hne : n < e)
    (h : a0 + n + ρ + 1 ≤ k) :
    FaultSeg (gridD he hef k hk).toDissection ((gridL he hef).pt (a0 : ℝ) (ρ : ℝ))
      ((gridL he hef).pt ((a0 : ℝ) + n) (ρ : ℝ)) (crossL (-(gridL he hef).e0))
      (cross (-(gridL he hef).e0) ((gridL he hef).pt (a0 : ℝ) (ρ : ℝ))) ∧
    dist ((gridL he hef).pt (a0 : ℝ) (ρ : ℝ)) ((gridL he hef).pt ((a0 : ℝ) + n) (ρ : ℝ)) = (n : ℝ) * tc e f ∧
    (∀ e' ∈ (gridD he hef k hk).toDissection.lineChain (crossL (-(gridL he hef).e0))
        (cross (-(gridL he hef).e0) ((gridL he hef).pt (a0 : ℝ) (ρ : ℝ))),
      ((gridD he hef k hk).tile e'.1).edge e'.2 ⊆ segment ℝ ((gridL he hef).pt (a0 : ℝ) (ρ : ℝ))
          ((gridL he hef).pt ((a0 : ℝ) + n) (ρ : ℝ)) →
      dist (((gridD he hef k hk).tile e'.1).pts e'.2) (((gridD he hef k hk).tile e'.1).pts (e'.2 + 1)) = (ta e f : ℝ) ∨
      dist (((gridD he hef k hk).tile e'.1).pts e'.2) (((gridD he hef k hk).tile e'.1).pts (e'.2 + 1)) = (tc e f : ℝ)) :=
  ⟨grid_row_faultSeg he hef hk a0 ρ n hρ hn h, grid_row_dist he hef a0 ρ n,
    fun e' he' hsub => Or.inr ((grid_C1_c he hef hk hcop a0 ρ n hρ hn hne h).1 e' he' hsub)⟩

/-- **Witness for `C1_counts_invariant`**: two grid rows of the same length `n c`, `n < e`, at different places, satisfy its
hypotheses, and their numbers of `a`- and `c`-edges agree (`0` and `n`). -/
theorem grid_C1_counts (hcop : Nat.Coprime e f) (a0 ρ a1 ρ1 n : ℕ) (hρ : 1 ≤ ρ) (hρ1 : 1 ≤ ρ1) (hn : 1 ≤ n)
    (hne : n < e) (h : a0 + n + ρ + 1 ≤ k) (h1 : a1 + n + ρ1 + 1 ≤ k) :
    lenCount (gridD he hef k hk).toDissection (crossL (-(gridL he hef).e0))
        (cross (-(gridL he hef).e0) ((gridL he hef).pt (a0 : ℝ) (ρ : ℝ)))
        ((gridL he hef).pt (a0 : ℝ) (ρ : ℝ)) ((gridL he hef).pt ((a0 : ℝ) + n) (ρ : ℝ)) (ta e f : ℝ) =
      lenCount (gridD he hef k hk).toDissection (crossL (-(gridL he hef).e0))
        (cross (-(gridL he hef).e0) ((gridL he hef).pt (a1 : ℝ) (ρ1 : ℝ)))
        ((gridL he hef).pt (a1 : ℝ) (ρ1 : ℝ)) ((gridL he hef).pt ((a1 : ℝ) + n) (ρ1 : ℝ)) (ta e f : ℝ) ∧
    lenCount (gridD he hef k hk).toDissection (crossL (-(gridL he hef).e0))
        (cross (-(gridL he hef).e0) ((gridL he hef).pt (a0 : ℝ) (ρ : ℝ)))
        ((gridL he hef).pt (a0 : ℝ) (ρ : ℝ)) ((gridL he hef).pt ((a0 : ℝ) + n) (ρ : ℝ)) (tc e f : ℝ) =
      lenCount (gridD he hef k hk).toDissection (crossL (-(gridL he hef).e0))
        (cross (-(gridL he hef).e0) ((gridL he hef).pt (a1 : ℝ) (ρ1 : ℝ)))
        ((gridL he hef).pt (a1 : ℝ) (ρ1 : ℝ)) ((gridL he hef).pt ((a1 : ℝ) + n) (ρ1 : ℝ)) (tc e f : ℝ) := by
  classical
  have hP := grid_C1_c he hef hk hcop a0 ρ n hρ hn hne h
  have hP1 := grid_C1_c he hef hk hcop a1 ρ1 n hρ1 hn hne h1
  refine C1_counts_invariant he hef hcop (grid_row_faultSeg he hef hk a0 ρ n hρ hn h)
    (grid_row_faultSeg he hef hk a1 ρ1 n hρ1 hn h1) ?_ ?_ ?_ ?_
  · intro e' he'
    obtain ⟨hch, hsub⟩ := Finset.mem_filter.mp he'
    exact Or.inr (hP.1 e' hch hsub)
  · intro e' he'
    obtain ⟨hch, hsub⟩ := Finset.mem_filter.mp he'
    exact Or.inr (hP1.1 e' hch hsub)
  · rw [grid_row_dist he hef a0 ρ n, grid_row_dist he hef a1 ρ1 n]
  · rw [grid_row_dist he hef a0 ρ n]
    have : (n : ℝ) < e := by exact_mod_cast hne
    have hc : (0 : ℝ) < tc e f := by exact_mod_cast LaczColumn.tc_pos' e f hef
    nlinarith

end Grid

variable {N : ℕ}

/-- The lattice of a wall frame. -/
def WFrame.toBLat' {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ} {p q r : Fin 3}
    (F : WFrame D e f α β γ p q r) : BLat e f := ⟨F.O, F.e0, F.v, F.he0, F.hv, F.hu, F.hcr⟩

/-- The wall rule `T(m)` is the bare predicate `TRuleB` of `LaczFormalMJBare` at the levels `lv ≥ 1`. -/
theorem WFrame.TRule_iff {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ} {p q r : Fin 3}
    (F : WFrame D e f α β γ p q r) (H m : ℕ) :
    F.TRule H m ↔ ∀ lv : ℕ, 1 ≤ lv → lv + m + 1 ≤ H → m + 1 ≤ e → GroundB D.tile F.toBLat' lv (m + 1) →
      (∀ x : ℕ, x ≤ m → UpCellB D.tile F.toBLat' (x : ℝ) (lv : ℝ)) → DownCellB D.tile F.toBLat' (m : ℝ) (lv : ℝ) :=
  Iff.rfl

section GridRule

variable {e f : ℕ} (he : 1 ≤ e) (hef : e < f) {k : ℕ} (hk : 0 < k)

/-- **The premises of the wall rule `T(m)` are satisfied and its conclusion holds on the genuine grid** (levels `lv ≥ 1`;
this is `grid_TRule_premises`, i.e. the bare predicates of `WFrame.TRule_iff` are exercised on a real dissection). -/
theorem grid_TRule_exercised {m lv : ℕ} (hlv : 1 ≤ lv) (h : lv + m + 2 ≤ k) :
    GroundB (gridD he hef k hk).tile (gridL he hef) lv (m + 1) ∧
    (∀ x : ℕ, x ≤ m → UpCellB (gridD he hef k hk).tile (gridL he hef) (x : ℝ) (lv : ℝ)) ∧
    DownCellB (gridD he hef k hk).tile (gridL he hef) (m : ℝ) (lv : ℝ) :=
  grid_TRule_premises he hef hk h

end GridRule

end Erdos634.LaczCol
