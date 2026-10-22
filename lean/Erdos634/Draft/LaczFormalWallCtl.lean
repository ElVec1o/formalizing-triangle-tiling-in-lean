import Erdos634.Draft.LaczFormalMJCellCtl
import Erdos634.Draft.LaczFormalWall

/-!
# Non-vacuity control for the wall layer: a genuine interior straight wall in a real dissection

Erdős #634, base-`β` band, Wall Lemma layer.  This file proves NOTHING new about #634.  Credit: AI assistant (Wall Lemma
proposal), Beeson–Roșu, Beeson, Laczkovich, Paliy.  UNAUDITED.  Axiom-clean; no `sorry`.

In the grid dissection `gridD` (`k²` copies of the tile of `(e,f)` in the triangle `kT`, a real `CongruentDissection`)
the lattice line `x = 1` (direction `v`, the `a`-direction) is an INTERIOR straight line crossed by no tile:
`grid_wall_side`.  So the hypothesis `hside` of `wall_figure`, `wall_leg_fig`, `wall_not_straddled` is satisfiable,
and `grid_wall_not_straddled` is an instance of `wall_not_straddled` on a real dissection (no horizontal chain edge
passes through the interior of a point of the wall).  `grid_cross_not_straddled_fails` is the negative control: on the
non-wall line `x = 1/2` (crossed by tiles) the corresponding statement is FALSE — a chain edge of the grid passes
through the point `pt (1/2) 1`.

WHAT IS NOT DONE: `wall_figure` itself is not exercised (it needs a `BandSetup`, which a grid does not have: the
grid is not a band target).
-/

namespace Erdos634.LaczMJ

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.LaczJunction Erdos634.LaczJunction.Walk
  Erdos634.LaczJunction.Grammar Erdos634.Subdivision Erdos634.CertCoord Erdos634.Draft.TraceCovering

section Ctl

variable {e f : ℕ} (he : 1 ≤ e) (hef : e < f) {k : ℕ} (hk : 0 < k)

theorem cross_v_pt (L : BLat e f) (x y : ℝ) :
    cross L.v (L.pt x y) = cross L.v L.O - x * cross L.e0 L.v := by
  simp only [cross, BLat.pt, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring

theorem cross_e0_pt (L : BLat e f) (x y : ℝ) :
    cross L.e0 (L.pt x y) = cross L.e0 L.O + y * cross L.e0 L.v := by
  simp only [cross, BLat.pt, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring

/-- Every tile of the grid is an up cell or a down cell. -/
theorem grid_tile_cases (n : Fin (k * k)) :
    (∃ i j : ℕ, i + j + 1 ≤ k ∧
        (gridD he hef k hk).tile n = cellUp ptA (gB e f) (gC e f) (gInd he hef) i j) ∨
    (∃ i j : ℕ, i + j + 2 ≤ k ∧
        (gridD he hef k hk).tile n = cellDown ptA (gB e f) (gC e f) (gInd he hef) i j) := by
  obtain ⟨⟨⟨b, i, j⟩, hmem⟩, hn⟩ : ∃ z : {x // x ∈ cellSet k}, z = cellIdx k n := ⟨_, rfl⟩
  have ht : (gridD he hef k hk).tile n = cellOf ptA (gB e f) (gC e f) (gInd he hef) (b, i, j) := by
    show cellOf ptA (gB e f) (gC e f) (gInd he hef) ((cellIdx k n : Bool × ℕ × ℕ)) = _
    rw [← hn]
  simp only [cellSet, Finset.mem_union, Finset.mem_image] at hmem
  rcases hmem with ⟨⟨i', j'⟩, hm, heq⟩ | ⟨⟨i', j'⟩, hm, heq⟩
  · have hb : b = true := (congrArg Prod.fst heq).symm
    have h2 : (i, j) = (i', j') := (congrArg Prod.snd heq).symm
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h2
    subst hb
    exact Or.inl ⟨i, j, mem_upSet.mp hm, by rw [ht]; simp [cellOf]⟩
  · have hb : b = false := (congrArg Prod.fst heq).symm
    have h2 : (i, j) = (i', j') := (congrArg Prod.snd heq).symm
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h2
    subst hb
    exact Or.inr ⟨i, j, mem_downSet.mp hm, by rw [ht]; simp [cellOf]⟩

/-- **The wall `x = 1` of the grid.**  Every tile of the grid lies wholly on one closed side of the lattice line
`{x = 1}` (direction `v`): tiles in columns `i ≥ 1` on the side `x ≥ 1`, tiles in column `0` on the side `x ≤ 1`.
Here `g = crossL v` (so `g (pt x y) = cross v O − x κ`, `κ = cross e0 v > 0`) and `c = g (pt 1 0)`. -/
theorem grid_wall_side (n : Fin (k * k)) :
    ((gridD he hef k hk).tile n).carrier ⊆
        {y | crossL (gridL he hef).v y ≤ cross (gridL he hef).v ((gridL he hef).pt 1 0)} ∨
    ((gridD he hef k hk).tile n).carrier ⊆
        {y | cross (gridL he hef).v ((gridL he hef).pt 1 0) ≤ crossL (gridL he hef).v y} := by
  set L := gridL he hef with hL
  have hκ : 0 < cross L.e0 L.v := L.hcr
  have key : ∀ (T : Tri), (∀ i, ∃ x y : ℝ, T.pts i = L.pt x y ∧ 1 ≤ x) ∨
      (∀ i, ∃ x y : ℝ, T.pts i = L.pt x y ∧ x ≤ 1) →
      T.carrier ⊆ {y | crossL L.v y ≤ cross L.v (L.pt 1 0)} ∨
        T.carrier ⊆ {y | cross L.v (L.pt 1 0) ≤ crossL L.v y} := by
    intro T hT
    rcases hT with h | h
    · left
      intro y hy
      refine Tri.carrier_subset_halfplane T (crossL L.v) (cross L.v (L.pt 1 0)) (fun i => ?_) y hy
      obtain ⟨x, y', hp, hx⟩ := h i
      rw [hp, crossL_apply, cross_v_pt, cross_v_pt]
      nlinarith
    · right
      intro y hy
      have := Tri.carrier_subset_halfplane T (-(crossL L.v)) (-(cross L.v (L.pt 1 0))) (fun i => ?_) y hy
      · simp only [LinearMap.neg_apply] at this
        simp only [Set.mem_setOf_eq]
        linarith
      · obtain ⟨x, y', hp, hx⟩ := h i
        simp only [LinearMap.neg_apply]
        rw [hp, crossL_apply, cross_v_pt, cross_v_pt]
        nlinarith
  rcases grid_tile_cases he hef hk n with ⟨i, j, -, hn⟩ | ⟨i, j, -, hn⟩
  · obtain ⟨h0, h1, h2⟩ := tile_up_pts he hef hk hn
    refine key _ ?_
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · right
      intro m
      rcases fin3_cases m with rfl | rfl | rfl
      · exact ⟨_, _, h0, by simp⟩
      · exact ⟨_, _, h1, by simp⟩
      · exact ⟨_, _, h2, by simp⟩
    · left
      have hi' : (1 : ℝ) ≤ i := by exact_mod_cast hi
      intro m
      rcases fin3_cases m with rfl | rfl | rfl
      · exact ⟨_, _, h0, hi'⟩
      · exact ⟨_, _, h1, by linarith⟩
      · exact ⟨_, _, h2, hi'⟩
  · obtain ⟨h0, h1, h2⟩ := tile_down_pts he hef hk hn
    refine key _ ?_
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · right
      intro m
      rcases fin3_cases m with rfl | rfl | rfl
      · exact ⟨_, _, h0, by simp⟩
      · exact ⟨_, _, h1, by simp⟩
      · exact ⟨_, _, h2, by simp⟩
    · left
      have hi' : (1 : ℝ) ≤ i := by exact_mod_cast hi
      intro m
      rcases fin3_cases m with rfl | rfl | rfl
      · exact ⟨_, _, h0, by linarith⟩
      · exact ⟨_, _, h1, hi'⟩
      · exact ⟨_, _, h2, by linarith⟩

/-- Transversality of the wall direction `v` and the base direction `e0`. -/
theorem grid_trans (w : Plane) (h1 : crossL (gridL he hef).v w = 0) (h2 : crossL (gridL he hef).e0 w = 0) :
    w = 0 := by
  have hκ : cross (gridL he hef).e0 (gridL he hef).v ≠ 0 := (gridL he hef).hcr.ne'
  simp only [crossL_apply, cross] at h1 h2 hκ
  have p0 : w 0 * ((gridL he hef).e0 0 * (gridL he hef).v 1 - (gridL he hef).e0 1 * (gridL he hef).v 0) = 0 := by
    linear_combination (-((gridL he hef).e0 0)) * h1 + ((gridL he hef).v 0) * h2
  have p1 : w 1 * ((gridL he hef).e0 0 * (gridL he hef).v 1 - (gridL he hef).e0 1 * (gridL he hef).v 0) = 0 := by
    linear_combination ((gridL he hef).v 1) * h2 - ((gridL he hef).e0 1) * h1
  have w0 : w 0 = 0 := (mul_eq_zero.mp p0).resolve_right hκ
  have w1 : w 1 = 0 := (mul_eq_zero.mp p1).resolve_right hκ
  ext m
  fin_cases m
  · exact w0
  · exact w1

/-- **Instance of `wall_not_straddled` on a real dissection**: no chain edge on a horizontal line `{cross e0 · = d}`
passes through the interior of a point of the wall `x = 1`. -/
theorem grid_wall_not_straddled (d : ℝ) {x : Plane}
    (hx : crossL (gridL he hef).v x = cross (gridL he hef).v ((gridL he hef).pt 1 0)) :
    ¬ Straddled (gridD he hef k hk).toDissection (crossL (gridL he hef).e0) d x :=
  Erdos634.LaczWall.wall_not_straddled _ (crossL (gridL he hef).v) (crossL (gridL he hef).e0)
    (cross (gridL he hef).v ((gridL he hef).pt 1 0)) d hx (grid_trans he hef)
    (fun i _ => grid_wall_side he hef hk i)

/-- **Negative control.**  On the line `x = 1/2` of the grid (`k ≥ 2`) the hypothesis `hside` of
`wall_not_straddled` FAILS (a tile of column `0` has vertices strictly on both sides), and so does its conclusion:
the up cell `(0,1)` has a horizontal edge through `pt (1/2) 1`.  So `hside` cannot be dropped. -/
theorem grid_half_not_wall (hk2 : 2 ≤ k) :
    (∃ n : Fin (k * k),
        ¬ (((gridD he hef k hk).tile n).carrier ⊆
            {y | crossL (gridL he hef).v y ≤ cross (gridL he hef).v ((gridL he hef).pt (1 / 2) 0)}) ∧
        ¬ (((gridD he hef k hk).tile n).carrier ⊆
            {y | cross (gridL he hef).v ((gridL he hef).pt (1 / 2) 0) ≤ crossL (gridL he hef).v y})) ∧
    Straddled (gridD he hef k hk).toDissection (crossL (-(gridL he hef).e0))
      (cross (-(gridL he hef).e0) ((gridL he hef).pt 0 1)) ((gridL he hef).pt (1 / 2) 1) := by
  set L := gridL he hef with hL
  have hκ : 0 < cross L.e0 L.v := L.hcr
  constructor
  · obtain ⟨n, hn⟩ := gridDiss_tile_up ptA (gB e f) (gC e f) (gInd he hef) k hk (i := 0) (j := 0) (by omega)
    have hn' : (gridD he hef k hk).tile n = cellUp ptA (gB e f) (gC e f) (gInd he hef) 0 0 := hn
    obtain ⟨h0, h1, h2⟩ := tile_up_pts he hef hk hn'
    refine ⟨n, fun h => ?_, fun h => ?_⟩
    · have hm : ((gridD he hef k hk).tile n).pts 0 ∈ ((gridD he hef k hk).tile n).carrier :=
        subset_convexHull ℝ _ ⟨_, rfl⟩
      have := h hm
      simp only [Set.mem_setOf_eq] at this
      rw [h0, crossL_apply] at this
      simp only [Nat.cast_zero] at this
      rw [cross_v_pt, cross_v_pt] at this
      nlinarith
    · have hm : ((gridD he hef k hk).tile n).pts 1 ∈ ((gridD he hef k hk).tile n).carrier :=
        subset_convexHull ℝ _ ⟨_, rfl⟩
      have := h hm
      simp only [Set.mem_setOf_eq] at this
      rw [h1, crossL_apply] at this
      simp only [Nat.cast_zero] at this
      rw [cross_v_pt, cross_v_pt] at this
      nlinarith
  · obtain ⟨n, hn⟩ := gridDiss_tile_up ptA (gB e f) (gC e f) (gInd he hef) k hk (i := 0) (j := 1) (by omega)
    have hn' : (gridD he hef k hk).tile n = cellUp ptA (gB e f) (gC e f) (gInd he hef) 0 1 := hn
    obtain ⟨h0, h1, h2⟩ := tile_up_pts he hef hk hn'
    simp only [Nat.cast_zero, Nat.cast_one, zero_add] at h0 h1 h2
    have hch := upTile_mem_lineChain (gridD he hef k hk).toDissection L (n := n) (x := 0) (ρ := 1)
      (by simpa using h0) (by simpa using h1) (by simpa using h2)
    refine ⟨(n, 0), hch, ?_⟩
    have e0' : ((gridD he hef k hk).tile n).pts ((0 : Fin 3) + 1) = L.pt 1 1 := by
      have : (0 : Fin 3) + 1 = 1 := rfl
      rw [this]; simpa using h1
    have e00 : ((gridD he hef k hk).tile n).pts (0 : Fin 3) = L.pt 0 1 := by simpa using h0
    show L.pt (1 / 2) 1 ∈ openSegment ℝ (((gridD he hef k hk).tile n).pts 0)
      (((gridD he hef k hk).tile n).pts ((0 : Fin 3) + 1))
    rw [e0', e00]
    refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
    simp only [BLat.pt]
    module

end Ctl

end Erdos634.LaczMJ
