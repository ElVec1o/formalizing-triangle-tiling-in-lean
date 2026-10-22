-- Draft/BeesonCol4Side.lean -- edge-level placement layer, part 2 (a side of a convex polygon; vertex types on the side).
--   `open_edge_not_vertex`  : a point of an open polygon edge is not a polygon vertex;
--   `tile_step_of_side`     : a tile with two corners on the line of side `i` has a left step along the side (the tile lies inside the polygon);
--   `side_corner_tile_in_walk` : such a tile IS a step tile of the walk along the side (completeness: "tiles with an edge on AB");
--   `tjunction_Asum`        : (edge ends inside another tile's edge) the corner angles at a vertex lying in the relative interior of another tile's side sum to pi;
--   `bdy_corn_ge_three`     : (alpha,beta,2alpha)-tiling: a non-corner vertex in the open side carries >= 3 tile corners (types (3,1,0), (1,1,1)).
-- Reusable for Beeson (arXiv 1206.2229 v4) Lemma 31 Cases 1a-2 and Lemma 40.  NOTE, UNAUDITED.
-- Credit: Beeson (arXiv 1206.2229 v4), Beeson-Rosu, Laczkovich (DCG 48 (2012), Sect. 4), Beeson-Zhang.  Formalization debt, not progress on the /goal outcomes.
import Erdos634.Draft.BeesonCol4Walk
import Erdos634.Draft.LaczFormalBZL7f2

open scoped Classical
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ} [NeZero M]

/-- A point of an open polygon edge is not a vertex of the polygon (strict convexity). -/
theorem open_edge_not_vertex (P : ConvPoly M) {i : Fin M} {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (m : Fin M) :
    (1 - t) • P.v i + t • P.v (i + 1) ≠ P.v m := by
  intro h
  have h1 : P.c m (P.v m) = 0 := P.c_self m
  have h2 : P.c (m - 1) (P.v m) = 0 := P.c_prev_next P.three_le m
  rw [← h] at h1 h2
  have hpos : ∀ j, j ≠ i → 0 < P.c j ((1 - t) • P.v i + t • P.v (i + 1)) := fun j hj =>
    P.c_edge_pos P.three_le i ⟨ht0.le, ht1.le⟩ hj (fun _ => ht1) (fun _ => ht0)
  have hm : m = i := by by_contra hne; exact (hpos m hne).ne' h1
  have hm1 : m - 1 = i := by by_contra hne; exact (hpos _ hne).ne' h2
  obtain ⟨hf1, -, -, -, hf5, -⟩ := ConvPoly.fin_facts P.three_le m
  have hmm : m - 1 = m := hm1.trans hm.symm
  rw [hmm] at hf5
  exact hf1 hf5

theorem tri_crs_ne (T : Tri) {a b g : Fin 3} (hab : b ≠ a) (hga : g ≠ a) (hgb : g ≠ b) :
    crs (toV2 (T.pts b - T.pts a)) (toV2 (T.pts g - T.pts a)) ≠ 0 := by
  have hdet := T.det_ne_zero
  unfold Tri.det at hdet
  simp only [PiLp.sub_apply] at hdet
  unfold crs
  rw [toV2_sub, toV2_sub]
  simp only [PiLp.sub_apply]
  intro h
  apply hdet
  revert hab hga hgb h
  fin_cases a <;> fin_cases b <;> fin_cases g <;> simp <;> intro h <;>
    first | linear_combination h | linear_combination -h

/-- A tile with a corner `a` on the line of side `i`, whose edge `a -> b` is a positive multiple of the side direction, has a left step along the side. -/
theorem tile_step_of_side (D : CongruentRegionDissection N) (P : ConvPoly M) (hreg : D.region = P.carrier) (i : Fin M)
    (q : Fin N) {a b g : Fin 3} (hab : b ≠ a) (hga : g ≠ a) (hgb : g ≠ b)
    (ha : P.c i ((D.tile q).pts a) = 0) {c : ℝ} (hc : 0 < c)
    (hv : toV2 ((D.tile q).pts b - (D.tile q).pts a) = (c * (toV2 (P.e i)).1, c * (toV2 (P.e i)).2)) :
    TriStep (D.tile q) (toV2 (P.e i)) ((D.tile q).pts a) ((D.tile q).pts b) := by
  have hd : toV2 (P.e i) ≠ 0 := toV2_ne_zero (P.e_ne_zero P.three_le i)
  have hg : (D.tile q).pts g ∈ P.carrier := by
    rw [← hreg, ← D.covers]; exact Set.mem_iUnion.mpr ⟨q, subset_convexHull ℝ _ ⟨g, rfl⟩⟩
  have hcg : 0 ≤ P.c i ((D.tile q).pts g) := (P.mem_carrier_iff _).1 hg i
  have hcrs : crs (toV2 (P.e i)) (toV2 ((D.tile q).pts g - (D.tile q).pts a)) = P.c i ((D.tile q).pts g) := by
    have e1 : P.c i ((D.tile q).pts g) = crs (toV2 (P.e i)) (toV2 ((D.tile q).pts g - P.v i)) := rfl
    have e2 : P.c i ((D.tile q).pts a) = crs (toV2 (P.e i)) (toV2 ((D.tile q).pts a - P.v i)) := rfl
    rw [e2] at ha
    rw [e1]
    unfold crs at ha ⊢
    simp only [toV2_sub] at ha ⊢
    linear_combination (-1 : ℝ) * ha
  have hne := tri_crs_ne (D.tile q) hab hga hgb
  have hne' : crs (toV2 (P.e i)) (toV2 ((D.tile q).pts g - (D.tile q).pts a)) ≠ 0 := by
    intro h0
    apply hne
    rw [hv]
    unfold crs at h0 ⊢
    linear_combination c * h0
  have hpos : 0 < crs (toV2 (P.e i)) (toV2 ((D.tile q).pts g - (D.tile q).pts a)) := by
    rw [hcrs] at hne' ⊢
    exact lt_of_le_of_ne hcg (Ne.symm hne')
  exact ⟨a, b, g, rfl, rfl, hab, hga, hgb, smul_par hc hd hv, hpos⟩

/-- Coordinates of a tiling vertex on side `i`: `U = v_i + t d`, `v_{i+1} = U + (1-t) d`, `0 <= t <= 1`, `d = toV2 (e_i)`. -/
theorem side_param (D : RegionDissection N) (P : ConvPoly M) (hreg : D.region = P.carrier) (i : Fin M) {U : Plane}
    (hU : ∃ j k, (D.tile j).pts k = U) (h : P.c i U = 0) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ toV2 (U - P.v i) = (t * (toV2 (P.e i)).1, t * (toV2 (P.e i)).2) ∧
      toV2 (P.v (i + 1) - U) = ((1 - t) * (toV2 (P.e i)).1, (1 - t) * (toV2 (P.e i)).2) := by
  obtain ⟨t, ht, hUt⟩ := vertex_on_edge D P hreg i hU h
  refine ⟨t, ht.1, ht.2, ?_, ?_⟩
  · rw [vec_iff]
    subst hUt
    simp only [toV2, ConvPoly.e, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
    constructor <;> ring
  · rw [vec_iff]
    subst hUt
    simp only [toV2, ConvPoly.e, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
    constructor <;> ring

/-- Ordered case of `side_corner_tile_in_walk`. -/
theorem side_pair_in_walk (D : CongruentRegionDissection N) (P : ConvPoly M) (hreg : D.region = P.carrier) (i : Fin M)
    {L : List (Fin N × Plane × Plane)} (W : WalkT D.toRegionDissection (toV2 (P.e i)) (P.v i) (P.v (i + 1)) L)
    {q : Fin N} {k1 k2 : Fin 3} (hne : k1 ≠ k2) (h1 : P.c i ((D.tile q).pts k1) = 0) (h2 : P.c i ((D.tile q).pts k2) = 0)
    {t1 t2 : ℝ} (ht1 : 0 ≤ t1) (ht12 : t1 < t2) (ht2 : t2 ≤ 1)
    (hU1 : toV2 ((D.tile q).pts k1 - P.v i) = (t1 * (toV2 (P.e i)).1, t1 * (toV2 (P.e i)).2))
    (hU2 : toV2 ((D.tile q).pts k2 - P.v i) = (t2 * (toV2 (P.e i)).1, t2 * (toV2 (P.e i)).2))
    (hY2 : toV2 (P.v (i + 1) - (D.tile q).pts k2) = ((1 - t2) * (toV2 (P.e i)).1, (1 - t2) * (toV2 (P.e i)).2)) :
    ∃ e ∈ L, e.1 = q := by
  have hd : toV2 (P.e i) ≠ 0 := toV2_ne_zero (P.e_ne_zero P.three_le i)
  have hfin : ∀ a b : Fin 3, a ≠ b → ∃ g : Fin 3, g ≠ a ∧ g ≠ b := by decide
  obtain ⟨g, hg1, hg2⟩ := hfin k1 k2 hne
  have hv : toV2 ((D.tile q).pts k2 - (D.tile q).pts k1) = ((t2 - t1) * (toV2 (P.e i)).1, (t2 - t1) * (toV2 (P.e i)).2) := by
    rw [vec_iff] at hU1 hU2 ⊢
    constructor <;> linarith [hU1.1, hU1.2, hU2.1, hU2.2]
  have hstep := tile_step_of_side D P hreg i q (a := k1) (b := k2) (g := g) (Ne.symm hne) hg1 hg2 h1 (by linarith) hv
  have hmem := walk_complete W hstep (s := t1) (c := t2 - t1) (u := 1 - t2) hd ht1 (by linarith) (by linarith) hU1 hv hY2
  exact ⟨_, hmem, rfl⟩

/-- **A tile with two corners on the line of side `i` is a step tile of the walk along the side.** -/
theorem side_corner_tile_in_walk (D : CongruentRegionDissection N) (P : ConvPoly M) (hreg : D.region = P.carrier) (i : Fin M)
    {L : List (Fin N × Plane × Plane)} (W : WalkT D.toRegionDissection (toV2 (P.e i)) (P.v i) (P.v (i + 1)) L)
    {q : Fin N} {k1 k2 : Fin 3} (hne : k1 ≠ k2) (h1 : P.c i ((D.tile q).pts k1) = 0) (h2 : P.c i ((D.tile q).pts k2) = 0) :
    ∃ e ∈ L, e.1 = q := by
  obtain ⟨t1, ht1, ht1', hU1, hY1⟩ := side_param D.toRegionDissection P hreg i ⟨q, k1, rfl⟩ h1
  obtain ⟨t2, ht2, ht2', hU2, hY2⟩ := side_param D.toRegionDissection P hreg i ⟨q, k2, rfl⟩ h2
  rcases lt_trichotomy t1 t2 with h | h | h
  · exact side_pair_in_walk D P hreg i W hne h1 h2 ht1 h ht2' hU1 hU2 hY2
  · exfalso
    subst h
    apply (D.tile q).indep.injective.ne hne
    rw [vec_iff] at hU1 hU2
    have c0 : ((D.tile q).pts k1) 0 = ((D.tile q).pts k2) 0 := by linarith [hU1.1, hU2.1]
    have c1 : ((D.tile q).pts k1) 1 = ((D.tile q).pts k2) 1 := by linarith [hU1.2, hU2.2]
    ext k; fin_cases k
    · exact c0
    · exact c1
  · exact side_pair_in_walk D P hreg i W (Ne.symm hne) h2 h1 ht2 h ht1' hU2 hU1 hY1

/-- **Edge ends inside another tile's edge (T-junction).**  If `X` is a tiling vertex lying on tile `q` but not a corner of `q`, and not a polygon vertex,
the corner angles of the tiles with a corner at `X` sum to exactly `pi`. -/
theorem tjunction_Asum (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v)
    {X : Plane} (hvert : ∃ j k, (D.tile j).pts k = X) {q : Fin N} (hq : X ∈ (D.tile q).carrier) (hqv : ∀ k, (D.tile q).pts k ≠ X)
    (hXP : ∀ m : Fin M, X ≠ P.v m) : Asum D idx X = Real.pi := by
  have hpi := Real.pi_pos
  have hA := Asum_pos D idx hvert
  have hqS : q ∈ Strn D.toRegionDissection X := by
    unfold Strn; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨hq, hqv⟩
  have hc1 : (1 : ℝ) ≤ (Strn D.toRegionDissection X).card := by exact_mod_cast Finset.card_pos.mpr ⟨q, hqS⟩
  by_cases hint : X ∈ interior D.region
  · obtain ⟨F⟩ := extFan_interior D.toRegionDissection X hvert hint
    have hang := head_angle_sum D idx hidxA F inferInstance
    have hAe : Asum D idx X + Real.pi * ((Strn D.toRegionDissection X).card : ℝ) = 2 * Real.pi := hang
    rcases Nat.lt_or_ge (Strn D.toRegionDissection X).card 2 with hlt | hge
    · have : (Strn D.toRegionDissection X).card = 1 := by
        have := Finset.card_pos.mpr ⟨q, hqS⟩; omega
      rw [this] at hAe; simp at hAe; linarith
    · exfalso
      have : (2 : ℝ) ≤ (Strn D.toRegionDissection X).card := by exact_mod_cast hge
      nlinarith
  · rcases vertex_A D P hreg idx hidxA hvert with ⟨h, -⟩ | ⟨-, h | ⟨k, hk, -⟩⟩
    · exact absurd h hint
    · exact h
    · exact absurd hk (hXP _)

/-- **Boundary vertex types.**  In an `(alpha, beta, 2 alpha)`-tiling with `alpha` not a rational multiple of `pi`, a tiling vertex in the open side `i` (not a polygon vertex)
carries counts `(3,1,0)` or `(1,1,1)`, in particular at least three tile corners. -/
theorem bdy_corn_ge_three (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v)
    (hβ : D.model.angleAt 1 = Real.pi - 3 * D.model.angleAt 0) (hγ : D.model.angleAt 2 = 2 * D.model.angleAt 0)
    (hα : ¬ ∃ r : ℚ, D.model.angleAt 0 = (r : ℝ) * Real.pi)
    {X : Plane} (hvert : ∃ j k, (D.tile j).pts k = X) {i : Fin M} (hline : P.c i X = 0) (hXP : ∀ m : Fin M, X ≠ P.v m) :
    3 ≤ (Corn D.toRegionDissection X).card := by
  have hnint : X ∉ interior D.region := by rw [hreg]; exact not_interior_of_c_zero P hline
  have hAπ : Asum D idx X = Real.pi := by
    rcases vertex_A D P hreg idx hidxA hvert with ⟨h, -⟩ | ⟨-, h | ⟨k, hk, -⟩⟩
    · exact absurd h hnint
    · exact h
    · exact absurd hk (hXP _)
  have hAexp : (cnt D idx X 0 : ℝ) * D.model.angleAt 0 + (cnt D idx X 1 : ℝ) * D.model.angleAt 1
      + (cnt D idx X 2 : ℝ) * (2 * D.model.angleAt 0) = Real.pi := by
    rw [← hγ, ← hAπ]; unfold Asum; rw [Fin.sum_univ_three]
  have := boundary_vtype hβ hα _ _ _ hAexp
  rw [card_corn D idx X, Fin.sum_univ_three]
  omega

/-- **Boundary vertex types for any tile with no two angles summing to `pi`.**  A tiling vertex in the open side (not a polygon vertex) carries at least three tile corners:
its corner angles sum to `pi` (`vertex_A`), and one or two corners would give a single angle `= pi` or two angles summing to `pi`.  For the tile of Beeson's `3 alpha + 2 beta = pi`
case (angles `alpha, beta, 2 alpha + beta`, `alpha, beta > 0`) the two hypotheses hold: see `pairs_of_3a2b`. -/
theorem bdy_corn_ge_three_pairs (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v)
    (hlt : ∀ a : Fin 3, D.model.angleAt a < Real.pi) (hpair : ∀ a b : Fin 3, D.model.angleAt a + D.model.angleAt b ≠ Real.pi)
    {X : Plane} (hvert : ∃ j k, (D.tile j).pts k = X) {i : Fin M} (hline : P.c i X = 0) (hXP : ∀ m : Fin M, X ≠ P.v m) :
    3 ≤ (Corn D.toRegionDissection X).card := by
  have hnint : X ∉ interior D.region := by rw [hreg]; exact not_interior_of_c_zero P hline
  have hAπ : Asum D idx X = Real.pi := by
    rcases vertex_A D P hreg idx hidxA hvert with ⟨h, -⟩ | ⟨-, h | ⟨k, hk, -⟩⟩
    · exact absurd h hnint
    · exact h
    · exact absurd hk (hXP _)
  rw [card_corn D idx X, Fin.sum_univ_three]
  unfold Asum at hAπ
  rw [Fin.sum_univ_three] at hAπ
  by_contra hlt3
  push Not at hlt3
  have hpi := Real.pi_pos
  have h0 := hlt 0
  have h1 := hlt 1
  have h2 := hlt 2
  generalize cnt D idx X 0 = c0 at hAπ hlt3
  generalize cnt D idx X 1 = c1 at hAπ hlt3
  generalize cnt D idx X 2 = c2 at hAπ hlt3
  have hc0 : c0 ≤ 2 := by omega
  have hc1 : c1 ≤ 2 := by omega
  have hc2 : c2 ≤ 2 := by omega
  interval_cases c0 <;> interval_cases c1 <;> interval_cases c2 <;>
  first
  | omega
  | (norm_num at hAπ
     first
     | linarith
     | exact hpair 0 0 (by linarith) | exact hpair 0 1 (by linarith) | exact hpair 0 2 (by linarith)
     | exact hpair 1 1 (by linarith) | exact hpair 1 2 (by linarith) | exact hpair 2 2 (by linarith))

/-- The angles of Beeson's tile with `3 alpha + 2 beta = pi`: `alpha`, `beta`, `gamma = 2 alpha + beta`, all positive, are each `< pi` and no two sum to `pi`. -/
theorem pairs_of_3a2b {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : c = 2 * a + b) (h : 3 * a + 2 * b = Real.pi)
    (f : Fin 3 → ℝ) (hf0 : f 0 = a) (hf1 : f 1 = b) (hf2 : f 2 = c) :
    (∀ x : Fin 3, f x < Real.pi) ∧ (∀ x y : Fin 3, f x + f y ≠ Real.pi) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  refine ⟨?_, ?_⟩
  · intro x; fin_cases x <;> simp [hf0, hf1, hf2, hc] <;> linarith
  · intro x y; fin_cases x <;> fin_cases y <;> simp [hf0, hf1, hf2, hc] <;> intro hh <;> linarith

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.side_corner_tile_in_walk
#print axioms Erdos634.Draft.LaczFormal.RG.tjunction_Asum
#print axioms Erdos634.Draft.LaczFormal.RG.bdy_corn_ge_three
#print axioms Erdos634.Draft.LaczFormal.RG.open_edge_not_vertex
#print axioms Erdos634.Draft.LaczFormal.RG.bdy_corn_ge_three_pairs
#print axioms Erdos634.Draft.LaczFormal.RG.pairs_of_3a2b
