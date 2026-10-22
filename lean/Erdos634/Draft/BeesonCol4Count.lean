-- Draft/BeesonCol4Count.lean -- edge-level placement layer, part 3: COUNTING the tiles that touch a side of the target.
--   Walk lemmas: `walk_same_tail`, `walk_same_head` (two steps with the same tail / head are equal), `walk_pred` (every step not starting at `X` is preceded by a step ending at its tail),
--   `walk_head_param`, `walk_interior_count` (`n` steps have exactly `n - 1` interior vertices).
--   `interior_inbetween` : at an interior vertex `U` of the walk (a vertex in the open side, hence of type (3,1,0) or (1,1,1), >= 3 corners) there is a tile with a corner at `U`
--                          which is NOT a step tile ("in-between" tile).
--   `tiles_touching_side_ge` : for a walk with `n` steps along side `i`, at least `n + (n - 1) = 2n - 1` tiles touch the side (n step tiles + one in-between per interior vertex);
--                          for `n = 7` this is the printed "13 tiles touching AB" (Beeson, 1206.2229 v4, Lemma 40).
-- NOTE, UNAUDITED.  Credit: Beeson (arXiv 1206.2229 v4), Beeson-Rosu, Laczkovich (DCG 48 (2012), Sect. 4), Beeson-Zhang.  Formalization debt, not progress on the /goal outcomes.
import Erdos634.Draft.BeesonCol4Side

open scoped Classical
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ} [NeZero M]

theorem step_coeff {T : Tri} {d : V2} {U U' : Plane} (h : TriStep T d U U') :
    ∃ c : ℝ, 0 < c ∧ toV2 (U' - U) = (c * d.1, c * d.2) := by
  obtain ⟨-, -, -, -, -, -, -, -, hpar, -⟩ := id h
  exact hpar.smul

/-- Every step of a walk ends at `Y - u d` with `u >= 0`. -/
theorem walk_head_param {D : RegionDissection N} {d : V2} {X Y : Plane} {L : List (Fin N × Plane × Plane)}
    (W : WalkT D d X Y L) : ∀ e ∈ L, ∃ u : ℝ, 0 ≤ u ∧ toV2 (Y - e.2.2) = (u * d.1, u * d.2) := by
  induction W with
  | nil X => intro e he; exact absurd he (by simp)
  | @cons i X X' Y L hS W ih =>
    intro e he
    rcases List.mem_cons.mp he with rfl | h
    · obtain ⟨T, hT, hTe, -⟩ := walkT_progress W
      exact ⟨T, hT, hTe⟩
    · exact ih e h

/-- Two steps of a walk with the same tail are equal. -/
theorem walk_same_tail {D : RegionDissection N} {d : V2} {X Y : Plane} {L : List (Fin N × Plane × Plane)}
    (W : WalkT D d X Y L) {e e' : Fin N × Plane × Plane} (he : e ∈ L) (he' : e' ∈ L) (h : e.2.1 = e'.2.1) : e = e' := by
  have hS := walkT_mem_step W e he
  have hS' := walkT_mem_step W e' he'
  obtain ⟨c1, hc1, hcw1⟩ := step_coeff hS
  obtain ⟨c2, hc2, hcw2⟩ := step_coeff hS'
  have hii : e'.1 = e.1 := by
    refine overlap_eq D hS' hS hc1 hc2 (r := 0) le_rfl hc1 hcw1 hcw2 ?_
    rw [← h]; rw [vec_iff]; simp
  exact (List.inj_on_of_nodup_map (walk_tiles_nodup W) he he' hii.symm)

theorem overlap_same_head {D : RegionDissection N} {d : V2} {i j : Fin N} {A B U V : Plane}
    (hi : TriStep (D.tile i) d U V) (hj : TriStep (D.tile j) d A B) (hBV : B = V)
    {c1 c2 : ℝ} (hc1 : 0 < c1) (hc2 : 0 < c2) (hle : c2 ≤ c1)
    (hAB : toV2 (B - A) = (c1 * d.1, c1 * d.2)) (hUV : toV2 (V - U) = (c2 * d.1, c2 * d.2)) : i = j := by
  subst hBV
  refine overlap_eq D hi hj hc1 hc2 (r := c1 - c2) (by linarith) (by linarith) hAB hUV ?_
  rw [vec_iff] at hAB hUV ⊢
  constructor <;> linarith [hAB.1, hAB.2, hUV.1, hUV.2]

/-- Two steps of a walk with the same head are equal. -/
theorem walk_same_head {D : RegionDissection N} {d : V2} {X Y : Plane} {L : List (Fin N × Plane × Plane)}
    (W : WalkT D d X Y L) {e e' : Fin N × Plane × Plane} (he : e ∈ L) (he' : e' ∈ L) (h : e.2.2 = e'.2.2) : e = e' := by
  have hS := walkT_mem_step W e he
  have hS' := walkT_mem_step W e' he'
  obtain ⟨c1, hc1, hcw1⟩ := step_coeff hS
  obtain ⟨c2, hc2, hcw2⟩ := step_coeff hS'
  have hii : e'.1 = e.1 := by
    rcases le_total c2 c1 with hle | hle
    · exact overlap_same_head hS' hS h hc1 hc2 hle hcw1 hcw2
    · exact (overlap_same_head hS hS' h.symm hc2 hc1 hle hcw2 hcw1).symm
  exact (List.inj_on_of_nodup_map (walk_tiles_nodup W) he he' hii.symm)

/-- Every step either starts at `X` or is preceded by a step ending at its tail. -/
theorem walk_pred {D : RegionDissection N} {d : V2} {X Y : Plane} {L : List (Fin N × Plane × Plane)}
    (W : WalkT D d X Y L) : ∀ e ∈ L, e.2.1 = X ∨ ∃ e' ∈ L, e'.2.2 = e.2.1 := by
  induction W with
  | nil X => intro e he; exact absurd he (by simp)
  | @cons i X X' Y L hS W ih =>
    intro e he
    rcases List.mem_cons.mp he with rfl | h
    · exact Or.inl rfl
    · rcases ih e h with h1 | ⟨e', he', h2⟩
      · exact Or.inr ⟨(i, X, X'), List.mem_cons_self .., h1.symm⟩
      · exact Or.inr ⟨e', List.mem_cons_of_mem _ he', h2⟩

/-- The tail of a step is `X` only for the first step: `n` steps have `n - 1` interior vertices. -/
theorem walk_interior_count {D : RegionDissection N} {d : V2} {X Y : Plane} {L : List (Fin N × Plane × Plane)}
    (W : WalkT D d X Y L) (hL : L ≠ []) : (L.filter (fun e => e.2.1 ≠ X)).length + 1 = L.length := by
  cases W with
  | nil => exact absurd rfl hL
  | cons hS W' =>
    rename_i i X1 L'
    obtain ⟨c1, hc1, hcw1⟩ := step_coeff hS
    have hall : L'.filter (fun e => e.2.1 ≠ X) = L' := by
      rw [List.filter_eq_self]
      intro e he
      obtain ⟨t, ht, hte⟩ := walk_tail_param W' e he
      simp only [decide_eq_true_eq]
      intro heq
      rw [heq, vec_iff] at hte
      rw [vec_iff] at hcw1
      have hd : d ≠ 0 := by
        obtain ⟨-, -, -, -, -, -, -, -, hpar, -⟩ := id hS
        exact hpar.ne_right
      have h1 : (c1 + t) * d.1 = 0 := by linarith [hte.1, hcw1.1]
      have h2 : (c1 + t) * d.2 = 0 := by linarith [hte.2, hcw1.2]
      have hpos : c1 + t ≠ 0 := by positivity
      exact hd (Prod.ext ((mul_eq_zero.mp h1).resolve_left hpos) ((mul_eq_zero.mp h2).resolve_left hpos))
    simp only [List.filter_cons, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, if_false, List.length_cons]
    rw [hall]

/-- The vertex-type input of the counting: every tiling vertex lying on a side of the polygon and not a polygon vertex carries at least three tile corners
(from the angle sum `pi` and the angles of the tile: `bdy_corn_ge_three` for `(alpha, beta, 2 alpha)`, `bdy_corn_ge_three_pairs` for any tile with no two angles summing to `pi`). -/
def BdyGe3 (D : CongruentRegionDissection N) (P : ConvPoly M) : Prop :=
  ∀ X : Plane, (∃ j k, (D.tile j).pts k = X) → (∃ s : Fin M, P.c s X = 0) → (∀ m : Fin M, X ≠ P.v m) →
    3 ≤ (Corn D.toRegionDissection X).card

theorem crs_diff_of_c_zero (P : ConvPoly M) (i : Fin M) {U V : Plane} (hU : P.c i U = 0) (hV : P.c i V = 0) :
    crs (toV2 (P.e i)) (toV2 (U - V)) = 0 := by
  have e1 : P.c i U = crs (toV2 (P.e i)) (toV2 (U - P.v i)) := rfl
  have e2 : P.c i V = crs (toV2 (P.e i)) (toV2 (V - P.v i)) := rfl
  rw [e1] at hU; rw [e2] at hV
  unfold crs at hU hV ⊢
  simp only [toV2_sub] at hU hV ⊢
  linear_combination hU - hV

/-- The tail of every step of the walk along side `i` lies on the line of the side. -/
theorem walk_c_zero (D : CongruentRegionDissection N) (P : ConvPoly M) (i : Fin M)
    {L : List (Fin N × Plane × Plane)} (W : WalkT D.toRegionDissection (toV2 (P.e i)) (P.v i) (P.v (i + 1)) L)
    {e : Fin N × Plane × Plane} (he : e ∈ L) : P.c i e.2.1 = 0 := by
  obtain ⟨t, -, hte⟩ := walk_tail_param W e he
  have e1 : P.c i e.2.1 = crs (toV2 (P.e i)) (toV2 (e.2.1 - P.v i)) := rfl
  rw [e1, hte]; unfold crs; ring

/-- An interior vertex of the walk (the tail of a step other than the first) lies in the open side and is not a polygon vertex. -/
theorem interior_entry_facts (D : CongruentRegionDissection N) (P : ConvPoly M) (hreg : D.region = P.carrier) (i : Fin M)
    {L : List (Fin N × Plane × Plane)} (W : WalkT D.toRegionDissection (toV2 (P.e i)) (P.v i) (P.v (i + 1)) L)
    {e : Fin N × Plane × Plane} (he : e ∈ L) (hX : e.2.1 ≠ P.v i) :
    (∃ j k, (D.tile j).pts k = e.2.1) ∧ P.c i e.2.1 = 0 ∧ ∀ m : Fin M, e.2.1 ≠ P.v m := by
  have hS := walkT_mem_step W e he
  have hvert : ∃ j k, (D.tile j).pts k = e.2.1 := by
    obtain ⟨kk, -, -, hk, -⟩ := hS
    exact ⟨e.1, kk, hk⟩
  have hc0 := walk_c_zero D P i W he
  refine ⟨hvert, hc0, ?_⟩
  have hd : toV2 (P.e i) ≠ 0 := toV2_ne_zero (P.e_ne_zero P.three_le i)
  obtain ⟨t, ht, hUt⟩ := vertex_on_edge D.toRegionDissection P hreg i hvert hc0
  have ht0 : 0 < t := by
    rcases ht.1.eq_or_lt with h0 | h0
    · exfalso; apply hX; rw [hUt, ← h0]; simp
    · exact h0
  -- the end of the step is beyond the tail, and the walk ends at Y
  obtain ⟨u, hu, hue⟩ := walk_head_param W e he
  obtain ⟨c, hc, hcw⟩ := step_coeff hS
  have ht1 : t < 1 := by
    rcases ht.2.eq_or_lt with h1 | h1
    · exfalso
      have hUY : e.2.1 = P.v (i + 1) := by rw [hUt, h1]; simp
      rw [hUY] at hcw
      rw [vec_iff] at hcw hue
      have h1' : (c + u) * (toV2 (P.e i)).1 = 0 := by linarith [hcw.1, hue.1]
      have h2' : (c + u) * (toV2 (P.e i)).2 = 0 := by linarith [hcw.2, hue.2]
      have hpos : c + u ≠ 0 := by positivity
      exact hd (Prod.ext ((mul_eq_zero.mp h1').resolve_left hpos) ((mul_eq_zero.mp h2').resolve_left hpos))
    · exact h1
  intro m
  rw [hUt]
  exact open_edge_not_vertex P ht0 ht1 m

/-- **An in-between tile.**  At an interior vertex `U` of the walk along side `i` there is a tile with a corner at `U` that is not a step tile of the walk. -/
theorem interior_inbetween (D : CongruentRegionDissection N) (P : ConvPoly M) (hreg : D.region = P.carrier)
    (h3 : BdyGe3 D P) (i : Fin M)
    {L : List (Fin N × Plane × Plane)} (W : WalkT D.toRegionDissection (toV2 (P.e i)) (P.v i) (P.v (i + 1)) L)
    {e : Fin N × Plane × Plane} (he : e ∈ L) (hX : e.2.1 ≠ P.v i) :
    ∃ q : Fin N, (∃ k, (D.tile q).pts k = e.2.1) ∧ ¬ ∃ g ∈ L, g.1 = q := by
  obtain ⟨hvert, hc0, hXP⟩ := interior_entry_facts D P hreg i W he hX
  have h3' := h3 _ hvert ⟨i, hc0⟩ hXP
  obtain ⟨e', he', hhead⟩ : ∃ e' ∈ L, e'.2.2 = e.2.1 := by
    rcases walk_pred W e he with h | h
    · exact absurd h hX
    · exact h
  by_contra H
  push Not at H
  have hsub : Corn D.toRegionDissection e.2.1 ⊆ {e.1, e'.1} := by
    intro q hq
    unfold Corn at hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
    obtain ⟨g, hg, hgq⟩ := H q hq
    obtain ⟨k, hk⟩ := hq
    have hS := walkT_mem_step W g hg
    obtain ⟨kk, f, g3, hkk, hf, hfk, hgk, hgf, hpar, hleft⟩ := hS
    rw [← hgq] at hk
    have f3 : ∀ k kk f g3 : Fin 3, f ≠ kk → g3 ≠ kk → g3 ≠ f → k = kk ∨ k = f ∨ k = g3 := by decide
    rcases f3 k kk f g3 hfk hgk hgf with h | h | h
    · rw [h] at hk
      have : g.2.1 = e.2.1 := hkk.symm.trans hk
      have := walk_same_tail W hg he this
      rw [Finset.mem_insert]; left; rw [← hgq, this]
    · rw [h] at hk
      have : g.2.2 = e'.2.2 := (hf.symm.trans hk).trans hhead.symm
      have := walk_same_head W hg he' this
      rw [Finset.mem_insert, Finset.mem_singleton]; right; rw [← hgq, this]
    · exfalso
      rw [h] at hk
      have hcg3 : P.c i ((D.tile g.1).pts g3) = 0 := by rw [hk]; exact hc0
      have h0 := crs_diff_of_c_zero P i hcg3 (walk_c_zero D P i W hg)
      linarith
  have hcard : (Corn D.toRegionDissection e.2.1).card ≤ 2 :=
    (Finset.card_le_card hsub).trans (Finset.card_le_two)
  omega

/-- **Tiles touching a side.**  For the walk `L` along side `i` (the tiles with an edge on the side), the tiles that either have an edge on the side or have a corner at an interior vertex of the walk
number at least `|L| + (number of interior vertices)`: one in-between tile per interior vertex, distinct from each other and from the step tiles. -/
theorem tiles_touching_side_ge (D : CongruentRegionDissection N) (P : ConvPoly M) (hreg : D.region = P.carrier)
    (h3 : BdyGe3 D P) (i : Fin M)
    {L : List (Fin N × Plane × Plane)} (W : WalkT D.toRegionDissection (toV2 (P.e i)) (P.v i) (P.v (i + 1)) L) :
    L.length + (L.filter (fun e => e.2.1 ≠ P.v i)).length ≤
      (Finset.univ.filter (fun q : Fin N => (∃ e ∈ L, e.1 = q) ∨
        ∃ e ∈ L, e.2.1 ≠ P.v i ∧ ∃ k, (D.tile q).pts k = e.2.1)).card := by
  by_cases hL : L = []
  · subst hL; simp
  obtain ⟨e0, he0⟩ := List.exists_mem_of_ne_nil L hL
  haveI : Nonempty (Fin N) := ⟨e0.1⟩
  have hex : ∀ e : Fin N × Plane × Plane, ∃ q : Fin N, e ∈ L → e.2.1 ≠ P.v i →
      (∃ k, (D.tile q).pts k = e.2.1) ∧ ¬ ∃ g ∈ L, g.1 = q := by
    intro e
    by_cases h : e ∈ L ∧ e.2.1 ≠ P.v i
    · obtain ⟨q, hq⟩ := interior_inbetween D P hreg h3 i W h.1 h.2
      exact ⟨q, fun _ _ => hq⟩
    · exact ⟨e0.1, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  choose f hf using hex
  set Lint := L.filter (fun e => e.2.1 ≠ P.v i) with hLint
  have hmemInt : ∀ e ∈ Lint, e ∈ L ∧ e.2.1 ≠ P.v i := by
    intro e he; simpa [hLint, List.mem_filter] using he
  have hnodupL : L.Nodup := List.Nodup.of_map _ (walk_tiles_nodup W)
  have hnodupInt : Lint.Nodup := hnodupL.filter _
  set S : Finset (Fin N) := (L.map fun e => e.1).toFinset with hS
  set B : Finset (Fin N) := Lint.toFinset.image f with hB
  have hcS : S.card = L.length := by
    rw [hS, List.toFinset_card_of_nodup (walk_tiles_nodup W), List.length_map]
  have hdisj : Disjoint S B := by
    rw [Finset.disjoint_left]
    intro q hqS hqB
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hqB
    obtain ⟨he1, he2⟩ := hmemInt e (List.mem_toFinset.mp he)
    obtain ⟨-, hnot⟩ := hf e he1 he2
    apply hnot
    simp only [hS, List.mem_toFinset, List.mem_map] at hqS
    exact hqS
  have hinj : Set.InjOn f (Lint.toFinset : Set (Fin N × Plane × Plane)) := by
    intro e1 h1 e2 h2 heq
    simp only [Finset.mem_coe, List.mem_toFinset] at h1 h2
    obtain ⟨he1L, he1X⟩ := hmemInt e1 h1
    obtain ⟨he2L, he2X⟩ := hmemInt e2 h2
    by_contra hne
    have hU : e1.2.1 ≠ e2.2.1 := fun h => hne (walk_same_tail W he1L he2L h)
    obtain ⟨⟨k1, hk1⟩, -⟩ := hf e1 he1L he1X
    obtain ⟨⟨k2, hk2⟩, hnot⟩ := hf e2 he2L he2X
    rw [← heq] at hk2
    apply (hf e1 he1L he1X).2
    have hkne : k1 ≠ k2 := by
      intro h; apply hU; rw [← hk1, ← hk2, h]
    exact side_corner_tile_in_walk D P hreg i W hkne (hk1 ▸ walk_c_zero D P i W he1L) (hk2 ▸ walk_c_zero D P i W he2L)
  have hcB : B.card = Lint.length := by
    rw [hB, Finset.card_image_of_injOn hinj, List.toFinset_card_of_nodup hnodupInt]
  have hsub : S ∪ B ⊆ Finset.univ.filter (fun q : Fin N => (∃ e ∈ L, e.1 = q) ∨
        ∃ e ∈ L, e.2.1 ≠ P.v i ∧ ∃ k, (D.tile q).pts k = e.2.1) := by
    intro q hq
    simp only [Finset.mem_union] at hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hq with hq | hq
    · left
      simpa [hS, List.mem_toFinset, List.mem_map] using hq
    · right
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hq
      obtain ⟨he1, he2⟩ := hmemInt e (List.mem_toFinset.mp he)
      exact ⟨e, he1, he2, (hf e he1 he2).1⟩
  calc L.length + Lint.length = (S ∪ B).card := by rw [Finset.card_union_of_disjoint hdisj, hcS, hcB]
    _ ≤ _ := Finset.card_le_card hsub

/-- **`2n - 1` tiles touch the side**: `n` step tiles and `n - 1` in-between tiles; for `n = 7` this is the printed "13 tiles touching AB" (Beeson 1206.2229 v4, Lemma 40). -/
theorem tiles_touching_side_ge_two_n (D : CongruentRegionDissection N) (P : ConvPoly M) (hreg : D.region = P.carrier)
    (h3 : BdyGe3 D P) (i : Fin M)
    {L : List (Fin N × Plane × Plane)} (W : WalkT D.toRegionDissection (toV2 (P.e i)) (P.v i) (P.v (i + 1)) L) (hL : L ≠ []) :
    2 * L.length - 1 ≤
      (Finset.univ.filter (fun q : Fin N => (∃ e ∈ L, e.1 = q) ∨
        ∃ e ∈ L, e.2.1 ≠ P.v i ∧ ∃ k, (D.tile q).pts k = e.2.1)).card := by
  have h1 := tiles_touching_side_ge D P hreg h3 i W
  have h2 := walk_interior_count W hL
  omega

/-- The printed count: a side divided into 7 tile edges is touched by at least 13 tiles. -/
theorem seven_edges_thirteen_tiles (D : CongruentRegionDissection N) (P : ConvPoly M) (hreg : D.region = P.carrier)
    (h3 : BdyGe3 D P) (i : Fin M)
    {L : List (Fin N × Plane × Plane)} (W : WalkT D.toRegionDissection (toV2 (P.e i)) (P.v i) (P.v (i + 1)) L) (h7 : L.length = 7) :
    13 ≤ (Finset.univ.filter (fun q : Fin N => (∃ e ∈ L, e.1 = q) ∨
        ∃ e ∈ L, e.2.1 ≠ P.v i ∧ ∃ k, (D.tile q).pts k = e.2.1)).card := by
  have hL : L ≠ [] := by intro h; rw [h] at h7; simp at h7
  have := tiles_touching_side_ge_two_n D P hreg h3 i W hL
  omega

/-- Existence form (the walk exists for every side, `side_walk_exists_poly`): some walk along side `i` has at least `2n - 1` touching tiles, `n` its number of steps. -/
theorem exists_walk_touching_ge (D : CongruentRegionDissection N) (P : ConvPoly M) (hreg : D.region = P.carrier)
    (h3 : BdyGe3 D P) (i : Fin M) :
    ∃ L : List (Fin N × Plane × Plane), WalkT D.toRegionDissection (toV2 (P.e i)) (P.v i) (P.v (i + 1)) L ∧ L ≠ [] ∧ 2 * L.length - 1 ≤
      (Finset.univ.filter (fun q : Fin N => (∃ e ∈ L, e.1 = q) ∨
        ∃ e ∈ L, e.2.1 ≠ P.v i ∧ ∃ k, (D.tile q).pts k = e.2.1)).card := by
  obtain ⟨L, W⟩ := side_walk_exists_poly D.toRegionDissection P hreg i
  have hL : L ≠ [] := by
    intro hL0
    subst hL0
    have h := walkT_dist_sum W
    simp only [List.map_nil, List.sum_nil] at h
    have h0 : P.v i = P.v (i + 1) := dist_eq_zero.mp h.symm
    exact P.e_ne_zero P.three_le i (by unfold ConvPoly.e; rw [← h0]; simp)
  exact ⟨L, W, hL, tiles_touching_side_ge_two_n D P hreg h3 i W hL⟩

/-- `BdyGe3` for any tile with no two angles summing to `pi` (in particular Beeson's `3 alpha + 2 beta = pi` tile, `pairs_of_3a2b`). -/
theorem bdyGe3_of_pairs (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v)
    (hlt : ∀ a : Fin 3, D.model.angleAt a < Real.pi) (hpair : ∀ a b : Fin 3, D.model.angleAt a + D.model.angleAt b ≠ Real.pi) : BdyGe3 D P := by
  intro X hv ⟨s, hs⟩ hXP
  exact bdy_corn_ge_three_pairs D P hreg idx hidxA hlt hpair hv hs hXP

/-- `BdyGe3` for an `(alpha, beta, 2 alpha)`-tile, `beta = pi - 3 alpha`, `alpha` not a rational multiple of `pi`. -/
theorem bdyGe3_of_abg (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v)
    (hβ : D.model.angleAt 1 = Real.pi - 3 * D.model.angleAt 0) (hγ : D.model.angleAt 2 = 2 * D.model.angleAt 0)
    (hα : ¬ ∃ r : ℚ, D.model.angleAt 0 = (r : ℝ) * Real.pi) : BdyGe3 D P := by
  intro X hv ⟨s, hs⟩ hXP
  exact bdy_corn_ge_three D P hreg idx hidxA hβ hγ hα hv hs hXP

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.tiles_touching_side_ge
#print axioms Erdos634.Draft.LaczFormal.RG.seven_edges_thirteen_tiles
#print axioms Erdos634.Draft.LaczFormal.RG.exists_walk_touching_ge
