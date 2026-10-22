-- Draft/BeesonIso2b.lean -- Beeson, "Tilings of an isosceles triangle" (arXiv 1206.1974v7), Lemma 11.13: every side has a c edge (r >= 1, already `side_has_c_step`) and the BASE has a b edge (q >= 1).
--   `walk_l_step`       : `walk_c_step` (LaczFormalBZL7h1) for an arbitrary corner label `l`;
--   `cnt1_corner_zero`  : no beta corner at a polygon vertex of angle alpha;   `cnt1_le_one_bdy` : at most one beta corner at a non-interior tiling vertex;
--   `side_has_b_step`   : a left walk along a side P.v i -> P.v (i+1) whose two ends are polygon corners of angle alpha contains a step whose tile has no beta corner at either end (= its b edge lies on the side).
-- PRINTED GAP (Lemma 11.13): the statement is about X = pa+qb+rc for the legs AB/BC, the printed proof ("the top and bottom tiles have their alpha angles at C and A") only covers the BASE AC.  On a leg the apex B has angle
-- alpha+beta and hosts one beta, so the pigeonhole (k tiles, k-1 interior vertices) has exactly enough room; q >= 1 on a leg is NOT proved here.  r >= 1 holds on every side (`side_has_c_step`).
-- Witness status: the hypotheses are those of `side_has_c_step` plus two alpha corners on the side; the 1125-tiling meets the former (BZL7h17 `witness_1125_thm107`); `side_has_b_step` itself is NOT instantiated on it here.  NOTE, UNAUDITED.
-- Credit: Beeson (arXiv 1206.1974v7, Lemma 11.13), Laczkovich (DCG 48 (2012), Sect. 4), Beeson-Zhang, Herdt, Zhang.
import Erdos634.Draft.LaczFormalBZL7h1

open scoped Classical
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ} [NeZero M]

/-- `walk_c_step` for any corner label `l` (pigeonhole along a left walk). -/
theorem walk_l_step (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) (l : Fin 3) {d : V2} {X0 : Plane}
    (hcap : ∀ U, (∃ j k, (D.tile j).pts k = U) → crs d (toV2 (U - X0)) = 0 → cnt D idx U l ≤ 1)
    {X Y : Plane} {L : List (Fin N × Plane × Plane)} (W : WalkT D.toRegionDissection d X Y L) :
    L ≠ [] → crs d (toV2 (X - X0)) = 0 → cnt D idx Y l = 0 →
    (∀ i k, (D.tile i).pts k = X → idx i k = l → ∃ Z, TriStep (D.tile i) d Z X) →
    ∃ e ∈ L, ∀ k, ((D.tile e.1).pts k = e.2.1 ∨ (D.tile e.1).pts k = e.2.2) → idx e.1 k ≠ l := by
  induction W with
  | nil X => intro hL; exact absurd rfl hL
  | @cons i X X' Y L hS W ih =>
    intro hL hXl hY0 hX
    by_contra hno
    push Not at hno
    obtain ⟨k, hk, hk2⟩ := hno (i, X, X') (List.mem_cons_self ..)
    rcases hk with hk | hk
    · obtain ⟨Z, hZ⟩ := hX i k hk hk2
      exact no_through_step hZ hS
    · by_cases hLe : L = []
      · subst hLe
        have hXY : X' = Y := by
          cases W
          rfl
        subst hXY
        have hk' : (D.tile i).pts k = X' := hk
        have := cnt_pos_of_corner_h1 D idx hk' hk2
        omega
      · have hXl' : crs d (toV2 (X' - X0)) = 0 := by
          obtain ⟨-, -, -, -, -, -, -, -, hpar, -⟩ := id hS
          obtain ⟨c, hc, hcw⟩ := hpar.smul
          have hdec : toV2 (X' - X0) = ((toV2 (X' - X)).1 + (toV2 (X - X0)).1, (toV2 (X' - X)).2 + (toV2 (X - X0)).2) := by
            unfold toV2; ext <;> simp
          rw [hdec, hcw]
          unfold crs at hXl ⊢; simp only at hXl ⊢; nlinarith [hXl]
        have hvert' : ∃ j k, (D.tile j).pts k = X' := ⟨i, k, hk⟩
        have hX' : ∀ i' k', (D.tile i').pts k' = X' → idx i' k' = l → ∃ Z, TriStep (D.tile i') d Z X' := by
          intro i' k' hk' hk2'
          have := corner_eq_of_cnt_le_one_h1 D idx (hcap X' hvert' hXl') hk hk2 hk' hk2'
          subst this
          exact ⟨X, hS⟩
        obtain ⟨e, he, hee⟩ := ih hLe hXl' hY0 hX'
        obtain ⟨k', hk', hk2'⟩ := hno e (List.mem_cons_of_mem _ he)
        exact hee k' hk' hk2'

/-- No beta corner at a polygon vertex of angle alpha. -/
theorem cnt1_corner_zero (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v)
    (hβ : D.model.angleAt 1 = Real.pi - 3 * D.model.angleAt 0) (hγ : D.model.angleAt 2 = 2 * D.model.angleAt 0)
    (hα : ¬ ∃ r : ℚ, D.model.angleAt 0 = (r : ℝ) * Real.pi)
    (m : Fin M) (hm : P.angle m = D.model.angleAt 0) : cnt D idx (P.v m) 1 = 0 := by
  have hk : m - 1 + 1 = m := (ConvPoly.fin_facts P.three_le m).2.2.2.2.1
  have hvert : ∃ j k', (D.tile j).pts k' = P.v (m - 1 + 1) := by rw [hk]; exact poly_vertex_is_tile_vertex D.toRegionDissection P hreg m
  have hA := corner_A D P hreg idx hidxA (m - 1) hvert
  rw [hk] at hA
  have hAexp : Asum D idx (P.v m) = (cnt D idx (P.v m) 0 : ℝ) * D.model.angleAt 0 + (cnt D idx (P.v m) 1 : ℝ) * D.model.angleAt 1
      + (cnt D idx (P.v m) 2 : ℝ) * (2 * D.model.angleAt 0) := by
    unfold Asum; rw [Fin.sum_univ_three, hγ]
  have key : ∀ p : ℤ, ∀ q : ℕ, Asum D idx (P.v m) = p * D.model.angleAt 0 + q * Real.pi →
      (cnt D idx (P.v m) 1 : ℤ) = q ∧ (cnt D idx (P.v m) 0 : ℤ) + 2 * cnt D idx (P.v m) 2 - 3 * cnt D idx (P.v m) 1 = p := by
    intro p q h
    refine vtype_arith (α := D.model.angleAt 0) (β := D.model.angleAt 1) hβ hα _ _ _ p q ?_
    rw [← hAexp]; exact h
  have := key 1 0 (by rw [hA, hm]; push_cast; ring)
  omega

/-- At most one beta corner at a non-interior tiling vertex (polygon angles alpha or pi - 2 alpha). -/
theorem cnt1_le_one_bdy (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v)
    (hβ : D.model.angleAt 1 = Real.pi - 3 * D.model.angleAt 0) (hγ : D.model.angleAt 2 = 2 * D.model.angleAt 0)
    (hα : ¬ ∃ r : ℚ, D.model.angleAt 0 = (r : ℝ) * Real.pi)
    (hPang : ∀ k : Fin M, P.angle (k + 1) = D.model.angleAt 0 ∨ P.angle (k + 1) = Real.pi - 2 * D.model.angleAt 0)
    {X : Plane} (hvert : ∃ j k, (D.tile j).pts k = X) (hnint : X ∉ interior D.region) : cnt D idx X 1 ≤ 1 := by
  have hAexp : Asum D idx X = (cnt D idx X 0 : ℝ) * D.model.angleAt 0 + (cnt D idx X 1 : ℝ) * D.model.angleAt 1
      + (cnt D idx X 2 : ℝ) * (2 * D.model.angleAt 0) := by
    unfold Asum; rw [Fin.sum_univ_three, hγ]
  have key : ∀ p : ℤ, ∀ q : ℕ, Asum D idx X = p * D.model.angleAt 0 + q * Real.pi →
      (cnt D idx X 1 : ℤ) = q ∧ (cnt D idx X 0 : ℤ) + 2 * cnt D idx X 2 - 3 * cnt D idx X 1 = p := by
    intro p q h
    refine vtype_arith (α := D.model.angleAt 0) (β := D.model.angleAt 1) hβ hα _ _ _ p q ?_
    rw [← hAexp]; exact h
  rcases vertex_A D P hreg idx hidxA hvert with ⟨hint, -⟩ | ⟨-, h1 | ⟨k, -, hk⟩⟩
  · exact absurd hint hnint
  · have := key 0 1 (by rw [h1]; push_cast; ring)
    omega
  · rcases hPang k with hk1 | hk1
    · have := key 1 0 (by rw [hk, hk1]; push_cast; ring)
      omega
    · have := key (-2) 1 (by rw [hk, hk1]; push_cast; ring)
      omega

/-- **Beeson Lemma 11.13, b-edge half (base).**  A left walk along the side `P.v i -> P.v (i+1)` of the polygon, both of whose ends are corners of angle alpha, contains a step `(j, U, U')` whose tile has no
beta corner at `U` or `U'`: its b edge (the edge opposite beta) lies on the side. -/
theorem side_has_b_step (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v)
    (hβ : D.model.angleAt 1 = Real.pi - 3 * D.model.angleAt 0) (hγ : D.model.angleAt 2 = 2 * D.model.angleAt 0)
    (hα : ¬ ∃ r : ℚ, D.model.angleAt 0 = (r : ℝ) * Real.pi)
    (hPang : ∀ k : Fin M, P.angle (k + 1) = D.model.angleAt 0 ∨ P.angle (k + 1) = Real.pi - 2 * D.model.angleAt 0)
    (i : Fin M) (hi0 : P.angle i = D.model.angleAt 0) (hi1 : P.angle (i + 1) = D.model.angleAt 0)
    {L : List (Fin N × Plane × Plane)} (W : WalkT D.toRegionDissection (toV2 (P.e i)) (P.v i) (P.v (i + 1)) L) :
    ∃ e ∈ L, ∀ k, ((D.tile e.1).pts k = e.2.1 ∨ (D.tile e.1).pts k = e.2.2) → idx e.1 k ≠ 1 := by
  have hL : L ≠ [] := by
    intro hL0
    subst hL0
    have h := walkT_dist_sum W
    simp only [List.map_nil, List.sum_nil] at h
    have h0 : P.v i = P.v (i + 1) := dist_eq_zero.mp h.symm
    exact P.e_ne_zero P.three_le i (by unfold ConvPoly.e; rw [← h0]; simp)
  refine walk_l_step D idx 1 (X0 := P.v i) ?_ W hL (by unfold crs toV2; simp) (cnt1_corner_zero D P hreg idx hidxA hβ hγ hα (i + 1) hi1) ?_
  · intro U hU hline
    obtain ⟨j, k, hjk⟩ := hU
    have hUP : U ∈ P.carrier := by
      rw [← hreg, ← D.covers]
      exact Set.mem_iUnion.mpr ⟨j, hjk ▸ subset_convexHull ℝ _ ⟨k, rfl⟩⟩
    have h0 : P.c i U = 0 := by
      have : P.c i U = crs (toV2 (P.e i)) (toV2 (U - P.v i)) := rfl
      rw [this]; exact hline
    refine cnt1_le_one_bdy D P hreg idx hidxA hβ hγ hα hPang ⟨j, k, hjk⟩ ?_
    rw [hreg]
    exact not_interior_of_c_zero P h0
  · intro i' k hk hk2
    have := cnt_pos_of_corner_h1 D idx hk hk2
    have h0 := cnt1_corner_zero D P hreg idx hidxA hβ hγ hα i hi0
    omega

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.walk_l_step
#print axioms Erdos634.Draft.LaczFormal.RG.cnt1_corner_zero
#print axioms Erdos634.Draft.LaczFormal.RG.cnt1_le_one_bdy
#print axioms Erdos634.Draft.LaczFormal.RG.side_has_b_step
