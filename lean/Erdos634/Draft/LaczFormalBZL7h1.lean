-- Draft/LaczFormalBZL7h1.lean -- Beeson (arXiv 1206.1974v7) Lemma 10.6, the printed PIGEONHOLE (G6): "there is at least one c edge on AC (and on AB)".
--   Printed argument: if no tile supported by the side has its c edge on it, each such tile has its gamma angle at a vertex of the side; no vertex has two gamma angles;
--   gamma does not occur at the corners (only alpha / alpha+beta there); so there is one more gamma than there are vertices to receive them.
--   Here, on a REAL dissection: `cnt2_le_one_bdy` (a non-interior tiling vertex carries at most one gamma corner), `cnt2_corner_zero` (no gamma corner at a polygon vertex with angle alpha or pi-2alpha),
--   `no_through_step` (one tile cannot have steps both ending and starting at the same vertex along d), `walk_c_step` (induction along the left walk) and `side_has_c_step`:
--   every left walk along a side of the polygon contains a step whose tile has NO gamma corner at either end, i.e. a c-edge step.
-- NOT here: the transition c-run / non-c edge and the link start at the boundary (stay in linkC).  NOTE, UNAUDITED.
-- Credit: Beeson (arXiv 1206.1974v7, Lemma 10.6), Laczkovich (DCG 48 (2012), Sect. 4: the walk along a side), Beeson-Zhang.
import Erdos634.Draft.LaczFormalBZL7g1
import Erdos634.Draft.LaczFormalRGWalk2
import Erdos634.Draft.LaczFormalRGBdy4

open scoped Classical
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ} [NeZero M]

/-- A non-interior tiling vertex carries at most one gamma corner (boundary non-corner: counts (3,1,0) / (1,1,1); polygon corner of angle alpha or pi-2alpha: no gamma). -/
theorem cnt2_le_one_bdy (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v)
    (hβ : D.model.angleAt 1 = Real.pi - 3 * D.model.angleAt 0) (hγ : D.model.angleAt 2 = 2 * D.model.angleAt 0)
    (hα : ¬ ∃ r : ℚ, D.model.angleAt 0 = (r : ℝ) * Real.pi)
    (hPang : ∀ k : Fin M, P.angle (k + 1) = D.model.angleAt 0 ∨ P.angle (k + 1) = Real.pi - 2 * D.model.angleAt 0)
    {X : Plane} (hvert : ∃ j k, (D.tile j).pts k = X) (hnint : X ∉ interior D.region) : cnt D idx X 2 ≤ 1 := by
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

/-- No gamma corner at a vertex of the polygon (its angle is alpha or pi-2alpha). -/
theorem cnt2_corner_zero (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v)
    (hβ : D.model.angleAt 1 = Real.pi - 3 * D.model.angleAt 0) (hγ : D.model.angleAt 2 = 2 * D.model.angleAt 0)
    (hα : ¬ ∃ r : ℚ, D.model.angleAt 0 = (r : ℝ) * Real.pi)
    (hPang : ∀ k : Fin M, P.angle (k + 1) = D.model.angleAt 0 ∨ P.angle (k + 1) = Real.pi - 2 * D.model.angleAt 0)
    (m : Fin M) : cnt D idx (P.v m) 2 = 0 := by
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
  have hP := hPang (m - 1)
  rw [hk] at hP
  rcases hP with h1 | h1
  · have := key 1 0 (by rw [hA, h1]; push_cast; ring)
    omega
  · have := key (-2) 1 (by rw [hA, h1]; push_cast; ring)
    omega

theorem fin3_aux1 : ∀ k1 k2 f2 g1 : Fin 3, k2 ≠ k1 → g1 ≠ k1 → g1 ≠ k2 → f2 ≠ k2 → f2 = k1 ∨ f2 = g1 := by decide
theorem fin3_aux2 : ∀ k1 k2 f2 g1 g2 : Fin 3, k2 ≠ k1 → g1 ≠ k1 → g1 ≠ k2 → f2 ≠ k2 → g2 ≠ k2 → g2 ≠ f2 → f2 = g1 → g2 = k1 := by decide

/-- A tile cannot have a step ending at `X` and another step starting at `X` along the same direction `d`. -/
theorem no_through_step {T : Tri} {d : V2} {Z X X' : Plane} (h1 : TriStep T d Z X) (h2 : TriStep T d X X') : False := by
  obtain ⟨kk1, f1, g1, hk1, hf1, hfk1, hgk1, hgf1, hpar1, hleft1⟩ := h1
  obtain ⟨kk2, f2, g2, hk2, hf2, hfk2, hgk2, hgf2, hpar2, hleft2⟩ := h2
  have e1 : kk2 = f1 := T.indep.injective (hk2.trans hf1.symm)
  subst e1
  obtain ⟨c1, hc1, hc1e⟩ := hpar1.smul
  obtain ⟨c2, hc2, hc2e⟩ := hpar2.smul
  have hd : d ≠ 0 := hpar1.ne_right
  -- f2 is kk1 or the third vertex g1
  have hcases : f2 = kk1 ∨ f2 = g1 := fin3_aux1 kk1 kk2 f2 g1 hfk1 hgk1 hgf1 hfk2
  rcases hcases with h | h
  · subst h
    -- X' = Z
    have hX' : X' = Z := by rw [← hf2, ← hk1]
    subst hX'
    have a1 : toV2 (X' - X) = (-(toV2 (X - X')).1, -(toV2 (X - X')).2) := by unfold toV2; ext <;> simp
    rw [hc1e] at a1
    rw [hc2e] at a1
    have b1 := congrArg Prod.fst a1
    have b2 := congrArg Prod.snd a1
    simp only at b1 b2
    apply hd
    have : (c1 + c2) * d.1 = 0 := by linarith
    have : (c1 + c2) * d.2 = 0 := by linarith
    have hpos : c1 + c2 ≠ 0 := by positivity
    exact Prod.ext (by simpa [hpos] using (by linarith : (c1 + c2) * d.1 = 0)) (by simpa [hpos] using (by linarith : (c1 + c2) * d.2 = 0))
  · have hg : g2 = kk1 := fin3_aux2 kk1 kk2 f2 g1 g2 hfk1 hgk1 hgf1 hfk2 hgk2 hgf2 h
    subst hg
    rw [hk1] at hleft2
    have : crs d (toV2 (Z - X)) = 0 := by
      have a1 : toV2 (Z - X) = (-(toV2 (X - Z)).1, -(toV2 (X - Z)).2) := by unfold toV2; ext <;> simp
      rw [a1, hc1e]; unfold crs; simp only; ring
    linarith

theorem cnt_pos_of_corner_h1 (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) {i : Fin N} {k : Fin 3} {X : Plane} {l : Fin 3}
    (hk : (D.tile i).pts k = X) (hl : idx i k = l) : 1 ≤ cnt D idx X l := by
  unfold cnt
  exact Finset.card_pos.mpr ⟨(i, k), by simp [hk, hl]⟩

theorem corner_eq_of_cnt_le_one_h1 (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) {i i' : Fin N} {k k' : Fin 3} {X : Plane} {l : Fin 3}
    (h1 : cnt D idx X l ≤ 1) (hk : (D.tile i).pts k = X) (hl : idx i k = l) (hk' : (D.tile i').pts k' = X) (hl' : idx i' k' = l) : i = i' := by
  unfold cnt at h1
  have := Finset.card_le_one.mp h1 (i, k) (by simp [hk, hl]) (i', k') (by simp [hk', hl'])
  exact congrArg Prod.fst this

/-- **Induction along a left walk (Beeson L10.6, pigeonhole core).**  If every step of a nonempty walk had a gamma corner at one of its ends, with at most one gamma corner at any vertex on the
line, no gamma corner at the end `Y`, and no gamma corner at the start that is not already a step's head, we get a contradiction; so some step is a c-edge step. -/
theorem walk_c_step (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) {d : V2} {X0 : Plane}
    (hcap : ∀ U, (∃ j k, (D.tile j).pts k = U) → crs d (toV2 (U - X0)) = 0 → cnt D idx U 2 ≤ 1)
    {X Y : Plane} {L : List (Fin N × Plane × Plane)} (W : WalkT D.toRegionDissection d X Y L) :
    L ≠ [] → crs d (toV2 (X - X0)) = 0 → cnt D idx Y 2 = 0 →
    (∀ i k, (D.tile i).pts k = X → idx i k = 2 → ∃ Z, TriStep (D.tile i) d Z X) →
    ∃ e ∈ L, ∀ k, ((D.tile e.1).pts k = e.2.1 ∨ (D.tile e.1).pts k = e.2.2) → idx e.1 k ≠ 2 := by
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
        have hX' : ∀ i' k', (D.tile i').pts k' = X' → idx i' k' = 2 → ∃ Z, TriStep (D.tile i') d Z X' := by
          intro i' k' hk' hk2'
          have := corner_eq_of_cnt_le_one_h1 D idx (hcap X' hvert' hXl') hk hk2 hk' hk2'
          subst this
          exact ⟨X, hS⟩
        obtain ⟨e, he, hee⟩ := ih hLe hXl' hY0 hX'
        obtain ⟨k', hk', hk2'⟩ := hno e (List.mem_cons_of_mem _ he)
        exact hee k' hk' hk2'

/-- **Beeson Lemma 10.6, printed pigeonhole (G6), on a real dissection.**  Every left walk along a side `P.v i -> P.v (i+1)` of the polygon contains a step `(j, U, U')` such that the
tile `j` has no gamma corner at `U` or `U'`: its edge on the side is its c edge (the edge opposite gamma).  Hypotheses as in `exists_center_a2`. -/
theorem side_has_c_step (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v)
    (hβ : D.model.angleAt 1 = Real.pi - 3 * D.model.angleAt 0) (hγ : D.model.angleAt 2 = 2 * D.model.angleAt 0)
    (hα : ¬ ∃ r : ℚ, D.model.angleAt 0 = (r : ℝ) * Real.pi)
    (hPang : ∀ k : Fin M, P.angle (k + 1) = D.model.angleAt 0 ∨ P.angle (k + 1) = Real.pi - 2 * D.model.angleAt 0)
    (i : Fin M) {L : List (Fin N × Plane × Plane)} (W : WalkT D.toRegionDissection (toV2 (P.e i)) (P.v i) (P.v (i + 1)) L) :
    ∃ e ∈ L, ∀ k, ((D.tile e.1).pts k = e.2.1 ∨ (D.tile e.1).pts k = e.2.2) → idx e.1 k ≠ 2 := by
  have hL : L ≠ [] := by
    intro hL0
    subst hL0
    have h := walkT_dist_sum W
    simp only [List.map_nil, List.sum_nil] at h
    have h0 : P.v i = P.v (i + 1) := dist_eq_zero.mp h.symm
    exact P.e_ne_zero P.three_le i (by unfold ConvPoly.e; rw [← h0]; simp)
  refine walk_c_step D idx (X0 := P.v i) ?_ W hL (by unfold crs toV2; simp) (cnt2_corner_zero D P hreg idx hidxA hβ hγ hα hPang (i + 1)) ?_
  · intro U hU hline
    obtain ⟨j, k, hjk⟩ := hU
    have hUP : U ∈ P.carrier := by
      rw [← hreg, ← D.covers]
      exact Set.mem_iUnion.mpr ⟨j, hjk ▸ subset_convexHull ℝ _ ⟨k, rfl⟩⟩
    have h0 : P.c i U = 0 := by
      have : P.c i U = crs (toV2 (P.e i)) (toV2 (U - P.v i)) := rfl
      rw [this]; exact hline
    refine cnt2_le_one_bdy D P hreg idx hidxA hβ hγ hα hPang ⟨j, k, hjk⟩ ?_
    rw [hreg]
    exact not_interior_of_c_zero P h0
  · intro i' k hk hk2
    have := cnt_pos_of_corner_h1 D idx hk hk2
    have h0 := cnt2_corner_zero D P hreg idx hidxA hβ hγ hα hPang i
    omega


end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.side_has_c_step
