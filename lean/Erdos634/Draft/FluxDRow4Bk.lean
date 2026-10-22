-- Draft/FluxDRow4Bk.lean — ROW 4, L8's `b^k` HALF ((private working notes, not included) §3 "L8, Leg =
-- b^k (Beeson's Case 2)") and, with Draft/FluxDRow4L8.lean, THEOREM R4(ii): no prime `N`.
-- Imported directly by All.lean (stale "NOT imported" header corrected 2026-10-04).
--
-- The file's argument: the `k` b-edges of a leg carry `k` γ-corners; no γ sits at a corner of the
-- target (L1); a point inside a side carries at most one γ (L1: figures `(1,1,1)`, `(3,1,0)`); so the
-- `k` γ-corners need `k` distinct interior junctions, but there are only `k − 1`.
-- Formal route (named): the junctions are counted by POSITIONS.  The leg `[P, B]` is parametrized by
-- `AffineMap.lineMap P B`; each b-edge is the image of an interval of length `1/k`; two side edges meet
-- in at most a point (`Dissection.sameside_edges_subsingleton`), so the scaled left ends are `k`
-- reals in `[0, k − 1]` pairwise `≥ 1` apart — hence exactly `0, 1, …, k − 1` (`Row4.lattice`).  Every
-- γ-corner then sits at an integer position in `{1, …, k − 1}`, injectively: `k ≤ k − 1`.
--
-- CONDITIONAL AT THE GEOMETRIC LEVEL (no Lean tiling of the base-α target for the `γ = 2α` tile;
-- DESIGN.md §5).  Witnesses: Draft/FluxDRow4L8Witness.lean (the lattice lemma on `{0, 1, 2}`, the L1 figures).
--
-- Formalization debt; not progress on the three /goal outcomes (row 4 is not the base-β branch).
import Erdos634.Draft.FluxDRow4L8Recovered -- [2026-09-26, EVIDENCE A36] was FluxDRow4L8, whose content P88 overwrote
import Erdos634.SideWall

open scoped Classical

namespace Erdos634.Geometry

variable {N : ℕ}

/-! ## The lattice lemma -/

/-- **`k` reals in `[0, k − 1]`, pairwise at least `1` apart, are `0, 1, …, k − 1`.** -/
theorem Row4.lattice : ∀ (k : ℕ) (S : Finset ℝ), S.card = k → (∀ x ∈ S, 0 ≤ x) →
    (∀ x ∈ S, x ≤ (k : ℝ) - 1) → (∀ x ∈ S, ∀ y ∈ S, x < y → x + 1 ≤ y) →
    S = (Finset.range k).image (fun n : ℕ => (n : ℝ)) := by
  intro k
  induction k with
  | zero =>
    intro S hc _ _ _
    rw [Finset.card_eq_zero.mp hc]; rfl
  | succ k ih =>
    intro S hc h0 h1 hgap
    have hne : S.Nonempty := Finset.card_pos.mp (by omega)
    set m := S.max' hne with hmdef
    have hm : m ∈ S := S.max'_mem hne
    have hle : ∀ x ∈ S, x ≤ m := fun x hx => S.le_max' x hx
    set S' := S.erase m with hS'
    have hc' : S'.card = k := by rw [Finset.card_erase_of_mem hm, hc]; rfl
    have hlt : ∀ x ∈ S', x < m := fun x hx =>
      lt_of_le_of_ne (hle x (Finset.mem_of_mem_erase hx)) (Finset.ne_of_mem_erase hx)
    have hm1 : m ≤ (k : ℝ) := by have := h1 m hm; push_cast at this; linarith
    have hS'eq := ih S' hc' (fun x hx => h0 x (Finset.mem_of_mem_erase hx))
      (fun x hx => by
        have := hgap x (Finset.mem_of_mem_erase hx) m hm (hlt x hx); linarith)
      (fun x hx y hy hxy => hgap x (Finset.mem_of_mem_erase hx) y (Finset.mem_of_mem_erase hy) hxy)
    have hmk : m = k := by
      rcases Nat.eq_zero_or_pos k with hk | hk
      · subst hk
        have := h0 m hm
        push_cast at hm1 ⊢
        linarith
      · have hmem : ((k - 1 : ℕ) : ℝ) ∈ S' := by
          rw [hS'eq]; exact Finset.mem_image.mpr ⟨k - 1, Finset.mem_range.mpr (by omega), rfl⟩
        have := hgap _ (Finset.mem_of_mem_erase hmem) m hm (hlt _ hmem)
        have hk1 : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
          rw [Nat.cast_sub (by omega)]; simp
        rw [hk1] at this
        linarith
    rw [← Finset.insert_erase hm, ← hS', hS'eq, hmk, Finset.range_add_one, Finset.image_insert]

/-! ## b-edges -/

/-- **A `b`-edge's ends carry `α` and `γ`** (one each); its opposite vertex carries `β`. -/
theorem Row4.b_edge_ends (D : CongruentDissection N) {α a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (h : D.model.TwoAlphaData α a b c) (i : Fin N)
    (k : Fin 3) (hlen : D.eLen (i, k) = b) :
    (D.tile i).angleAt (k + 2) = Real.pi - 3 * α ∧
      (((D.tile i).angleAt k = 2 * α ∧ (D.tile i).angleAt (k + 1) = α) ∨
        ((D.tile i).angleAt k = α ∧ (D.tile i).angleAt (k + 1) = 2 * α)) := by
  obtain ⟨hab, hac, hbc⟩ := Row4.scalene D hα h
  have hopp : (D.tile i).oppLen (k + 2) = b := by
    rw [← hlen]; unfold Tri.oppLen Dissection.eLen
    rw [show k + 2 + 1 = k by fin_cases k <;> rfl, show k + 2 + 2 = k + 1 by fin_cases k <;> rfl]
  obtain ⟨σ', hσ'⟩ := (D.tiles_congruent i).exists_perm
  have hk2 : (D.tile i).angleAt (k + 2) = Real.pi - 3 * α := by
    obtain ⟨σ, h0, o0, h1, o1, h2, o2⟩ := h
    rw [(hσ' (k + 2)).1]
    rw [(hσ' (k + 2)).2] at hopp
    obtain ⟨m, hm⟩ := σ.surjective (σ' (k + 2))
    rw [← hm] at hopp ⊢
    have h3 : m = 0 ∨ m = 1 ∨ m = 2 := by fin_cases m <;> simp
    rcases h3 with rfl | rfl | rfl
    · rw [o0] at hopp; exact absurd hopp hab
    · exact h1
    · rw [o2] at hopp; exact absurd hopp.symm hbc
  have hne0 : k ≠ k + 2 := by fin_cases k <;> decide
  have hne1 : k + 1 ≠ k + 2 := by fin_cases k <;> decide
  have hne01 : k ≠ k + 1 := by fin_cases k <;> decide
  have a0 := Row4.tile_angles_ne D hα h i hne0
  have a1 := Row4.tile_angles_ne D hα h i hne1
  have a01 := Row4.tile_angles_ne D hα h i hne01
  rw [hk2] at a0 a1
  refine ⟨hk2, ?_⟩
  rcases Row4.tile_angle_mem D h i k with e | e | e <;>
    rcases Row4.tile_angle_mem D h i (k + 1) with f | f | f
  · exact absurd (e.trans f.symm) a01
  · exact absurd f a1
  · exact Or.inr ⟨e, f⟩
  · exact absurd e a0
  · exact absurd e a0
  · exact absurd e a0
  · exact Or.inl ⟨e, f⟩
  · exact absurd f a1
  · exact absurd (e.trans f.symm) a01

/-- **One `b`-edge per tile.** -/
theorem Row4.b_edge_unique (D : CongruentDissection N) {α a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (h : D.model.TwoAlphaData α a b c) (i : Fin N)
    {k k' : Fin 3} (hk : D.eLen (i, k) = b) (hk' : D.eLen (i, k') = b) : k = k' := by
  have e1 := (Row4.b_edge_ends D hα h i k hk).1
  have e2 := (Row4.b_edge_ends D hα h i k' hk').1
  by_contra hne
  have : k + 2 ≠ k' + 2 := fun e => hne (by simpa using e)
  exact Row4.tile_angles_ne D hα h i this (e1.trans e2.symm)

/-- Two distinct tile edges on the same target side meet in at most a point. -/
theorem Row4.sideEdges_subsingleton (D : CongruentDissection N) (j : Fin 3)
    {e₁ e₂ : Fin N × Fin 3} (h₁ : e₁ ∈ D.sideEdges j) (h₂ : e₂ ∈ D.sideEdges j) (hne : e₁ ≠ e₂) :
    (D.eSet e₁ ∩ D.eSet e₂).Subsingleton := by
  obtain ⟨g, c, hg, hle, hj, hj1, hj2⟩ := exists_supporting D.target j
  have hS : {x ∈ D.target.carrier | g x = c} = D.target.edge j :=
    target_contact_side D.target g c hle hj hj1 hj2
  have hon : ∀ e ∈ D.sideEdges j, ∀ y ∈ (D.tile e.1).edge e.2, g y = c := by
    intro e he y hy
    unfold Dissection.sideEdges at he
    have hy' : y ∈ {x ∈ D.target.carrier | g x = c} := by
      rw [hS]; exact (Finset.mem_filter.mp he).2 hy
    exact hy'.2
  have hleT : ∀ e : Fin N × Fin 3, ∀ y ∈ (D.tile e.1).carrier, g y ≤ c :=
    fun e y hy => hle y (tile_subset_target D.toDissection e.1 hy)
  exact D.toDissection.sameside_edges_subsingleton g c hg hne (hleT e₁) (hleT e₂)
    (hon e₁ h₁) (hon e₂ h₂)

/-! ## The `b^k` leg -/

/-- **L8, the `b^k` half** (Beeson's Case 2), for one leg `[P, B]`: `k ≥ 2` edges, all of length `b`,
cannot cover it — the `k` γ-corners would need `k` distinct interior junctions, of which there are
`k − 1`. -/
theorem Row4.bk_leg (D : CongruentDissection N) {α a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (h : D.model.TwoAlphaData α a b c) {j : Fin 3}
    {P B : Plane} (hPB : P ≠ B) (hside : D.target.edge j = segment ℝ P B)
    (hlen : dist P B = dist (D.target.pts j) (D.target.pts (j + 1)))
    (hends : ∀ v, D.target.pts v ∈ segment ℝ P B → D.target.pts v = P ∨ D.target.pts v = B)
    (hPγ : ∀ i, (D.tile i).localAngle P ≠ 2 * α) (hBγ : ∀ i, (D.tile i).localAngle B ≠ 2 * α)
    {k : ℕ} (hk : 2 ≤ k) (hcard : ((D.sideEdges j).filter (fun e => D.eLen e = b)).card = k)
    (hall : ∀ e ∈ D.sideEdges j, D.eLen e = b) : False := by
  obtain ⟨hα0, hα3, ha, -, hb⟩ := Row4.model_sides D h
  have hπ := Real.pi_pos
  have hκ : 1 / 2 < Real.cos α := by
    rw [← Real.cos_pi_div_three]
    exact Real.cos_lt_cos_of_nonneg_of_le_pi hα0.le (by linarith) (by linarith)
  have hb0 : 0 < b := by rw [hb]; exact mul_pos (by nlinarith) ha
  have hfilt : (D.sideEdges j).filter (fun e => D.eLen e = b) = D.sideEdges j :=
    Finset.filter_true_of_mem hall
  have hEcard : (D.sideEdges j).card = k := by rw [← hfilt]; exact hcard
  have hkR : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hL : dist P B = k * b := by
    have hs := D.toDissection.side_len_sum j
    rw [Finset.sum_congr rfl (fun e he => hall e he), Finset.sum_const, hEcard, nsmul_eq_mul] at hs
    rw [hlen, ← hs]
  -- the parametrization `f = lineMap P B` and its inverse `θ` on the leg
  set f : ℝ →ᵃ[ℝ] Plane := AffineMap.lineMap P B with hfdef
  have hf_inj : Function.Injective f := by
    intro t₁ t₂ ht
    simp only [hfdef, AffineMap.lineMap_apply] at ht
    have hv : B -ᵥ P ≠ 0 := vsub_ne_zero.mpr hPB.symm
    have h1 := vadd_right_cancel P ht
    have h2 : (t₁ - t₂) • (B -ᵥ P) = 0 := by rw [sub_smul, h1, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp h2).resolve_right hv)
  have hseg : segment ℝ P B = f '' Set.Icc 0 1 := segment_eq_image_lineMap ℝ P B
  set θ := Function.invFunOn f (Set.Icc (0 : ℝ) 1) with hθdef
  have hθ : ∀ x ∈ segment ℝ P B, θ x ∈ Set.Icc (0 : ℝ) 1 ∧ f (θ x) = x := by
    intro x hx
    rw [hseg] at hx
    exact ⟨Function.invFunOn_mem hx, Function.invFunOn_eq hx⟩
  have hdist : ∀ t₁ t₂ : ℝ, dist (f t₁) (f t₂) = |t₁ - t₂| * (k * b) := by
    intro t₁ t₂
    rw [hfdef, dist_lineMap_lineMap, Real.dist_eq, hL]
  have hf0 : f 0 = P := by rw [hfdef, AffineMap.lineMap_apply_zero]
  have hf1 : f 1 = B := by rw [hfdef, AffineMap.lineMap_apply_one]
  have hsub : ∀ e ∈ D.sideEdges j, D.eSet e ⊆ segment ℝ P B := fun e he => by
    rw [← hside]; unfold Dissection.sideEdges at he; exact (Finset.mem_filter.mp he).2
  have hend : ∀ e ∈ D.sideEdges j, ∀ m : Fin 3, (m = e.2 ∨ m = e.2 + 1) →
      (D.tile e.1).pts m ∈ segment ℝ P B := by
    intro e he m hm
    apply hsub e he
    rcases hm with rfl | rfl
    · exact left_mem_segment ℝ _ _
    · exact right_mem_segment ℝ _ _
  -- each edge: parameters `t₀, t₁` with `|t₀ − t₁| = 1/k`; scaled left end `lo e`
  let t0 : Fin N × Fin 3 → ℝ := fun e => θ ((D.tile e.1).pts e.2)
  let t1 : Fin N × Fin 3 → ℝ := fun e => θ ((D.tile e.1).pts (e.2 + 1))
  let lo : Fin N × Fin 3 → ℝ := fun e => k * min (t0 e) (t1 e)
  have hunit : ∀ e ∈ D.sideEdges j, |t0 e - t1 e| * k = 1 := by
    intro e he
    have h1 := (hθ _ (hend e he e.2 (Or.inl rfl))).2
    have h2 := (hθ _ (hend e he (e.2 + 1) (Or.inr rfl))).2
    have hd := hdist (t0 e) (t1 e)
    rw [h1, h2] at hd
    have hl : dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) = b := hall e he
    rw [hl] at hd
    have e2 : b * (|t0 e - t1 e| * k - 1) = 0 := by linear_combination -hd
    linarith [(mul_eq_zero.mp e2).resolve_left hb0.ne']
  have hlo0 : ∀ e ∈ D.sideEdges j, 0 ≤ lo e := by
    intro e he
    have := (hθ _ (hend e he e.2 (Or.inl rfl))).1.1
    have := (hθ _ (hend e he (e.2 + 1) (Or.inr rfl))).1.1
    exact mul_nonneg hkR.le (le_min (by assumption) (by assumption))
  have hmaxmin : ∀ e ∈ D.sideEdges j, k * max (t0 e) (t1 e) = lo e + 1 := by
    intro e he
    have hu := hunit e he
    have : max (t0 e) (t1 e) - min (t0 e) (t1 e) = |t0 e - t1 e| := by
      rw [max_sub_min_eq_abs, abs_sub_comm]
    show k * max (t0 e) (t1 e) = k * min (t0 e) (t1 e) + 1
    nlinarith
  have hlo1 : ∀ e ∈ D.sideEdges j, lo e ≤ (k : ℝ) - 1 := by
    intro e he
    have := hmaxmin e he
    have h1 := (hθ _ (hend e he e.2 (Or.inl rfl))).1.2
    have h2 := (hθ _ (hend e he (e.2 + 1) (Or.inr rfl))).1.2
    have : max (t0 e) (t1 e) ≤ 1 := max_le h1 h2
    nlinarith
  -- points of the parameter interval lie on the edge
  have hmem : ∀ e ∈ D.sideEdges j, ∀ t, lo e ≤ k * t → k * t ≤ lo e + 1 → f t ∈ D.eSet e := by
    intro e he t ht1 ht2
    have h1 := (hθ _ (hend e he e.2 (Or.inl rfl))).2
    have h2 := (hθ _ (hend e he (e.2 + 1) (Or.inr rfl))).2
    have hmm := hmaxmin e he
    have htseg : t ∈ segment ℝ (t0 e) (t1 e) := by
      rw [segment_eq_uIcc]
      constructor
      · show min (t0 e) (t1 e) ≤ t
        have : k * min (t0 e) (t1 e) ≤ k * t := ht1
        exact le_of_mul_le_mul_left this hkR
      · show t ≤ max (t0 e) (t1 e)
        have : k * t ≤ k * max (t0 e) (t1 e) := by rw [hmm]; exact ht2
        exact le_of_mul_le_mul_left this hkR
    have := Set.mem_image_of_mem f htseg
    rw [image_segment ℝ f (t0 e) (t1 e)] at this
    show f t ∈ segment ℝ ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1))
    rw [← h1, ← h2]; exact this
  -- the gaps: distinct edges have left ends at least `1` apart
  have hgap : ∀ e ∈ D.sideEdges j, ∀ e' ∈ D.sideEdges j, e ≠ e' → lo e ≤ lo e' →
      lo e + 1 ≤ lo e' := by
    intro e he e' he' hne hle
    by_contra hcon
    push Not at hcon
    have hsing := Row4.sideEdges_subsingleton D j he he' hne
    have hz : ∀ z : ℝ, lo e' ≤ z → z ≤ lo e + 1 → f (z / k) ∈ D.eSet e ∩ D.eSet e' := by
      intro z hz1 hz2
      have hkz : k * (z / k) = z := by field_simp
      refine ⟨hmem e he _ (by rw [hkz]; linarith) (by rw [hkz]; linarith),
        hmem e' he' _ (by rw [hkz]; linarith) (by rw [hkz]; linarith)⟩
    have hA := hz (lo e') le_rfl hcon.le
    have hB := hz ((lo e' + lo e + 1) / 2) (by linarith) (by linarith)
    have h1 := hf_inj (hsing hA hB)
    have h2 : lo e' = (lo e' + lo e + 1) / 2 := by
      field_simp at h1; linarith
    linarith
  have hloinj : Set.InjOn lo (D.sideEdges j) := by
    intro e he e' he' hh
    by_contra hne
    have := hgap e he e' he' hne hh.le
    linarith
  -- the lattice: every `lo e` is a natural number `< k`
  have hS := Row4.lattice k ((D.sideEdges j).image lo)
    (by rw [Finset.card_image_of_injOn hloinj, hEcard])
    (fun x hx => by obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hx; exact hlo0 e he)
    (fun x hx => by obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hx; exact hlo1 e he)
    (fun x hx y hy hxy => by
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨e', he', rfl⟩ := Finset.mem_image.mp hy
      exact hgap e he e' he' (fun hh => by rw [hh] at hxy; exact lt_irrefl _ hxy) hxy.le)
  have hlonat : ∀ e ∈ D.sideEdges j, ∃ n : ℕ, n < k ∧ lo e = n := by
    intro e he
    have hm : lo e ∈ (D.sideEdges j).image lo := Finset.mem_image_of_mem lo he
    rw [hS] at hm
    obtain ⟨n, hn, hn'⟩ := Finset.mem_image.mp hm
    exact ⟨n, Finset.mem_range.mp hn, hn'.symm⟩
  -- the γ-end of each edge sits at scaled position `lo e` or `lo e + 1`
  let gpt : Fin N × Fin 3 → Plane := fun e =>
    if (D.tile e.1).angleAt e.2 = 2 * α then (D.tile e.1).pts e.2 else (D.tile e.1).pts (e.2 + 1)
  have hgγ : ∀ e ∈ D.sideEdges j, (D.tile e.1).localAngle (gpt e) = 2 * α ∧
      (k * θ (gpt e) = lo e ∨ k * θ (gpt e) = lo e + 1) ∧ gpt e ∈ segment ℝ P B := by
    intro e he
    obtain ⟨-, hends'⟩ := Row4.b_edge_ends D hα h e.1 e.2 (hall e he)
    have hmm := hmaxmin e he
    by_cases hc : (D.tile e.1).angleAt e.2 = 2 * α
    · have hg : gpt e = (D.tile e.1).pts e.2 := if_pos hc
      rw [hg]
      refine ⟨by rw [(D.tile e.1).localAngle_vertex]; exact hc, ?_, hend e he e.2 (Or.inl rfl)⟩
      rcases le_total (t0 e) (t1 e) with hle | hle
      · left; show (k : ℝ) * t0 e = k * min (t0 e) (t1 e); rw [min_eq_left hle]
      · right; show (k : ℝ) * t0 e = lo e + 1; rw [← hmm, max_eq_left hle]
    · have hg : gpt e = (D.tile e.1).pts (e.2 + 1) := if_neg hc
      have hc' : (D.tile e.1).angleAt (e.2 + 1) = 2 * α := by
        rcases hends' with ⟨h1, -⟩ | ⟨-, h2⟩
        · exact absurd h1 hc
        · exact h2
      rw [hg]
      refine ⟨by rw [(D.tile e.1).localAngle_vertex]; exact hc', ?_, hend e he (e.2 + 1) (Or.inr rfl)⟩
      rcases le_total (t0 e) (t1 e) with hle | hle
      · right; show (k : ℝ) * t1 e = lo e + 1; rw [← hmm, max_eq_right hle]
      · left; show (k : ℝ) * t1 e = k * min (t0 e) (t1 e); rw [min_eq_right hle]
  -- L1 on the side: at most one γ at a point inside the leg
  have hfig : ∀ Q ∈ segment ℝ P B, Q ≠ P → Q ≠ B → ∀ i i' : Fin N,
      (D.tile i).localAngle Q = 2 * α → (D.tile i').localAngle Q = 2 * α → i = i' := by
    intro Q hQ hQP hQB i i' hi hi'
    have hQf : Q ∈ frontier D.target.carrier :=
      Erdos634.SideWall.edge_subset_frontier D.target j (by rw [hside]; exact hQ)
    have hQv : Q ∉ Set.range D.target.pts := by
      rintro ⟨v, hv⟩
      rcases hends v (by rw [hv]; exact hQ) with h1 | h1
      · exact hQP (hv.symm.trans h1)
      · exact hQB (hv.symm.trans h1)
    have hc := Row4.count_eq D hα h hα0 hα3 Q
    rw [D.target.localAngle_frontier hQf hQv] at hc
    set P₁ := ({i | (D.tile i).localAngle Q = α} : Finset (Fin N)).card
    set Q₁ := ({i | (D.tile i).localAngle Q = Real.pi - 3 * α} : Finset (Fin N)).card
    set R₁ := ({i | (D.tile i).localAngle Q = 2 * α} : Finset (Fin N)).card with hR₁
    set S₁ := ({i | (D.tile i).localAngle Q = Real.pi} : Finset (Fin N)).card
    set T₁ := ({i | (D.tile i).localAngle Q = 2 * Real.pi} : Finset (Fin N)).card
    obtain ⟨h1, h2⟩ := Row4.fig_arith hα (P := P₁) (Q := Q₁) (R := R₁) (S := S₁) (T := T₁)
      (j := 1) (k := 0) (by push_cast; linear_combination -hc)
    have hR : R₁ ≤ 1 := by omega
    exact Finset.card_le_one.mp hR i (by simp [hi]) i' (by simp [hi'])
  -- the γ positions are integers in `{1, …, k − 1}`
  have hpos : ∀ e ∈ D.sideEdges j, ∃ n : ℕ, 1 ≤ n ∧ n ≤ k - 1 ∧ (k : ℝ) * θ (gpt e) = n := by
    intro e he
    obtain ⟨hγ, hlo, hsg⟩ := hgγ e he
    obtain ⟨n, hn, hn'⟩ := hlonat e he
    have hθg := hθ (gpt e) hsg
    have hne0 : (k : ℝ) * θ (gpt e) ≠ 0 := by
      intro h0
      have ht0 : θ (gpt e) = 0 := (mul_eq_zero.mp h0).resolve_left hkR.ne'
      have hP' : gpt e = P := by rw [← hθg.2, ht0, hf0]
      exact hPγ e.1 (by rw [← hP']; exact hγ)
    have hnek : (k : ℝ) * θ (gpt e) ≠ k := by
      intro hk'
      have ht1 : θ (gpt e) = 1 := mul_left_cancel₀ hkR.ne' (hk'.trans (mul_one (k : ℝ)).symm)
      have hB' : gpt e = B := by rw [← hθg.2, ht1, hf1]
      exact hBγ e.1 (by rw [← hB']; exact hγ)
    rcases hlo with h' | h'
    · refine ⟨n, ?_, by omega, by rw [h', hn']⟩
      by_contra h0
      push Not at h0
      have hn0 : n = 0 := by omega
      exact hne0 (by rw [h', hn', hn0]; simp)
    · refine ⟨n + 1, by omega, ?_, by rw [h', hn']; push_cast; ring⟩
      by_contra hc
      push Not at hc
      have hnk : n + 1 = k := by omega
      exact hnek (by rw [h', hn']; exact_mod_cast hnk)
  choose! npos hnpos using hpos
  have hmaps : ∀ e ∈ D.sideEdges j, npos e ∈ Finset.Icc 1 (k - 1) := fun e he =>
    Finset.mem_Icc.mpr ⟨(hnpos e he).1, (hnpos e he).2.1⟩
  have hinj : Set.InjOn npos (D.sideEdges j) := by
    intro e he e' he' hh
    by_contra hne
    obtain ⟨hγ, -, hsg⟩ := hgγ e he
    obtain ⟨hγ', -, hsg'⟩ := hgγ e' he'
    have hθeq : θ (gpt e) = θ (gpt e') := by
      have h1 := (hnpos e he).2.2
      have h2 := (hnpos e' he').2.2
      have hh' : (npos e : ℝ) = npos e' := by rw [hh]
      exact mul_left_cancel₀ hkR.ne' (h1.trans (hh'.trans h2.symm))
    have hgeq : gpt e = gpt e' := by
      rw [← (hθ _ hsg).2, ← (hθ _ hsg').2, hθeq]
    have hQP : gpt e ≠ P := fun hq => hPγ e.1 (by rw [← hq]; exact hγ)
    have hQB : gpt e ≠ B := fun hq => hBγ e.1 (by rw [← hq]; exact hγ)
    have hti : e.1 = e'.1 := hfig (gpt e) hsg hQP hQB e.1 e'.1 hγ (by rw [hgeq]; exact hγ')
    have hk' : e.2 = e'.2 :=
      Row4.b_edge_unique D hα h e.1 (hall e he) (by rw [hti]; exact hall e' he')
    exact hne (Prod.ext hti hk')
  have hle := Finset.card_le_card_of_injOn npos (fun e he => hmaps e he) hinj
  rw [hEcard, Nat.card_Icc] at hle
  omega

/-- The vertex of a triangle opposite a side is not on that side. -/
theorem Row4.third_not_on_side (T : Tri) (j : Fin 3) :
    T.pts (j + 2) ∉ segment ℝ (T.pts j) (T.pts (j + 1)) := by
  intro hmem
  obtain ⟨g, c, -, hle, hj, hj1, hj2⟩ := exists_supporting T j
  have hS := target_contact_side T g c hle hj hj1 hj2
  rw [← hS] at hmem
  linarith [hmem.2]

/-- **THEOREM R4(ii)** (row4/PROOF.md P2): an `N`-tiling of the base-α target by the `γ = 2α` tile
with `α ∉ ℚπ` (reflections allowed, not necessarily edge-to-edge) has `N` NOT prime.
CONDITIONAL: the target shape has no Lean witness. -/
theorem Row4.not_prime (D : CongruentDissection N) {α a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (h : D.model.TwoAlphaData α a b c)
    (hA : D.target.angleAt 0 = α) (hC : D.target.angleAt 1 = α) : ¬ N.Prime := by
  intro hN
  obtain ⟨j, hj, k, hk2, -, hcard, hall⟩ := Row4.prime_reduced D hα h hA hC hN
  obtain ⟨hα0, hα3, -⟩ := Row4.model_sides D h
  have hB : D.target.angleAt 2 = Real.pi - 2 * α := by
    have := D.target.angleAt_sum; rw [hA, hC] at this; linarith
  obtain ⟨hBγ, -⟩ := Row4.corner_B D hα h hα0 hα3 hB
  have hne : ∀ i j : Fin 3, i ≠ j → D.target.pts i ≠ D.target.pts j := fun i j hij e =>
    hij (D.target.indep.injective e)
  rcases hj with rfl | rfl
  · -- the leg `CB = [pts 1, pts 2]`
    refine Row4.bk_leg D hα h (hne 1 2 (by decide)) rfl rfl ?_
      (fun i => (Row4.corner_A D hα h hα0 hα3 hC i).2) hBγ hk2 hcard hall
    intro v hv
    have h3 : v = 0 ∨ v = 1 ∨ v = 2 := by fin_cases v <;> simp
    rcases h3 with rfl | rfl | rfl
    · exact absurd hv (Row4.third_not_on_side D.target 1)
    · exact Or.inl rfl
    · exact Or.inr rfl
  · -- the leg `AB = [pts 0, pts 2]`
    have hsAB : D.target.edge 2 = segment ℝ (D.target.pts 0) (D.target.pts 2) := by
      show segment ℝ (D.target.pts 2) (D.target.pts (2 + 1)) = _
      rw [show (2 : Fin 3) + 1 = 0 from rfl, segment_symm]
    refine Row4.bk_leg D hα h (hne 0 2 (by decide)) hsAB (by rw [dist_comm]; rfl) ?_
      (fun i => (Row4.corner_A D hα h hα0 hα3 hA i).2) hBγ hk2 hcard hall
    intro v hv
    have h3 : v = 0 ∨ v = 1 ∨ v = 2 := by fin_cases v <;> simp
    rcases h3 with rfl | rfl | rfl
    · exact Or.inl rfl
    · rw [segment_symm] at hv
      exact absurd hv (Row4.third_not_on_side D.target 2)
    · exact Or.inr rfl

end Erdos634.Geometry

#print axioms Erdos634.Geometry.Row4.lattice
#print axioms Erdos634.Geometry.Row4.b_edge_ends
#print axioms Erdos634.Geometry.Row4.b_edge_unique
#print axioms Erdos634.Geometry.Row4.sideEdges_subsingleton
#print axioms Erdos634.Geometry.Row4.bk_leg
#print axioms Erdos634.Geometry.Row4.third_not_on_side
#print axioms Erdos634.Geometry.Row4.not_prime
