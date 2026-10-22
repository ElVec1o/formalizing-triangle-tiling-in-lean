/-
Draft/F1KappaSide2.lean — geometry of an F1 side covered ONLY by `b`-edges (the F1 analogue of `Row4.bk_leg`).
A side of length `κ b` (κ ≥ 1) of the target of a 2π/3 tile (a, b, c pairwise distinct, α ∉ ℚπ), all of whose tile edges have
length `b`, cannot exist: the `κ` b-edges carry `κ` γ-corners (2π/3); no γ at a target corner (`f1_no_gamma_at_corners`); at most one
γ at a boundary point (angle sum π); so `κ` γ-corners need `κ` distinct interior junctions, of which there are `κ − 1`.
Copy of `FluxDRow4Bk.Row4.bk_leg` with the 2α-tile data replaced by 2π/3-tile data.  UNAUDITED.  No sorry, no native_decide.
-/
import Erdos634.Draft.F1KappaSide
import Erdos634.Draft.F1K2Core
import Erdos634.SideWall
import Erdos634.PinPlumbing

open scoped Classical

namespace Erdos634.Draft.F1KappaSide

open Erdos634.Geometry Erdos634.Draft.TheoremPConditional

variable {N : ℕ}

theorem f1_bk_leg (D : CongruentDissection N) {α a b c : ℝ}
    (hm : D.model.TwoPiThreeData α a b c) (hba : b ≠ a) (hbc : b ≠ c) (hac : a ≠ c)
    {j : Fin 3}
    {P B : Plane} (hPB : P ≠ B) (hside : D.target.edge j = segment ℝ P B)
    (hlen : dist P B = dist (D.target.pts j) (D.target.pts (j + 1)))
    (hends : ∀ v, D.target.pts v ∈ segment ℝ P B → D.target.pts v = P ∨ D.target.pts v = B)
    (hPγ : ∀ i, (D.tile i).localAngle P ≠ 2 * Real.pi / 3)
    (hBγ : ∀ i, (D.tile i).localAngle B ≠ 2 * Real.pi / 3)
    {k : ℕ} (hk : 1 ≤ k)
    (hL' : dist (D.target.pts j) (D.target.pts (j + 1)) = k * b)
    (hall : ∀ e ∈ D.sideEdges j, D.eLen e = b) : False := by
  obtain ⟨-, hc0, ha0, hb0⟩ := cos_alpha_of_TwoPiThree D.model hm
  have hπ := Real.pi_pos
  have hfilt : (D.sideEdges j).filter (fun e => D.eLen e = b) = D.sideEdges j :=
    Finset.filter_true_of_mem hall
  have hkR : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hEcard : (D.sideEdges j).card = k := by
    have hs := D.toDissection.side_len_sum j
    rw [Finset.sum_congr rfl (fun e he => hall e he), Finset.sum_const, nsmul_eq_mul, hL'] at hs
    have : ((D.sideEdges j).card : ℝ) = k := by
      have := mul_right_cancel₀ hb0.ne' (by linarith [hs] : ((D.sideEdges j).card : ℝ) * b = k * b)
      exact this
    exact_mod_cast this
  have hL : dist P B = k * b := by rw [hlen]; exact hL'
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
    if (D.tile e.1).localAngle ((D.tile e.1).pts e.2) = 2 * Real.pi / 3 then (D.tile e.1).pts e.2
    else (D.tile e.1).pts (e.2 + 1)
  have hgγ : ∀ e ∈ D.sideEdges j, (D.tile e.1).localAngle (gpt e) = 2 * Real.pi / 3 ∧
      (k * θ (gpt e) = lo e ∨ k * θ (gpt e) = lo e + 1) ∧ gpt e ∈ segment ℝ P B := by
    intro e he
    have hlb : dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) = b := hall e he
    have hends' := tile_b_edge_gamma_gen D hm hba hbc hac e.1 e.2 hlb
    have hmm := hmaxmin e he
    by_cases hc : (D.tile e.1).localAngle ((D.tile e.1).pts e.2) = 2 * Real.pi / 3
    · have hg : gpt e = (D.tile e.1).pts e.2 := if_pos hc
      rw [hg]
      refine ⟨hc, ?_, hend e he e.2 (Or.inl rfl)⟩
      rcases le_total (t0 e) (t1 e) with hle | hle
      · left; show (k : ℝ) * t0 e = k * min (t0 e) (t1 e); rw [min_eq_left hle]
      · right; show (k : ℝ) * t0 e = lo e + 1; rw [← hmm, max_eq_left hle]
    · have hg : gpt e = (D.tile e.1).pts (e.2 + 1) := if_neg hc
      have hc' : (D.tile e.1).localAngle ((D.tile e.1).pts (e.2 + 1)) = 2 * Real.pi / 3 := by
        rcases hends' with h1 | h2
        · exact absurd h1 hc
        · exact h2
      rw [hg]
      refine ⟨hc', ?_, hend e he (e.2 + 1) (Or.inr rfl)⟩
      rcases le_total (t0 e) (t1 e) with hle | hle
      · right; show (k : ℝ) * t1 e = lo e + 1; rw [← hmm, max_eq_right hle]
      · left; show (k : ℝ) * t1 e = k * min (t0 e) (t1 e); rw [min_eq_right hle]
  -- L1 on the side: at most one γ at a point inside the leg (angle sum `π`)
  have hfig : ∀ Q ∈ segment ℝ P B, Q ≠ P → Q ≠ B → ∀ i i' : Fin N,
      (D.tile i).localAngle Q = 2 * Real.pi / 3 → (D.tile i').localAngle Q = 2 * Real.pi / 3 → i = i' := by
    intro Q hQ hQP hQB i i' hi hi'
    have hQf : Q ∈ frontier D.target.carrier :=
      Erdos634.SideWall.edge_subset_frontier D.target j (by rw [hside]; exact hQ)
    have hQv : Q ∉ Set.range D.target.pts := by
      rintro ⟨v, hv⟩
      rcases hends v (by rw [hv]; exact hQ) with h1 | h1
      · exact hQP (hv.symm.trans h1)
      · exact hQB (hv.symm.trans h1)
    have hsum := Erdos634.PinPlumbing.pin_angle_sum D.toDissection hQf hQv
    by_contra hne
    have hle : ∑ m ∈ ({i, i'} : Finset (Fin N)), (D.tile m).localAngle Q ≤ ∑ m, (D.tile m).localAngle Q :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun m _ _ => (D.tile m).localAngle_nonneg Q)
    rw [Finset.sum_pair hne, hi, hi', hsum] at hle
    linarith [Real.pi_pos]
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
      b_edge_unique_F1 D hm hba hbc e.1 (hall e he) (by rw [hti]; exact hall e' he')
    exact hne (Prod.ext hti hk')
  have hle := Finset.card_le_card_of_injOn npos (fun e he => hmaps e he) hinj
  rw [hEcard, Nat.card_Icc] at hle
  omega


/-- **An F1 target side covered only by `b`-edges is impossible** (`κ ≥ 1` edges, side length `κ b`). -/
theorem f1_bk_side (D : CongruentDissection N) {α a b c μ : ℝ}
    (hirr : IrrPi α) (hm : D.model.TwoPiThreeData α a b c) (hF1 : D.target.F1Data α a b c μ)
    (hba : b ≠ a) (hbc : b ≠ c) (hac : a ≠ c) {j : Fin 3} {k : ℕ} (hk : 1 ≤ k)
    (hL' : dist (D.target.pts j) (D.target.pts (j + 1)) = k * b)
    (hall : ∀ e ∈ D.sideEdges j, D.eLen e = b) : False := by
  have h1 : ∀ j : Fin 3, j ≠ j + 1 := by decide
  have hne : D.target.pts j ≠ D.target.pts (j + 1) := fun h => h1 j (D.target.indep.injective h)
  refine f1_bk_leg D hm hba hbc hac (j := j) (P := D.target.pts j) (B := D.target.pts (j + 1)) hne rfl rfl ?_
    (fun i => f1_no_gamma_at_corners D hirr hm hF1 j i)
    (fun i => f1_no_gamma_at_corners D hirr hm hF1 (j + 1) i) hk hL' hall
  intro v hv
  have h3 : ∀ j v : Fin 3, v = j ∨ v = j + 1 ∨ v = j + 2 := by decide
  rcases h3 j v with rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact absurd hv (Row4.third_not_on_side D.target j)

end Erdos634.Draft.F1KappaSide

#print axioms Erdos634.Draft.F1KappaSide.f1_bk_leg
#print axioms Erdos634.Draft.F1KappaSide.f1_bk_side
