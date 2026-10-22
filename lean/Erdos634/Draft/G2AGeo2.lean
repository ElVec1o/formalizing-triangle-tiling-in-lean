/-
Draft/G2AGeo2.lean — a `γ = 2α` leg with NO `b`-edge: the edge at the apex carries `β` at the apex.
Every `a`/`c` edge has exactly one `β` end (`Row4.edge_beta_end`); at a boundary point at most one tile presents `β`
(angle sum `π`, `Row4.fig_arith`); no `β` at the base corner (`Row4.corner_A`).  By `G2AChain.no_left_marked` no edge has
its `β` at its left end, so the edge ending at the apex has `β` there.  UNAUDITED.  No sorry, no native_decide.
-/
import Erdos634.Draft.G2AGeo1
import Erdos634.SideWall
import Erdos634.PinPlumbing

open scoped Classical

namespace Erdos634.Geometry

variable {N : ℕ}

/-- At a boundary point which is not a target vertex at most one tile presents `β = π − 3α` (figures `(3,1,0)`, `(1,1,1)`). -/
theorem Row4.beta_le_one_boundary (D : CongruentDissection N) {α a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (h : D.model.TwoAlphaData α a b c)
    {Q : Plane} (hQf : Q ∈ frontier D.target.carrier) (hQv : Q ∉ Set.range D.target.pts)
    {i i' : Fin N} (hi : (D.tile i).localAngle Q = Real.pi - 3 * α)
    (hi' : (D.tile i').localAngle Q = Real.pi - 3 * α) : i = i' := by
  obtain ⟨hα0, hα3, -⟩ := Row4.model_sides D h
  have hc := Row4.count_eq D hα h hα0 hα3 Q
  rw [D.target.localAngle_frontier hQf hQv] at hc
  set P₁ := ({i | (D.tile i).localAngle Q = α} : Finset (Fin N)).card
  set Q₁ := ({i | (D.tile i).localAngle Q = Real.pi - 3 * α} : Finset (Fin N)).card with hQ₁
  set R₁ := ({i | (D.tile i).localAngle Q = 2 * α} : Finset (Fin N)).card
  set S₁ := ({i | (D.tile i).localAngle Q = Real.pi} : Finset (Fin N)).card
  set T₁ := ({i | (D.tile i).localAngle Q = 2 * Real.pi} : Finset (Fin N)).card
  obtain ⟨h1, h2⟩ := Row4.fig_arith hα (P := P₁) (Q := Q₁) (R := R₁) (S := S₁) (T := T₁)
    (j := 1) (k := 0) (by push_cast; linear_combination -hc)
  have hR : Q₁ ≤ 1 := by omega
  exact Finset.card_le_one.mp hR i (by simp [hi]) i' (by simp [hi'])

/-- **A leg with no `b`-edge: the edge ending at the apex presents `β` at the apex.** -/
theorem Row4.leg_beta_apex (D : CongruentDissection N) {α a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (h : D.model.TwoAlphaData α a b c) {j : Fin 3}
    {P B : Plane} (hPB : P ≠ B) (hside : D.target.edge j = segment ℝ P B)
    (hends : ∀ v, D.target.pts v ∈ segment ℝ P B → D.target.pts v = P ∨ D.target.pts v = B)
    (hP : ∀ i, (D.tile i).localAngle P ≠ Real.pi - 3 * α)
    (hnob : ∀ e ∈ D.sideEdges j, D.eLen e ≠ b) :
    ∃ e ∈ D.sideEdges j, (D.tile e.1).localAngle B = Real.pi - 3 * α ∧
      ∃ m : Fin 3, (m = e.2 ∨ m = e.2 + 1) ∧ (D.tile e.1).pts m = B := by
  classical
  set E := D.sideEdges j with hE
  -- parametrization of the leg
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
  have hf0 : f 0 = P := by rw [hfdef, AffineMap.lineMap_apply_zero]
  have hf1 : f 1 = B := by rw [hfdef, AffineMap.lineMap_apply_one]
  have hfmem : ∀ t ∈ Set.Icc (0 : ℝ) 1, f t ∈ segment ℝ P B := fun t ht => by
    rw [hseg]; exact ⟨t, ht, rfl⟩
  have hθf : ∀ t ∈ Set.Icc (0 : ℝ) 1, θ (f t) = t := fun t ht => by
    apply hf_inj
    exact (hθ (f t) (hfmem t ht)).2
  have hsub : ∀ e ∈ E, D.eSet e ⊆ segment ℝ P B := fun e he => by
    have he2 : e ∈ D.sideEdges j := he
    rw [← hside]; unfold Dissection.sideEdges at he2; exact (Finset.mem_filter.mp he2).2
  have hend : ∀ e ∈ E, ∀ m : Fin 3, (m = e.2 ∨ m = e.2 + 1) →
      (D.tile e.1).pts m ∈ segment ℝ P B := by
    intro e he m hm
    apply hsub e he
    rcases hm with rfl | rfl
    · exact left_mem_segment ℝ _ _
    · exact right_mem_segment ℝ _ _
  let t0 : Fin N × Fin 3 → ℝ := fun e => θ ((D.tile e.1).pts e.2)
  let t1 : Fin N × Fin 3 → ℝ := fun e => θ ((D.tile e.1).pts (e.2 + 1))
  let lo : Fin N × Fin 3 → ℝ := fun e => min (t0 e) (t1 e)
  let hi : Fin N × Fin 3 → ℝ := fun e => max (t0 e) (t1 e)
  have hsucc : ∀ k : Fin 3, k ≠ k + 1 := by decide
  have ht0 : ∀ e ∈ E, t0 e ∈ Set.Icc (0 : ℝ) 1 ∧ f (t0 e) = (D.tile e.1).pts e.2 := fun e he =>
    hθ _ (hend e he e.2 (Or.inl rfl))
  have ht1 : ∀ e ∈ E, t1 e ∈ Set.Icc (0 : ℝ) 1 ∧ f (t1 e) = (D.tile e.1).pts (e.2 + 1) := fun e he =>
    hθ _ (hend e he (e.2 + 1) (Or.inr rfl))
  have hne01 : ∀ e ∈ E, t0 e ≠ t1 e := by
    intro e he heq
    have := (ht0 e he).2.symm.trans ((congrArg f heq).trans (ht1 e he).2)
    exact hsucc e.2 ((D.tile e.1).indep.injective this)
  have hlt : ∀ e ∈ E, lo e < hi e := by
    intro e he
    rcases lt_or_gt_of_ne (hne01 e he) with h' | h'
    · simp only [lo, hi, min_eq_left h'.le, max_eq_right h'.le]; exact h'
    · simp only [lo, hi, min_eq_right h'.le, max_eq_left h'.le]; exact h'
  have h0 : ∀ e ∈ E, 0 ≤ lo e := fun e he => le_min (ht0 e he).1.1 (ht1 e he).1.1
  have h1 : ∀ e ∈ E, hi e ≤ 1 := fun e he => max_le (ht0 e he).1.2 (ht1 e he).1.2
  -- points of the parameter interval lie on the edge, and conversely
  have hmem : ∀ e ∈ E, ∀ t, lo e ≤ t → t ≤ hi e → f t ∈ D.eSet e := by
    intro e he t htl hth
    have htseg : t ∈ segment ℝ (t0 e) (t1 e) := by
      rw [segment_eq_uIcc]
      exact ⟨htl, hth⟩
    have := Set.mem_image_of_mem f htseg
    rw [image_segment ℝ f (t0 e) (t1 e)] at this
    show f t ∈ segment ℝ ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1))
    rw [← (ht0 e he).2, ← (ht1 e he).2]; exact this
  have hmem' : ∀ e ∈ E, ∀ t ∈ Set.Icc (0 : ℝ) 1, f t ∈ D.eSet e → lo e ≤ t ∧ t ≤ hi e := by
    intro e he t ht hfe
    have hfe' : f t ∈ segment ℝ (f (t0 e)) (f (t1 e)) := by
      rw [(ht0 e he).2, (ht1 e he).2]; exact hfe
    rw [← image_segment ℝ f (t0 e) (t1 e)] at hfe'
    obtain ⟨s, hs, hst⟩ := hfe'
    have := hf_inj hst
    rw [← this, segment_eq_uIcc] at *
    exact hs
  -- disjoint interiors
  have hgap : ∀ e ∈ E, ∀ e' ∈ E, e ≠ e' → hi e ≤ lo e' ∨ hi e' ≤ lo e := by
    intro e he e' he' hne
    by_contra hcon
    push Not at hcon
    obtain ⟨hc1, hc2⟩ := hcon
    have hsing := Row4.sideEdges_subsingleton D j he he' hne
    set L := max (lo e) (lo e')
    set U := min (hi e) (hi e')
    have hLU : L < U := by
      simp only [L, U, max_lt_iff, lt_min_iff]
      exact ⟨⟨hlt e he, by linarith⟩, ⟨by linarith, hlt e' he'⟩⟩
    have hz : ∀ z : ℝ, L ≤ z → z ≤ U → f z ∈ D.eSet e ∩ D.eSet e' := by
      intro z hz1 hz2
      refine ⟨hmem e he z ((le_max_left _ _).trans hz1) (hz2.trans (min_le_left _ _)),
        hmem e' he' z ((le_max_right _ _).trans hz1) (hz2.trans (min_le_right _ _))⟩
    have hA := hz L le_rfl hLU.le
    have hB := hz ((L + U) / 2) (by linarith) (by linarith)
    have h1' := hf_inj (hsing hA hB)
    linarith
  have hcov : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∃ e ∈ E, lo e ≤ t ∧ t ≤ hi e := by
    intro t ht0' ht1'
    obtain ⟨part, hpart⟩ := hasEdgeChains_edge D.toDissection j
    have hft0 : f t ∈ D.target.edge j := by rw [hside]; exact hfmem t ⟨ht0', ht1'⟩
    have hft : f t ∈ segment ℝ (D.target.pts j) (D.target.pts (j + 1)) := hft0
    rw [← hpart] at hft
    obtain ⟨e, hep, hfe⟩ := Set.mem_iUnion₂.mp hft
    have heE : e ∈ E := by
      show e ∈ D.sideEdges j
      unfold Dissection.sideEdges
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun z hz => ?_⟩
      have : z ∈ ⋃ e ∈ part, (D.tile e.1).edge e.2 := Set.mem_iUnion₂.mpr ⟨e, hep, hz⟩
      rw [hpart] at this; exact this
    exact ⟨e, heE, hmem' e heE t ⟨ht0', ht1'⟩ hfe⟩
  -- left / right end points
  let Lp : Fin N × Fin 3 → Plane := fun e =>
    if t0 e ≤ t1 e then (D.tile e.1).pts e.2 else (D.tile e.1).pts (e.2 + 1)
  let Rp : Fin N × Fin 3 → Plane := fun e =>
    if t0 e ≤ t1 e then (D.tile e.1).pts (e.2 + 1) else (D.tile e.1).pts e.2
  have hLp : ∀ e ∈ E, θ (Lp e) = lo e ∧ Lp e ∈ segment ℝ P B := by
    intro e he
    by_cases hc : t0 e ≤ t1 e
    · simp only [Lp, if_pos hc, lo, min_eq_left hc]
      exact ⟨rfl, hend e he e.2 (Or.inl rfl)⟩
    · simp only [Lp, if_neg hc, lo, min_eq_right (not_le.mp hc).le]
      exact ⟨rfl, hend e he (e.2 + 1) (Or.inr rfl)⟩
  have hRp : ∀ e ∈ E, θ (Rp e) = hi e ∧ Rp e ∈ segment ℝ P B := by
    intro e he
    by_cases hc : t0 e ≤ t1 e
    · simp only [Rp, if_pos hc, hi, max_eq_right hc]
      exact ⟨rfl, hend e he (e.2 + 1) (Or.inr rfl)⟩
    · simp only [Rp, if_neg hc, hi, max_eq_left (not_le.mp hc).le]
      exact ⟨rfl, hend e he e.2 (Or.inl rfl)⟩
  have hLpv : ∀ e ∈ E, ∃ m : Fin 3, (m = e.2 ∨ m = e.2 + 1) ∧ (D.tile e.1).pts m = Lp e := by
    intro e he
    by_cases hc : t0 e ≤ t1 e
    · exact ⟨e.2, Or.inl rfl, by simp [Lp, hc]⟩
    · exact ⟨e.2 + 1, Or.inr rfl, by simp [Lp, hc]⟩
  have hRpv : ∀ e ∈ E, ∃ m : Fin 3, (m = e.2 ∨ m = e.2 + 1) ∧ (D.tile e.1).pts m = Rp e := by
    intro e he
    by_cases hc : t0 e ≤ t1 e
    · exact ⟨e.2 + 1, Or.inr rfl, by simp [Rp, hc]⟩
    · exact ⟨e.2, Or.inl rfl, by simp [Rp, hc]⟩
  -- exactly one of the two ends carries β
  let Lm : Fin N × Fin 3 → Prop := fun e => (D.tile e.1).localAngle (Lp e) = Real.pi - 3 * α
  let Rm : Fin N × Fin 3 → Prop := fun e => (D.tile e.1).localAngle (Rp e) = Real.pi - 3 * α
  have hdich : ∀ e ∈ E, Lm e ∨ Rm e := by
    intro e he
    have hnb := hnob e he
    have hbe := Row4.edge_beta_end D hα h e.1 e.2 hnb
    have h00 : (D.tile e.1).localAngle ((D.tile e.1).pts e.2) = (D.tile e.1).angleAt e.2 :=
      (D.tile e.1).localAngle_vertex e.2
    have h11 : (D.tile e.1).localAngle ((D.tile e.1).pts (e.2 + 1)) = (D.tile e.1).angleAt (e.2 + 1) :=
      (D.tile e.1).localAngle_vertex (e.2 + 1)
    by_cases hc : t0 e ≤ t1 e
    · simp only [Lm, Rm, Lp, Rp, if_pos hc]
      rcases hbe with ⟨hb0, -⟩ | ⟨-, hb1⟩
      · left; rw [h00]; exact hb0
      · right; rw [h11]; exact hb1
    · simp only [Lm, Rm, Lp, Rp, if_neg hc]
      rcases hbe with ⟨hb0, -⟩ | ⟨-, hb1⟩
      · right; rw [h00]; exact hb0
      · left; rw [h11]; exact hb1
  have hL0 : ∀ e ∈ E, lo e = 0 → ¬ Lm e := by
    intro e he hlo hL
    have hth := (hLp e he).1
    rw [hlo] at hth
    have : Lp e = P := by
      rw [← (hθ _ (hLp e he).2).2, hth, hf0]
    exact hP e.1 (by rw [← this]; exact hL)
  have hclash : ∀ e ∈ E, ∀ e' ∈ E, e' ≠ e → hi e' = lo e → Lm e → Rm e' → False := by
    intro e he e' he' hne hhi hL hR
    have hJ : Rp e' = Lp e := by
      rw [← (hθ _ (hRp e' he').2).2, ← (hθ _ (hLp e he).2).2, (hRp e' he').1, (hLp e he).1, hhi]
    have hlo0 : 0 < lo e := by
      have := h0 e' he'
      have := hlt e' he'
      linarith
    have hhi1 : lo e < 1 := lt_of_lt_of_le (hlt e he) (h1 e he)
    set J := Lp e with hJdef
    have hJseg : J ∈ segment ℝ P B := (hLp e he).2
    have hJP : J ≠ P := by
      intro hJP
      have : θ J = 0 := by rw [hJP, ← hf0]; exact hθf 0 ⟨le_rfl, zero_le_one⟩
      rw [(hLp e he).1] at this; linarith
    have hJB : J ≠ B := by
      intro hJB
      have : θ J = 1 := by rw [hJB, ← hf1]; exact hθf 1 ⟨zero_le_one, le_rfl⟩
      rw [(hLp e he).1] at this; linarith
    have hJf : J ∈ frontier D.target.carrier :=
      Erdos634.SideWall.edge_subset_frontier D.target j (by rw [hside]; exact hJseg)
    have hJv : J ∉ Set.range D.target.pts := by
      rintro ⟨v, hv⟩
      rcases hends v (by rw [hv]; exact hJseg) with h1' | h1'
      · exact hJP (hv.symm.trans h1')
      · exact hJB (hv.symm.trans h1')
    have hR' : (D.tile e'.1).localAngle J = Real.pi - 3 * α := by rw [← hJ]; exact hR
    have htile := Row4.beta_le_one_boundary D hα h hJf hJv hL hR'
    have := Row4.two_edges_one_tile D j he he' htile
    exact hne (Prod.ext htile.symm this.symm)
  have hnoL := Erdos634.Draft.G2AChain.no_left_marked E lo hi hlt h0 h1 hgap hcov Lm Rm hdich hL0 hclash
  -- the edge ending at the apex
  obtain ⟨e, he, hle, hge⟩ := hcov 1 zero_le_one le_rfl
  have hhi1 : hi e = 1 := le_antisymm (h1 e he) hge
  have hRB : Rp e = B := by
    rw [← (hθ _ (hRp e he).2).2, (hRp e he).1, hhi1, hf1]
  have hRe : Rm e := (hdich e he).resolve_left (hnoL e he)
  obtain ⟨m, hm, hmB⟩ := hRpv e he
  exact ⟨e, he, by simpa [Rm, hRB] using hRe, m, hm, hmB.trans hRB⟩

end Erdos634.Geometry

#print axioms Erdos634.Geometry.Row4.beta_le_one_boundary
#print axioms Erdos634.Geometry.Row4.leg_beta_apex
