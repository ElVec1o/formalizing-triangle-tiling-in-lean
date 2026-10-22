import Erdos634.Draft.LaczFormalJunctionRules

/-!
# Band corner rule C0, at the level of tokens

Erdős #634, base-`β` band.  Credit: AI assistant (item 3, the placement-rule program), Beeson–Roșu (the
tile, the band grammar), Beeson, Laczkovich, Paliy.  Hand proof: (private working notes, not included)
(and its audit).  STATUS: UNAUDITED by a second reader; axiom-clean (see the `#print axioms` at the end).

## Statement (rule C0)
If the base word of a tiling begins with the corner tile `cBA`, its second token is `cBA`.  Equivalently
no tiling has a base word beginning `cBA, X` with `X ∈ {bAG, cAB, bGA}`.  Mirror (C0m): if the base
word ends with `cAB`, the second last token is `cAB`.

## What is proved (all for a real `CongruentDissection`, reflections allowed)
* `bedge_ends_perm`: the two ends of a `b`-edge of a tile present `α` and `γ`, one each.
* `corner_far_gamma`: the corner tile `T₁` (α at `P`, `b`-edge `PG`, `G` interior to the left side)
  has, on the far side of `PG`, a tile `T'` presenting `γ` at `P`.  This is steps 2 and 3 of the hand
  proof.  The step-2 covering fact is **not** assumed: it is the Lean theorem `far_edge_exists`
  (the chord `PG` from the open base side to the open left side, covered on its far side by a single
  `b`-edge, `L2` = `cover_unique`).
* `band_C0_word`: any further tile `T₂ ≠ T₁` presenting `α` at `P` is impossible.  Proof by the
  *boundary-figure classification at `P`* (`{3α,2β}` or `{α,β,γ}`): `T'` presents `γ`, so the figure is
  `{α,β,γ}` with `α` exactly once, but `T₁` and `T₂` both present `α`.  (The hand proof's wedge arithmetic
  `R = β − α` and `L0` are replaced by this classification.)
* `band_C0_tok`: the same for the base tokens `cBA` followed by a token with left angle `A`
  (`bAG`, `cAB`).  `band_C0_full`: together with `band_S_tok` the second token `bAG`, `cAB`, `bGA`
  is excluded.  `band_C0m_full`: the mirror (`cAB` last).

## Hypotheses (all witnessed)
The geometric hypotheses are those of `band_S_tok`: `D` a congruent dissection by the tile
`(ef, f²−e², f²)`, `1 ≤ e < f` coprime, `3α+2β = π`, `γ = 2α+β`, `α ∉ ℚπ`, and the target dimensions
`c < |base|`, `a < |left leg|` (true for the isosceles band targets, `LaczFormalJunctionTarget`:
`base_gt_c`, `leg_gt_a`).  Nothing here needs `e ≥ 2`, `M`, or `b > a`.

Engine control (PROOF_C0.md, not a Lean fact): the allowed branch `cBA, cBA` is realised by a tiling of
`T_3(1,2)` found by the window oracle, so the rule is consistent and not vacuous.  The negative control: the surviving branch `cBA, cBA` is *not* excluded; `band_C0_tok`
requires the second token to present `α` at `P`, and a `cBA` presents `β` there.
-/

namespace Erdos634.LaczJunction

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.Geometry.Dissection

variable {N : ℕ}

/-- The two ends of a `b`-edge present `α` and `γ`, one each. -/
theorem bedge_ends_perm (D : CongruentDissection N) (α β γ : ℝ)
    (hα' : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hβ' : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hγ' : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    (hab : sideOpp D.model 0 ≠ sideOpp D.model 1) (hbc : sideOpp D.model 1 ≠ sideOpp D.model 2)
    (hac : sideOpp D.model 0 ≠ sideOpp D.model 2)
    (i : Fin N) (k : Fin 3)
    (h : dist ((D.tile i).pts k) ((D.tile i).pts (k+1)) = sideOpp D.model 1) :
    ((D.tile i).localAngle ((D.tile i).pts k) = α ∧
        (D.tile i).localAngle ((D.tile i).pts (k+1)) = γ) ∨
    ((D.tile i).localAngle ((D.tile i).pts k) = γ ∧
        (D.tile i).localAngle ((D.tile i).pts (k+1)) = α) := by
  have hm := tile_multiset D i k
  rw [h] at hm
  have hm' : ({dist ((D.tile i).pts (k+2)) ((D.tile i).pts k),
      dist ((D.tile i).pts (k+1)) ((D.tile i).pts (k+2)), sideOpp D.model 1} : Multiset ℝ) =
      {sideOpp D.model 2, sideOpp D.model 1, sideOpp D.model 0} := by
    rw [← hm]
    ext s
    simp only [Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton]
    split_ifs <;> omega
  have hpair := pair_of_triple hm' hab hbc hac
  have e1 : k + 1 + 1 = k + 2 := by fin_cases k <;> rfl
  have e2 : k + 1 + 2 = k := by fin_cases k <;> rfl
  have hk := tile_vertex_angle_cases D α β γ hα' hβ' hγ' i k
  have hk1 := tile_vertex_angle_cases D α β γ hα' hβ' hγ' i (k+1)
  rw [e1, e2] at hk1
  rcases hpair with ⟨hy, hz⟩ | ⟨hy, hz⟩
  · -- y = c, z = a : angle at k is α, at k+1 is γ
    left
    constructor
    · rcases hk with ⟨h1, _⟩ | ⟨_, h1⟩ | ⟨_, h1⟩
      · exact h1
      · exfalso; rw [hz] at h1; exact hab h1
      · exfalso; rw [hz] at h1; exact hac h1
    · rcases hk1 with ⟨_, h1⟩ | ⟨_, h1⟩ | ⟨h1, _⟩
      · exfalso; rw [hy] at h1; exact hac h1.symm
      · exfalso; rw [hy] at h1; exact hbc h1.symm
      · exact h1
  · right
    constructor
    · rcases hk with ⟨_, h1⟩ | ⟨_, h1⟩ | ⟨h1, _⟩
      · exfalso; rw [hz] at h1; exact hac h1.symm
      · exfalso; rw [hz] at h1; exact hbc h1.symm
      · exact h1
    · rcases hk1 with ⟨h1, _⟩ | ⟨_, h1⟩ | ⟨_, h1⟩
      · exact h1
      · exfalso; rw [hy] at h1; exact hab h1
      · exfalso; rw [hy] at h1; exact hac h1

/-- **Steps 2 and 3 of the C0 proof.**  The corner tile `T₁` presents `α` at `P` with its `b`-edge
`[P,G]`, `P` strictly inside the base side `[A_p,A_q]` and `G` strictly inside the left side
`[A_p,A_r]`.  Then another tile `T'` presents `γ` at `P` (its `b`-edge is the far side of `PG`). -/
theorem corner_far_gamma (D : CongruentDissection N) (e f : ℕ) (he : 1 ≤ e)
    (hef : e < f) (hcop : Nat.Coprime e f) (α β γ : ℝ)
    (hγdef : γ = 2 * α + β) (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hα0 : 0 < α) (hβ0 : 0 < β)
    (hα' : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hβ' : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hγ' : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    (hsa : sideOpp D.model 0 = (ta e f : ℝ)) (hsb : sideOpp D.model 1 = (tb e f : ℝ))
    (hsc : sideOpp D.model 2 = (tc e f : ℝ))
    {P G : Plane} {p q r : Fin 3} (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (hP : P ∈ openSegment ℝ (D.target.pts p) (D.target.pts q))
    (hG : G ∈ openSegment ℝ (D.target.pts p) (D.target.pts r))
    (hPG : dist P G = (tb e f : ℝ))
    (i1 : Fin N) (j1 : Fin 3) (hPv : (D.tile i1).pts j1 = P) (hGv : (D.tile i1).pts (j1+1) = G)
    (hα1 : (D.tile i1).localAngle P = α) :
    ∃ i' : Fin N, i' ≠ i1 ∧ (D.tile i').localAngle P = γ := by
  have hB : 0 < tb e f := b_pos e f he hef
  have hneab : sideOpp D.model 0 ≠ sideOpp D.model 1 := by
    rw [hsa, hsb]; intro h
    have h' : ta e f = tb e f := by exact_mod_cast h
    exact a_not_dvd_b e f he hef hcop (h' ▸ dvd_refl _)
  have hnebc : sideOpp D.model 1 ≠ sideOpp D.model 2 := by
    rw [hsb, hsc]; intro h
    have h' : tb e f = tc e f := by exact_mod_cast h
    have := b_lt_c e f he hef; omega
  have hnec : sideOpp D.model 0 ≠ sideOpp D.model 2 := by
    rw [hsa, hsc]; intro h
    have h' : ta e f = tc e f := by exact_mod_cast h
    have hac : ta e f < tc e f := by unfold ta tc; nlinarith
    omega
  have hαγ : α ≠ γ := by rw [hγdef]; intro h; linarith
  have hαβ : α ≠ β := by
    intro h
    apply hirr
    refine ⟨1/5, ?_⟩
    have : α = Real.pi / 5 := by rw [← h] at hrel; linarith
    rw [this]; push_cast; ring
  have hfar := far_edge_exists D.toDissection hpq hpr hqr (ta e f) (tb e f) (tc e f)
    (fun x y z h => cover_unique e f x y z he hef hcop h)
    (fun i k => by
      rcases edge_length_mem D i k with h | h | h
      · exact Or.inr (Or.inr (by rw [h, hsc]))
      · exact Or.inr (Or.inl (by rw [h, hsb]))
      · exact Or.inl (by rw [h, hsa]))
    hP hG hPG hB i1 j1 hPv hGv
  obtain ⟨i', k, hi'1, hbk, hends⟩ := hfar
  have hbk' : dist ((D.tile i').pts k) ((D.tile i').pts (k+1)) = sideOpp D.model 1 := by
    rw [hbk, hsb]
  have hb1 : dist ((D.tile i1).pts j1) ((D.tile i1).pts (j1+1)) = sideOpp D.model 1 := by
    rw [hPv, hGv, hPG, hsb]
  obtain ⟨hfrontG, hnvG⟩ := side_frontier D.target hpr hpq hqr.symm hG
  -- tile `i1` presents `γ` at `G`
  have hG1 : (D.tile i1).localAngle G = γ := by
    rcases bedge_ends_perm D α β γ hα' hβ' hγ' hneab hnebc hnec i1 j1 hb1 with ⟨_, h2⟩ | ⟨h1, _⟩
    · rw [hGv] at h2; exact h2
    · rw [hPv] at h1; exact absurd (hα1.symm.trans h1) hαγ
  have hnoG : (D.tile i').localAngle G ≠ γ := by
    intro hg
    exact congruentDissection_no_double_gamma D α β γ hαβ hαγ
      (by intro h; have := Real.pi_pos; linarith) hα0.ne' (by rw [hγdef]; intro h; linarith)
      (by intro h; linarith) hβ0.ne' (by intro h; linarith) (by intro h; linarith)
      Real.pi_ne_zero hγdef hrel hirr hα' hβ' hγ' hfrontG hnvG i1 i' hi'1.symm hG1 hg
  refine ⟨i', hi'1, ?_⟩
  rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rcases bedge_ends_perm D α β γ hα' hβ' hγ' hneab hnebc hnec i' k hbk' with ⟨_, hb⟩ | ⟨ha, _⟩
    · rw [h2] at hb; exact absurd hb hnoG
    · rw [h1] at ha; exact ha
  · rcases bedge_ends_perm D α β γ hα' hβ' hγ' hneab hnebc hnec i' k hbk' with ⟨_, hb⟩ | ⟨hg, _⟩
    · rw [h2] at hb; exact hb
    · rw [h1] at hg; exact absurd hg hnoG


/-- The corner tile `cBA` read off the corner angles (this is the first half of the proof of
`band_S_word`): `|PG| = b`, `|A_pP| = c`, `|GA_p| = a`, and `P`, `G` are strictly inside the two
target sides because `c <` base and `a <` left side. -/
theorem corner_tile_geometry (D : CongruentDissection N) (e f : ℕ) (he : 1 ≤ e)
    (hef : e < f) (hcop : Nat.Coprime e f) (α β γ : ℝ)
    (hγdef : γ = 2 * α + β) (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hα0 : 0 < α) (hβ0 : 0 < β)
    (hα' : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hβ' : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hγ' : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    (hsa : sideOpp D.model 0 = (ta e f : ℝ)) (hsb : sideOpp D.model 1 = (tb e f : ℝ))
    (hsc : sideOpp D.model 2 = (tc e f : ℝ))
    {p q r : Fin 3}
    (hcB : (tc e f : ℝ) < dist (D.target.pts p) (D.target.pts q))
    (haL : (ta e f : ℝ) < dist (D.target.pts p) (D.target.pts r))
    {P G : Plane} (i1 : Fin N) (j1 : Fin 3)
    (hQv : (D.tile i1).pts (j1+2) = D.target.pts p) (hPv : (D.tile i1).pts j1 = P)
    (hGv : (D.tile i1).pts (j1+1) = G)
    (hPb : P ∈ segment ℝ (D.target.pts p) (D.target.pts q))
    (hGl : G ∈ segment ℝ (D.target.pts p) (D.target.pts r))
    (hα1 : (D.tile i1).localAngle P = α) (hβ1 : (D.tile i1).localAngle (D.target.pts p) = β) :
    dist P G = (tb e f : ℝ) ∧ P ∈ openSegment ℝ (D.target.pts p) (D.target.pts q) ∧
      G ∈ openSegment ℝ (D.target.pts p) (D.target.pts r) := by
  have hαβ : α ≠ β := by
    intro h
    apply hirr
    refine ⟨1/5, ?_⟩
    have : α = Real.pi / 5 := by rw [← h] at hrel; linarith
    rw [this]; push_cast; ring
  have hβγ : β ≠ γ := by rw [hγdef]; intro h; linarith
  have hαγ : α ≠ γ := by rw [hγdef]; intro h; linarith
  have hnea : sideOpp D.model 0 ≠ sideOpp D.model 1 := by
    rw [hsa, hsb]; intro h
    have h' : ta e f = tb e f := by exact_mod_cast h
    exact a_not_dvd_b e f he hef hcop (h' ▸ dvd_refl _)
  have hneb : sideOpp D.model 1 ≠ sideOpp D.model 2 := by
    rw [hsb, hsc]; intro h
    have h' : tb e f = tc e f := by exact_mod_cast h
    have := b_lt_c e f he hef; omega
  have hac : ta e f < tc e f := by unfold ta tc; nlinarith
  have hnec : sideOpp D.model 0 ≠ sideOpp D.model 2 := by
    rw [hsa, hsc]; intro h
    have h' : ta e f = tc e f := by exact_mod_cast h
    omega
  have hapos : (0:ℝ) < (ta e f : ℝ) := by exact_mod_cast a_pos e f he hef
  have hcpos : (0:ℝ) < (tc e f : ℝ) := by
    have : 0 < tc e f := lt_trans (a_pos e f he hef) hac
    exact_mod_cast this
  have hGQ : dist G (D.target.pts p) = (ta e f : ℝ) := by
    have hα1' : (D.tile i1).localAngle ((D.tile i1).pts j1) = α := by rw [hPv]; exact hα1
    rcases tile_vertex_angle_cases D α β γ hα' hβ' hγ' i1 j1 with ⟨_, h1⟩ | ⟨h1, _⟩ | ⟨h1, _⟩
    · rw [hGv, hQv] at h1; rw [h1, hsa]
    · exact absurd (hα1'.symm.trans h1) hαβ
    · exact absurd (hα1'.symm.trans h1) hαγ
  have hβ1' : (D.tile i1).localAngle ((D.tile i1).pts (j1+2)) = β := by rw [hQv]; exact hβ1
  obtain ⟨hPG', hedges⟩ := beta_vertex_edges D α β γ hα' hβ' hγ' hαβ hβγ hnea hneb hnec i1 (j1+2) hβ1'
  have e1 : j1 + 2 + 1 = j1 := by fin_cases j1 <;> rfl
  have e2 : j1 + 2 + 2 = j1 + 1 := by fin_cases j1 <;> rfl
  rw [e1, e2, hPv, hGv, hsb] at hPG'
  have hPc : dist (D.target.pts p) P = (tc e f : ℝ) := by
    rw [e1, e2, hPv, hGv, hQv] at hedges
    rcases hedges with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, hsc]
    · exfalso
      rw [hGQ, hsc] at h2
      have h' : ta e f = tc e f := by exact_mod_cast h2
      omega
  refine ⟨hPG', ?_, ?_⟩
  · exact openSegment_of_dist hPb (by rw [hPc]; exact hcpos) (by rw [hPc]; exact hcB)
  · exact openSegment_of_dist hGl (by rw [dist_comm, hGQ]; exact hapos)
      (by rw [dist_comm, hGQ]; exact haL)

/-- **Rule C0, word level, left angle `α`.**  The corner tile `cBA` (β at the corner `A_p`, `α` at `P`,
third vertex `G` on the left side) cannot be followed, at `P`, by a different tile `T₂` that presents
`α` at `P`.  Proof: `corner_far_gamma` gives a tile `T'` presenting `γ` at `P`; the boundary figure
at `P` is therefore `{α,β,γ}` with `α` exactly once, but `T₁ ≠ T₂` both present `α`. -/
theorem band_C0_word (D : CongruentDissection N) (e f : ℕ) (he : 1 ≤ e)
    (hef : e < f) (hcop : Nat.Coprime e f) (α β γ : ℝ)
    (hγdef : γ = 2 * α + β) (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hα0 : 0 < α) (hβ0 : 0 < β)
    (hα' : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hβ' : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hγ' : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    (hsa : sideOpp D.model 0 = (ta e f : ℝ)) (hsb : sideOpp D.model 1 = (tb e f : ℝ))
    (hsc : sideOpp D.model 2 = (tc e f : ℝ))
    {p q r : Fin 3} (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (hcB : (tc e f : ℝ) < dist (D.target.pts p) (D.target.pts q))
    (haL : (ta e f : ℝ) < dist (D.target.pts p) (D.target.pts r))
    {P G : Plane} (i1 : Fin N) (j1 : Fin 3)
    (hQv : (D.tile i1).pts (j1+2) = D.target.pts p) (hPv : (D.tile i1).pts j1 = P)
    (hGv : (D.tile i1).pts (j1+1) = G)
    (hPb : P ∈ segment ℝ (D.target.pts p) (D.target.pts q))
    (hGl : G ∈ segment ℝ (D.target.pts p) (D.target.pts r))
    (hα1 : (D.tile i1).localAngle P = α) (hβ1 : (D.tile i1).localAngle (D.target.pts p) = β)
    (i2 : Fin N) (hne : i2 ≠ i1) (hα2 : (D.tile i2).localAngle P = α) : False := by
  classical
  obtain ⟨hPG, hPo, hGo⟩ := corner_tile_geometry D e f he hef hcop α β γ hγdef hrel hirr hα0 hβ0 hα' hβ' hγ'
    hsa hsb hsc hcB haL i1 j1 hQv hPv hGv hPb hGl hα1 hβ1
  obtain ⟨i', hi'1, hγ'P⟩ := corner_far_gamma D e f he hef hcop α β γ hγdef hrel hirr hα0 hβ0
    hα' hβ' hγ' hsa hsb hsc hpq hpr hqr hPo hGo hPG i1 j1 hPv hGv hα1
  obtain ⟨hfront, hnv⟩ := side_frontier D.target hpq hpr hqr hPo
  have hαβ : α ≠ β := by
    intro h
    apply hirr
    refine ⟨1/5, ?_⟩
    have : α = Real.pi / 5 := by rw [← h] at hrel; linarith
    rw [this]; push_cast; ring
  have hfig := congruentDissection_boundary_figure_cases_at_vertex D α β γ hαβ
    (by rw [hγdef]; intro h; linarith) (by intro h; linarith) hα0.ne'
    (by rw [hγdef]; intro h; linarith) (by intro h; linarith) hβ0.ne'
    (by intro h; linarith) (by intro h; linarith) Real.pi_ne_zero hγdef hrel hirr hα' hβ' hγ'
    hfront hnv i' (Or.inr (Or.inr hγ'P))
  have hmemγ : i' ∈ ({i | (D.tile i).localAngle P = γ} : Finset (Fin N)) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hγ'P
  have hm1 : i1 ∈ ({i | (D.tile i).localAngle P = α} : Finset (Fin N)) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hα1
  have hm2 : i2 ∈ ({i | (D.tile i).localAngle P = α} : Finset (Fin N)) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hα2
  rcases hfig with ⟨_, _, hg0⟩ | ⟨hαc, _, _⟩
  · rw [Finset.card_eq_zero.mp hg0] at hmemγ; simp at hmemγ
  · obtain ⟨y, hy⟩ := Finset.card_eq_one.mp hαc
    rw [hy] at hm1 hm2
    simp at hm1 hm2
    exact hne (hm2.trans hm1.symm)


/-- **Rule C0 at the level of tokens (left angle `A`).**  The base word begins with `cBA` (tile `i1`,
corner `A_p`, junction `P`, top vertex `G` on the left side) followed by a token `i2` whose left angle
is `A` (`bAG`, `cAB`): impossible.  Orientation of the tile `i1` is handled by `revAt`, as in
`band_S_tok`. -/
theorem band_C0_tok (D : CongruentDissection N) (e f : ℕ) (he : 1 ≤ e)
    (hef : e < f) (hcop : Nat.Coprime e f) (α β γ : ℝ)
    (hγdef : γ = 2 * α + β) (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hα0 : 0 < α) (hβ0 : 0 < β)
    (hα' : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hβ' : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hγ' : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    (hsa : sideOpp D.model 0 = (ta e f : ℝ)) (hsb : sideOpp D.model 1 = (tb e f : ℝ))
    (hsc : sideOpp D.model 2 = (tc e f : ℝ))
    {p q r : Fin 3} (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (hcB : (tc e f : ℝ) < dist (D.target.pts p) (D.target.pts q))
    (haL : (ta e f : ℝ) < dist (D.target.pts p) (D.target.pts r))
    {P G E Z2 : Plane} (i1 i2 : Fin N) (hne : i2 ≠ i1) (x2 : Side) (r2 : Corner)
    (t1 : BaseTok D p q (angOf α β γ) (lenOf (ta e f) (tb e f) (tc e f)) .c .B .A i1
      (D.target.pts p) P G)
    (hGl : G ∈ segment ℝ (D.target.pts p) (D.target.pts r))
    (t2 : BaseTok D p q (angOf α β γ) (lenOf (ta e f) (tb e f) (tc e f)) x2 .A r2 i2 P E Z2) :
    False := by
  have hα2 : (D.tile i2).localAngle P = α := t2.left_angle
  have hα1 : (D.tile i1).localAngle P = α := t1.right_angle
  have hβ1 : (D.tile i1).localAngle (D.target.pts p) = β := t1.left_angle
  have hv : TileVerts (D.tile i1) P G (D.target.pts p) := t1.verts.swap12.swap23
  rcases hv.oriented with ⟨j1, hP, hG, hQ⟩ | ⟨j1, hP, hG, hQ⟩
  · exact band_C0_word D e f he hef hcop α β γ hγdef hrel hirr hα0 hβ0 hα' hβ' hγ' hsa hsb hsc
      hpq hpr hqr hcB haL i1 j1 hQ hP hG t1.right_mem hGl hα1 hβ1 i2 hne hα2
  · refine band_C0_word (D.revAt i1) e f he hef hcop α β γ hγdef hrel hirr hα0 hβ0 hα' hβ' hγ'
      hsa hsb hsc hpq hpr hqr hcB haL i1 j1 ?_ ?_ ?_ t1.right_mem hGl ?_ ?_ i2 hne ?_
    · rw [revAt_tile_self]; exact hQ
    · rw [revAt_tile_self]; exact hP
    · rw [revAt_tile_self]; exact hG
    · rw [revAt_tile_self, rev_localAngle]; exact hα1
    · rw [revAt_tile_self, rev_localAngle]; exact hβ1
    · rw [revAt_tile_ne D hne]; exact hα2

/-- **Rule C0, full form.**  A base word beginning `cBA` has second token `cBA`: the second token is
not `bAG`, `cAB` (`band_C0_tok`) and not `bGA` (rule S, `band_S_tok`). -/
theorem band_C0_full (D : CongruentDissection N) (e f : ℕ) (he : 1 ≤ e)
    (hef : e < f) (hcop : Nat.Coprime e f) (α β γ : ℝ)
    (hγdef : γ = 2 * α + β) (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hα0 : 0 < α) (hβ0 : 0 < β)
    (hα' : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hβ' : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hγ' : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    (hsa : sideOpp D.model 0 = (ta e f : ℝ)) (hsb : sideOpp D.model 1 = (tb e f : ℝ))
    (hsc : sideOpp D.model 2 = (tc e f : ℝ))
    {p q r : Fin 3} (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (hcB : (tc e f : ℝ) < dist (D.target.pts p) (D.target.pts q))
    (haL : (ta e f : ℝ) < dist (D.target.pts p) (D.target.pts r))
    {P G E Z2 : Plane} (i1 i2 : Fin N) (hne : i2 ≠ i1) (x2 : Side) (l2 r2 : Corner)
    (hlr : l2 = .A ∨ (x2 = .b ∧ l2 = .G ∧ r2 = .A))
    (t1 : BaseTok D p q (angOf α β γ) (lenOf (ta e f) (tb e f) (tc e f)) .c .B .A i1
      (D.target.pts p) P G)
    (hGl : G ∈ segment ℝ (D.target.pts p) (D.target.pts r))
    (t2 : BaseTok D p q (angOf α β γ) (lenOf (ta e f) (tb e f) (tc e f)) x2 l2 r2 i2 P E Z2) :
    False := by
  rcases hlr with rfl | ⟨rfl, rfl, rfl⟩
  · exact band_C0_tok D e f he hef hcop α β γ hγdef hrel hirr hα0 hβ0 hα' hβ' hγ' hsa hsb hsc
      hpq hpr hqr hcB haL i1 i2 hne x2 r2 t1 hGl t2
  · exact band_S_tok D e f he hef hcop α β γ hγdef hrel hirr hα0 hβ0 hα' hβ' hγ' hsa hsb hsc
      hpq hpr hqr hcB haL i1 i2 hne t1 hGl t2

/-- **Rule C0m** (mirror): the base word ends with `cAB` and the second last token has right angle
`A` or (`bAG`) `G`: impossible.  Obtained by reflecting the base. -/
theorem band_C0m_full (D : CongruentDissection N) (e f : ℕ) (he : 1 ≤ e)
    (hef : e < f) (hcop : Nat.Coprime e f) (α β γ : ℝ)
    (hγdef : γ = 2 * α + β) (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hα0 : 0 < α) (hβ0 : 0 < β)
    (hα' : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hβ' : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hγ' : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    (hsa : sideOpp D.model 0 = (ta e f : ℝ)) (hsb : sideOpp D.model 1 = (tb e f : ℝ))
    (hsc : sideOpp D.model 2 = (tc e f : ℝ))
    {p q r : Fin 3} (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (hcB : (tc e f : ℝ) < dist (D.target.pts p) (D.target.pts q))
    (haR : (ta e f : ℝ) < dist (D.target.pts q) (D.target.pts r))
    {P G E Z2 : Plane} (i1 i2 : Fin N) (hne : i2 ≠ i1) (x2 : Side) (l2 r2 : Corner)
    (hlr : r2 = .A ∨ (x2 = .b ∧ r2 = .G ∧ l2 = .A))
    (t2 : BaseTok D p q (angOf α β γ) (lenOf (ta e f) (tb e f) (tc e f)) x2 l2 r2 i2 E P Z2)
    (t1 : BaseTok D p q (angOf α β γ) (lenOf (ta e f) (tb e f) (tc e f)) .c .A .B i1
      P (D.target.pts q) G)
    (hGr : G ∈ segment ℝ (D.target.pts q) (D.target.pts r)) : False := by
  have hcB' : (tc e f : ℝ) < dist (D.target.pts q) (D.target.pts p) := by
    rw [dist_comm]; exact hcB
  exact band_C0_full D e f he hef hcop α β γ hγdef hrel hirr hα0 hβ0 hα' hβ' hγ' hsa hsb hsc
    hpq.symm hqr hpr hcB' haR i1 i2 hne x2 r2 l2
    (by rcases hlr with h | ⟨h1, h2, h3⟩
        · exact Or.inl h
        · exact Or.inr ⟨h1, h2, h3⟩)
    t1.reflect hGr t2.reflect

#print axioms band_C0_word
#print axioms band_C0_tok
#print axioms band_C0_full
#print axioms band_C0m_full

end Erdos634.LaczJunction
