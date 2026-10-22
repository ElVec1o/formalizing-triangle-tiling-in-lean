import Erdos634.Draft.LaczFormalJunctionRuleI

/-!
# Band junction rules: word-level statements

Erdős #634, base-`β` band.  Credit: AI assistant (band lemma / item-3 proposal), Beeson–Roșu, Beeson,
Laczkovich, Paliy.

`band_S_word` and `band_I_word` restate Theorems 1 and 2 with the placement of the first tokens
read off the word itself:

* the corner tile `cBA` has its `β`-vertex at the target corner `A_p`, its `α`-vertex at `P` on the
  base `[A_p,A_q]` and its third vertex `G` on the left side `[A_p,A_r]`; the lengths `|PG| = b`,
  `|A_pG| = a`, `|A_pP| = c` are *derived* from the corner angles, and `P`, `G` are strictly inside the
  two sides because `c < |A_pA_q|` and `a < |A_pA_r|` (`L > a`);
* `bGA` has a vertex at `P` presenting `γ` and a `b`-edge on the base.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.LaczJunction

open Erdos634.Geometry Erdos634.TilePlacement

variable {N : ℕ}

theorem openSegment_of_dist {A B X : Plane} (hX : X ∈ segment ℝ A B) (h0 : 0 < dist A X)
    (h1 : dist A X < dist A B) : X ∈ openSegment ℝ A B := by
  rw [segment_eq_image_lineMap] at hX
  obtain ⟨t, ⟨ht0, ht1⟩, rfl⟩ := hX
  rw [dist_left_lineMap, Real.norm_of_nonneg ht0] at h0 h1
  rw [openSegment_eq_image_lineMap]
  refine ⟨t, ⟨?_, ?_⟩, rfl⟩
  · rcases ht0.lt_or_eq with h | h
    · exact h
    · rw [← h] at h0; simp at h0
  · by_contra h
    have h : 1 ≤ t := not_lt.mp h
    have : t = 1 := le_antisymm ht1 h
    rw [this] at h1; simp at h1

theorem segment_coord_zero (T : Tri) {p q r : Fin 3} (hpr : p ≠ r) (hqr : q ≠ r)
    {X : Plane} (hX : X ∈ segment ℝ (T.pts p) (T.pts q)) : T.basis.coord r X = 0 := by
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hX
  rw [coord_combo T r hab]
  simp [coord_vertex, hpr.symm, hqr.symm]

theorem pair_of_triple {x y a b c : ℝ} (hm : ({x, y, b} : Multiset ℝ) = {c, b, a})
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) : (x = c ∧ y = a) ∨ (x = a ∧ y = c) := by
  have hx : x ∈ ({c, b, a} : Multiset ℝ) := by rw [← hm]; simp
  have hy : y ∈ ({c, b, a} : Multiset ℝ) := by rw [← hm]; simp
  simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hx hy
  have hba := hab.symm
  have hcb := hbc.symm
  have hca := hac.symm
  rcases hx with hx | hx | hx <;> rcases hy with hy | hy | hy
  · exfalso; rw [hx, hy] at hm; have := congrArg (Multiset.count c) hm
    simp [Multiset.count_cons, hab, hbc, hac, hba, hcb, hca] at this
  · exfalso; rw [hx, hy] at hm; have := congrArg (Multiset.count b) hm
    simp [Multiset.count_cons, hab, hbc, hac, hba, hcb, hca] at this
  · exact Or.inl ⟨hx, hy⟩
  · exfalso; rw [hx, hy] at hm; have := congrArg (Multiset.count b) hm
    simp [Multiset.count_cons, hab, hbc, hac, hba, hcb, hca] at this
  · exfalso; rw [hx, hy] at hm; have := congrArg (Multiset.count b) hm
    simp [Multiset.count_cons, hab, hbc, hac, hba, hcb, hca] at this
  · exfalso; rw [hx, hy] at hm; have := congrArg (Multiset.count b) hm
    simp [Multiset.count_cons, hab, hbc, hac, hba, hcb, hca] at this
  · exact Or.inr ⟨hx, hy⟩
  · exfalso; rw [hx, hy] at hm; have := congrArg (Multiset.count b) hm
    simp [Multiset.count_cons, hab, hbc, hac, hba, hcb, hca] at this
  · exfalso; rw [hx, hy] at hm; have := congrArg (Multiset.count a) hm
    simp [Multiset.count_cons, hab, hbc, hac, hba, hcb, hca] at this

/-- The two edges at a `β`-corner are `a` and `c`, the opposite side is `b`. -/
theorem beta_vertex_edges (D : CongruentDissection N) (α β γ : ℝ)
    (hα' : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hβ' : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hγ' : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    (hαβ : α ≠ β) (hβγ : β ≠ γ)
    (hab : sideOpp D.model 0 ≠ sideOpp D.model 1) (hbc : sideOpp D.model 1 ≠ sideOpp D.model 2)
    (hac : sideOpp D.model 0 ≠ sideOpp D.model 2)
    (i : Fin N) (j : Fin 3) (h : (D.tile i).localAngle ((D.tile i).pts j) = β) :
    dist ((D.tile i).pts (j+1)) ((D.tile i).pts (j+2)) = sideOpp D.model 1 ∧
    ((dist ((D.tile i).pts j) ((D.tile i).pts (j+1)) = sideOpp D.model 2 ∧
        dist ((D.tile i).pts (j+2)) ((D.tile i).pts j) = sideOpp D.model 0) ∨
     (dist ((D.tile i).pts j) ((D.tile i).pts (j+1)) = sideOpp D.model 0 ∧
        dist ((D.tile i).pts (j+2)) ((D.tile i).pts j) = sideOpp D.model 2)) := by
  have hz : dist ((D.tile i).pts (j+1)) ((D.tile i).pts (j+2)) = sideOpp D.model 1 := by
    rcases tile_vertex_angle_cases D α β γ hα' hβ' hγ' i j with ⟨h1, _⟩ | ⟨_, h1⟩ | ⟨h1, _⟩
    · exact absurd (h.symm.trans h1) hαβ.symm
    · exact h1
    · exact absurd (h.symm.trans h1) hβγ
  refine ⟨hz, ?_⟩
  have hm := tile_multiset D i j
  rw [hz] at hm
  exact pair_of_triple hm hab hbc hac

/-- **Rule S (and its mirror E), read off the word.**  The base word of a tiling begins with the
corner tile `cBA` (`β` at the corner `A_p`, `α` at `P` on the base, third vertex `G` on the left
side) followed by `bGA` (`γ` at `P`, a `b`-edge on the base): impossible, provided the base is
longer than `c` and the left side longer than `a` (`L > a`). -/
theorem band_S_word (D : CongruentDissection N) (e f : ℕ) (he : 1 ≤ e)
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
    (i2 : Fin N) (j2 : Fin 3)
    (hb2P : ((D.tile i2).pts j2 = P ∧
        (D.tile i2).pts (j2+1) ∈ segment ℝ (D.target.pts p) (D.target.pts q)) ∨
      ((D.tile i2).pts (j2+1) = P ∧
        (D.tile i2).pts j2 ∈ segment ℝ (D.target.pts p) (D.target.pts q)))
    (hb2 : dist ((D.tile i2).pts j2) ((D.tile i2).pts (j2+1)) = (tb e f : ℝ))
    (hγ2 : (D.tile i2).localAngle P = γ) : False := by
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
  have hPopen : P ∈ openSegment ℝ (D.target.pts p) (D.target.pts q) :=
    openSegment_of_dist hPb (by rw [hPc]; exact hcpos) (by rw [hPc]; exact hcB)
  have hGopen : G ∈ openSegment ℝ (D.target.pts p) (D.target.pts r) :=
    openSegment_of_dist hGl (by rw [dist_comm, hGQ]; exact hapos) (by rw [dist_comm, hGQ]; exact haL)
  have hb2a : D.target.basis.coord r ((D.tile i2).pts j2) = 0 := by
    rcases hb2P with ⟨h1, _⟩ | ⟨_, h2⟩
    · rw [h1]; exact segment_coord_zero D.target hpr hqr hPb
    · exact segment_coord_zero D.target hpr hqr h2
  have hb2b : D.target.basis.coord r ((D.tile i2).pts (j2+1)) = 0 := by
    rcases hb2P with ⟨_, h2⟩ | ⟨h1, _⟩
    · exact segment_coord_zero D.target hpr hqr h2
    · rw [h1]; exact segment_coord_zero D.target hpr hqr hPb
  exact band_corner_pair_impossible D e f he hef hcop α β γ hγdef hrel hirr hα0 hβ0 hα' hβ' hγ'
    hsa hsb hsc hpq hpr hqr hPopen hGopen hPG' i1 j1 hPv hGv i2 j2 hγ2 hb2 hb2a hb2b

/-- **Rule I (and its mirror Im), `|PG| = b` read off the corner angles.**  The configuration
`X, cBA, bGA` at consecutive positions with `cBA` at an interior base point is impossible. -/
theorem band_I_word (D : CongruentDissection N) (e f : ℕ) (he : 1 ≤ e) (hef : e < f)
    (hcop : Nat.Coprime e f) (hband : ta e f < tb e f) (α β γ : ℝ)
    (hγdef : γ = 2 * α + β) (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hα0 : 0 < α) (hβ0 : 0 < β)
    (hα' : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hβ' : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hγ' : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    (hsa : sideOpp D.model 0 = (ta e f : ℝ)) (hsb : sideOpp D.model 1 = (tb e f : ℝ))
    (hsc : sideOpp D.model 2 = (tc e f : ℝ))
    {p q r : Fin 3} (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    {P Q G : Plane}
    (hP : P ∈ openSegment ℝ (D.target.pts p) (D.target.pts q))
    (hQ : Q ∈ openSegment ℝ (D.target.pts p) (D.target.pts q))
    (i1 : Fin N) (j1 : Fin 3) (hPv : (D.tile i1).pts j1 = P) (hGv : (D.tile i1).pts (j1+1) = G)
    (hQv : (D.tile i1).pts (j1+2) = Q)
    (hα1 : (D.tile i1).localAngle P = α) (hβ1 : (D.tile i1).localAngle Q = β)
    (iX : Fin N) (kX mX : Fin 3) (Y : Plane) (hXQ : (D.tile iX).pts kX = Q)
    (hXY : (D.tile iX).pts mX = Y) (hmk : mX ≠ kX) (s : ℝ) (hs : 0 < s)
    (hYQ : Y - Q = (-s) • (P - Q))
    (hXne : iX ≠ i1) (hXang : (D.tile iX).localAngle Q = β ∨ (D.tile iX).localAngle Q = γ)
    (i2 : Fin N) (j2 : Fin 3) (hγ2 : (D.tile i2).localAngle P = γ)
    (hb2 : dist ((D.tile i2).pts j2) ((D.tile i2).pts (j2+1)) = (tb e f : ℝ))
    (hb2a : D.target.basis.coord r ((D.tile i2).pts j2) = 0)
    (hb2b : D.target.basis.coord r ((D.tile i2).pts (j2+1)) = 0) : False := by
  have hαβ : α ≠ β := by
    intro h
    apply hirr
    refine ⟨1/5, ?_⟩
    have : α = Real.pi / 5 := by rw [← h] at hrel; linarith
    rw [this]; push_cast; ring
  have hβγ : β ≠ γ := by rw [hγdef]; intro h; linarith
  have hnea : sideOpp D.model 0 ≠ sideOpp D.model 1 := by
    rw [hsa, hsb]; intro h
    have h' : ta e f = tb e f := by exact_mod_cast h
    omega
  have hneb : sideOpp D.model 1 ≠ sideOpp D.model 2 := by
    rw [hsb, hsc]; intro h
    have h' : tb e f = tc e f := by exact_mod_cast h
    have := b_lt_c e f he hef; omega
  have hac : ta e f < tc e f := by unfold ta tc; nlinarith
  have hnec : sideOpp D.model 0 ≠ sideOpp D.model 2 := by
    rw [hsa, hsc]; intro h
    have h' : ta e f = tc e f := by exact_mod_cast h
    omega
  have hβ1' : (D.tile i1).localAngle ((D.tile i1).pts (j1+2)) = β := by rw [hQv]; exact hβ1
  obtain ⟨hPG', -⟩ := beta_vertex_edges D α β γ hα' hβ' hγ' hαβ hβγ hnea hneb hnec i1 (j1+2) hβ1'
  have e1 : j1 + 2 + 1 = j1 := by fin_cases j1 <;> rfl
  have e2 : j1 + 2 + 2 = j1 + 1 := by fin_cases j1 <;> rfl
  rw [e1, e2, hPv, hGv, hsb] at hPG'
  exact band_rule_I D e f he hef hcop hband α β γ hγdef hrel hirr hα0 hβ0 hα' hβ' hγ' hsa hsb hsc
    hpq hpr hqr hP hQ hPG' i1 j1 hPv hGv hQv hα1 hβ1 iX kX mX Y hXQ hXY hmk s hs hYQ hXne hXang
    i2 j2 hγ2 hb2 hb2a hb2b

#print axioms band_I_word

#print axioms band_S_word

end Erdos634.LaczJunction
