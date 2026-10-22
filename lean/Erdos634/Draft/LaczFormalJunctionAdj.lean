import Erdos634.Draft.LaczFormalJunctionInt

/-!
# Band junction rules: the tile adjacent to `cBA`'s `a`-edge (the input `hU` of Theorem 2)

Erdős #634, base-`β` band.  Credit: AI assistant (band lemma / item-3 proposal), Beeson–Roșu, Beeson,
Laczkovich, Paliy.

For the tile `T₁ = cBA` at an interior base point `Q`, with `a`-edge `[Q,G]`, the far side of the
line `QG` starts at `Q` with a tile edge: `exists_start_edge`.  That tile `U` presents a corner at
`Q`; the boundary figure at `Q` (`{3α,2β}` or `{α,β,γ}`, containing `cBA`'s `β` and the left
neighbour's `β`/`γ`) makes it an `α`-corner, so its edge along `QG` has length `b` or `c`, longer
than `a`.  Hence `G` is strictly inside an edge of `U`.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.LaczJunction

open Erdos634.Geometry Erdos634.Draft.TraceCovering Erdos634.TilePlacement Erdos634.CornerBaseEdgesReal Erdos634.Geometry.Dissection Set

variable {N : ℕ}

/-- A functional vanishing on the edge `[A,B]` of a tile, with the third vertex strictly below. -/
theorem side_functional (T1 : Tri) (j : Fin 3) {A B : Plane} (hA : T1.pts j = A)
    (hB : T1.pts (j+1) = B) :
    ∃ (f : Plane →ₗ[ℝ] ℝ) (c : ℝ), f ≠ 0 ∧ f A = c ∧ f B = c ∧ f (T1.pts (j+2)) < c := by
  have hne : A ≠ B := by
    rw [← hA, ← hB]; exact T1.indep.injective.ne (fin3_succ_ne j)
  have hdet : cross (B - A) (T1.pts (j+2) - A) = T1.det := by
    have := T1.det_cyclic j
    rwa [hA, hB] at this
  have hdet0 : T1.det ≠ 0 := T1.det_ne_zero
  have hu0 : B - A ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  have hcrossne : crossL (B - A) ≠ 0 := by
    intro h
    apply hu0
    apply eq_zero_of_cross_eq_zero
    intro v
    have := congrArg (fun g : Plane →ₗ[ℝ] ℝ => g v) h
    simpa using this
  have hBA : crossL (B - A) B = crossL (B - A) A := by
    have : cross (B - A) (B - A) = 0 := cross_self _
    rw [cross_sub_right] at this
    simpa using (sub_eq_zero.mp this)
  have hVc : crossL (B - A) (T1.pts (j+2)) - crossL (B - A) A = T1.det := by
    rw [crossL_apply, crossL_apply, ← cross_sub_right, hdet]
  rcases lt_or_gt_of_ne hdet0 with hneg | hpos
  · exact ⟨crossL (B - A), crossL (B - A) A, hcrossne, rfl, hBA, by linarith⟩
  · refine ⟨-crossL (B - A), -crossL (B - A) A, ?_, rfl, ?_, ?_⟩
    · intro h; apply hcrossne; simpa using h
    · simp [hBA]
    · simp only [LinearMap.neg_apply]; linarith

/-- **The far side of a wall starts with an edge at the start point.**  If the open stretch
`(X, X + a•u)` is a wall inside the target and no far-side edge passes through `X`, some far-side
chain edge has its lower end exactly at `X`. -/
theorem exists_start_edge (D : Dissection N) {X u : Plane} {f : Plane →ₗ[ℝ] ℝ} {c a : ℝ}
    (hf0 : f ≠ 0) (hX : f X = c) (hu : f u = 0) (hu1 : ‖u‖ = 1) (ha : 0 < a)
    (hint : ∀ x ∈ Ioo 0 a, X + x • u ∈ interior D.target.carrier)
    (hwall : ∀ x ∈ Ioo 0 a, ∀ i, X + x • u ∉ interior (D.tile i).carrier)
    (hs : ¬ Straddled D (-f) (-c) X) :
    ∃ e ∈ D.lineChain (-f) (-c), lo D X u e = 0 ∧ 0 < hi D X u e := by
  classical
  have hu0 := ne_zero_of_norm hu1
  have hnf : (-f : Plane →ₗ[ℝ] ℝ) ≠ 0 := fun h => hf0 (neg_eq_zero.mp h)
  have hgd : ∀ y, (-f) y = -c ↔ f y = c := neg_iff
  have hs' : ¬ PStr (D.lineChain (-f) (-c)) (lo D X u) (hi D X u) 0 := by
    have := (str_iff (D := D) hgd hf0 hX hu hu0 0).not.mp
    apply this
    rw [zero_smul, add_zero]; exact hs
  by_contra H
  push_neg at H
  set S := D.lineChain (-f) (-c) with hS
  have hlt : ∀ e ∈ S, lo D X u e < hi D X u e := fun e he =>
    (edge_data hf0 hX hu hu0 (onLine hgd he).1 (onLine hgd he).2).1
  -- a positive lower bound for the positive `lo`'s
  obtain ⟨δ, hδ, hδle⟩ : ∃ δ > 0, ∀ e ∈ S, 0 < lo D X u e → δ ≤ lo D X u e := by
    by_cases hne : (S.filter fun e => 0 < lo D X u e).Nonempty
    · obtain ⟨e, he, hmin⟩ := Finset.exists_min_image _ (lo D X u) hne
      refine ⟨lo D X u e, (Finset.mem_filter.mp he).2, fun e' he' hpos => ?_⟩
      exact hmin e' (Finset.mem_filter.mpr ⟨he', hpos⟩)
    · refine ⟨1, one_pos, fun e he hpos => ?_⟩
      exact absurd ⟨e, Finset.mem_filter.mpr ⟨he, hpos⟩⟩ hne
  have hfin := finite_vertex_params (D := D) (X := X) hu0
  have hinf : (Ioo (0:ℝ) (min δ a)).Infinite := Set.Ioo_infinite (lt_min hδ ha)
  obtain ⟨x, hx, hxv⟩ := hinf.exists_notMem_finite hfin
  have hxa : x ∈ Ioo (0:ℝ) a := ⟨hx.1, lt_of_lt_of_le hx.2 (min_le_right _ _)⟩
  have hcov := wall_cover_param (D := D) hnf hgd hf0 hX hu hu0 ha hint hwall hxa hxv
  obtain ⟨e, he, h1, h2⟩ := hcov
  rcases lt_trichotomy (lo D X u e) 0 with hneg | hzero | hpos
  · exact hs' ⟨e, he, hneg, lt_of_lt_of_le hx.1 h2⟩
  · exact (H e he hzero).not_gt (lt_of_lt_of_le hx.1 h2)
  · have := hδle e he hpos
    have := lt_of_lt_of_le hx.2 (min_le_left _ _)
    linarith

/-- **Corner angle and opposite side go together.**  At each vertex of a tile, the corner angle is
`α` with opposite side `a`, `β` with `b`, or `γ` with `c`. -/
theorem tile_vertex_angle_cases (D : CongruentDissection N) (α β γ : ℝ)
    (hα' : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hβ' : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hγ' : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    (i : Fin N) (j : Fin 3) :
    ((D.tile i).localAngle ((D.tile i).pts j) = α ∧
        dist ((D.tile i).pts (j+1)) ((D.tile i).pts (j+2)) = sideOpp D.model 0) ∨
    ((D.tile i).localAngle ((D.tile i).pts j) = β ∧
        dist ((D.tile i).pts (j+1)) ((D.tile i).pts (j+2)) = sideOpp D.model 1) ∨
    ((D.tile i).localAngle ((D.tile i).pts j) = γ ∧
        dist ((D.tile i).pts (j+1)) ((D.tile i).pts (j+2)) = sideOpp D.model 2) := by
  obtain ⟨k0, hk0angle, hk0side⟩ := congruent_opposite_side (D.tiles_congruent i).symm j
  rw [Tri.localAngle_vertex, hk0angle]
  fin_cases k0
  · left; exact ⟨hα', by rw [← hk0side]; simp [sideOpp]⟩
  · right; left; exact ⟨hβ', by rw [← hk0side]; simp [sideOpp]⟩
  · right; right; exact ⟨hγ', by rw [← hk0side]; simp [sideOpp]⟩

/-- An `α`-corner of a tile has both incident edges of length `b` or `c` (never `a`). -/
theorem alpha_vertex_edges (D : CongruentDissection N) (α β γ : ℝ)
    (hα' : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hβ' : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hγ' : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    (hαβ : α ≠ β) (hαγ : α ≠ γ)
    (hab : sideOpp D.model 0 ≠ sideOpp D.model 1) (hac : sideOpp D.model 0 ≠ sideOpp D.model 2)
    (i : Fin N) (j : Fin 3) (h : (D.tile i).localAngle ((D.tile i).pts j) = α) :
    (dist ((D.tile i).pts j) ((D.tile i).pts (j+1)) = sideOpp D.model 1 ∨
       dist ((D.tile i).pts j) ((D.tile i).pts (j+1)) = sideOpp D.model 2) ∧
    (dist ((D.tile i).pts (j+2)) ((D.tile i).pts j) = sideOpp D.model 1 ∨
       dist ((D.tile i).pts (j+2)) ((D.tile i).pts j) = sideOpp D.model 2) := by
  have hz : dist ((D.tile i).pts (j+1)) ((D.tile i).pts (j+2)) = sideOpp D.model 0 := by
    rcases tile_vertex_angle_cases D α β γ hα' hβ' hγ' i j with ⟨_, h1⟩ | ⟨h1, _⟩ | ⟨h1, _⟩
    · exact h1
    · exact absurd (h.symm.trans h1) hαβ
    · exact absurd (h.symm.trans h1) hαγ
  have hm := tile_multiset D i j
  have hcount := congrArg (Multiset.count (sideOpp D.model 0)) hm
  have hx : dist ((D.tile i).pts j) ((D.tile i).pts (j+1)) ∈
      ({sideOpp D.model 2, sideOpp D.model 1, sideOpp D.model 0} : Multiset ℝ) := by
    rw [← hm]; simp
  have hy : dist ((D.tile i).pts (j+2)) ((D.tile i).pts j) ∈
      ({sideOpp D.model 2, sideOpp D.model 1, sideOpp D.model 0} : Multiset ℝ) := by
    rw [← hm]; simp
  simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hx hy
  rw [hz] at hcount
  constructor
  · rcases hx with h1 | h1 | h1
    · exact Or.inr h1
    · exact Or.inl h1
    · exfalso
      simp [Multiset.count_cons, h1, hab, hac] at hcount <;> split_ifs at hcount <;> omega
  · rcases hy with h1 | h1 | h1
    · exact Or.inr h1
    · exact Or.inl h1
    · exfalso
      simp [Multiset.count_cons, h1, hab, hac] at hcount <;> split_ifs at hcount <;> omega

/-- **The figure at `Q` forces an `α`-corner.**  At a non-vertex frontier point `Q` carrying a `β`
corner (`i1`) and a second tile `iX ≠ i1` presenting `β` or `γ`, any third tile `iU` with a corner
at `Q` presents `α`. -/
theorem alpha_corner_of_figure (D : CongruentDissection N) (α β γ : ℝ)
    (hγdef : γ = 2 * α + β) (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hα0 : 0 < α) (hβ0 : 0 < β)
    (hα' : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hβ' : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hγ' : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    {Q : Plane} (hfront : Q ∈ frontier D.target.carrier) (hnv : Q ∉ Set.range D.target.pts)
    (i1 iX iU : Fin N) (h1 : (D.tile i1).localAngle Q = β)
    (hX : (D.tile iX).localAngle Q = β ∨ (D.tile iX).localAngle Q = γ) (hXne : iX ≠ i1)
    (hUne1 : iU ≠ i1) (hUneX : iU ≠ iX)
    (hU : (D.tile iU).localAngle Q = α ∨ (D.tile iU).localAngle Q = β ∨
      (D.tile iU).localAngle Q = γ) :
    (D.tile iU).localAngle Q = α := by
  classical
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
    hfront hnv i1 (Or.inr (Or.inl h1))
  have mem : ∀ (θ : ℝ) (i : Fin N), (D.tile i).localAngle Q = θ ↔
      i ∈ ({i | (D.tile i).localAngle Q = θ} : Finset (Fin N)) := by
    intro θ i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
  rcases hU with hUα | hUβ | hUγ
  · exact hUα
  · exfalso
    rcases hfig with ⟨_, hbc, hg0⟩ | ⟨_, hbc, hgc⟩
    · -- (3,2,0)
      have hXβ : (D.tile iX).localAngle Q = β := by
        rcases hX with h | h
        · exact h
        · exfalso
          have := (mem γ iX).mp h
          rw [Finset.card_eq_zero.mp hg0] at this; simp at this
      have hsub : ({i1, iX, iU} : Finset (Fin N)) ⊆
          ({i | (D.tile i).localAngle Q = β} : Finset (Fin N)) := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl
        · exact (mem β _).mp h1
        · exact (mem β _).mp hXβ
        · exact (mem β _).mp hUβ
      have h3 : ({i1, iX, iU} : Finset (Fin N)).card = 3 :=
        Finset.card_eq_three.mpr ⟨i1, iX, iU, hXne.symm, hUne1.symm, hUneX.symm, rfl⟩
      have := Finset.card_le_card hsub
      omega
    · -- (1,1,1)
      have := Finset.card_le_one.mp hbc.le
      exact hUne1 (this _ ((mem β _).mp hUβ) _ ((mem β _).mp h1))
  · exfalso
    rcases hfig with ⟨_, _, hg0⟩ | ⟨_, hbc, hgc⟩
    · have := (mem γ iU).mp hUγ
      rw [Finset.card_eq_zero.mp hg0] at this; simp at this
    · rcases hX with hXβ | hXγ
      · have := Finset.card_le_one.mp hbc.le
        exact hXne (this _ ((mem β _).mp hXβ) _ ((mem β _).mp h1))
      · have := Finset.card_le_one.mp hgc.le
        exact hUneX (this _ ((mem γ _).mp hUγ) _ ((mem γ _).mp hXγ))

end Erdos634.LaczJunction
