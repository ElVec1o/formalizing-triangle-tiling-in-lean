import Erdos634.Draft.LaczFormalMJFig
import Erdos634.Draft.HalfAngle

/-!
# The Wall Lemma, first layer: the one-sided vertex figure and the transversal non-straddling lemma

Erdős #634, base-`β` band, rule `M(j)` at a β-wall.  Credit: AI assistant (the Wall Lemma proposal,
`FABLE_PROPAGATE_2026-10-21`, Idea 3), Beeson–Roșu (the tile, vertex figures), Beeson, Laczkovich
(fan/chord covers), Paliy; `Erdos634.HalfAngle.half_angle_sum` (the one-sided angle sum) is used as it stands.
UNAUDITED.  Axiom-clean; no `sorry`.

The `M(j)` induction (`LaczFormalMJ*`) touches the left leg of the target in exactly three kinds of places:

* (F) the **vertex figure at a leg point** (`leg_fig`, `bfig`: boundary figure, angle sum `π`);
* (E) **the line leaves the target** past a leg point or below the base (`ns_end_x`, `ns_start_y`);
* (I) **lattice points are interior / on the frontier of the target** (`pt_interior`, `chord_interior`, `Bnd`).

This file supplies the wall replacement of (F) and (E), for a wall = a straight line `{f = c}` such that every tile
meeting a stretch of it lies wholly on one closed side:

* `wall_side_sum`: at an interior point `p` of the wall, the tiles on the closed side `{f ≤ c}` have angles
  summing to `π` (this is `half_angle_sum`);
* `wall_figure`: hence on that side the figure at `p` is `π`, or `{3α,2β}`, or `{α,β,γ}` — exactly the boundary
  figure, now for the side tiles (`scnt` counts side tiles only);
* `wall_leg_fig`: the wall version of `leg_fig`: if a side tile presents `γ` and a side tile presents `α` at `p`,
  exactly one side tile presents each of `α, β, γ`, none presents `π`;
* `wall_not_straddled`: a line transversal to the wall is not straddled at a point of the open wall (an edge
  through that point would cross the wall) — the wall version of `ns_end_x`.

NOT done here: the frame constructor (the structure `LFrame` carries the target corner fields `lam, mu, hq, hr`,
and (I) is stated in them); see the report of room `LEAN_WALL_2026-10-21`.
-/

namespace Erdos634.LaczWall

open Erdos634.Geometry Erdos634.VertexFigureReal Erdos634.LaczMJ Erdos634.LaczJunction
  Erdos634.LaczJunction.Walk Erdos634.Draft.TraceCovering Set

variable {N : ℕ}

open Classical in
/-- The tiles lying wholly on the closed side `{f ≤ c}`. -/
noncomputable def Side (D : Dissection N) (f : Plane →ₗ[ℝ] ℝ) (c : ℝ) : Finset (Fin N) :=
  Finset.univ.filter (fun i => (D.tile i).carrier ⊆ {y | f y ≤ c})

open Classical in
/-- The number of side tiles whose local angle at `v` is `θ`. -/
noncomputable def scnt (D : Dissection N) (f : Plane →ₗ[ℝ] ℝ) (c : ℝ) (v : Plane) (θ : ℝ) : ℕ :=
  ((Side D f c).filter (fun i => (D.tile i).localAngle v = θ)).card

theorem mem_Side {D : Dissection N} {f : Plane →ₗ[ℝ] ℝ} {c : ℝ} {i : Fin N} :
    i ∈ Side D f c ↔ (D.tile i).carrier ⊆ {y | f y ≤ c} := by
  classical
  simp [Side]

theorem scnt_ge_one {D : Dissection N} {f : Plane →ₗ[ℝ] ℝ} {c : ℝ} {v : Plane} {θ : ℝ} {i : Fin N}
    (hi : i ∈ Side D f c) (h : (D.tile i).localAngle v = θ) : 1 ≤ scnt D f c v θ := by
  classical
  unfold scnt
  exact Finset.card_pos.mpr ⟨i, by simp [hi, h]⟩

theorem scnt_ge_two {D : Dissection N} {f : Plane →ₗ[ℝ] ℝ} {c : ℝ} {v : Plane} {θ : ℝ} {i j : Fin N}
    (hij : i ≠ j) (hi : i ∈ Side D f c) (hj : j ∈ Side D f c) (hi' : (D.tile i).localAngle v = θ)
    (hj' : (D.tile j).localAngle v = θ) : 2 ≤ scnt D f c v θ := by
  classical
  unfold scnt
  exact Finset.one_lt_card.mpr ⟨i, by simp [hi, hi'], j, by simp [hj, hj'], hij⟩

/-- Counting a sum over a finset by its values. -/
theorem sum_on_by_value {ι : Type*} [DecidableEq ι] (s : Finset ι) (S : Finset ℝ) (g : ι → ℝ)
    (h : ∀ i ∈ s, g i ∈ S) :
    ∑ i ∈ s, g i = ∑ v ∈ S, (((s.filter (fun i => g i = v)).card : ℕ) : ℝ) * v := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to h g]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Finset.sum_congr rfl (fun i hi => (Finset.mem_filter.mp hi).2), Finset.sum_const, nsmul_eq_mul]

/-- **The one-sided angle sum at a wall point** (`Erdos634.HalfAngle.half_angle_sum`). -/
theorem wall_side_sum (D : Dissection N) (f : Plane →ₗ[ℝ] ℝ) (hf : f ≠ 0) (c : ℝ) {p : Plane}
    (hp : f p = c) (hpint : p ∈ interior D.target.carrier)
    (hside : ∀ i, p ∈ (D.tile i).carrier →
      (D.tile i).carrier ⊆ {y | f y ≤ c} ∨ (D.tile i).carrier ⊆ {y | c ≤ f y}) :
    ∑ i ∈ Side D f c, (D.tile i).localAngle p = Real.pi := by
  classical
  have := Erdos634.HalfAngle.half_angle_sum D f hf c hp hpint hside
  unfold Side
  convert this

variable {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ} {p q r : Fin 3}

/-- **The wall figure.**  At an interior point `x` of the target lying on a wall `{g = c}` (`g ≠ 0`; every tile
containing `x` lies wholly on one closed side), the tiles on the side `{g ≤ c}` present exactly one of the boundary
figures: `π`; `{3α, 2β}`; `{α, β, γ}`. -/
theorem wall_figure (S : BandSetup D e f α β γ p q r) (g : Plane →ₗ[ℝ] ℝ) (hg : g ≠ 0) (c : ℝ) {x : Plane}
    (hx : g x = c) (hxint : x ∈ interior D.target.carrier)
    (hside : ∀ i, x ∈ (D.tile i).carrier →
      (D.tile i).carrier ⊆ {y | g y ≤ c} ∨ (D.tile i).carrier ⊆ {y | c ≤ g y}) :
    (scnt D.toDissection g c x Real.pi = 1 ∧ scnt D.toDissection g c x α = 0 ∧
        scnt D.toDissection g c x β = 0 ∧ scnt D.toDissection g c x γ = 0) ∨
    (scnt D.toDissection g c x Real.pi = 0 ∧ scnt D.toDissection g c x α = 3 ∧
        scnt D.toDissection g c x β = 2 ∧ scnt D.toDissection g c x γ = 0) ∨
    (scnt D.toDissection g c x Real.pi = 0 ∧ scnt D.toDissection g c x α = 1 ∧
        scnt D.toDissection g c x β = 1 ∧ scnt D.toDissection g c x γ = 1) := by
  classical
  obtain ⟨hapi, hbpi, hgpi, ha2, hb2, hg2, ha0, hb0, hg0⟩ := ang_ne S
  obtain ⟨hαβ, hβγ, hαγ, -, -, -⟩ := BandSetup.distinct S
  have hpi := Real.pi_pos
  have hsum := wall_side_sum D.toDissection g hg c hx hxint hside
  have hcorn := Erdos634.Geometry.Dissection.congruentDissection_hcorners D α β γ S.hα' S.hβ' S.hγ'
  have hnn : ∀ i, 0 ≤ (D.tile i).localAngle x := fun i => (D.tile i).localAngle_nonneg x
  have hvals : ∀ i ∈ Side D.toDissection g c,
      (D.tile i).localAngle x ∈ ({α, β, γ, Real.pi, 0} : Finset ℝ) := by
    intro i hi
    have h6 := interior_localAngle_mem D.toDissection α β γ hcorn x i
    simp only [Finset.mem_insert, Finset.mem_singleton] at h6 ⊢
    rcases h6 with h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exfalso
      have h1 : (D.tile i).localAngle x ≤ ∑ j ∈ Side D.toDissection g c, (D.tile j).localAngle x :=
        Finset.single_le_sum (fun j _ => hnn j) hi
      rw [hsum, h] at h1
      linarith
    · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
  rw [sum_on_by_value (Side D.toDissection g c) ({α, β, γ, Real.pi, 0} : Finset ℝ) _ hvals] at hsum
  rw [show ({α, β, γ, Real.pi, 0} : Finset ℝ)
      = insert α (insert β (insert γ (insert Real.pi {0}))) from rfl] at hsum
  rw [Finset.sum_insert (by simp [hαβ, hαγ, hapi, ha0]),
      Finset.sum_insert (by simp [hβγ, hbpi, hb0]),
      Finset.sum_insert (by simp [hgpi, hg0]),
      Finset.sum_insert (by simp [hpi.ne']), Finset.sum_singleton] at hsum
  have hs : ((scnt D.toDissection g c x α : ℕ) : ℝ) * α + ((scnt D.toDissection g c x β : ℕ) : ℝ) * β +
      ((scnt D.toDissection g c x γ : ℕ) : ℝ) * γ + ((scnt D.toDissection g c x Real.pi : ℕ) : ℝ) * Real.pi =
        Real.pi := by
    unfold scnt
    push_cast at hsum ⊢
    linarith [hsum]
  have := boundary_figure_cases S.hγdef S.hrel S.hirr _ _ _ _ hs
  rcases this with ⟨hs1, hp, hq, hr⟩ | ⟨hs0, hc⟩
  · exact Or.inl ⟨hs1, hp, hq, hr⟩
  · rcases hc with ⟨hp, hq, hr⟩ | ⟨hp, hq, hr⟩
    · exact Or.inr (Or.inl ⟨hs0, hp, hq, hr⟩)
    · exact Or.inr (Or.inr ⟨hs0, hp, hq, hr⟩)

/-- **The wall version of `leg_fig`.**  If a side tile presents `γ` and a side tile presents `α` at an interior wall
point `x`, then exactly one side tile presents each of `α`, `β`, `γ` and none presents `π`. -/
theorem wall_leg_fig (S : BandSetup D e f α β γ p q r) (g : Plane →ₗ[ℝ] ℝ) (hg : g ≠ 0) (c : ℝ) {x : Plane}
    (hx : g x = c) (hxint : x ∈ interior D.target.carrier)
    (hside : ∀ i, x ∈ (D.tile i).carrier →
      (D.tile i).carrier ⊆ {y | g y ≤ c} ∨ (D.tile i).carrier ⊆ {y | c ≤ g y})
    {iγ iα : Fin N} (hiγ : iγ ∈ Side D.toDissection g c) (hiα : iα ∈ Side D.toDissection g c)
    (hγ : (D.tile iγ).localAngle x = γ) (hα : (D.tile iα).localAngle x = α) :
    scnt D.toDissection g c x α = 1 ∧ scnt D.toDissection g c x β = 1 ∧ scnt D.toDissection g c x γ = 1 ∧
      scnt D.toDissection g c x Real.pi = 0 := by
  have h1 := scnt_ge_one hiγ hγ
  have h2 := scnt_ge_one hiα hα
  rcases wall_figure S g hg c hx hxint hside with h | h | h <;> omega

/-- **The wall version of `ns_end_x`.**  Let `x` lie on the open stretch of a wall `{g = c}` (`g x = c`), and let
`h = {k = d}` be a line through `x` transversal to it (`g w = 0 → k w = 0 → w = 0`).  If every tile containing `x`
lies wholly on one closed side of the wall, then no edge of the chain on `h` passes through `x` in its relative
interior: such an edge, together with its tile, would cross the wall. -/
theorem wall_not_straddled (D : Dissection N) (g k : Plane →ₗ[ℝ] ℝ) (c d : ℝ) {x : Plane} (hx : g x = c)
    (htrans : ∀ w, g w = 0 → k w = 0 → w = 0)
    (hside : ∀ i, x ∈ (D.tile i).carrier →
      (D.tile i).carrier ⊆ {y | g y ≤ c} ∨ (D.tile i).carrier ⊆ {y | c ≤ g y}) :
    ¬ Straddled D k d x := by
  rintro ⟨ε, hε, hxe⟩
  obtain ⟨hA, hB, -⟩ := (Dissection.mem_lineChain.mp hε)
  set A := (D.tile ε.1).pts ε.2
  set B := (D.tile ε.1).pts (ε.2 + 1)
  have hAt : A ∈ (D.tile ε.1).carrier := subset_convexHull ℝ _ ⟨_, rfl⟩
  have hBt : B ∈ (D.tile ε.1).carrier := subset_convexHull ℝ _ ⟨_, rfl⟩
  have hxt : x ∈ (D.tile ε.1).carrier :=
    (D.tile ε.1).edge_subset_carrier ε.2 (openSegment_subset_segment ℝ _ _ hxe)
  have hAB : A ≠ B := Erdos634.TilePlacement.pts_ne (D.tile ε.1) (fin3_succ_ne ε.2)
  obtain ⟨s, t, hs, ht, hst, rfl⟩ := hxe
  have hgx : g (s • A + t • B) = c := hx
  have hgx' : s * g A + t * g B = c := by simpa [map_add, map_smul] using hgx
  have hsum1 : c = (s + t) * c := by rw [hst]; ring
  have key : g A = c ∧ g B = c := by
    rcases hside ε.1 hxt with h | h
    · have h1 : g A ≤ c := h hAt
      have h2 : g B ≤ c := h hBt
      have n1 := mul_nonneg hs.le (sub_nonneg.2 h1)
      have n2 := mul_nonneg ht.le (sub_nonneg.2 h2)
      have z1 : s * (c - g A) = 0 := by nlinarith
      have z2 : t * (c - g B) = 0 := by nlinarith
      rcases mul_eq_zero.mp z1 with h | h
      · exact absurd h hs.ne'
      rcases mul_eq_zero.mp z2 with h' | h'
      · exact absurd h' ht.ne'
      constructor <;> linarith
    · have h1 : c ≤ g A := h hAt
      have h2 : c ≤ g B := h hBt
      have n1 := mul_nonneg hs.le (sub_nonneg.2 h1)
      have n2 := mul_nonneg ht.le (sub_nonneg.2 h2)
      have z1 : s * (g A - c) = 0 := by nlinarith
      have z2 : t * (g B - c) = 0 := by nlinarith
      rcases mul_eq_zero.mp z1 with h | h
      · exact absurd h hs.ne'
      rcases mul_eq_zero.mp z2 with h' | h'
      · exact absurd h' ht.ne'
      constructor <;> linarith
  apply hAB
  have hw : B - A = 0 := by
    apply htrans
    · simp [map_sub, key.1, key.2]
    · simp [map_sub, hA, hB]
  exact (sub_eq_zero.mp hw).symm

end Erdos634.LaczWall
