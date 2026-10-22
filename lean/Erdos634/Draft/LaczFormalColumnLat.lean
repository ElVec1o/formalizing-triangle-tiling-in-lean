import Erdos634.Draft.LaczFormalMJMain
import Erdos634.Draft.LaczFormalWall

/-!
# The wall frame `WFrame`: the lattice frame at a `β`-wall (Column Lemma, C1–C4)

Erdős #634, base-`β` row.  Credit: AI assistant (the Column Lemma proposal, `FABLE_MIXEDROW_2026-10-21/ANSWER.md`),
Beeson–Roșu (the tile, Lemmas 28–37), Beeson, Laczkovich, Paliy.  UNAUDITED.  Axiom-clean; no `sorry`.

`LFrame` (`LaczFormalMJLat`) is the lattice frame at the *left corner of a band target*: its leg is a side of the
target.  The induction `MJ_main` touches the target only at (i) interior lattice points, (ii) the left leg
(`leg_fig`, `ns_end_x`, `leg_front` + `no_double_gamma_S`), (iii) level 0 (`ns_start_y`, `base_front`).
`WFrame` replaces the target-specific fields of `LFrame` by hypotheses about a `β`-WALL, i.e. an interior straight
segment `{O + y v : 0 < y < μ}` in the direction `v` (`|v| = a`, the direction `u_β`) *crossed by no tile*:

* `hint` (the arena): the lattice points `O + x e0 + y v`, `x, y > 0`, `x/λ + y/μ < 1` lie in the interior of the
  target of `D` (`λ, μ` are only extents of the lattice triangle that the induction uses);
* `hside` (the wall): a tile containing a wall point lies wholly in one closed side of the line `{cross v z = cross v O}`;
* `hsum` (the one-sided angle sum): at a wall point the tiles in the closed right side `{cross v z ≤ cross v O}` have
  angles summing to `π` (for an interior wall this is `Erdos634.HalfAngle.half_angle_sum`: `hsum_of_interior`;
  for a leg of the target it is the boundary angle sum).

Nothing else about the target is used (the target `D.target` stays only as the ambient region of `interior`).
`LFrame` gives a `WFrame` (`ofLFrame`, `LaczFormalColumnWit`): `WFrame` is a genuine generalisation.
The induction is restricted to levels `lv ≥ 1`: level 0 is the target base, which a wall frame does not have.
-/

namespace Erdos634.LaczCol

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.LaczJunction Erdos634.LaczJunction.Walk
  Erdos634.LaczJunction.Grammar Erdos634.Draft.TraceCovering Erdos634.LaczMJ Erdos634.LaczWall Erdos634.VertexFigureReal Set

variable {N : ℕ}

/-- The lattice frame at a `β`-wall of a (band) dissection. -/
structure WFrame (D : CongruentDissection N) (e f : ℕ) (α β γ : ℝ) (p q r : Fin 3) where
  S : BandSetup D e f α β γ p q r
  O : Plane
  e0 : Plane
  v : Plane
  he0 : ‖e0‖ = (tc e f : ℝ)
  hv : ‖v‖ = (ta e f : ℝ)
  hu : ‖v - e0‖ = (tb e f : ℝ)
  hcr : 0 < cross e0 v
  lam : ℝ
  mu : ℝ
  hlam : 0 < lam
  hmu : 0 < mu
  /-- the arena: lattice points of the open triangle `x, y > 0`, `x/λ + y/μ < 1` are interior to the target. -/
  hint : ∀ x y : ℝ, 0 < x → 0 < y → x / lam + y / mu < 1 →
    (O + x • e0 + y • v) ∈ interior D.target.carrier
  /-- the wall: a tile through a wall point lies wholly on one closed side of the wall line. -/
  hside : ∀ y : ℝ, 0 < y → y < mu → ∀ i : Fin N, (O + y • v) ∈ (D.tile i).carrier →
    (D.tile i).carrier ⊆ {z | (crossL v) z ≤ cross v O} ∨ (D.tile i).carrier ⊆ {z | cross v O ≤ (crossL v) z}
  /-- the one-sided angle sum at the wall points. -/
  hsum : ∀ y : ℝ, 0 < y → y < mu →
    ∑ i ∈ Side D.toDissection (crossL v) (cross v O), (D.tile i).localAngle (O + y • v) = Real.pi

theorem wall_figure_sum {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ} {p q r : Fin 3}
    (S : BandSetup D e f α β γ p q r) (g : Plane →ₗ[ℝ] ℝ) (c : ℝ) {x : Plane}
    (hsum : ∑ i ∈ Side D.toDissection g c, (D.tile i).localAngle x = Real.pi) :
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


namespace WFrame

variable {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ} {p q r : Fin 3}
  (F : WFrame D e f α β γ p q r)

/-- The lattice point `O + x e0 + y v`. -/
def pt (x y : ℝ) : Plane := F.O + x • F.e0 + y • F.v

theorem pt_interior {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (hxy : x / F.lam + y / F.mu < 1) :
    F.pt x y ∈ interior D.target.carrier := F.hint x y hx hy hxy

/-- The wall functional and its level. -/
noncomputable def wg : Plane →ₗ[ℝ] ℝ := crossL F.v

noncomputable def wc : ℝ := cross F.v F.O

theorem wg_pt (x y : ℝ) : F.wg (F.pt x y) = F.wc - x * cross F.e0 F.v := by
  simp only [wg, wc, crossL_apply, pt, cross, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring

theorem wall_pt (y : ℝ) : F.O + y • F.v = F.pt 0 y := by simp [pt]

/-- The wall points have `wg = wc`. -/
theorem wg_wall (y : ℝ) : F.wg (F.pt 0 y) = F.wc := by rw [F.wg_pt]; ring

/-- `Side` is the closed right side `{x ≥ 0}`. -/
theorem mem_Side_iff {i : Fin N} :
    i ∈ Side D.toDissection F.wg F.wc ↔ (D.tile i).carrier ⊆ {z | F.wg z ≤ F.wc} := mem_Side

theorem hside' {y : ℝ} (h0 : 0 < y) (h1 : y < F.mu) {i : Fin N} (hi : F.pt 0 y ∈ (D.tile i).carrier) :
    (D.tile i).carrier ⊆ {z | F.wg z ≤ F.wc} ∨ (D.tile i).carrier ⊆ {z | F.wc ≤ F.wg z} :=
  F.hside y h0 h1 i (by rw [F.wall_pt]; exact hi)

theorem hsum' {y : ℝ} (h0 : 0 < y) (h1 : y < F.mu) :
    ∑ i ∈ Side D.toDissection F.wg F.wc, (D.tile i).localAngle (F.pt 0 y) = Real.pi := by
  have := F.hsum y h0 h1
  rw [F.wall_pt] at this
  exact this

/-- A tile with a vertex on the wall and a vertex strictly to the right of it is a side tile. -/
theorem tile_mem_Side {i : Fin N} {y x' y' : ℝ} (h0 : 0 < y) (h1 : y < F.mu) (hx' : 0 < x')
    (hA : ∃ k, (D.tile i).pts k = F.pt 0 y) (hB : ∃ k, (D.tile i).pts k = F.pt x' y') :
    i ∈ Side D.toDissection F.wg F.wc := by
  obtain ⟨k, hk⟩ := hA
  obtain ⟨k', hk'⟩ := hB
  have hAt : F.pt 0 y ∈ (D.tile i).carrier := by
    rw [← hk]; exact subset_convexHull ℝ _ ⟨_, rfl⟩
  have hBt : F.pt x' y' ∈ (D.tile i).carrier := by
    rw [← hk']; exact subset_convexHull ℝ _ ⟨_, rfl⟩
  rw [F.mem_Side_iff]
  rcases F.hside' h0 h1 hAt with h | h
  · exact h
  · exfalso
    have := h hBt
    simp only [Set.mem_setOf_eq] at this
    rw [F.wg_pt] at this
    have := F.hcr
    nlinarith

theorem cramer2 (a b w : Plane) : cross a b • w = cross w b • a + cross a w • b := by
  ext i; fin_cases i <;> simp [cross] <;> ring

theorem w_zero_of (F : WFrame D e f α β γ p q r) {w : Plane} (h1 : cross F.v w = 0) (h2 : cross F.e0 w = 0) :
    w = 0 := by
  have h := cramer2 F.e0 F.v w
  have h3 : cross w F.v = 0 := by
    have : cross w F.v = -cross F.v w := by simp [cross]; ring
    rw [this, h1]; simp
  rw [h3, h2] at h
  simp only [zero_smul, add_zero] at h
  rcases smul_eq_zero.mp h with h' | h'
  · exact absurd h' F.hcr.ne'
  · exact h'

/-- Transversality of the wall with the horizontal line. -/
theorem trans_e0 : ∀ w, F.wg w = 0 → (crossL (-F.e0) : Plane →ₗ[ℝ] ℝ) w = 0 → w = 0 := by
  intro w h1 h2
  simp only [wg, crossL_apply] at h1 h2
  refine F.w_zero_of h1 ?_
  have : cross (-F.e0) w = -cross F.e0 w := by simp [cross]; ring
  linarith

theorem trans_u : ∀ w, F.wg w = 0 → (crossL (F.v - F.e0) : Plane →ₗ[ℝ] ℝ) w = 0 → w = 0 := by
  intro w h1 h2
  simp only [wg, crossL_apply] at h1 h2
  refine F.w_zero_of h1 ?_
  have : cross (F.v - F.e0) w = cross F.v w - cross F.e0 w := by simp [cross]; ring
  linarith

/-- **The wall version of `ns_end_x`**: no chain edge of a transversal line passes through a wall point. -/
theorem ns_wall (k : Plane →ₗ[ℝ] ℝ) (d : ℝ) (htrans : ∀ w, F.wg w = 0 → k w = 0 → w = 0) {y : ℝ}
    (h0 : 0 < y) (h1 : y < F.mu) : ¬ Straddled D.toDissection k d (F.pt 0 y) :=
  wall_not_straddled D.toDissection F.wg k F.wc d (F.wg_wall y) htrans (fun i hi => F.hside' h0 h1 hi)

/-- **The wall figure at a wall point** (the wall version of `leg_fig`): if a side tile presents `γ` and a side tile
presents `α`, exactly one side tile presents each of `α, β, γ` and none presents `π`. -/
theorem wall_fig {y : ℝ} (h0 : 0 < y) (h1 : y < F.mu) {iγ iα : Fin N}
    (hiγ : iγ ∈ Side D.toDissection F.wg F.wc) (hiα : iα ∈ Side D.toDissection F.wg F.wc)
    (hγ : (D.tile iγ).localAngle (F.pt 0 y) = γ) (hα : (D.tile iα).localAngle (F.pt 0 y) = α) :
    scnt D.toDissection F.wg F.wc (F.pt 0 y) α = 1 ∧ scnt D.toDissection F.wg F.wc (F.pt 0 y) β = 1 ∧
      scnt D.toDissection F.wg F.wc (F.pt 0 y) γ = 1 ∧ scnt D.toDissection F.wg F.wc (F.pt 0 y) Real.pi = 0 := by
  have c1 := scnt_ge_one hiγ hγ
  have c2 := scnt_ge_one hiα hα
  rcases wall_figure_sum F.S F.wg F.wc (F.hsum' h0 h1) with h | h | h <;> omega

end WFrame

end Erdos634.LaczCol
