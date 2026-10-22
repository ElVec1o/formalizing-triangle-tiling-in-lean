-- Draft/FluxDRow4L8Recovered.lean — RECOVERY (2026-09-26) of the pre-P88 Draft/FluxDRow4L8.lean
-- (built 2026-09-24 by subagent a05297c391d16a52e, overwritten 2026-09-26 11:04, EVIDENCE P88).
-- Reconstructed byte-for-byte by replaying a session's recorded Write (transcript line 589) and its
-- five python edits + one sed (lines 599-632) from its session transcript; final state 631 lines,
-- same 18 declaration names as the surviving 2026-09-24 axiom log. Only this comment block is new.
-- Existence check before writing: `ls -la` → No such file; not in All.lean.
-- Formalization debt on a paper-level-PROVED result; not /goal progress. Not in All.lean.
-- Draft/FluxDRow4L8.lean — ROW 4, L8's `{a, c}` HALF ((private working notes, not included) §3 "L8,
-- Leg = {a, c}") on a real `CongruentDissection`, with L1's corner figures at `A` and `B`.
-- Imported via AllNew8.lean → All.lean:853 (stale "NOT imported" header corrected 2026-10-04).
--
-- * `Row4.fig_arith` (L1's arithmetic): `Pα + Q(π−3α) + R·2α + Sπ + T·2π = jπ + kα` with `α ∉ ℚπ`
--   forces `Q + S + 2T = j`, `P − 3Q + 2R = k`.
-- * `Row4.corner_A` / `Row4.corner_B` (L1 at the corners, real dissection): no tile presents `β` or `γ`
--   at a base corner (angle `α`); at the apex `B` (angle `π − 2α`) no tile presents `γ` and at most one
--   presents `β` — through `Dissection.sum_localAngle_eq` and `VertexFigureReal.sum_by_value`.
-- * `Row4.a_edge_ends`: an edge of length `a` of a real tile has `β`/`γ` at its ends (the model is
--   scalene: `Row4.scalene`, using `α ≠ π/4, π/5`).
-- * `Row4.endpoint_of_subsegment`: a target vertex on a tile edge inside a target side is an end of it.
-- * `Row4.L8_ac`: if BOTH legs have the typed word `{a, c}` (side counts `(1, 0, 1)`), then — the
--   a-edge of each leg cannot end at the base corner (its end angle would be `β`/`γ` there), so it ends
--   at `B` with `β`; the two tiles differ (`sideEdges_disjoint`, one a-edge per tile) — `B` receives two
--   `β`: contradiction.  This is the file's `{a, c}` argument, with the corner tile at `A` replaced by
--   the equivalent end-angle count (named deviation).
-- NOT FORMALIZED (named blocker): L8's `b^k` half (Beeson's Case 2): it needs the POSITIONS of the `k`
-- b-edges along a leg (every junction at a multiple of `b`, so only `k − 1` interior junctions for the
-- `k` γ-corners) — the corpus has no ordered side chain (`EdgeChain.side_walk` is an unordered
-- partition).  So R4(ii) ("N is not prime") is reduced to that half, not closed.
--
-- CONDITIONAL AT THE GEOMETRIC LEVEL (no Lean tiling of this target; DESIGN.md §5).  Witnesses
-- (Draft/FluxDRow4L8Witness.lean) cover the arithmetic lemmas (`fig_arith` at the corner figures of
-- the file: `(1,0,0)` at `A`, `(1,1,0)` at `B`, `(1,1,1)`/`(3,1,0)` on a side) and `endpoint_of_subsegment`.
--
-- Formalization debt; not progress on the three /goal outcomes.
import Erdos634.Draft.FluxDRow4
import Erdos634.Draft.FluxDRow2S1
import Erdos634.VertexFigureReal
import Erdos634.PinPlumbing

open scoped Classical

namespace Erdos634.Geometry

variable {N : ℕ}

/-! ## L1's arithmetic -/

/-- `α ∉ ℚπ` separates the coefficients of `π` and `α`. -/
theorem Row4.coeff_split {α : ℝ} (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) {x y : ℤ}
    (h : (x : ℝ) * Real.pi + (y : ℝ) * α = 0) : x = 0 ∧ y = 0 := by
  by_cases hy : y = 0
  · subst hy
    have h' : (x : ℝ) * Real.pi = 0 := by simpa using h
    have hx : (x : ℝ) = 0 := (mul_eq_zero.mp h').resolve_right Real.pi_ne_zero
    exact ⟨by exact_mod_cast hx, rfl⟩
  · exfalso
    apply hα
    have hy' : (y : ℝ) ≠ 0 := by exact_mod_cast hy
    refine ⟨-x / y, ?_⟩
    push_cast
    rw [div_mul_eq_mul_div, eq_div_iff hy']
    linarith

/-- **L1's arithmetic** for the `γ = 2α` tile. -/
theorem Row4.fig_arith {α : ℝ} (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) {P Q R S T : ℕ} {j k : ℤ}
    (h : (P : ℝ) * α + (Q : ℝ) * (Real.pi - 3 * α) + (R : ℝ) * (2 * α) + (S : ℝ) * Real.pi
      + (T : ℝ) * (2 * Real.pi) = (j : ℝ) * Real.pi + (k : ℝ) * α) :
    (Q : ℤ) + S + 2 * T = j ∧ (P : ℤ) - 3 * Q + 2 * R = k := by
  have := Row4.coeff_split hα (x := (Q : ℤ) + S + 2 * T - j) (y := (P : ℤ) - 3 * Q + 2 * R - k)
    (by push_cast; linear_combination h)
  omega

/-! ## Angles of real tiles -/

/-- Every corner angle of a real tile is `α`, `π − 3α` or `2α`. -/
theorem Row4.tile_angle_mem (D : CongruentDissection N) {α a b c : ℝ}
    (h : D.model.TwoAlphaData α a b c) (i : Fin N) (j : Fin 3) :
    (D.tile i).angleAt j = α ∨ (D.tile i).angleAt j = Real.pi - 3 * α ∨
      (D.tile i).angleAt j = 2 * α := by
  obtain ⟨σ', hσ'⟩ := (D.tiles_congruent i).exists_perm
  obtain ⟨σ, h0, -, h1, -, h2, -⟩ := h
  rw [(hσ' j).1]
  obtain ⟨m, hm⟩ := σ.surjective (σ' j)
  rw [← hm]
  have hm3 : m = 0 ∨ m = 1 ∨ m = 2 := by fin_cases m <;> simp
  rcases hm3 with rfl | rfl | rfl
  · exact Or.inl h0
  · exact Or.inr (Or.inl h1)
  · exact Or.inr (Or.inr h2)

/-- Every local angle of a real tile is one of `α, π − 3α, 2α, π, 2π, 0`. -/
theorem Row4.localAngle_mem (D : CongruentDissection N) {α a b c : ℝ}
    (h : D.model.TwoAlphaData α a b c) (v : Plane) (i : Fin N) :
    (D.tile i).localAngle v
      ∈ ({α, Real.pi - 3 * α, 2 * α, Real.pi, 2 * Real.pi, 0} : Finset ℝ) := by
  rcases Erdos634.PinPlumbing.localAngle_cases (D.tile i) v with ⟨j, -, hval⟩ | h2 | h1 | h0
  · rw [hval]
    show (D.tile i).angleAt j ∈ _
    rcases Row4.tile_angle_mem D h i j with e | e | e <;> rw [e] <;> simp
  · rw [h2]; simp
  · rw [h1]; simp
  · rw [h0]; simp

/-- **The count equation** at any point: the tiles' local angles, grouped by value. -/
theorem Row4.count_eq (D : CongruentDissection N) {α a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (h : D.model.TwoAlphaData α a b c)
    (hα0 : 0 < α) (hα3 : α < Real.pi / 3) (v : Plane) :
    D.target.localAngle v
      = (({i | (D.tile i).localAngle v = α} : Finset (Fin N)).card : ℝ) * α
        + (({i | (D.tile i).localAngle v = Real.pi - 3 * α} : Finset (Fin N)).card : ℝ)
          * (Real.pi - 3 * α)
        + (({i | (D.tile i).localAngle v = 2 * α} : Finset (Fin N)).card : ℝ) * (2 * α)
        + (({i | (D.tile i).localAngle v = Real.pi} : Finset (Fin N)).card : ℝ) * Real.pi
        + (({i | (D.tile i).localAngle v = 2 * Real.pi} : Finset (Fin N)).card : ℝ)
          * (2 * Real.pi) := by
  have hπ := Real.pi_pos
  have d1 : α ≠ Real.pi - 3 * α := fun e => hα ⟨1 / 4, by push_cast; linarith⟩
  have d6 : Real.pi - 3 * α ≠ 2 * α := fun e => hα ⟨1 / 5, by push_cast; linarith⟩
  have hsum := D.toDissection.sum_localAngle_eq v
  rw [Erdos634.VertexFigureReal.sum_by_value _ _ (Row4.localAngle_mem D h v)] at hsum
  rw [Finset.sum_insert (by simp [d1, (by linarith : α ≠ 2 * α), (by linarith : α ≠ Real.pi),
      (by linarith : α ≠ 2 * Real.pi), (by linarith : α ≠ 0)]),
    Finset.sum_insert (by simp [d6, (by linarith : Real.pi - 3 * α ≠ Real.pi),
      (by linarith : Real.pi - 3 * α ≠ 2 * Real.pi), (by linarith : Real.pi - 3 * α ≠ 0)]),
    Finset.sum_insert (by simp [(by linarith : 2 * α ≠ Real.pi), (by linarith : 2 * α ≠ 2 * Real.pi),
      (by linarith : 2 * α ≠ 0)]),
    Finset.sum_insert (by simp [(by linarith : Real.pi ≠ 2 * Real.pi), Real.pi_ne_zero]),
    Finset.sum_insert (by simp [Real.pi_ne_zero]), Finset.sum_singleton] at hsum
  linarith

/-- **L1 at a base corner** (target angle `α`): no tile presents `π − 3α` or `2α`. -/
theorem Row4.corner_A (D : CongruentDissection N) {α a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (h : D.model.TwoAlphaData α a b c)
    (hα0 : 0 < α) (hα3 : α < Real.pi / 3) {k : Fin 3} (hk : D.target.angleAt k = α) (i : Fin N) :
    (D.tile i).localAngle (D.target.pts k) ≠ Real.pi - 3 * α ∧
      (D.tile i).localAngle (D.target.pts k) ≠ 2 * α := by
  have hc := Row4.count_eq D hα h hα0 hα3 (D.target.pts k)
  rw [D.target.localAngle_vertex k] at hc
  change D.target.angleAt k = _ at hc
  rw [hk] at hc
  set P := ({i | (D.tile i).localAngle (D.target.pts k) = α} : Finset (Fin N)).card
  set Q := ({i | (D.tile i).localAngle (D.target.pts k) = Real.pi - 3 * α} : Finset (Fin N)).card
  set R := ({i | (D.tile i).localAngle (D.target.pts k) = 2 * α} : Finset (Fin N)).card
  set S := ({i | (D.tile i).localAngle (D.target.pts k) = Real.pi} : Finset (Fin N)).card
  set T := ({i | (D.tile i).localAngle (D.target.pts k) = 2 * Real.pi} : Finset (Fin N)).card
  obtain ⟨h1, h2⟩ := Row4.fig_arith hα (P := P) (Q := Q) (R := R) (S := S) (T := T) (j := 0) (k := 1)
    (by push_cast; linear_combination -hc)
  have hQ : Q = 0 := by omega
  have hR : R = 0 := by omega
  constructor
  · intro e
    have : i ∈ ({i | (D.tile i).localAngle (D.target.pts k) = Real.pi - 3 * α} : Finset (Fin N)) := by
      simp [e]
    rw [Finset.card_eq_zero.mp hQ] at this; simp at this
  · intro e
    have : i ∈ ({i | (D.tile i).localAngle (D.target.pts k) = 2 * α} : Finset (Fin N)) := by
      simp [e]
    rw [Finset.card_eq_zero.mp hR] at this; simp at this

/-- **L1 at the apex** (target angle `π − 2α`): no tile presents `2α`, and at most one presents
`π − 3α`. -/
theorem Row4.corner_B (D : CongruentDissection N) {α a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (h : D.model.TwoAlphaData α a b c)
    (hα0 : 0 < α) (hα3 : α < Real.pi / 3) {k : Fin 3}
    (hk : D.target.angleAt k = Real.pi - 2 * α) :
    (∀ i, (D.tile i).localAngle (D.target.pts k) ≠ 2 * α) ∧
      ∀ i j, (D.tile i).localAngle (D.target.pts k) = Real.pi - 3 * α →
        (D.tile j).localAngle (D.target.pts k) = Real.pi - 3 * α → i = j := by
  have hc := Row4.count_eq D hα h hα0 hα3 (D.target.pts k)
  rw [D.target.localAngle_vertex k] at hc
  change D.target.angleAt k = _ at hc
  rw [hk] at hc
  set P := ({i | (D.tile i).localAngle (D.target.pts k) = α} : Finset (Fin N)).card
  set Q := ({i | (D.tile i).localAngle (D.target.pts k) = Real.pi - 3 * α} : Finset (Fin N)).card
    with hQdef
  set R := ({i | (D.tile i).localAngle (D.target.pts k) = 2 * α} : Finset (Fin N)).card with hRdef
  set S := ({i | (D.tile i).localAngle (D.target.pts k) = Real.pi} : Finset (Fin N)).card
  set T := ({i | (D.tile i).localAngle (D.target.pts k) = 2 * Real.pi} : Finset (Fin N)).card
  obtain ⟨h1, h2⟩ := Row4.fig_arith hα (P := P) (Q := Q) (R := R) (S := S) (T := T) (j := 1)
    (k := -2) (by push_cast; linear_combination -hc)
  have hQ : Q ≤ 1 := by omega
  have hR : R = 0 := by omega
  constructor
  · intro i e
    have : i ∈ ({i | (D.tile i).localAngle (D.target.pts k) = 2 * α} : Finset (Fin N)) := by
      simp [e]
    rw [Finset.card_eq_zero.mp hR] at this; simp at this
  · intro i j ei ej
    have hi : i ∈ ({i | (D.tile i).localAngle (D.target.pts k) = Real.pi - 3 * α} : Finset (Fin N)) := by
      simp [ei]
    have hj : j ∈ ({i | (D.tile i).localAngle (D.target.pts k) = Real.pi - 3 * α} : Finset (Fin N)) := by
      simp [ej]
    exact Finset.card_le_one.mp hQ i hi j hj

/-! ## The model is scalene; the ends of an `a`-edge -/

/-- The model's sides in terms of `cos α` (re-derivation of the model half of `Row4.sides`, which
does not export `κ = cos α`). -/
theorem Row4.model_sides (D : CongruentDissection N) {α a b c : ℝ}
    (h : D.model.TwoAlphaData α a b c) :
    0 < α ∧ α < Real.pi / 3 ∧ 0 < a ∧ c = 2 * Real.cos α * a ∧
      b = (4 * Real.cos α ^ 2 - 1) * a := by
  obtain ⟨σ, h0, o0, h1, o1, h2, o2⟩ := h
  have hαpos : 0 < α := h0 ▸ D.model.angleAt_pos' (σ 0)
  have hβpos : 0 < Real.pi - 3 * α := h1 ▸ D.model.angleAt_pos' (σ 1)
  have hπ := Real.pi_pos
  have hsα : 0 < Real.sin α := Real.sin_pos_of_pos_of_lt_pi hαpos (by linarith)
  have hs3 : Real.sin (Real.pi - 3 * α) = Real.sin α * (4 * Real.cos α ^ 2 - 1) := by
    rw [Real.sin_pi_sub, Real.sin_three_mul]
    have p := Real.sin_sq_add_cos_sq α
    linear_combination (-4 * Real.sin α) * p
  have ls1 := D.model.lawSin (σ 0) (σ 2)
  have ls2 := D.model.lawSin (σ 0) (σ 1)
  rw [h0, o2, h2, o0, Real.sin_two_mul] at ls1
  rw [h0, o1, h1, o0, hs3] at ls2
  refine ⟨hαpos, by linarith, o0 ▸ D.model.oppLen_pos (σ 0), ?_, ?_⟩
  · exact mul_left_cancel₀ hsα.ne' (by linear_combination ls1)
  · exact mul_left_cancel₀ hsα.ne' (by linear_combination ls2)

/-- **The `γ = 2α` tile is scalene** (`a = b` would give `α = π/4`, `b = c` would give `α = π/5`). -/
theorem Row4.scalene (D : CongruentDissection N) {α a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (h : D.model.TwoAlphaData α a b c) :
    a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  obtain ⟨hα0, hα3, ha, hc, hb⟩ := Row4.model_sides D h
  have hπ := Real.pi_pos
  have hκ1 : 1 / 2 < Real.cos α := by
    rw [← Real.cos_pi_div_three]
    exact Real.cos_lt_cos_of_nonneg_of_le_pi hα0.le (by linarith) (by linarith)
  have hmem : α ∈ Set.Icc 0 Real.pi := ⟨hα0.le, by linarith⟩
  refine ⟨fun hab => ?_, fun hac => ?_, fun hbc => ?_⟩
  · -- `cos² α = 1/2 = cos²(π/4)`
    have e : a * (2 * (Real.cos α ^ 2 - Real.cos (Real.pi / 4) ^ 2)) = 0 := by
      rw [Real.cos_pi_div_four]
      have h2 : √(2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
      rw [hb] at hab
      linear_combination (-1 / 2 : ℝ) * hab - a / 2 * h2
    have e2 := (mul_eq_zero.mp e).resolve_left ha.ne'
    have hc4 : 0 < Real.cos (Real.pi / 4) := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
    have e3 : (Real.cos α - Real.cos (Real.pi / 4)) * (Real.cos α + Real.cos (Real.pi / 4)) = 0 := by
      linear_combination e2 / 2
    have e4 := sub_eq_zero.mp ((mul_eq_zero.mp e3).resolve_right (by linarith))
    have := Real.injOn_cos hmem ⟨by linarith, by linarith⟩ e4
    exact hα ⟨1 / 4, by rw [this]; push_cast; ring⟩
  · rw [hc] at hac
    have : a * (1 - 2 * Real.cos α) = 0 := by linear_combination hac
    have := (mul_eq_zero.mp this).resolve_left ha.ne'
    linarith
  · -- `4cos²α − 2cos α − 1 = 0`, the quadratic of `cos(π/5)`
    have q5 : 4 * Real.cos (Real.pi / 5) ^ 2 - 2 * Real.cos (Real.pi / 5) - 1 = 0 :=
      Real.quadratic_root_cos_pi_div_five
    rw [hb, hc] at hbc
    have e : a * (4 * Real.cos α ^ 2 - 2 * Real.cos α - 1) = 0 := by linear_combination hbc
    have e2 := (mul_eq_zero.mp e).resolve_left ha.ne'
    have hc5 : 0 < Real.cos (Real.pi / 5) := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
    have e3 : (Real.cos α - Real.cos (Real.pi / 5))
        * (4 * (Real.cos α + Real.cos (Real.pi / 5)) - 2) = 0 := by linear_combination e2 - q5
    have e4 := sub_eq_zero.mp ((mul_eq_zero.mp e3).resolve_right (by linarith))
    have := Real.injOn_cos hmem ⟨by linarith, by linarith⟩ e4
    exact hα ⟨1 / 5, by rw [this]; push_cast; ring⟩

/-- The three corner angles of a real tile are pairwise distinct. -/
theorem Row4.tile_angles_ne (D : CongruentDissection N) {α a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (h : D.model.TwoAlphaData α a b c) (i : Fin N)
    {j j' : Fin 3} (hjj' : j ≠ j') : (D.tile i).angleAt j ≠ (D.tile i).angleAt j' := by
  obtain ⟨hα0, hα3, -⟩ := Row4.model_sides D h
  have hπ := Real.pi_pos
  have d1 : α ≠ Real.pi - 3 * α := fun e => hα ⟨1 / 4, by push_cast; linarith⟩
  have d6 : Real.pi - 3 * α ≠ 2 * α := fun e => hα ⟨1 / 5, by push_cast; linarith⟩
  have d2 : α ≠ 2 * α := by intro e; linarith
  obtain ⟨σ', hσ'⟩ := (D.tiles_congruent i).exists_perm
  obtain ⟨σ, h0, -, h1, -, h2, -⟩ := h
  rw [(hσ' j).1, (hσ' j').1]
  have hne : σ' j ≠ σ' j' := fun e => hjj' (σ'.injective e)
  obtain ⟨m, hm⟩ := σ.surjective (σ' j)
  obtain ⟨m', hm'⟩ := σ.surjective (σ' j')
  rw [← hm, ← hm'] at hne ⊢
  have hmm : m ≠ m' := fun e => hne (by rw [e])
  have h3 : ∀ x : Fin 3, x = 0 ∨ x = 1 ∨ x = 2 := by decide
  rcases h3 m with rfl | rfl | rfl <;> rcases h3 m' with rfl | rfl | rfl
  · exact absurd rfl hmm
  · rw [h0, h1]; exact d1
  · rw [h0, h2]; exact d2
  · rw [h1, h0]; exact d1.symm
  · exact absurd rfl hmm
  · rw [h1, h2]; exact d6
  · rw [h2, h0]; exact d2.symm
  · rw [h2, h1]; exact d6.symm
  · exact absurd rfl hmm

/-- **An `a`-edge's ends carry `β`/`γ`**: if tile `i`'s edge `k` has length `a`, its vertex `k + 2`
carries `α` and its two ends `k`, `k + 1` carry `π − 3α` or `2α`. -/
theorem Row4.a_edge_ends (D : CongruentDissection N) {α a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (h : D.model.TwoAlphaData α a b c) (i : Fin N)
    (k : Fin 3) (hlen : D.eLen (i, k) = a) :
    (D.tile i).angleAt (k + 2) = α ∧
      ((D.tile i).angleAt k = Real.pi - 3 * α ∨ (D.tile i).angleAt k = 2 * α) ∧
      ((D.tile i).angleAt (k + 1) = Real.pi - 3 * α ∨ (D.tile i).angleAt (k + 1) = 2 * α) := by
  obtain ⟨hab, hac, hbc⟩ := Row4.scalene D hα h
  have hopp : (D.tile i).oppLen (k + 2) = a := by
    rw [← hlen]; unfold Tri.oppLen Dissection.eLen
    rw [show k + 2 + 1 = k by fin_cases k <;> rfl, show k + 2 + 2 = k + 1 by fin_cases k <;> rfl]
  obtain ⟨σ', hσ'⟩ := (D.tiles_congruent i).exists_perm
  have hk2 : (D.tile i).angleAt (k + 2) = α := by
    obtain ⟨σ, h0, o0, h1, o1, h2, o2⟩ := h
    rw [(hσ' (k + 2)).1]
    rw [(hσ' (k + 2)).2] at hopp
    obtain ⟨m, hm⟩ := σ.surjective (σ' (k + 2))
    rw [← hm] at hopp ⊢
    have h3 : m = 0 ∨ m = 1 ∨ m = 2 := by fin_cases m <;> simp
    rcases h3 with rfl | rfl | rfl
    · exact h0
    · rw [o1] at hopp; exact absurd hopp.symm hab
    · rw [o2] at hopp; exact absurd hopp.symm hac
  have hne0 : k ≠ k + 2 := by fin_cases k <;> decide
  have hne1 : k + 1 ≠ k + 2 := by fin_cases k <;> decide
  have a0 := Row4.tile_angles_ne D hα h i hne0
  have a1 := Row4.tile_angles_ne D hα h i hne1
  rw [hk2] at a0 a1
  refine ⟨hk2, ?_, ?_⟩
  · rcases Row4.tile_angle_mem D h i k with e | e | e
    · exact absurd e a0
    · exact Or.inl e
    · exact Or.inr e
  · rcases Row4.tile_angle_mem D h i (k + 1) with e | e | e
    · exact absurd e a1
    · exact Or.inl e
    · exact Or.inr e

/-- **One `a`-edge per tile.** -/
theorem Row4.a_edge_unique (D : CongruentDissection N) {α a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (h : D.model.TwoAlphaData α a b c) (i : Fin N)
    {k k' : Fin 3} (hk : D.eLen (i, k) = a) (hk' : D.eLen (i, k') = a) : k = k' := by
  have e1 := (Row4.a_edge_ends D hα h i k hk).1
  have e2 := (Row4.a_edge_ends D hα h i k' hk').1
  by_contra hne
  have : k + 2 ≠ k' + 2 := fun e => hne (by simpa using e)
  exact Row4.tile_angles_ne D hα h i this (e1.trans e2.symm)

/-! ## Target vertices on side edges -/

/-- A point `x` of a sub-segment `[p, q] ⊆ [x, y]`, `x ≠ y`, is one of its ends. -/
theorem Row4.endpoint_of_subsegment {x y p q : Plane} (hxy : x ≠ y)
    (hsub : segment ℝ p q ⊆ segment ℝ x y) (hx : x ∈ segment ℝ p q) : x = p ∨ x = q := by
  have hp : p ∈ segment ℝ x y := hsub (left_mem_segment ℝ p q)
  have hq : q ∈ segment ℝ x y := hsub (right_mem_segment ℝ p q)
  rw [segment_eq_image'] at hp hq hx
  obtain ⟨s, ⟨hs0, hs1⟩, hps⟩ := hp
  obtain ⟨t, ⟨ht0, ht1⟩, hqt⟩ := hq
  obtain ⟨l, ⟨hl0, hl1⟩, hl⟩ := hx
  simp only at hps hqt hl
  have hyx : y - x ≠ 0 := sub_ne_zero.mpr hxy.symm
  have e : (s + l * (t - s)) • (y - x) = 0 := by
    rw [← hps, ← hqt] at hl
    rw [← sub_eq_zero.mpr hl]
    module
  have e2 : s + l * (t - s) = 0 := (smul_eq_zero.mp e).resolve_right hyx
  by_cases hl1' : l < 1
  · left
    have : s = 0 := by nlinarith
    rw [← hps, this, zero_smul, add_zero]
  · right
    have hl' : l = 1 := le_antisymm hl1 (not_lt.mp hl1')
    rw [hl'] at e2
    have : t = 0 := by linarith
    rw [← hqt, this, zero_smul, add_zero]

/-- A target vertex `P` at an end of target side `j` is an END of some tile edge on that side, and
that tile presents one of its own corner angles at `P`. -/
theorem Row4.vertex_on_side (D : CongruentDissection N) (j : Fin 3) {P Q : Plane}
    (hPQ : P ≠ Q) (hside : D.target.edge j = segment ℝ P Q) :
    ∃ e ∈ D.sideEdges j, ∃ m : Fin 3, (m = e.2 ∨ m = e.2 + 1) ∧ (D.tile e.1).pts m = P := by
  obtain ⟨part, hpart⟩ := hasEdgeChains_edge D.toDissection j
  have hP : P ∈ segment ℝ (D.target.pts j) (D.target.pts (j + 1)) := by
    rw [show segment ℝ (D.target.pts j) (D.target.pts (j + 1)) = D.target.edge j from rfl, hside]
    exact left_mem_segment ℝ P Q
  rw [← hpart] at hP
  obtain ⟨e, he, hPe⟩ := Set.mem_iUnion₂.mp hP
  have hsub : D.eSet e ⊆ D.target.edge j := fun z hz => by
    have : z ∈ ⋃ e ∈ part, (D.tile e.1).edge e.2 := Set.mem_iUnion₂.mpr ⟨e, he, hz⟩
    rw [hpart] at this; exact this
  refine ⟨e, ?_, ?_⟩
  · unfold Dissection.sideEdges; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsub⟩
  · rw [hside] at hsub
    rcases Row4.endpoint_of_subsegment hPQ hsub hPe with h1 | h1
    · exact ⟨e.2, Or.inl rfl, h1.symm⟩
    · exact ⟨e.2 + 1, Or.inr rfl, h1.symm⟩

/-! ## L8, the `{a, c}` legs -/

/-- **One leg with word `{a, c}`**: the leg `[P, B]` (base corner `P`, apex `B`) is covered by one
`a`-edge and one `c`-edge; the `a`-edge cannot end at `P` (its ends carry `β`/`γ`, which `P` excludes),
so it ends at `B`, where its tile presents `β` (`γ` is excluded at `B`). -/
theorem Row4.leg_beta_at_apex (D : CongruentDissection N) {α a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (h : D.model.TwoAlphaData α a b c) {j : Fin 3}
    {P B : Plane} (hPB : P ≠ B) (hside : D.target.edge j = segment ℝ P B)
    (hP : ∀ i, (D.tile i).localAngle P ≠ Real.pi - 3 * α ∧ (D.tile i).localAngle P ≠ 2 * α)
    (hBγ : ∀ i, (D.tile i).localAngle B ≠ 2 * α) {ea ec : Fin N × Fin 3}
    (hset : D.sideEdges j = {ea, ec}) (hea : D.eLen ea = a) (hec : D.eLen ec = c)
    (hlen : dist P B = a + c) (ha : 0 < a) :
    (D.tile ea.1).localAngle B = Real.pi - 3 * α := by
  -- the edge through `P` is the `c`-edge
  obtain ⟨eP, heP, m, hm, hmP⟩ := Row4.vertex_on_side D j hPB hside
  have hends : ∀ (e : Fin N × Fin 3) (m : Fin 3), (m = e.2 ∨ m = e.2 + 1) → D.eLen e = a →
      (D.tile e.1).localAngle ((D.tile e.1).pts m) = Real.pi - 3 * α ∨
        (D.tile e.1).localAngle ((D.tile e.1).pts m) = 2 * α := by
    intro e m hm he
    rw [(D.tile e.1).localAngle_vertex m]
    show (D.tile e.1).angleAt m = _ ∨ (D.tile e.1).angleAt m = _
    obtain ⟨-, h1, h2⟩ := Row4.a_edge_ends D hα h e.1 e.2 he
    rcases hm with rfl | rfl
    · exact h1
    · exact h2
  have hmemP : eP = ea ∨ eP = ec := by
    rw [hset] at heP; simpa using heP
  have hePc : eP = ec := by
    rcases hmemP with e | e
    · exfalso
      have := hends eP m hm (e ▸ hea)
      rw [hmP] at this
      rcases this with h' | h'
      · exact (hP eP.1).1 h'
      · exact (hP eP.1).2 h'
    · exact e
  -- the edge through `B`
  have hside' : D.target.edge j = segment ℝ B P := by rw [hside, segment_symm]
  obtain ⟨eB, heB, m', hm', hm'B⟩ := Row4.vertex_on_side D j hPB.symm hside'
  have hmemB : eB = ea ∨ eB = ec := by
    rw [hset] at heB; simpa using heB
  have heBa : eB = ea := by
    rcases hmemB with e | e
    · exact e
    · exfalso
      -- `P` and `B` would both be ends of the `c`-edge: `dist P B = c`
      rw [e] at hm' hm'B
      rw [hePc] at hm hmP
      have hmm : m ≠ m' := fun e' => hPB (by rw [← hmP, ← hm'B, e'])
      have hd : dist P B = D.eLen ec := by
        unfold Dissection.eLen
        rw [← hmP, ← hm'B]
        rcases hm with rfl | rfl <;> rcases hm' with rfl | rfl
        · exact absurd rfl hmm
        · rfl
        · exact dist_comm _ _
        · exact absurd rfl hmm
      rw [hec, hlen] at hd
      linarith
  have := hends eB m' hm' (heBa ▸ hea)
  rw [hm'B, heBa] at this
  rcases this with h' | h'
  · exact h'
  · exact absurd h' (hBγ ea.1)

/-- **L8, the `{a, c}` half** (row4/PROOF.md §3): if both legs are covered by one `a`-edge and one
`c`-edge, the apex receives two `β`: impossible. -/
theorem Row4.L8_ac (D : CongruentDissection N) {α a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (h : D.model.TwoAlphaData α a b c)
    (hA : D.target.angleAt 0 = α) (hC : D.target.angleAt 1 = α)
    {ea₁ ec₁ ea₂ ec₂ : Fin N × Fin 3}
    (hAB : D.sideEdges 2 = {ea₁, ec₁}) (ha₁ : D.eLen ea₁ = a) (hc₁ : D.eLen ec₁ = c)
    (hCB : D.sideEdges 1 = {ea₂, ec₂}) (ha₂ : D.eLen ea₂ = a) (hc₂ : D.eLen ec₂ = c) : False := by
  obtain ⟨hα0, hα3, ha, -, -⟩ := Row4.model_sides D h
  obtain ⟨-, hac, -⟩ := Row4.scalene D hα h
  have hB : D.target.angleAt 2 = Real.pi - 2 * α := by
    have := D.target.angleAt_sum; rw [hA, hC] at this; linarith
  have hP0 := fun i => Row4.corner_A D hα h hα0 hα3 hA i
  have hP1 := fun i => Row4.corner_A D hα h hα0 hα3 hC i
  obtain ⟨hBγ, hBβ⟩ := Row4.corner_B D hα h hα0 hα3 hB
  have hne : ∀ i j : Fin 3, i ≠ j → D.target.pts i ≠ D.target.pts j := fun i j hij e =>
    hij (D.target.indep.injective e)
  -- the leg lengths are `a + c`
  have hlen : ∀ {j : Fin 3} {ea ec : Fin N × Fin 3}, D.sideEdges j = {ea, ec} → D.eLen ea = a →
      D.eLen ec = c → dist (D.target.pts j) (D.target.pts (j + 1)) = a + c := by
    intro j ea ec hs hea hec
    have hsum := D.toDissection.side_len_sum j
    have hneq : ea ≠ ec := fun e => hac (by rw [← hea, ← hec, e])
    rw [hs, Finset.sum_pair hneq, hea, hec] at hsum
    exact hsum.symm
  -- leg AB = `edge 2` = `[A, B]`, leg CB = `edge 1` = `[C, B]`
  have hsAB : D.target.edge 2 = segment ℝ (D.target.pts 0) (D.target.pts 2) := by
    show segment ℝ (D.target.pts 2) (D.target.pts (2 + 1)) = _
    rw [show (2 : Fin 3) + 1 = 0 from rfl, segment_symm]
  have hsCB : D.target.edge 1 = segment ℝ (D.target.pts 1) (D.target.pts 2) := rfl
  have hl₁ : dist (D.target.pts 0) (D.target.pts 2) = a + c := by
    rw [dist_comm]; have := hlen hAB ha₁ hc₁; simpa using this
  have hl₂ : dist (D.target.pts 1) (D.target.pts 2) = a + c := by
    have := hlen hCB ha₂ hc₂; simpa using this
  have hβ₁ := Row4.leg_beta_at_apex D hα h (hne 0 2 (by decide)) hsAB hP0 hBγ hAB ha₁ hc₁ hl₁ ha
  have hβ₂ := Row4.leg_beta_at_apex D hα h (hne 1 2 (by decide)) hsCB hP1 hBγ hCB ha₂ hc₂ hl₂ ha
  -- the same tile, hence the same `a`-edge, on two sides
  have ht := hBβ ea₁.1 ea₂.1 hβ₁ hβ₂
  have hk := Row4.a_edge_unique D hα h ea₁.1 (k := ea₁.2) (k' := ea₂.2) ha₁ (ht ▸ ha₂)
  have heq : ea₁ = ea₂ := Prod.ext ht hk
  have h1 : ea₁ ∈ D.sideEdges 2 := by rw [hAB]; simp
  have h2 : ea₁ ∈ D.sideEdges 1 := by rw [hCB, heq]; simp
  exact Finset.disjoint_left.mp (D.toDissection.sideEdges_disjoint (by decide : (2 : Fin 3) ≠ 1)) h1 h2

/-! ## R4(ii) reduced to the `b^k` half -/

/-- Every tile edge has length `a`, `b` or `c`. -/
theorem Row4.eLen_abc (D : CongruentDissection N) {α a b c : ℝ} (h : D.model.TwoAlphaData α a b c)
    (e : Fin N × Fin 3) : D.eLen e = a ∨ D.eLen e = b ∨ D.eLen e = c := by
  obtain ⟨k, hk⟩ := D.eLen_mem e
  obtain ⟨σ, -, o0, -, o1, -, o2⟩ := h
  obtain ⟨m, rfl⟩ := σ.surjective k
  have h3 : m = 0 ∨ m = 1 ∨ m = 2 := by fin_cases m <;> simp
  rcases h3 with rfl | rfl | rfl
  · exact Or.inl (hk.trans o0)
  · exact Or.inr (Or.inl (hk.trans o1))
  · exact Or.inr (Or.inr (hk.trans o2))

/-- The typed counts of a side, and their word: `leg = p·a + q·b + r·c`. -/
theorem Row4.side_word_counts (D : CongruentDissection N) {α a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (h : D.model.TwoAlphaData α a b c) (i : Fin 3) :
    D.target.oppLen i = (((D.sideEdges (i + 1)).filter (fun e => D.eLen e = a)).card : ℝ) * a
      + (((D.sideEdges (i + 1)).filter (fun e => D.eLen e = b)).card : ℝ) * b
      + (((D.sideEdges (i + 1)).filter (fun e => D.eLen e = c)).card : ℝ) * c := by
  obtain ⟨hab, hac, hbc⟩ := Row4.scalene D hα h
  obtain ⟨σ, h0, o0, h1, o1, h2, o2⟩ := h
  have hscal : ∀ k k', k ≠ k' → D.model.oppLen k ≠ D.model.oppLen k' := by
    intro k k' hkk'
    obtain ⟨m, rfl⟩ := σ.surjective k
    obtain ⟨m', rfl⟩ := σ.surjective k'
    have hmm : m ≠ m' := fun e => hkk' (by rw [e])
    have h3 : ∀ x : Fin 3, x = 0 ∨ x = 1 ∨ x = 2 := by decide
    rcases h3 m with rfl | rfl | rfl <;> rcases h3 m' with rfl | rfl | rfl
    · exact absurd rfl hmm
    · rw [o0, o1]; exact hab
    · rw [o0, o2]; exact hac
    · rw [o1, o0]; exact hab.symm
    · exact absurd rfl hmm
    · rw [o1, o2]; exact hbc
    · rw [o2, o0]; exact hac.symm
    · rw [o2, o1]; exact hbc.symm
    · exact absurd rfl hmm
  have hs := D.sideCount_sum hscal i
  rw [← Equiv.sum_comp σ (fun k => (D.sideCount i k : ℝ) * D.model.oppLen k), Fin.sum_univ_three,
    o0, o1, o2] at hs
  unfold CongruentDissection.sideCount at hs
  rw [o0, o1, o2] at hs
  exact hs.symm

/-- **R4(ii), reduced** (C6 + L7 + typed side counts + L8's `{a, c}` half): at prime `N`, SOME leg
(side `edge 1` or `edge 2`) consists of exactly `k ≥ 2` edges, all of length `b`.  What remains of
R4(ii) is L8's `b^k` half: that such a leg is impossible (named blocker). -/
theorem Row4.prime_reduced (D : CongruentDissection N) {α a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (h : D.model.TwoAlphaData α a b c)
    (hA : D.target.angleAt 0 = α) (hC : D.target.angleAt 1 = α) (hN : N.Prime) :
    ∃ j : Fin 3, (j = 1 ∨ j = 2) ∧ ∃ k : ℕ, 2 ≤ k ∧ N = 2 * k + 1 ∧
      ((D.sideEdges j).filter (fun e => D.eLen e = b)).card = k ∧
      ∀ e ∈ D.sideEdges j, D.eLen e = b := by
  obtain ⟨k, hk2, hNk, -, -, -, hwords⟩ := Row4.prime_leg_words D hα h hA hC hN
  obtain ⟨-, -, -, -, -, -, -, -, hX1⟩ := Row4.sides D h hA hC
  obtain ⟨hab, hac, hbc⟩ := Row4.scalene D hα h
  -- the word of each leg is `(0,k,0)` or `(1,0,1)`
  have hw : ∀ i : Fin 3, (i = 0 ∨ i = 1) →
      (((D.sideEdges (i + 1)).filter (fun e => D.eLen e = a)).card = 0 ∧
        ((D.sideEdges (i + 1)).filter (fun e => D.eLen e = b)).card = k ∧
        ((D.sideEdges (i + 1)).filter (fun e => D.eLen e = c)).card = 0) ∨
      (((D.sideEdges (i + 1)).filter (fun e => D.eLen e = a)).card = 1 ∧
        ((D.sideEdges (i + 1)).filter (fun e => D.eLen e = b)).card = 0 ∧
        ((D.sideEdges (i + 1)).filter (fun e => D.eLen e = c)).card = 1) := by
    intro i hi
    apply hwords
    rw [← Row4.side_word_counts D hα h i]
    rcases hi with rfl | rfl
    · rfl
    · exact hX1.symm
  -- an `(1,0,1)` leg is `{ea, ec}`
  have hstruct : ∀ j : Fin 3,
      ((D.sideEdges j).filter (fun e => D.eLen e = a)).card = 1 →
      ((D.sideEdges j).filter (fun e => D.eLen e = b)).card = 0 →
      ((D.sideEdges j).filter (fun e => D.eLen e = c)).card = 1 →
      ∃ ea ec, D.sideEdges j = {ea, ec} ∧ D.eLen ea = a ∧ D.eLen ec = c := by
    intro j h1 h2 h3
    obtain ⟨ea, hea⟩ := Finset.card_eq_one.mp h1
    obtain ⟨ec, hec⟩ := Finset.card_eq_one.mp h3
    have hmea : ea ∈ (D.sideEdges j).filter (fun e => D.eLen e = a) := by rw [hea]; simp
    have hmec : ec ∈ (D.sideEdges j).filter (fun e => D.eLen e = c) := by rw [hec]; simp
    refine ⟨ea, ec, ?_, (Finset.mem_filter.mp hmea).2, (Finset.mem_filter.mp hmec).2⟩
    ext e
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro he
      rcases Row4.eLen_abc D h e with e1 | e1 | e1
      · left
        have : e ∈ (D.sideEdges j).filter (fun e => D.eLen e = a) := Finset.mem_filter.mpr ⟨he, e1⟩
        rw [hea] at this; simpa using this
      · exfalso
        have : e ∈ (D.sideEdges j).filter (fun e => D.eLen e = b) := Finset.mem_filter.mpr ⟨he, e1⟩
        rw [Finset.card_eq_zero.mp h2] at this; simp at this
      · right
        have : e ∈ (D.sideEdges j).filter (fun e => D.eLen e = c) := Finset.mem_filter.mpr ⟨he, e1⟩
        rw [hec] at this; simpa using this
    · rintro (rfl | rfl)
      · exact (Finset.mem_filter.mp hmea).1
      · exact (Finset.mem_filter.mp hmec).1
  have hbk : ∀ j : Fin 3,
      ((D.sideEdges j).filter (fun e => D.eLen e = a)).card = 0 →
      ((D.sideEdges j).filter (fun e => D.eLen e = c)).card = 0 →
      ∀ e ∈ D.sideEdges j, D.eLen e = b := by
    intro j h1 h3 e he
    rcases Row4.eLen_abc D h e with e1 | e1 | e1
    · exfalso
      have : e ∈ (D.sideEdges j).filter (fun e => D.eLen e = a) := Finset.mem_filter.mpr ⟨he, e1⟩
      rw [Finset.card_eq_zero.mp h1] at this; simp at this
    · exact e1
    · exfalso
      have : e ∈ (D.sideEdges j).filter (fun e => D.eLen e = c) := Finset.mem_filter.mpr ⟨he, e1⟩
      rw [Finset.card_eq_zero.mp h3] at this; simp at this
  rcases hw 0 (Or.inl rfl) with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · exact ⟨1, Or.inl rfl, k, hk2, hNk, h2, hbk 1 h1 h3⟩
  rcases hw 1 (Or.inr rfl) with ⟨h1', h2', h3'⟩ | ⟨h1', h2', h3'⟩
  · exact ⟨2, Or.inr rfl, k, hk2, hNk, h2', hbk 2 h1' h3'⟩
  exfalso
  obtain ⟨ea₂, ec₂, hs₂, ha₂, hc₂⟩ := hstruct 1 h1 h2 h3
  obtain ⟨ea₁, ec₁, hs₁, ha₁, hc₁⟩ := hstruct 2 h1' h2' h3'
  exact Row4.L8_ac D hα h hA hC hs₁ ha₁ hc₁ hs₂ ha₂ hc₂

end Erdos634.Geometry

#print axioms Erdos634.Geometry.Row4.coeff_split
#print axioms Erdos634.Geometry.Row4.fig_arith
#print axioms Erdos634.Geometry.Row4.localAngle_mem
#print axioms Erdos634.Geometry.Row4.count_eq
#print axioms Erdos634.Geometry.Row4.corner_A
#print axioms Erdos634.Geometry.Row4.corner_B
#print axioms Erdos634.Geometry.Row4.scalene
#print axioms Erdos634.Geometry.Row4.tile_angles_ne
#print axioms Erdos634.Geometry.Row4.a_edge_ends
#print axioms Erdos634.Geometry.Row4.a_edge_unique
#print axioms Erdos634.Geometry.Row4.endpoint_of_subsegment
#print axioms Erdos634.Geometry.Row4.vertex_on_side
#print axioms Erdos634.Geometry.Row4.model_sides
#print axioms Erdos634.Geometry.Row4.leg_beta_at_apex
#print axioms Erdos634.Geometry.Row4.L8_ac
#print axioms Erdos634.Geometry.Row4.eLen_abc
#print axioms Erdos634.Geometry.Row4.side_word_counts
#print axioms Erdos634.Geometry.Row4.prime_reduced
