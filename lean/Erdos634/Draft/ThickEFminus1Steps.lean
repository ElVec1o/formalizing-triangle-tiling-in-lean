-- Draft/ThickEFminus1Steps.lean — formalization of proof_R1_compressed.md (room W2), steps 2–4 and
-- glue G3.  Imported directly by All.lean (stale "NOT imported" header corrected 2026-10-04).  Tile (a,b,c) = (ef, f²−e², f²), γ = 2α+β, 3α+2β = π.
import Erdos634.VertexFigureReal

namespace Erdos634.Draft.ThickEFminus1Steps

open Erdos634.Geometry Finset

/-! ## Step 2 (arithmetic): `a = ef` has only the trivial representation by sides. -/

/-- **Step 2.** For coprime `1 ≤ e < f` and `B = f² − e²`, the only way to write `a = ef` as a
nonnegative combination of `{ef, B, f²}` is `a` itself: one `a`-edge, no `b`, no `c`. -/
theorem a_rep_unique (e f na nb nc B : ℕ) (he : 1 ≤ e) (hef : e < f)
    (hcop : Nat.Coprime e f) (hB : B + e ^ 2 = f ^ 2)
    (h : na * (e * f) + nb * B + nc * f ^ 2 = e * f) :
    na = 1 ∧ nb = 0 ∧ nc = 0 := by
  have hf : 2 ≤ f := by omega
  have hef2 : e * f < f ^ 2 := by nlinarith
  have hnc : nc = 0 := by
    rcases Nat.eq_zero_or_pos nc with h0 | h0
    · exact h0
    · exfalso
      have : f ^ 2 ≤ nc * f ^ 2 := Nat.le_mul_of_pos_left _ h0
      omega
  subst hnc
  have hepos : 0 < e * f := by positivity
  have hBge : 1 < B := by
    by_contra hB1
    have : (e + 1) ^ 2 ≤ f ^ 2 := Nat.pow_le_pow_left hef 2
    nlinarith
  have hna : na ≤ 1 := by
    by_contra hc
    have : 2 * (e * f) ≤ na * (e * f) := Nat.mul_le_mul_right _ (by omega)
    omega
  rcases Nat.lt_or_ge na 1 with h0 | h1
  · -- na = 0 : nb·B = ef, impossible since B > 1 is coprime to ef
    exfalso
    have hna0 : na = 0 := by omega
    subst hna0
    have hnb : nb * B = e * f := by simpa using h
    have hdvd : B ∣ e * f := ⟨nb, by rw [← hnb, mul_comm]⟩
    have hcBe : Nat.Coprime B e := by
      have h1 : Nat.Coprime (f ^ 2) e := Nat.Coprime.pow_left 2 hcop.symm
      rw [← hB] at h1
      have : B + e ^ 2 = B + e * e := by ring
      rw [this] at h1
      exact (Nat.coprime_add_mul_right_left B e e).mp h1
    have hcBf : Nat.Coprime B f := by
      have h1 : Nat.Coprime (e ^ 2) f := Nat.Coprime.pow_left 2 hcop
      have hg1 : Nat.gcd B f ∣ B + e ^ 2 := by
        rw [hB]; exact Dvd.dvd.trans (Nat.gcd_dvd_right B f) (Dvd.intro_left _ (by ring))
      have hg2 : Nat.gcd B f ∣ e ^ 2 := (Nat.dvd_add_right (Nat.gcd_dvd_left B f)).mp hg1
      have hg3 : Nat.gcd B f ∣ Nat.gcd (e ^ 2) f := Nat.dvd_gcd hg2 (Nat.gcd_dvd_right B f)
      rw [h1] at hg3
      exact Nat.dvd_one.mp hg3
    have := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.mul_right hcBe hcBf) hdvd
    omega
  · have hna1 : na = 1 := by omega
    subst hna1
    have : nb * B = 0 := by omega
    rcases Nat.mul_eq_zero.mp this with h0 | h0
    · exact ⟨rfl, h0, rfl⟩
    · omega

/-- Step 2 at `e = f − 1` (coprimality is automatic): `a = f(f−1)`, `b = 2f−1`, `c = f²`. -/
theorem a_rep_unique_thick (f na nb nc : ℕ) (hf : 2 ≤ f)
    (h : na * ((f - 1) * f) + nb * (2 * f - 1) + nc * f ^ 2 = (f - 1) * f) :
    na = 1 ∧ nb = 0 ∧ nc = 0 := by
  obtain ⟨e, rfl⟩ : ∃ e, f = e + 1 := ⟨f - 1, by omega⟩
  have hcop : Nat.Coprime e (e + 1) := by
    simp [Nat.coprime_self_add_right]
  have hB : (2 * (e + 1) - 1) + e ^ 2 = (e + 1) ^ 2 := by
    have : 2 * (e + 1) - 1 = 2 * e + 1 := by omega
    rw [this]; ring
  simp only [Nat.add_sub_cancel] at h
  exact a_rep_unique e (e + 1) na nb nc _ (by omega) (by omega) hcop hB h

/-! ## Step 3 (fill): the remainder of `π − β` is `3α` or `α`, all α-corners. -/

/-- **Step 3.** At `V`, the angle `π − β` is filled by the corner `x ∈ {β, γ}` laid against `VP′`
(step 2) plus `p` α-, `q` β- and `r` γ-corners.  Then `q = r = 0`, and `p = 3` (if `x = β`) or
`p = 1` (if `x = γ`); in particular `p ≥ 1`, so the corner against `ρ` is an α-corner. -/
theorem fill_rest {α β γ : ℝ} (hγ : γ = 2 * α + β) (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) {x : ℝ} (hx : x = β ∨ x = γ) (p q r : ℕ)
    (hfill : x + (p : ℝ) * α + (q : ℝ) * β + (r : ℝ) * γ = Real.pi - β) :
    q = 0 ∧ r = 0 ∧ ((x = β ∧ p = 3) ∨ (x = γ ∧ p = 1)) := by
  subst hγ
  rcases hx with rfl | rfl
  · have h : (p : ℝ) * α + (q : ℝ) * x + (r : ℝ) * (2 * α + x)
        = ((3 : ℤ) : ℝ) * α + ((0 : ℤ) : ℝ) * x := by push_cast; linarith
    obtain ⟨h1, h2⟩ := vertex_multiplicities hrel hirr p q r 3 0 h
    refine ⟨by omega, by omega, Or.inl ⟨rfl, by omega⟩⟩
  · have h : (p : ℝ) * α + (q : ℝ) * β + (r : ℝ) * (2 * α + β)
        = ((1 : ℤ) : ℝ) * α + ((0 : ℤ) : ℝ) * β := by push_cast; linarith
    obtain ⟨h1, h2⟩ := vertex_multiplicities hrel hirr p q r 1 0 h
    refine ⟨by omega, by omega, Or.inr ⟨rfl, by omega⟩⟩

/-! ## Step 4 (depth), in the form the assembly consumes. -/

/-- **Step 4.**  `depth` is the (linear) coordinate along the target's axis, apex at depth `0`.
`V = c·u_r` with `depth u_r = cos(α/2)`; the α-corner's flank of length `c` from `V` runs along a unit
direction `u` with `depth u = cos(α/2)` (both `u(±α/2)` qualify).  The base is at depth
`f·b·cos(α/2)` (`ThickEFminus1Probe.base_depth_along_ray`).  Then the flank endpoint lies strictly
beyond the base iff `2c > f·b`. -/
theorem flank_endpoint_below_iff {E : Type*} [AddCommGroup E] [Module ℝ E] (depth : E →ₗ[ℝ] ℝ)
    {κ c fb : ℝ} (hκ : 0 < κ) (ur u : E) (hur : depth ur = κ) (hu : depth u = κ) :
    fb * κ < depth (c • ur + c • u) ↔ fb < 2 * c := by
  simp only [map_add, map_smul, smul_eq_mul, hur, hu]
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

/-- **Step 4 at `e = f − 1`.**  With `b = 2f − 1`, `c = f²`, `f ≥ 2`: `2c > f·b`, so the flank
endpoint lies strictly beyond the base line. -/
theorem flank_endpoint_below_thick {E : Type*} [AddCommGroup E] [Module ℝ E]
    (depth : E →ₗ[ℝ] ℝ) {κ f : ℝ} (hκ : 0 < κ) (hf : 1 < f) (ur u : E)
    (hur : depth ur = κ) (hu : depth u = κ) :
    f * (2 * f - 1) * κ < depth (f ^ 2 • ur + f ^ 2 • u) :=
  (flank_endpoint_below_iff depth hκ ur u hur hu).mpr (by nlinarith)

/-! ## Glue G3: two γ at an interior point forbid a straight angle there. -/

/-- **G3.**  At an interior point `P` of the target where two distinct tiles present `γ`, no tile
presents `π` (so no tile edge has `P` in its relative interior).  Proved against a real
`Dissection`, from the interior angle sum (`VertexFigureReal.interior_multiplicities_cards`). -/
theorem no_straight_at_two_gamma {N : ℕ} (D : Dissection N) {α β γ : ℝ}
    (hγ : γ = 2 * α + β) (hrel : 3 * α + 2 * β = Real.pi) (hα : 0 < α) (hβ : 0 < β)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    {P : Plane} (hP : P ∈ interior D.target.carrier)
    (hvals : ∀ i, (D.tile i).localAngle P ∈ ({α, β, γ, Real.pi, 2 * Real.pi, 0} : Finset ℝ))
    (i j : Fin N) (hij : i ≠ j)
    (hi : (D.tile i).localAngle P = γ) (hj : (D.tile j).localAngle P = γ) :
    ∀ k, (D.tile k).localAngle P ≠ Real.pi := by
  classical
  intro k hk
  have hπ := Real.pi_pos
  have hαβ : α ≠ β := by
    intro h; apply hirr; refine ⟨1/5, ?_⟩; push_cast; linarith
  have key := Erdos634.VertexFigureReal.interior_multiplicities_cards D α β γ hαβ
    (by intro h; linarith) (by intro h; linarith) (by intro h; linarith) (by intro h; linarith)
    (by intro h; linarith) (by intro h; linarith) (by intro h; linarith) (by intro h; linarith)
    (by intro h; linarith) (by intro h; linarith) (by intro h; linarith)
    (by intro h; linarith) (by intro h; linarith) (by intro h; linarith) hP hvals
  have hcγ : 2 ≤ ({i | (D.tile i).localAngle P = γ} : Finset (Fin N)).card := by
    have : ({i, j} : Finset (Fin N)) ⊆ ({i | (D.tile i).localAngle P = γ} : Finset (Fin N)) := by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> simp [hi, hj]
    have := Finset.card_le_card this
    rwa [Finset.card_pair hij] at this
  have hcπ : 1 ≤ ({i | (D.tile i).localAngle P = Real.pi} : Finset (Fin N)).card :=
    Finset.card_pos.mpr ⟨k, by simp [hk]⟩
  have hcγ' : (2 : ℝ) ≤ (({i | (D.tile i).localAngle P = γ} : Finset (Fin N)).card : ℝ) := by
    exact_mod_cast hcγ
  have hcπ' : (1 : ℝ) ≤ (({i | (D.tile i).localAngle P = Real.pi} : Finset (Fin N)).card : ℝ) := by
    exact_mod_cast hcπ
  have hγ0 : 0 < γ := by linarith
  set A := (({i | (D.tile i).localAngle P = α} : Finset (Fin N)).card : ℝ)
  set B := (({i | (D.tile i).localAngle P = β} : Finset (Fin N)).card : ℝ)
  set C := (({i | (D.tile i).localAngle P = 2 * Real.pi} : Finset (Fin N)).card : ℝ)
  have hA : 0 ≤ A := Nat.cast_nonneg _
  have hB : 0 ≤ B := Nat.cast_nonneg _
  have hC : 0 ≤ C := Nat.cast_nonneg _
  nlinarith [mul_nonneg hA hα.le, mul_nonneg hB hβ.le, mul_nonneg hC hπ.le]

/-- **G2 (angle half).**  At an interior point `V` where some tile presents a straight angle (the
piercing far-side edge, step 1) and some tile presents `β` (T₂), exactly one tile is straight, none
presents `2π`, and the remaining corners — the `β`-count less T₂ — sum to `π − β`. -/
theorem corners_fill_pi_sub_beta {N : ℕ} (D : Dissection N) {α β γ : ℝ}
    (hγ : γ = 2 * α + β) (hrel : 3 * α + 2 * β = Real.pi) (hα : 0 < α) (hβ : 0 < β)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    {V : Plane} (hV : V ∈ interior D.target.carrier)
    (hvals : ∀ i, (D.tile i).localAngle V ∈ ({α, β, γ, Real.pi, 2 * Real.pi, 0} : Finset ℝ))
    (k t : Fin N) (hk : (D.tile k).localAngle V = Real.pi) (ht : (D.tile t).localAngle V = β) :
    ({i | (D.tile i).localAngle V = Real.pi} : Finset (Fin N)).card = 1 ∧
    ({i | (D.tile i).localAngle V = 2 * Real.pi} : Finset (Fin N)).card = 0 ∧
    (({i | (D.tile i).localAngle V = α} : Finset (Fin N)).card : ℝ) * α
      + ((({i | (D.tile i).localAngle V = β} : Finset (Fin N)).card : ℝ) - 1) * β
      + (({i | (D.tile i).localAngle V = γ} : Finset (Fin N)).card : ℝ) * γ
      = Real.pi - β := by
  classical
  have hπ := Real.pi_pos
  have hαβ : α ≠ β := by
    intro h; apply hirr; refine ⟨1/5, ?_⟩; push_cast; linarith
  have key := Erdos634.VertexFigureReal.interior_multiplicities_cards D α β γ hαβ
    (by intro h; linarith) (by intro h; linarith) (by intro h; linarith) (by intro h; linarith)
    (by intro h; linarith) (by intro h; linarith) (by intro h; linarith) (by intro h; linarith)
    (by intro h; linarith) (by intro h; linarith) (by intro h; linarith)
    (by intro h; linarith) (by intro h; linarith) (by intro h; linarith) hV hvals
  have hcπ : 1 ≤ ({i | (D.tile i).localAngle V = Real.pi} : Finset (Fin N)).card :=
    Finset.card_pos.mpr ⟨k, by simp [hk]⟩
  have hcβ : 1 ≤ ({i | (D.tile i).localAngle V = β} : Finset (Fin N)).card :=
    Finset.card_pos.mpr ⟨t, by simp [ht]⟩
  set A := (({i | (D.tile i).localAngle V = α} : Finset (Fin N)).card : ℝ)
  set C := (({i | (D.tile i).localAngle V = γ} : Finset (Fin N)).card : ℝ)
  set nP := ({i | (D.tile i).localAngle V = Real.pi} : Finset (Fin N)).card with hnP
  set nB := ({i | (D.tile i).localAngle V = β} : Finset (Fin N)).card with hnB
  set n2 := ({i | (D.tile i).localAngle V = 2 * Real.pi} : Finset (Fin N)).card with hn2
  have hA : 0 ≤ A := Nat.cast_nonneg _
  have hC : 0 ≤ C := Nat.cast_nonneg _
  have hcπ' : (1 : ℝ) ≤ nP := by exact_mod_cast hcπ
  have hcβ' : (1 : ℝ) ≤ nB := by exact_mod_cast hcβ
  have hn2' : (0 : ℝ) ≤ n2 := Nat.cast_nonneg _
  have hγ0 : 0 < γ := by linarith
  have h2 : n2 = 0 := by
    by_contra h
    have : (1 : ℝ) ≤ n2 := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr h
    nlinarith [mul_nonneg hA hα.le, mul_nonneg hC hγ0.le]
  have hP1 : nP = 1 := by
    by_contra h
    have : (2 : ℝ) ≤ nP := by exact_mod_cast (show 2 ≤ nP by omega)
    nlinarith [mul_nonneg hA hα.le, mul_nonneg hC hγ0.le]
  refine ⟨hP1, h2, ?_⟩
  rw [hP1, h2] at key; push_cast at key
  linarith

end Erdos634.Draft.ThickEFminus1Steps

#print axioms Erdos634.Draft.ThickEFminus1Steps.a_rep_unique
#print axioms Erdos634.Draft.ThickEFminus1Steps.a_rep_unique_thick
#print axioms Erdos634.Draft.ThickEFminus1Steps.fill_rest
#print axioms Erdos634.Draft.ThickEFminus1Steps.flank_endpoint_below_iff
#print axioms Erdos634.Draft.ThickEFminus1Steps.flank_endpoint_below_thick
#print axioms Erdos634.Draft.ThickEFminus1Steps.no_straight_at_two_gamma
#print axioms Erdos634.Draft.ThickEFminus1Steps.corners_fill_pi_sub_beta
