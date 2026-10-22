-- Draft/LaczFormalT4.lean -- targets T2/T3/T4 of the L8-general plan, as far as they go (reptile theorem, SWW 1991):
-- for ANY N non-square and a dissection whose target is similar to the tile (same labels, ratio mu):
--   (a) if no model angle is a natural multiple of another (so the model is scalene), N = A^2 + B^2 and the tile is a
--       right triangle -- `Row2.theoremS_sorted` re-run WITHOUT primality (its only uses of primality were
--       `not_isSquare` and the final mod-4 step);
--   (b) otherwise (pi in 2*Lambda) all angles are rational multiples of pi with cosines in Q(sqrt N), so by T1/T2 the model is
--       one of: right isosceles (N = 2m^2 = m^2 + m^2: conclusion holds), 30-60-90 (N = 3m^2: conclusion holds),
--       30-30-120 (N = 3m^2), golden (36,72,72) or (36,36,108) (N = 5m^2): THE THREE UNRESOLVED MODELS.
-- Remaining for the full reptile theorem: kill the three unresolved models (SWW: they are not reptiles); see PLAN.md.
-- UNAUDITED.  Credit: Snover-Waiveris-Williams, Beeson (Triangle tiling I), Beeson-Rosu.
import Erdos634.Draft.LaczFormalT2
import Erdos634.Draft.LaczFormalL8Gen
import Erdos634.Draft.FluxERow2S
import Erdos634.Draft.LaczFormalL8Wit

open scoped Classical
open Real Erdos634.Geometry Erdos634.TilePlacement Erdos634.Draft.TheoremPConditional

namespace Erdos634.Draft.LaczFormal

/-- The tile is a right triangle (right angle at `k`) whose legs `i, j` have lengths in ratio `A : B`. -/
def RightLegs {N : ℕ} (D : CongruentDissection N) (A B : ℕ) : Prop :=
  ∃ i j k : Fin 3, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧ D.model.angleAt k = π / 2 ∧
    D.model.oppLen i * B = D.model.oppLen j * A

/-- **Sorted core, any `N` non-square**: `Row2.theoremS_sorted` without primality; concludes `N = A²+B²`, `γ = π/2`. -/
theorem sorted_general {N : ℕ} (D : CongruentDissection N) (μ : ℝ)
    (hsim : ∀ k, D.target.angleAt k = D.model.angleAt k ∧ D.target.oppLen k = μ * D.model.oppLen k)
    (hsq : ¬ IsSquare N)
    (h01 : D.model.angleAt 0 < D.model.angleAt 1) (h12 : D.model.angleAt 1 < D.model.angleAt 2)
    (hmult : ∀ k : ℕ, D.model.angleAt 1 ≠ k * D.model.angleAt 0)
    (hscal : ∀ k k', k ≠ k' → D.model.oppLen k ≠ D.model.oppLen k') :
    ∃ A B : ℕ, N = A ^ 2 + B ^ 2 ∧ D.model.angleAt 2 = π / 2 ∧
      D.model.oppLen 0 * B = D.model.oppLen 1 * A := by
  have hside : ∀ k, D.target.oppLen k = μ * D.model.oppLen k := fun k => (hsim k).2
  have hang : ∀ k, D.target.angleAt k = D.model.angleAt k := fun k => (hsim k).1
  have hA := Row2.cornerA D hang h01 h12
  have hB := Row2.cornerB D hang h01 h12 hmult
  obtain ⟨-, -, -, -, h22, -⟩ := Row2.lemmaD_tiling D μ hside hscal hsq hA hB
  have hR := Row2.lemmaR D hang h01 h12 (Row2.noc_of_sideCount D h22)
  obtain ⟨hμ, hp⟩ := Row2.mu_irrational D μ hside hsq
  obtain ⟨e0, e1, -⟩ := Row2.lemmaD_scale D.sideCount D.model.oppLen D.model.oppLen_pos hμ hp
    (Row2.sideCount_eigen D μ hside hscal) (Row2.sideCount_rows D hscal) hA hB
  have hμ2 : μ ^ 2 = N := by rw [hp]; push_cast; ring
  have hπ2 : D.model.angleAt 2 = π / 2 := by linarith
  have hcos : Real.cos (D.model.angleAt 2) = 0 := by rw [hπ2]; exact Real.cos_pi_div_two
  have hl := D.model.lawCos 2
  rw [hcos] at hl
  simp only [show (2 : Fin 3) + 1 = 0 from rfl, show (2 : Fin 3) + 2 = 1 from rfl] at hl
  have hc := D.model.oppLen_pos 2
  have hpy : D.model.oppLen 2 ^ 2 = D.model.oppLen 0 ^ 2 + D.model.oppLen 1 ^ 2 := by
    linarith [hl]
  have key : (N : ℝ) * D.model.oppLen 2 ^ 2
      = (((D.sideCount 0 2 : ℕ) : ℝ) ^ 2 + ((D.sideCount 1 2 : ℕ) : ℝ) ^ 2)
        * D.model.oppLen 2 ^ 2 := by
    have h1 : (N : ℝ) * D.model.oppLen 2 ^ 2
        = (μ * D.model.oppLen 0) ^ 2 + (μ * D.model.oppLen 1) ^ 2 := by
      rw [← hμ2, hpy]; ring
    rw [h1, e0, e1]; ring
  have hN' : (N : ℝ) = ((D.sideCount 0 2 : ℕ) : ℝ) ^ 2 + ((D.sideCount 1 2 : ℕ) : ℝ) ^ 2 :=
    mul_right_cancel₀ (pow_ne_zero 2 hc.ne') key
  have hμpos : 0 < μ := by
    have := (hside 0); have h1 := D.target.oppLen_pos 0; have h2 := D.model.oppLen_pos 0
    by_contra hc; push Not at hc; nlinarith
  refine ⟨_, _, by exact_mod_cast hN', hπ2, ?_⟩
  refine mul_left_cancel₀ hμpos.ne' ?_
  have hv0 := D.model.oppLen_pos 0
  linear_combination (D.sideCount 1 2 : ℝ) * e0 - (D.sideCount 0 2 : ℝ) * e1

/-- **Case (a), any vertex labelling:** no angle a natural multiple of another. -/
theorem no_multiple_case {N : ℕ} (D : CongruentDissection N) (μ : ℝ)
    (hsim : ∀ k, D.target.angleAt k = D.model.angleAt k ∧ D.target.oppLen k = μ * D.model.oppLen k)
    (hsq : ¬ IsSquare N)
    (hE : ∀ i j : Fin 3, i ≠ j → ∀ k : ℕ, D.model.angleAt j ≠ k * D.model.angleAt i) :
    ∃ A B : ℕ, N = A ^ 2 + B ^ 2 ∧ RightLegs D A B := by
  have hscal : ∀ i j : Fin 3, i ≠ j → D.model.oppLen i ≠ D.model.oppLen j := fun i j hij hl => by
    have := D.model.angle_eq_of_oppLen_eq hij hl
    exact hE i j hij 1 (by rw [this]; simp)
  have hdist : ∀ i j : Fin 3, i ≠ j → D.model.angleAt i ≠ D.model.angleAt j := fun i j hij h =>
    hE i j hij 1 (by rw [h]; simp)
  obtain ⟨σ, hmono⟩ : ∃ σ : Equiv.Perm (Fin 3), Monotone (D.model.angleAt ∘ σ) :=
    ⟨_, Tuple.monotone_sort _⟩
  have h01 : D.model.angleAt (σ 0) < D.model.angleAt (σ 1) :=
    lt_of_le_of_ne (hmono (show (0 : Fin 3) ≤ 1 by decide))
      (hdist _ _ (σ.injective.ne (by decide)))
  have h12 : D.model.angleAt (σ 1) < D.model.angleAt (σ 2) :=
    lt_of_le_of_ne (hmono (show (1 : Fin 3) ≤ 2 by decide))
      (hdist _ _ (σ.injective.ne (by decide)))
  let D' : CongruentDissection N :=
    { toDissection := Erdos634.NormalPosition.relabelTarget D.toDissection σ
      model := D.model.relabel σ
      tiles_congruent := fun i => (D.tiles_congruent i).relabel σ }
  have hTa := Row2.angleAt_comp D.target D'.target σ (fun k => rfl)
  have hMa := Row2.angleAt_comp D.model D'.model σ (fun k => rfl)
  have hsim' : ∀ k, D'.target.angleAt k = D'.model.angleAt k ∧
      D'.target.oppLen k = μ * D'.model.oppLen k := by
    intro k
    rw [(hTa k).1, (hMa k).1, (hTa k).2, (hMa k).2]
    exact hsim (σ k)
  obtain ⟨A, B, hAB, hr⟩ := sorted_general D' μ hsim' hsq
    (by rw [(hMa 0).1, (hMa 1).1]; exact h01) (by rw [(hMa 1).1, (hMa 2).1]; exact h12)
    (fun k => by rw [(hMa 1).1, (hMa 0).1]; exact hE (σ 0) (σ 1) (σ.injective.ne (by decide)) k)
    (fun k k' hkk' => by
      rw [(hMa k).2, (hMa k').2]
      exact hscal _ _ (σ.injective.ne hkk'))
  obtain ⟨hr, hleg⟩ := hr
  refine ⟨A, B, hAB, σ 0, σ 1, σ 2, σ.injective.ne (by decide), σ.injective.ne (by decide),
    σ.injective.ne (by decide), by rw [← (hMa 2).1]; exact hr, ?_⟩
  rw [← (hMa 0).2, ← (hMa 1).2]; exact hleg

/-- The rationality half of `Row2.lemmaE_abs` (no primality): if `θ_j = k θ_i` and `π ∈ 2Λ`, all angles are in `ℚπ`. -/
theorem rat_of_multiple (θ : Fin 3 → ℝ) (hsum : θ 0 + θ 1 + θ 2 = π)
    (hπ : ∃ y ∈ AddSubgroup.closure ({θ 0, θ 1, π} : Set ℝ), π = 2 * y)
    {i j : Fin 3} (hij : i ≠ j) (k : ℕ) (hjk : θ j = k * θ i) : ∀ l, ∃ r : ℚ, θ l = r * π := by
  set H : AddSubgroup ℝ := AddSubgroup.zmultiples (θ i) ⊔ AddSubgroup.zmultiples π with hH
  have mem : ∀ a b : ℤ, (a : ℝ) * θ i + b * π ∈ H := by
    intro a b
    refine AddSubgroup.mem_sup.mpr ⟨a * θ i, ?_, b * π, ?_, rfl⟩
    · exact AddSubgroup.mem_zmultiples_iff.mpr ⟨a, by rw [zsmul_eq_mul]⟩
    · exact AddSubgroup.mem_zmultiples_iff.mpr ⟨b, by rw [zsmul_eq_mul]⟩
  have hall : ∀ l, θ l ∈ H := by
    intro l
    by_cases hli : l = i
    · rw [hli]; simpa using mem 1 0
    by_cases hlj : l = j
    · rw [hlj, hjk]; simpa using mem k 0
    · rw [Row2.third_angle θ hsum hij hli hlj, hjk]
      have := mem (-(k : ℤ) - 1) 1
      convert this using 1
      push_cast; ring
  have hle : AddSubgroup.closure ({θ 0, θ 1, π} : Set ℝ) ≤ H := by
    rw [AddSubgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact hall 0
    · exact hall 1
    · simpa using mem 0 1
  obtain ⟨y, hyΛ, hy⟩ := hπ
  obtain ⟨u, hu, w, hw, huw⟩ := AddSubgroup.mem_sup.mp (hle hyΛ)
  obtain ⟨m, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hu
  obtain ⟨n, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hw
  rw [zsmul_eq_mul, zsmul_eq_mul] at huw
  rw [← huw] at hy
  have hm : m ≠ 0 := by
    rintro rfl
    have h0 : (1 - 2 * (n : ℝ)) * π = 0 := by push_cast at hy; linear_combination hy
    have h1 : (1 : ℝ) - 2 * n = 0 := (mul_eq_zero.mp h0).resolve_right Real.pi_ne_zero
    have h2 : (1 : ℤ) - 2 * n = 0 := by exact_mod_cast h1
    omega
  have hm' : (2 * (m : ℝ)) ≠ 0 := mul_ne_zero two_ne_zero (by exact_mod_cast hm)
  have hφrat : θ i = (((1 - 2 * n : ℤ) : ℚ) / (2 * m) : ℚ) * π := by
    have e : (2 * (m : ℝ)) * θ i = (1 - 2 * n) * π := by linear_combination (-1 : ℝ) * hy
    push_cast
    rw [div_mul_eq_mul_div, eq_div_iff hm']
    linear_combination e
  intro l
  have hrat : ∀ l, ∃ r : ℚ, θ l = r * π := by
    intro l
    obtain ⟨u', hu', w', hw', huw'⟩ := AddSubgroup.mem_sup.mp (hall l)
    obtain ⟨a, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hu'
    obtain ⟨b, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hw'
    rw [zsmul_eq_mul, zsmul_eq_mul, hφrat] at huw'
    exact ⟨a * (((1 - 2 * n : ℤ) : ℚ) / (2 * m)) + b, by rw [← huw']; push_cast; ring⟩
  exact hrat l

/-- **Reptile theorem, partial (any N non-square).**  A dissection whose target is similar to the tile:
either the tile is a right triangle with `N = A²+B²`, or it is the 30-60-90 triangle with `N = 3m²`
(both are conclusions of SWW's theorem), or it is one of THREE UNRESOLVED models: 30-30-120 (`N = 3m²`),
the golden triangles (36,72,72) / (36,36,108) (`N = 5m²`). -/
theorem similar_partial {N : ℕ} (D : CongruentDissection N) (μ : ℝ)
    (hsim : ∀ k, D.target.angleAt k = D.model.angleAt k ∧ D.target.oppLen k = μ * D.model.oppLen k)
    (hN : ¬ IsSquare N) :
    (∃ A B : ℕ, N = A ^ 2 + B ^ 2 ∧ RightLegs D A B) ∨
    ((∃ m : ℕ, N = 3 * m ^ 2) ∧ TileAngles D (π / 6) (π / 3) (π / 2)) ∨
    ((∃ m : ℕ, N = 3 * m ^ 2) ∧ TileAngles D (π / 6) (π / 6) (2 * π / 3)) ∨
    ((∃ m : ℕ, N = 5 * m ^ 2) ∧ TileAngles D (π / 5) (2 * π / 5) (2 * π / 5)) ∨
    ((∃ m : ℕ, N = 5 * m ^ 2) ∧ TileAngles D (π / 5) (π / 5) (3 * π / 5)) := by
  obtain ⟨⟨hNμ, hμq⟩, hπ, -, hnot, hcos⟩ := similar_reduction D μ hsim hN
  have hside : ∀ k, D.target.oppLen k = μ * D.model.oppLen k := fun k => (hsim k).2
  have hμ2 : μ ^ 2 = N := hNμ.symm
  by_cases hE : ∀ i j : Fin 3, i ≠ j → ∀ k : ℕ, D.model.angleAt j ≠ k * D.model.angleAt i
  · exact Or.inl (no_multiple_case D μ hsim hN hE)
  push Not at hE
  obtain ⟨i, j, hij, k, hjk⟩ := hE
  have hsum := angleAt_sum D.model
  have hrat := rat_of_multiple D.model.angleAt hsum hπ hij k hjk
  have htag : ∀ l, TagOK N (D.model.angleAt l) := by
    intro l
    have hl0 := D.model.angleAt_pos' l
    have hlπ : D.model.angleAt l < π := by
      have h0 := D.model.angleAt_pos' 0
      have h1 := D.model.angleAt_pos' 1
      have h2 := D.model.angleAt_pos' 2
      rcases (show l = 0 ∨ l = 1 ∨ l = 2 by fin_cases l <;> simp) with rfl | rfl | rfl <;> linarith
    exact tagOK_of_Q (lemmaQ_general hN hμ2 (hrat l) hl0 hlπ (hcos l))
  rcases class_of_rational D htag with hall | ⟨⟨m, hm⟩, hT⟩ | h | h | h | h
  · exfalso
    have hsin : Real.sin (π / 3) ≠ 0 :=
      (Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [Real.pi_pos])).ne'
    have hs : ∀ i j, D.model.oppLen i = D.model.oppLen j := by
      intro i j
      have h := D.model.lawSin i j
      rw [hall i, hall j] at h
      exact (mul_left_cancel₀ hsin h).symm
    exact hnot ⟨⟨1, by rw [hs 0 2]; simp⟩, ⟨1, by rw [hs 1 2]; simp⟩⟩
  · left
    obtain ⟨σ, h0, h1, h2⟩ := hT
    refine ⟨m, m, by rw [hm]; ring, σ 0, σ 1, σ 2, σ.injective.ne (by decide),
      σ.injective.ne (by decide), σ.injective.ne (by decide), h2, ?_⟩
    have hl := D.model.lawSin (σ 0) (σ 1)
    rw [h0, h1] at hl
    have hsp : 0 < Real.sin (π / 4) := Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [Real.pi_pos])
    have := mul_left_cancel₀ hsp.ne' (by linarith : Real.sin (π / 4) * D.model.oppLen (σ 1) = Real.sin (π / 4) * D.model.oppLen (σ 0))
    rw [this]
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr h)))

/-- `similar_partial` for an arbitrary vertex correspondence (`SimilarTM`). -/
theorem similar_partial_of_similarTM {N : ℕ} (D : CongruentDissection N) (hs : SimilarTM D)
    (hN : ¬ IsSquare N) :
    (∃ A B : ℕ, N = A ^ 2 + B ^ 2 ∧ RightLegs D A B) ∨
    ((∃ m : ℕ, N = 3 * m ^ 2) ∧ TileAngles D (π / 6) (π / 3) (π / 2)) ∨
    ((∃ m : ℕ, N = 3 * m ^ 2) ∧ TileAngles D (π / 6) (π / 6) (2 * π / 3)) ∨
    ((∃ m : ℕ, N = 5 * m ^ 2) ∧ TileAngles D (π / 5) (2 * π / 5) (2 * π / 5)) ∨
    ((∃ m : ℕ, N = 5 * m ^ 2) ∧ TileAngles D (π / 5) (π / 5) (3 * π / 5)) := by
  obtain ⟨μ, τ, h⟩ := hs
  have hMa := Row2.angleAt_comp D.model (D.relabelModel τ).model τ (fun k => rfl)
  have hsim : ∀ k, (D.relabelModel τ).target.angleAt k = (D.relabelModel τ).model.angleAt k ∧
      (D.relabelModel τ).target.oppLen k = μ * (D.relabelModel τ).model.oppLen k := fun k => by
    rw [(hMa k).1, (hMa k).2]; exact h k
  have tr : ∀ {x y z : ℝ}, TileAngles (D.relabelModel τ) x y z → TileAngles D x y z := by
    rintro x y z ⟨σ, h0, h1, h2⟩
    refine ⟨σ.trans τ, ?_, ?_, ?_⟩
    · rw [Equiv.trans_apply, ← (hMa (σ 0)).1]; exact h0
    · rw [Equiv.trans_apply, ← (hMa (σ 1)).1]; exact h1
    · rw [Equiv.trans_apply, ← (hMa (σ 2)).1]; exact h2
  rcases similar_partial (D.relabelModel τ) μ hsim hN with ⟨A, B, hAB, hk⟩ | ⟨m, hT⟩ | ⟨m, hT⟩ | ⟨m, hT⟩ | ⟨m, hT⟩
  · obtain ⟨i, j, k, hij, hik, hjk, hk, hl⟩ := hk
    exact Or.inl ⟨A, B, hAB, τ i, τ j, τ k, τ.injective.ne hij, τ.injective.ne hik, τ.injective.ne hjk,
      by rw [← (hMa k).1]; exact hk, by rw [← (hMa i).2, ← (hMa j).2]; exact hl⟩
  · exact Or.inr (Or.inl ⟨m, tr hT⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨m, tr hT⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨m, tr hT⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨m, tr hT⟩)))

end Erdos634.Draft.LaczFormal

#print axioms Erdos634.Draft.LaczFormal.sorted_general
#print axioms Erdos634.Draft.LaczFormal.no_multiple_case
#print axioms Erdos634.Draft.LaczFormal.rat_of_multiple
#print axioms Erdos634.Draft.LaczFormal.similar_partial
#print axioms Erdos634.Draft.LaczFormal.similar_partial_of_similarTM
