-- Draft/FluxERow2S.lean — ROW 2, THEOREM S ASSEMBLED ((private working notes, not included) §5 "Proof of
-- Theorem S"): a `CongruentDissection` whose target is similar to its model has a prime tile count
-- `N ≢ 3 (mod 4)` or `N = 3`.  Imported via AllNew8.lean → All.lean:853 (stale "NOT imported" header corrected 2026-10-04).
--
-- Chain (all cited, none re-derived here):
--   Lemma W  `Row2.lemmaW_not_prime` (Draft/FluxCRow2)            — so `π ∈ 2Λ`;
--   Lemma E  `Row2.lemmaE` (Draft/FluxERow2E, with Lemma Q Draft/FluxERow2Q and Lemma K any-model)
--            — no angle a natural multiple of another, model scalene;
--   sorting  Mathlib `Tuple.sort`; relabelling target and model by the same permutation
--            (`NormalPosition.relabelTarget`, `Tri.relabel`; `Row2.angleAt_comp`);
--   (A), (B) `Row2.cornerA`, `Row2.cornerB` (Draft/FluxERow2C);
--   Lemma D  `Row2.lemmaD_tiling`, `Row2.lemmaD_scale` (Draft/FluxDRow2S1, Draft/FluxDRow2D);
--   Lemma R  `Row2.lemmaR` (Draft/FluxERow2R);
--   S3       `Row2.mu_irrational` (`N = μ²`);
--   then `γ = π/2`, Pythagoras `c² = a² + b²`, `μa = A c`, `μb = B c` give `N = A² + B²`, and a sum of
--   two squares is never `3 (mod 4)` (`Row2.sq_add_sq_mod_four`).
--
-- * `Row2.theoremS_sorted`: the core, for a model with `angleAt 0 < angleAt 1 < angleAt 2`.
-- * `Row2.theoremS`: similarity with the same vertex labels (the corpus's convention, as in
--   `Row2.lemmaW`): `target.angleAt k = model.angleAt k`, `target.oppLen k = μ · model.oppLen k`.
-- * `Row2.theoremS_perm`: any vertex correspondence `τ` (the model relabelled, `relabelModel`).
--
-- WITNESS (Rule: every hypothesis): Theorem S's hypotheses cannot all hold (that is its content).
-- Every hypothesis except the arithmetic of `N` is met by the real `FluxRow2Witness.D2` (target =
-- 2·model, `N = 4`): Draft/FluxERow2Witness.lean runs `Row2.theoremS` on it (conclusion `4 % 4 ≠ 3`;
-- `Nat.Prime 4` fails, stated).  The sorted core's corner lemmas are run on `D2` relabelled.
--
-- Formalization debt; not progress on the three /goal outcomes (row 2 of thm:main at primes
-- `≡ 3 mod 4` is already PROVED at paper level; this moves it toward VERIFIED).
import Erdos634.Draft.FluxERow2R
import Erdos634.NormalPosition
import Mathlib.Data.Fin.Tuple.Sort

open scoped Classical

namespace Erdos634.Geometry

open Real

variable {N : ℕ}

theorem Row2.fin3_rot : ∀ a b c : Fin 3, b ≠ a → c ≠ a → b ≠ c →
    (b = a + 1 ∧ c = a + 2) ∨ (b = a + 2 ∧ c = a + 1) := by decide

theorem Row2.perm_succ (σ : Equiv.Perm (Fin 3)) (k : Fin 3) :
    (σ (k + 1) = σ k + 1 ∧ σ (k + 2) = σ k + 2) ∨ (σ (k + 1) = σ k + 2 ∧ σ (k + 2) = σ k + 1) := by
  have h1 : k + 1 ≠ k := by
    have : ∀ a : Fin 3, a + 1 ≠ a := by decide
    exact this k
  have h2 : k + 2 ≠ k := by
    have : ∀ a : Fin 3, a + 2 ≠ a := by decide
    exact this k
  have h12 : k + 1 ≠ k + 2 := by
    have : ∀ a : Fin 3, a + 1 ≠ a + 2 := by decide
    exact this k
  exact Row2.fin3_rot _ _ _ (fun h => h1 (σ.injective h)) (fun h => h2 (σ.injective h))
    (fun h => h12 (σ.injective h))

/-- **Angles and sides of a relabelled triangle**: if `U.pts = T.pts ∘ σ`, then
`U.angleAt k = T.angleAt (σ k)` and `U.oppLen k = T.oppLen (σ k)`. -/
theorem Row2.angleAt_comp (T U : Tri) (σ : Equiv.Perm (Fin 3)) (hU : ∀ k, U.pts k = T.pts (σ k))
    (k : Fin 3) : U.angleAt k = T.angleAt (σ k) ∧ U.oppLen k = T.oppLen (σ k) := by
  unfold Tri.angleAt Tri.oppLen
  simp only [hU]
  rcases Row2.perm_succ σ k with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]; exact ⟨rfl, rfl⟩
  · rw [h1, h2]; exact ⟨EuclideanGeometry.angle_comm _ _ _, dist_comm _ _⟩

/-- A sum of two squares is never `3 (mod 4)`. -/
theorem Row2.sq_add_sq_mod_four (x y : ℕ) : (x ^ 2 + y ^ 2) % 4 ≠ 3 := by
  have hx : x % 4 = 0 ∨ x % 4 = 1 ∨ x % 4 = 2 ∨ x % 4 = 3 := by omega
  have hy : y % 4 = 0 ∨ y % 4 = 1 ∨ y % 4 = 2 ∨ y % 4 = 3 := by omega
  rw [Nat.add_mod, Nat.pow_mod, Nat.pow_mod y]
  rcases hx with h | h | h | h <;> rcases hy with h' | h' | h' | h' <;> rw [h, h'] <;> norm_num

/-- **Theorem S, sorted core.**  A tile-similar `N`-tiling (same labels, ratio `μ`), `N` prime,
`N ≡ 3 (mod 4)`, with a scalene model whose angles satisfy `angleAt 0 < angleAt 1 < angleAt 2` and
`angleAt 1 ∉ ℕ·angleAt 0`, does not exist. -/
theorem Row2.theoremS_sorted (D : CongruentDissection N) (μ : ℝ)
    (hsim : ∀ k, D.target.angleAt k = D.model.angleAt k ∧ D.target.oppLen k = μ * D.model.oppLen k)
    (hN : N.Prime) (hN4 : N % 4 = 3)
    (h01 : D.model.angleAt 0 < D.model.angleAt 1) (h12 : D.model.angleAt 1 < D.model.angleAt 2)
    (hmult : ∀ k : ℕ, D.model.angleAt 1 ≠ k * D.model.angleAt 0)
    (hscal : ∀ k k', k ≠ k' → D.model.oppLen k ≠ D.model.oppLen k') : False := by
  have hsq : ¬ IsSquare N := hN.prime.not_isSquare
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
  -- Lemma R: `γ = π/2`, so Pythagoras
  have hcos : Real.cos (D.model.angleAt 2) = 0 := by
    rw [show D.model.angleAt 2 = π / 2 by linarith]; exact Real.cos_pi_div_two
  have hl := D.model.lawCos 2
  rw [hcos] at hl
  simp only [show (2 : Fin 3) + 1 = 0 from rfl, show (2 : Fin 3) + 2 = 1 from rfl] at hl
  have hc := D.model.oppLen_pos 2
  have hpy : D.model.oppLen 2 ^ 2 = D.model.oppLen 0 ^ 2 + D.model.oppLen 1 ^ 2 := by
    linarith [hl]
  -- `N c² = (μa)² + (μb)² = (A² + B²) c²`
  have key : (N : ℝ) * D.model.oppLen 2 ^ 2
      = (((D.sideCount 0 2 : ℕ) : ℝ) ^ 2 + ((D.sideCount 1 2 : ℕ) : ℝ) ^ 2)
        * D.model.oppLen 2 ^ 2 := by
    have h1 : (N : ℝ) * D.model.oppLen 2 ^ 2
        = (μ * D.model.oppLen 0) ^ 2 + (μ * D.model.oppLen 1) ^ 2 := by
      rw [← hμ2, hpy]; ring
    rw [h1, e0, e1]; ring
  have hN' : (N : ℝ) = ((D.sideCount 0 2 : ℕ) : ℝ) ^ 2 + ((D.sideCount 1 2 : ℕ) : ℝ) ^ 2 :=
    mul_right_cancel₀ (pow_ne_zero 2 hc.ne') key
  have hNnat : N = D.sideCount 0 2 ^ 2 + D.sideCount 1 2 ^ 2 := by exact_mod_cast hN'
  rw [hNnat] at hN4
  exact Row2.sq_add_sq_mod_four _ _ hN4

/-- **Theorem S (row 2).**  Let `D` be a dissection of a triangle into `N` congruent copies of a
tile (reflections allowed, not necessarily edge-to-edge) whose target is similar to the tile with
ratio `μ` (same vertex labels: `target.angleAt k = model.angleAt k`,
`target.oppLen k = μ · model.oppLen k`).  If `N` is prime, then `N ≢ 3 (mod 4)` or `N = 3`. -/
theorem Row2.theoremS (D : CongruentDissection N) (μ : ℝ)
    (hsim : ∀ k, D.target.angleAt k = D.model.angleAt k ∧ D.target.oppLen k = μ * D.model.oppLen k)
    (hN : N.Prime) : N % 4 ≠ 3 ∨ N = 3 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hN4, hN3⟩ := hcon
  have hN7 : 7 ≤ N := by have := hN.two_le; omega
  have hside : ∀ k, D.target.oppLen k = μ * D.model.oppLen k := fun k => (hsim k).2
  -- Lemma W: `π ∈ 2Λ`
  have hπ : ∃ y ∈ AddSubgroup.closure ({D.model.angleAt 0, D.model.angleAt 1, π} : Set ℝ),
      π = 2 * y := by
    by_contra hc
    push Not at hc
    exact Row2.lemmaW_not_prime D μ hsim hc hN
  -- Lemma E
  obtain ⟨hE, hscal⟩ := Row2.lemmaE D μ hside hN hN4 hN7 hπ
  have hdist : ∀ i j : Fin 3, i ≠ j → D.model.angleAt i ≠ D.model.angleAt j := fun i j hij h =>
    hE i j hij 1 (by rw [h]; simp)
  -- sort the angles
  obtain ⟨σ, hmono⟩ : ∃ σ : Equiv.Perm (Fin 3), Monotone (D.model.angleAt ∘ σ) :=
    ⟨_, Tuple.monotone_sort _⟩
  have h01 : D.model.angleAt (σ 0) < D.model.angleAt (σ 1) :=
    lt_of_le_of_ne (hmono (show (0 : Fin 3) ≤ 1 by decide))
      (hdist _ _ (σ.injective.ne (by decide)))
  have h12 : D.model.angleAt (σ 1) < D.model.angleAt (σ 2) :=
    lt_of_le_of_ne (hmono (show (1 : Fin 3) ≤ 2 by decide))
      (hdist _ _ (σ.injective.ne (by decide)))
  -- relabel target and model by `σ`
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
  refine Row2.theoremS_sorted D' μ hsim' hN hN4 ?_ ?_ ?_ ?_
  · rw [(hMa 0).1, (hMa 1).1]; exact h01
  · rw [(hMa 1).1, (hMa 2).1]; exact h12
  · intro k
    rw [(hMa 1).1, (hMa 0).1]
    exact hE (σ 0) (σ 1) (σ.injective.ne (by decide)) k
  · intro k k' hkk'
    rw [(hMa k).2, (hMa k').2]
    exact hscal _ _ (σ.injective.ne hkk')

/-- **Theorem S, any vertex correspondence** `τ` between target and model. -/
theorem Row2.theoremS_perm (D : CongruentDissection N) (μ : ℝ) (τ : Equiv.Perm (Fin 3))
    (hsim : ∀ k, D.target.angleAt k = D.model.angleAt (τ k) ∧
      D.target.oppLen k = μ * D.model.oppLen (τ k))
    (hN : N.Prime) : N % 4 ≠ 3 ∨ N = 3 := by
  have hMa := Row2.angleAt_comp D.model (D.relabelModel τ).model τ (fun k => rfl)
  refine Row2.theoremS (D.relabelModel τ) μ (fun k => ?_) hN
  rw [(hMa k).1, (hMa k).2]
  exact hsim k

end Erdos634.Geometry

#print axioms Erdos634.Geometry.Row2.angleAt_comp
#print axioms Erdos634.Geometry.Row2.sq_add_sq_mod_four
#print axioms Erdos634.Geometry.Row2.theoremS_sorted
#print axioms Erdos634.Geometry.Row2.theoremS
#print axioms Erdos634.Geometry.Row2.theoremS_perm
