import Mathlib
import Erdos634.Draft.BeesonRosu37
import Erdos634.Draft.SideRunGMain
import Erdos634.Draft.SideRunGCornerMainB

/-!
# Beeson-Rosu Theorem 37, Lemma 34 from the project's own side-run machinery (tile `(km, k^2-m^2, k^2)` = base-beta `(ef, f^2-e^2, f^2)`, `e = m`, `f = k`)

NOTE, UNAUDITED.  Credit: Michael Beeson and Rosu (arXiv 2607.23453 v2, Lemma 34, Lemma 30(D), Theorem 37), Beeson (arXiv 1206.2229
v4), Laczkovich.  Formalization debt, not progress on the /goal outcomes.

AUDIT WARNING 2026-10-22 (automated audit AUDIT_UNAUDITED_2026-10-22L): the existential conclusions of base_edges, leg_counts_thick (as used in thm37_no_a_edges_thick) are witnessed by (0,m,2m) / (0,0,k) by arithmetic alone, so the 'no a edge' claim is NOT in those statements; the tie to the chain's letters is only in the proofs. Do not cite them as geometry. The tied statement (counts = explicit sums of cA over the chain) is in BeesonRosu37c4a.counts_sums and the final theorem to come. base_counts (k<=z with the equation) is non-hollow; its (3,8,9)-(27,27,26) case agrees with the registry row NO_TILING (N=26).

STATEMENT MATCH (printed Lemma 34, as quoted in (private working notes, not included) and `paper_v2_outline.md`: "a side supports a run of
>= k consecutive c edges"; the v2 text itself is not in (private working notes, not included), only v1, which has no Lemma 34).  The tile of Thm 37,
`(a,b,c) = (km, k^2-m^2, k^2)`, IS the base-beta tile `(ef, f^2-e^2, f^2)` with `e = m`, `f = k`; the isosceles-beta triangle
`(beta, beta, 3 alpha)` with legs `k c = k^3` and base `m (b + 2c) = m (3k^2 - m^2)` IS `T_1(e, f)` (`SideRunGMain.thm_siderunall_T`).

* BASE `AC` (corners beta, beta): `base_counts`: `x a + y b + z c = m(3k^2-m^2)` with `k <= z` (Lemma 34 on `AC`; DERIVED from
  `setup_TG`, `side_theoremG_chain`, `sideG_counts`).  `base_edges`: with Lemma 30(D) the decomposition is `(0, m, 2m)`.
* LEG `AB` (corners beta at A, 3 alpha at B): `leg_counts`: counts `x a + y b + z c = k^3` and either `k <= z` or a stopped-at-the-
  corner run `C1^k'` with `m + 1 <= k' <= k - 1` (`thm:cornerrun` (ii), counted: `k' <= z`).  `leg_counts_thick`: for `m + 1 = k`
  the second alternative is empty, so `k <= z` (Lemma 34 on `AB`, thick members ONLY).
* `leg_p1_zero`: `k <= r1` forces `p1 = 0` on the leg (the arithmetic of `thm37_edges`, exposed).
* `thm37_no_a_edges_thick`: thick members (`m + 1 = k`), a dissection of `T_1(m,k)` (sides AND the corner angles named): there are
  counts of `AC` and `AB` with `p0 = 0` and `p1 = 0`, i.e. NEITHER side carries an `a` edge.

NOT PROVED (quoted exactly): the printed step (3), "the tile at `A` has beta at `A`, so an `a` edge lies on `AB` or `AC`", as a statement
about THESE counts.  The counts are existentials produced by two different typed chains (the chain of `AC` in the normal form of
`setup_TG`, the chain of `AB` in the normal form of `setup_of_corners`); the corner tile is the last tile of both chains, but that
identification across two normal forms is not in the repository (`rB`/`rB_A` say the last tile of a side at a beta corner is `A2` or
`C1`, which is the one-chain half).  Also not proved: Lemma 34 for the leg when `m + 1 < k` (alternative (ii) is not excluded
there), and the angle hypotheses of the leg are NAMED (they hold for the coordinate triangle: `BaseBetaTargetCoord.cornerAngle_apex`,
`cornerAngle_base₀/₁`; the passage from the printed side lengths to these angles for an arbitrary dissection is not written).
-/

open scoped Classical
set_option linter.unusedVariables false

namespace Erdos634.BeesonRosu37b1

open Erdos634.Geometry Erdos634.Draft.FDBBaseBetaE1 Erdos634.Draft.SideRunG Erdos634.Draft.SideRunGA
  Erdos634.Draft.SideRun Erdos634.Draft.W2E1 Erdos634.BaseBetaTargetCoord Erdos634.TilePlacement Erdos634.Geometry.Dissection

variable {N : ℕ}

/-- **Lemma 34 on the base `AC`** (corners beta, beta; `T_1(m, k)`): the edge decomposition `x a + y b + z c` of the base has `k <= z`. -/
theorem base_counts (k m : ℕ) (hm : 1 ≤ m) (hmk : m < k) (hco : Nat.Coprime m k) (D₀ : CongruentDissection N)
    (hT : HasSides D₀.target ((k : ℝ) ^ 3) ((k : ℝ) ^ 3) ((m : ℝ) * (3 * (k : ℝ) ^ 2 - (m : ℝ) ^ 2)))
    (hMod : HasSides D₀.model ((m : ℝ) * k) ((k : ℝ) ^ 2 - (m : ℝ) ^ 2) ((k : ℝ) ^ 2)) :
    ∃ x y z : ℕ, (x : ℤ) * ((k : ℤ) * m) + y * ((k : ℤ) ^ 2 - (m : ℤ) ^ 2) + z * (k : ℤ) ^ 2 =
        (m : ℤ) * (((k : ℤ) ^ 2 - (m : ℤ) ^ 2) + 2 * (k : ℤ) ^ 2) ∧ k ≤ z := by
  have hT' : HasSides D₀.target ((1 : ℝ) * (k : ℝ) ^ 3) ((1 : ℝ) * (k : ℝ) ^ 3)
      ((1 : ℝ) * ((m : ℝ) * (3 * (k : ℝ) ^ 2 - (m : ℝ) ^ 2))) := by simpa only [one_mul] using hT
  obtain ⟨D, g, k₀, k₁, ax, ay, -, -, -, -, S, Co⟩ := setup_TG m k hm hmk hco one_pos D₀ hT' hMod
  obtain ⟨c, X, tile, τ, Ch, hrun⟩ := S.side_theoremG_chain Co
  obtain ⟨x, y, z, hxyz, hz⟩ := S.sideG_counts Ch
  refine ⟨x, y, z, ?_, hz hrun⟩
  have : (((x : ℤ) * ((k : ℤ) * m) + y * ((k : ℤ) ^ 2 - (m : ℤ) ^ 2) + z * (k : ℤ) ^ 2 : ℤ) : ℝ) =
      (((m : ℤ) * (((k : ℤ) ^ 2 - (m : ℤ) ^ 2) + 2 * (k : ℤ) ^ 2) : ℤ) : ℝ) := by
    push_cast
    linarith [hxyz]
  exact_mod_cast this

/-- Base: Lemma 34 and Lemma 30(D) give the decomposition `(0, m, 2m)`. -/
theorem base_edges (k m : ℕ) (hm : 1 ≤ m) (hmk : m < k) (hco : Nat.Coprime m k) (D₀ : CongruentDissection N)
    (hT : HasSides D₀.target ((k : ℝ) ^ 3) ((k : ℝ) ^ 3) ((m : ℝ) * (3 * (k : ℝ) ^ 2 - (m : ℝ) ^ 2)))
    (hMod : HasSides D₀.model ((m : ℝ) * k) ((k : ℝ) ^ 2 - (m : ℝ) ^ 2) ((k : ℝ) ^ 2)) :
    ∃ x y z : ℕ, x = 0 ∧ y = m ∧ z = 2 * m ∧
      (x : ℤ) * ((k : ℤ) * m) + y * ((k : ℤ) ^ 2 - (m : ℤ) ^ 2) + z * (k : ℤ) ^ 2 =
        (m : ℤ) * (((k : ℤ) ^ 2 - (m : ℤ) ^ 2) + 2 * (k : ℤ) ^ 2) := by
  obtain ⟨x, y, z, h, hz⟩ := base_counts k m hm hmk hco D₀ hT hMod
  have hcz : IsCoprime (m : ℤ) (k : ℤ) := Nat.isCoprime_iff_coprime.mpr hco
  have hD := Erdos634.BeesonRowL30.lemma30_D (k := (k : ℤ)) (m := (m : ℤ)) (by exact_mod_cast hm)
    (by exact_mod_cast hmk) hcz (Int.natCast_nonneg x) (Int.natCast_nonneg y) (by exact_mod_cast hz) h
  refine ⟨x, y, z, by exact_mod_cast hD.1, by exact_mod_cast hD.2.1, by exact_mod_cast hD.2.2, h⟩


/-- `SetupG.sideG_counts` with the run bound for EVERY run (`n` consecutive `C1` or `C2` tiles give `n <= z`), same proof. -/
theorem counts_gen {e f : ℕ} {α β γ L ax ay : ℝ} {D : CongruentDissection N} {c : ℕ} {X : ℕ → ℝ} {tile : ℕ → Fin N}
    {τ : ℕ → Ty} (S : SetupG D e f α β γ L ax ay) (Ch : ChainG D e f L c X tile τ) :
    ∃ x y z : ℕ, (x : ℝ) * ((e : ℝ) * f) + y * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) + z * (f : ℝ) ^ 2 = L ∧
      ((∃ i, i + f ≤ c ∧ ((∀ j, j < f → τ (i + j) = Ty.C1) ∨ (∀ j, j < f → τ (i + j) = Ty.C2))) → f ≤ z) ∧
      (∀ i n, i + n ≤ c → ((∀ j, j < n → τ (i + j) = Ty.C1) ∨ (∀ j, j < n → τ (i + j) = Ty.C2)) → n ≤ z) := by
  have hsub : (((f ^ 2 - e ^ 2 : ℕ)) : ℝ) = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
    rw [Nat.cast_sub (Nat.pow_le_pow_left S.hef.le 2)]; push_cast; ring
  have hN : ∑ k ∈ Finset.range c, lenN e f (τ k)
      = (∑ k ∈ Finset.range c, (τ k).cA) * (e * f) + (∑ k ∈ Finset.range c, (τ k).cB) * (f ^ 2 - e ^ 2)
        + (∑ k ∈ Finset.range c, (τ k).cC) * f ^ 2 := by
    simp only [lenN, Finset.sum_add_distrib, Finset.sum_mul]
  have h1 : ∀ k ∈ Finset.range c, (τ k).lenG (e : ℝ) (f : ℝ) = X (k + 1) - X k := by
    intro k hk
    rw [Ch.hstep k (Finset.mem_range.mp hk)]; ring
  have h2 : L = ∑ k ∈ Finset.range c, (τ k).lenG (e : ℝ) (f : ℝ) := by
    rw [Finset.sum_congr rfl h1, Finset.sum_range_sub, Ch.hXm, Ch.hX0, sub_zero]
  have h3 : ∑ k ∈ Finset.range c, (τ k).lenG (e : ℝ) (f : ℝ)
      = ((∑ k ∈ Finset.range c, lenN e f (τ k) : ℕ) : ℝ) := by
    rw [Nat.cast_sum]; exact Finset.sum_congr rfl (fun k _ => lenG_cast S.hef (τ k))
  refine ⟨∑ k ∈ Finset.range c, (τ k).cA, ∑ k ∈ Finset.range c, (τ k).cB,
    ∑ k ∈ Finset.range c, (τ k).cC, ?_, ?_, ?_⟩
  · rw [h2, h3, hN]
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, hsub]
  · rintro ⟨i, him, hrun⟩
    exact Erdos634.Draft.SideRun.cC_run τ i f c him hrun
  · intro i n him hrun
    exact Erdos634.Draft.SideRun.cC_run τ i n c him hrun

/-- **Lemma 34 on the leg `AB`** (corner `3 alpha` at `B = τ 0`, `beta` at `A = τ 1`; leg length `k^3`), as `thm:cornerrun`: either `k <= z`,
or `z >= k'` for a corner run `C1^k'` with `m + 1 <= k' <= k - 1`. -/
theorem leg_counts (k m : ℕ) (hm : 1 ≤ m) (hmk : m < k) (hco : Nat.Coprime m k) (D₀ : CongruentDissection N)
    (hMod : HasSides D₀.model ((m : ℝ) * k) ((k : ℝ) ^ 2 - (m : ℝ) ^ 2) ((k : ℝ) ^ 2))
    (τ : Equiv.Perm (Fin 3))
    (hApex : cornerAngle (D₀.target.pts (τ 2)) (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) =
      3 * modelAlpha (m : ℝ) (k : ℝ))
    (hBeta : cornerAngle (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) (D₀.target.pts (τ 2)) =
      modelBeta (m : ℝ) (k : ℝ))
    (hlen : dist (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) = (k : ℝ) ^ 3) :
    ∃ x y z : ℕ, (x : ℤ) * ((k : ℤ) * m) + y * ((k : ℤ) ^ 2 - (m : ℤ) ^ 2) + z * (k : ℤ) ^ 2 = (k : ℤ) ^ 3 ∧
      (k ≤ z ∨ ∃ k' : ℕ, m + 1 ≤ k' ∧ k' < k ∧ k' ≤ z) := by
  obtain ⟨D, g, L, ax, ay, hL, hdist, hD, hP, hB, S, Co, -⟩ :=
    setup_of_corners m k hm hmk hco D₀ hMod τ (Or.inr hApex) (Or.inl hBeta)
  obtain ⟨c, X, tile, τ', Ch⟩ := S.exists_chainG
  obtain ⟨x, y, z, hxyz, hz, hz'⟩ := counts_gen S Ch
  refine ⟨x, y, z, ?_, ?_⟩
  · have : (((x : ℤ) * ((k : ℤ) * m) + y * ((k : ℤ) ^ 2 - (m : ℤ) ^ 2) + z * (k : ℤ) ^ 2 : ℤ) : ℝ) =
        (((k : ℤ) ^ 3 : ℤ) : ℝ) := by
      push_cast
      rw [← hlen, hdist]
      linarith [hxyz]
    exact_mod_cast this
  · rcases corner_side_theorem S Co Ch with h | ⟨k', hk1, hkf, hkm, hrun, hsucc⟩
    · exact Or.inl (hz h)
    · right
      have hsucc' : k' = c ∨ (k' < c ∧ τ' k' ≠ Ty.B1 ∧ τ' k' ≠ Ty.C1) := by
        rcases hsucc with h | ⟨h, h'⟩
        · exact Or.inl h
        · refine Or.inr ⟨h, ?_, ?_⟩ <;> rcases h' with h' | h' | h' <;> rw [h'] <;> decide
      have hek : m + 1 ≤ k' := by
        by_contra hlt
        exact corner_run_short S Co Ch hk1 (by omega) hrun hsucc'
      exact ⟨k', hek, hkf, hz' 0 k' (by omega) (Or.inl (fun j hj => by simpa using hrun j hj))⟩


/-- **Lemma 34 on the leg `AB`, thick members `m + 1 = k`**: `k <= z`. -/
theorem leg_counts_thick (k m : ℕ) (hm : 1 ≤ m) (hthick : m + 1 = k) (D₀ : CongruentDissection N)
    (hMod : HasSides D₀.model ((m : ℝ) * k) ((k : ℝ) ^ 2 - (m : ℝ) ^ 2) ((k : ℝ) ^ 2))
    (τ : Equiv.Perm (Fin 3))
    (hApex : cornerAngle (D₀.target.pts (τ 2)) (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) =
      3 * modelAlpha (m : ℝ) (k : ℝ))
    (hBeta : cornerAngle (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) (D₀.target.pts (τ 2)) =
      modelBeta (m : ℝ) (k : ℝ))
    (hlen : dist (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) = (k : ℝ) ^ 3) :
    ∃ x y z : ℕ, (x : ℤ) * ((k : ℤ) * m) + y * ((k : ℤ) ^ 2 - (m : ℤ) ^ 2) + z * (k : ℤ) ^ 2 = (k : ℤ) ^ 3 ∧ k ≤ z := by
  have hmk : m < k := by omega
  have hco : Nat.Coprime m k := by
    rw [← hthick]; exact Nat.coprime_self_add_right.mpr (Nat.coprime_one_right m)
  obtain ⟨x, y, z, h, hz | ⟨k', h1, h2, h3⟩⟩ := leg_counts k m hm hmk hco D₀ hMod τ hApex hBeta hlen
  · exact ⟨x, y, z, h, hz⟩
  · omega

/-- the arithmetic of `thm37_edges` for the leg: `k <= r1` forces `p1 = 0` -/
theorem leg_p1_zero {k m : ℤ} (hm : 0 < m) (hmk : m < k) {p1 q1 r1 : ℤ} (hp1 : 0 ≤ p1) (hq1 : 0 ≤ q1)
    (hleg : p1 * (k * m) + q1 * (k ^ 2 - m ^ 2) + r1 * k ^ 2 = k * k ^ 2) (hrun1 : k ≤ r1) : p1 = 0 := by
  have hk : 0 < k := by linarith
  have hb : 0 < k ^ 2 - m ^ 2 := by nlinarith
  have ha : 0 < k * m := by positivity
  have h1 : p1 * (k * m) + q1 * (k ^ 2 - m ^ 2) + (r1 - k) * k ^ 2 = 0 := by linear_combination hleg
  have : 0 ≤ (r1 - k) * k ^ 2 := mul_nonneg (by linarith) (by positivity)
  have h2 : p1 * (k * m) = 0 := by nlinarith [mul_nonneg hp1 ha.le, mul_nonneg hq1 hb.le]
  exact (mul_eq_zero.mp h2).resolve_right ha.ne'

/-- **Neither side carries an `a` edge** (thick members, a dissection of `T_1(m,k)` with the leg corners named): counts of `AC` and `AB`
with `p0 = 0`, `p1 = 0`.  The printed contradiction needs one more fact, quoted in the header (the corner tile's `a` edge). -/
theorem thm37_no_a_edges_thick (k m : ℕ) (hm : 1 ≤ m) (hthick : m + 1 = k) (D₀ : CongruentDissection N)
    (hT : HasSides D₀.target ((k : ℝ) ^ 3) ((k : ℝ) ^ 3) ((m : ℝ) * (3 * (k : ℝ) ^ 2 - (m : ℝ) ^ 2)))
    (hMod : HasSides D₀.model ((m : ℝ) * k) ((k : ℝ) ^ 2 - (m : ℝ) ^ 2) ((k : ℝ) ^ 2))
    (τ : Equiv.Perm (Fin 3))
    (hApex : cornerAngle (D₀.target.pts (τ 2)) (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) =
      3 * modelAlpha (m : ℝ) (k : ℝ))
    (hBeta : cornerAngle (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) (D₀.target.pts (τ 2)) =
      modelBeta (m : ℝ) (k : ℝ))
    (hlen : dist (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) = (k : ℝ) ^ 3) :
    (∃ x y z : ℕ, x = 0 ∧ y = m ∧ z = 2 * m) ∧
    ∃ x y z : ℕ, x = 0 ∧ (x : ℤ) * ((k : ℤ) * m) + y * ((k : ℤ) ^ 2 - (m : ℤ) ^ 2) + z * (k : ℤ) ^ 2 = (k : ℤ) ^ 3 := by
  have hmk : m < k := by omega
  have hco : Nat.Coprime m k := by
    rw [← hthick]; exact Nat.coprime_self_add_right.mpr (Nat.coprime_one_right m)
  obtain ⟨x0, y0, z0, h0x, h0y, h0z, -⟩ := base_edges k m hm hmk hco D₀ hT hMod
  obtain ⟨x, y, z, h, hz⟩ := leg_counts_thick k m hm hthick D₀ hMod τ hApex hBeta hlen
  refine ⟨⟨x0, y0, z0, h0x, h0y, h0z⟩, x, y, z, ?_, h⟩
  have := leg_p1_zero (k := (k : ℤ)) (m := (m : ℤ)) (p1 := (x : ℤ)) (q1 := (y : ℤ)) (r1 := (z : ℤ)) (by exact_mod_cast hm) (by exact_mod_cast hmk)
    (Int.natCast_nonneg x) (Int.natCast_nonneg y) (by linear_combination h) (by exact_mod_cast hz)
  exact_mod_cast this

/-- Non-vacuity of the arithmetic part: `(k,m) = (3,2)` (thick), base `(0,2,4)`, leg `(0,0,3)`. -/
theorem arith_witness : ((0:ℤ) * (3 * 2) + 2 * (3 ^ 2 - 2 ^ 2) + 4 * 3 ^ 2 = 2 * ((3 ^ 2 - 2 ^ 2) + 2 * 3 ^ 2)) ∧
    ((0:ℤ) * (3 * 2) + 0 * (3 ^ 2 - 2 ^ 2) + 3 * 3 ^ 2 = 3 ^ 3) := by norm_num

end Erdos634.BeesonRosu37b1

#print axioms Erdos634.BeesonRosu37b1.base_counts
#print axioms Erdos634.BeesonRosu37b1.base_edges
#print axioms Erdos634.BeesonRosu37b1.leg_counts
#print axioms Erdos634.BeesonRosu37b1.leg_counts_thick
#print axioms Erdos634.BeesonRosu37b1.thm37_no_a_edges_thick

