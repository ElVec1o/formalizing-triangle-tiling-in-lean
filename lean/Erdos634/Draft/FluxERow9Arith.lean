-- Draft/FluxERow9Arith.lean — ROW 9, the ARITHMETIC CORE ((private working notes, not included)
-- §3.D "Lemma P", §3.C–E "integer scale, k² = b, contradiction"; its own "Lean sketch, formalizable
-- now" list).  Pure arithmetic over ℤ, no geometry.  Imported directly by All.lean (stale "NOT imported" header corrected 2026-10-04).
--
-- * `Row9.coprime_c_a2b`: for an integer `120°` triple (`c² = a²+ab+b²`) with `IsCoprime a c`,
--   `IsCoprime c (a+2b)` — the file's Lemma P, via `4c² = (a+2b)² + 3a²`: `d := gcd(c,a+2b)` has
--   `d ∣ c` so `IsCoprime a d` (from `IsCoprime a c`); squaring, `IsCoprime a² d²`; `d² ∣ 4c²` and
--   `d² ∣ (a+2b)²` give `d² ∣ 3a²`, and coprimality cancels `a²`, leaving `d² ∣ 3`; `3` is not a
--   perfect square, so `d = 1`.
-- * `Row9.coprime_c_2ab`: the twin, `IsCoprime c (2a+b)` under `IsCoprime b c`, via
--   `4c² = (2a+b)² + 3b²`.
-- * `Row9.scale_int`: Bezout step — `μc, μ(a+2b) ∈ ℤ` and `IsCoprime c (a+2b)` give `μ ∈ ℤ`.
-- * `Row9.iso_closed_forms`: the two identities `(c−a−b)(c+a−b) = b(a+2b−2c)`,
--   `(c+a+b)(c+b−a) = b(a+2b+2c)`, by `ring` from `c² = a²+ab+b²`.
-- * `Row9.k_sq_eq_b`: from Lemma CF's `b·N = k²(a+2b)`, `N` prime, `a + 2b ≥ 3`,
--   `IsCoprime b (a+2b)`: `k² = b` and `N = a + 2b`.  (The only use of `N` prime.)
-- * `Row9.iso_arith_core`: the arithmetic assembly — `k² = b`, `k ∣ (c−a−b)`, `IsCoprime a k`
--   (from `k²=b`, `IsCoprime a b`) — and `NonIntegrality.k_not_dvd` (cited, VERIFIED) — gives `False`.
--   This is `iso_arith_core` from the file's own Lean sketch.
--
-- NOT done here (named blocker, per the file's own note): Lemma CF itself — deriving `k ∣ (c−a−b)`
-- and `bN = k²(a+2b)` from a REAL `CongruentDissection` via the `2π/3`-tile's flux functional Φ_f —
-- needs the `f_α`/`f_β` grid for the `2π/3` angle group; the Draft/Flux* layer built here covers the
-- `3α+2β=π` base-β grid, not this one.  So `iso_arith_core`'s hypotheses have no real-tiling witness
-- in the corpus.  (CORRECTION 2026-10-01, audit finding F-17: an earlier version of this header cited a
-- witness file `Draft/FluxERow9ArithWitness.lean`, which does NOT exist, and described N=33 on (5,3,7),
-- k=3 as witnessing the arithmetic hypotheses — it cannot: k²=9≠b=3 and k·M=−1 has no integer M. The
-- theorem is unaffected; no joint witness of the hypotheses is exhibited here.  No prime instance exists
-- by this file's own theorem.)
--
-- Formalization debt; not progress on the three /goal outcomes.
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Int.Basic
import Erdos634.NonIntegrality

open scoped Classical

namespace Erdos634.Geometry

/-! ## Lemma P: coprimality with the two combinations -/

/-- **Lemma P, first form.**  For an integer `120°` triple with `c ≠ 0` and `IsCoprime a c`,
`IsCoprime c (a+2b)`. -/
theorem Row9.coprime_c_a2b (a b c : ℤ) (hcne : c ≠ 0) (hc : c ^ 2 = a ^ 2 + a * b + b ^ 2)
    (hac : IsCoprime a c) : IsCoprime c (a + 2 * b) := by
  rw [Int.isCoprime_iff_gcd_eq_one] at hac ⊢
  set g : ℕ := Int.gcd c (a + 2 * b) with hg
  set d : ℤ := (g : ℤ) with hd
  have hdc : d ∣ c := Int.gcd_dvd_left c (a + 2 * b)
  have hdab : d ∣ (a + 2 * b) := Int.gcd_dvd_right c (a + 2 * b)
  have hcop_ad : IsCoprime a d := (Int.isCoprime_iff_gcd_eq_one.mpr hac).of_isCoprime_of_dvd_right hdc
  have hcop_a2d2 : IsCoprime (a ^ 2) (d ^ 2) := hcop_ad.pow
  have hd2 : d ^ 2 ∣ 3 * a ^ 2 := by
    have h1 : d ^ 2 ∣ 4 * c ^ 2 := (pow_dvd_pow_of_dvd hdc 2).mul_left 4
    have h2 : d ^ 2 ∣ (a + 2 * b) ^ 2 := pow_dvd_pow_of_dvd hdab 2
    have h3 : 3 * a ^ 2 = 4 * c ^ 2 - (a + 2 * b) ^ 2 := by nlinarith [hc]
    rw [h3]; exact dvd_sub h1 h2
  have hd2' : d ^ 2 ∣ 3 := hcop_a2d2.symm.dvd_of_dvd_mul_right hd2
  have hgnat : g ^ 2 ∣ 3 := by
    have : d ^ 2 = ((g ^ 2 : ℕ) : ℤ) := by rw [hd]; push_cast; ring
    rw [this] at hd2'
    exact_mod_cast hd2'
  have hgpos : 0 < g := by
    rw [hg]
    rw [Int.gcd_pos_iff]
    exact Or.inl hcne
  have hgle : g ≤ 1 := by
    by_contra hcon
    push Not at hcon
    have h4 : 4 ≤ g ^ 2 := by nlinarith
    have h3 : g ^ 2 ≤ 3 := Nat.le_of_dvd (by norm_num) hgnat
    omega
  have hg1 : g = 1 := by omega
  rw [hg1] at hg
  exact hg.symm

/-- **Lemma P, second form.**  For an integer `120°` triple with `c ≠ 0` and `IsCoprime b c`,
`IsCoprime c (2*a+b)`. -/
theorem Row9.coprime_c_2ab (a b c : ℤ) (hcne : c ≠ 0) (hc : c ^ 2 = a ^ 2 + a * b + b ^ 2)
    (hbc : IsCoprime b c) : IsCoprime c (2 * a + b) := by
  have hc' : c ^ 2 = b ^ 2 + b * a + a ^ 2 := by linarith [hc]
  have h := Row9.coprime_c_a2b b a c hcne hc' hbc
  rwa [show b + 2 * a = 2 * a + b from by ring] at h

/-! ## The Bezout scale step -/

/-- **Integer scale** (Bezout).  If `μc = (m:ℝ)` and `μ(a+2b) = (n:ℝ)` for integers `m, n`, and
`IsCoprime c (a+2b)`, then `μ = (k:ℝ)` for an integer `k`. -/
theorem Row9.scale_int (μ : ℝ) (c ab2 m n : ℤ) (h1 : μ * (c : ℝ) = m) (h2 : μ * (ab2 : ℝ) = n)
    (hcop : IsCoprime c ab2) : ∃ k : ℤ, μ = k := by
  obtain ⟨u, v, huv⟩ := hcop
  refine ⟨u * m + v * n, ?_⟩
  have : μ * ((u * c + v * ab2 : ℤ) : ℝ) = (u : ℝ) * m + (v : ℝ) * n := by
    push_cast
    rw [mul_add]
    rw [show μ * ((u:ℝ) * c) = (u:ℝ) * (μ * c) from by ring,
      show μ * ((v:ℝ) * ab2) = (v:ℝ) * (μ * ab2) from by ring, h1, h2]
  rw [huv] at this
  push_cast at this
  rw [mul_one] at this
  exact_mod_cast this

/-! ## The closed forms -/

/-- **The closed-form identities** (Lemma CF's ring facts), from `c² = a² + ab + b²`. -/
theorem Row9.iso_closed_forms (a b c : ℝ) (hc : c ^ 2 = a ^ 2 + a * b + b ^ 2) :
    (c - a - b) * (c + a - b) = b * (a + 2 * b - 2 * c) ∧
      (c + a + b) * (c + b - a) = b * (a + 2 * b + 2 * c) := by
  constructor <;> nlinarith [hc]

/-! ## `k² = b` from the prime tile count -/

/-- **`k² = b`.**  From `b·N = k²(a+2b)`, `N` prime, `a + 2b ≥ 3` (so `a+2b ≠ ±1`), and
`IsCoprime b (a+2b)`: `k² = b` and `N = a + 2b`. -/
theorem Row9.k_sq_eq_b (a b k : ℤ) (N : ℕ) (hN : N.Prime) (ha2b : 3 ≤ a + 2 * b)
    (hcop : IsCoprime b (a + 2 * b)) (harea : (b : ℤ) * (N : ℤ) = k ^ 2 * (a + 2 * b)) :
    k ^ 2 = b ∧ (N : ℤ) = a + 2 * b := by
  have hdvd : (a + 2 * b) ∣ b * N := ⟨k ^ 2, by rw [harea]; ring⟩
  have hdvd2 : (a + 2 * b) ∣ (N : ℤ) := hcop.symm.dvd_of_dvd_mul_left hdvd
  -- pass to `ℕ`: `a + 2b ≥ 3 > 0`
  set e : ℕ := (a + 2 * b).toNat with he
  have he' : (e : ℤ) = a + 2 * b := Int.toNat_of_nonneg (by linarith)
  have hdvdN : e ∣ N := by
    have : (e : ℤ) ∣ (N : ℤ) := by rw [he']; exact hdvd2
    exact_mod_cast this
  have he3 : 3 ≤ e := by
    have : (3 : ℤ) ≤ (e : ℤ) := by rw [he']; exact ha2b
    exact_mod_cast this
  rcases (hN.eq_one_or_self_of_dvd e hdvdN) with h | h
  · omega
  · have hNe : (N : ℤ) = a + 2 * b := by rw [← he', h]
    refine ⟨?_, hNe⟩
    have hNpos : (N : ℤ) ≠ 0 := by
      have : 0 < N := hN.pos
      omega
    have hcancel : b * (N : ℤ) = k ^ 2 * (N : ℤ) := by rw [harea, hNe]
    exact (mul_right_cancel₀ hNpos hcancel).symm

/-! ## The arithmetic assembly -/

/-- **`iso_arith_core`** (the file's own name).  A primitive `120°` integer triple (`a, b, c > 0`,
`c² = a²+ab+b²`, `IsCoprime a c`), `N` prime with `b·N = k²(a+2b)` (`k ≥ 1`, `IsCoprime b (a+2b)`),
and an integer `M` with `k · M = c − a − b`: `False`. -/
theorem Row9.iso_arith_core (a b c k M : ℤ) (N : ℕ) (ha : 0 < a) (hb : 0 < b) (hc0 : 0 < c)
    (hk : 0 < k) (hc : c ^ 2 = a ^ 2 + a * b + b ^ 2) (hac : IsCoprime a c) (hN : N.Prime)
    (ha2b : 3 ≤ a + 2 * b) (hcopN : IsCoprime b (a + 2 * b)) (habN : b * (N : ℤ) = k ^ 2 * (a + 2 * b))
    (hM : k * M = c - a - b) : False := by
  obtain ⟨hkb, -⟩ := Row9.k_sq_eq_b a b k N hN ha2b hcopN habN
  have hcop_ak : IsCoprime a k := by
    have hcop_ab : IsCoprime a b := by
      -- `d := gcd(a,b)` divides `c²` (from `c² = a²+ab+b²`); `d ∣ a` and `IsCoprime a c` give
      -- `IsCoprime d c`, hence `IsCoprime d (c²)`; with `d ∣ c²` this forces `d` a unit, so `d = 1`.
      rw [Int.isCoprime_iff_gcd_eq_one] at hac ⊢
      set d : ℤ := (Int.gcd a b : ℤ) with hd
      have hda : d ∣ a := Int.gcd_dvd_left a b
      have hdb : d ∣ b := Int.gcd_dvd_right a b
      have hdc2 : d ∣ c ^ 2 := by
        have heq : c ^ 2 = a * a + a * b + b * b := by rw [hc]; ring
        rw [heq]
        exact dvd_add (dvd_add (hda.mul_right a) (hda.mul_right b)) (hdb.mul_right b)
      have hcop_dc : IsCoprime d c :=
        (Int.isCoprime_iff_gcd_eq_one.mpr hac).of_isCoprime_of_dvd_left hda
      have hunit : IsUnit d := (hcop_dc.pow_right (n := 2)).isUnit_of_dvd hdc2
      have hdpos : 0 ≤ d := by rw [hd]; positivity
      rcases Int.isUnit_iff.mp hunit with h | h
      · rw [hd] at h; exact_mod_cast h
      · rw [hd] at h; omega
    have hcop_a_k2 : IsCoprime a (k ^ 2) := by rw [hkb]; exact hcop_ab
    exact hcop_a_k2.of_isCoprime_of_dvd_right (dvd_pow_self k two_ne_zero)
  have hkM : k ∣ (c - a - b) := ⟨M, hM.symm⟩
  exact NonIntegrality.k_not_dvd a k c ha hk hc0 hcop_ak (by
    rw [hkb]; linarith [hc]) (by
    have : a + k ^ 2 - c = -(c - a - b) - (b - k ^ 2) := by ring
    rw [this, hkb, sub_self, sub_zero]
    exact hkM.neg_right)

end Erdos634.Geometry

#print axioms Erdos634.Geometry.Row9.coprime_c_a2b
#print axioms Erdos634.Geometry.Row9.coprime_c_2ab
#print axioms Erdos634.Geometry.Row9.scale_int
#print axioms Erdos634.Geometry.Row9.iso_closed_forms
#print axioms Erdos634.Geometry.Row9.k_sq_eq_b
#print axioms Erdos634.Geometry.Row9.iso_arith_core
