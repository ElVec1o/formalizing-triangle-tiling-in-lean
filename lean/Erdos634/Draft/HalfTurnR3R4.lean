-- Draft/HalfTurnR3R4.lean — the ARITHMETIC of room HB's results R3, R4, P31 and the moderator's
-- (M)₂ step ((private working notes, not included) R3, R4, P31, P33; (private working notes, not included) S2/S4/S5,
-- report_neighbourhoods.md S1/S5/S6, moderator/report.md §3).  Imported directly by All.lean (stale "NOT imported" header corrected 2026-10-04).
-- Everything here is proved (no `sorry`).  The geometric glue is STATED, sorry-bodied, in
-- Draft/HalfTurnR3R4Glue.lean; nothing here depends on it.
--
-- Tile `(a,b,c) = (ef, b, f²)` with `b + e² = f²` (the `Inflation` convention; `b` a parameter).
-- A word is a count triple `(n_a, n_b, n_c)`, its value `n_a·a + n_b·b + n_c·c`.
--
-- REDISCOVERY LEDGER (corpus statements this file only cites, via one-line corollaries):
--   * Lemma A / piercing of chain points `k·V`, `k < f`  = `Inflation.c_side_no_b` (VERIFIED, All).
--   * `2a` has only `a + a` for `f ≥ 3`                  = `Inflation.a_side_no_b` + `a_side_rigid`.
--   * `c` has only the trivial representation, `e ≥ 2`  = `CChord.c_chord_unique_thick` (VERIFIED).
--   * the mod-`f` step of b-pinning                       = `WallStraddle.residue_mod_f`; the
--     "congruent mod f + short range ⇒ equal" technique is `WallStraddle.prefix_b_counts_equal`
--     (e = 1, window 3f²−1) and `Interface.no_small_mismatch`.  The general-`e` statement with the
--     window `[0, f·b)` is not in the corpus (grep "b-pinning", "same number of b").
--   * the angle bridge (real angle sums → integer counts) = `Geometry.vertex_multiplicities`.
--   * sharpness of the pinning window at `x = f·b`     = `Inflation.b_side_alt_word_at_f`.
-- Not found in the corpus ((private working notes, not included), 2026-09-23): "d*", "(-e^2) mod f", "2a − c",
-- "f(2e − f)", "pure chain", "first common junction".
import Erdos634.Inflation
import Erdos634.WallStraddle
import Erdos634.CChord
import Erdos634.Dissection
import Erdos634.MarchSlots

namespace Erdos634.Draft.HalfTurnR3R4

/-! ## §0 Conventions -/

/-- `x ∈ S = ⟨a, b, c⟩ = ⟨ef, b, f²⟩`.  (`Frontier.inSemi` is the same predicate with `b` computed;
here `b` is a parameter with `b + e² = f²`, as in `Inflation`.) -/
def InS (e f b x : ℕ) : Prop := ∃ na nb nc : ℕ, na * (e * f) + nb * b + nc * f ^ 2 = x

/-- R3's `n = ⌊f·b / c⌋`: the length of the pure `L_c` chain `c^n` along the mismatch ray `r`,
whose length at `m = 1` is `f·b`. -/
def nStar (f b : ℕ) : ℕ := f * b / f ^ 2

/-- R3's `d* = f·b − n·c`: the leftover of the ray after the pure chain. -/
def dStar (f b : ℕ) : ℕ := f * b - nStar f b * f ^ 2

/-- `ρ = (−e²) mod f`, in `[0, f)`. -/
def rho (e f : ℕ) : ℤ := (-(e : ℤ) ^ 2) % (f : ℤ)

theorem b_pos {e f b : ℕ} (hef : e < f) (hb : b + e ^ 2 = f ^ 2) : 0 < b := by
  have : e ^ 2 < f ^ 2 := Nat.pow_lt_pow_left hef (by norm_num)
  omega

/-! ## §1 R3 (a): b-pinning below `f·b` -/

/-- **R3(a), b-pinning.**  For coprime `e < f`, two words of equal value `x < f·b` carry the same
number of `b`-edges.  Mod `f` (corpus: `WallStraddle.residue_mod_f`) gives `f ∣ (n_b − n_b')·e²`,
hence `f ∣ n_b − n_b'`; and `n_b·b ≤ x < f·b` puts both counts in `[0, f)`. -/
theorem b_pinning {e f b na nb nc na' nb' nc' x : ℕ} (hcop : Nat.Coprime e f) (hef : e < f)
    (hb : b + e ^ 2 = f ^ 2)
    (h1 : na * (e * f) + nb * b + nc * f ^ 2 = x)
    (h2 : na' * (e * f) + nb' * b + nc' * f ^ 2 = x)
    (hx : x < f * b) : nb = nb' := by
  have hbpos := b_pos hef hb
  have hnb : nb < f := by
    have : nb * b < f * b := by
      have : nb * b ≤ x := by rw [← h1]; omega
      omega
    exact Nat.lt_of_mul_lt_mul_right this
  have hnb' : nb' < f := by
    have : nb' * b < f * b := by
      have : nb' * b ≤ x := by rw [← h2]; omega
      omega
    exact Nat.lt_of_mul_lt_mul_right this
  have hbz : (b : ℤ) = (f : ℤ) ^ 2 - (e : ℤ) ^ 2 := by
    have := congrArg (Nat.cast : ℕ → ℤ) hb
    push_cast at this; linarith
  have h1z : ((x : ℕ) : ℤ) = (na : ℤ) * ((e : ℤ) * f) + (nb : ℤ) * ((f : ℤ) ^ 2 - (e : ℤ) ^ 2)
      + (nc : ℤ) * (f : ℤ) ^ 2 := by
    rw [← hbz, ← h1]; push_cast; ring
  have h2z : ((x : ℕ) : ℤ) = (na' : ℤ) * ((e : ℤ) * f) + (nb' : ℤ) * ((f : ℤ) ^ 2 - (e : ℤ) ^ 2)
      + (nc' : ℤ) * (f : ℤ) ^ 2 := by
    rw [← hbz, ← h2]; push_cast; ring
  have r1 := WallStraddle.residue_mod_f (na : ℤ) nb nc e f x h1z
  have r2 := WallStraddle.residue_mod_f (na' : ℤ) nb' nc' e f x h2z
  have hd : (f : ℤ) ∣ ((nb : ℤ) - nb') * (e : ℤ) ^ 2 := by
    have := dvd_sub r1 r2
    have hrw : ((x : ℤ) + (nb : ℤ) * (e : ℤ) ^ 2 - ((x : ℤ) + (nb' : ℤ) * (e : ℤ) ^ 2))
        = ((nb : ℤ) - nb') * (e : ℤ) ^ 2 := by ring
    rwa [hrw] at this
  have hcopz : IsCoprime (f : ℤ) ((e : ℤ) ^ 2) := by
    have : IsCoprime (f : ℤ) (e : ℤ) := Nat.isCoprime_iff_coprime.mpr hcop.symm
    exact this.pow_right
  obtain ⟨k, hk⟩ := hcopz.dvd_of_dvd_mul_right hd
  have hlt1 : (nb : ℤ) < f := by exact_mod_cast hnb
  have hlt2 : (nb' : ℤ) < f := by exact_mod_cast hnb'
  have hn1 : (0 : ℤ) ≤ nb := Int.natCast_nonneg _
  have hn2 : (0 : ℤ) ≤ nb' := Int.natCast_nonneg _
  rcases lt_trichotomy k 0 with hk0 | hk0 | hk0
  · exfalso
    have : (f : ℤ) * k ≤ (f : ℤ) * (-1) := by
      apply mul_le_mul_of_nonneg_left (by omega) (by omega)
    linarith
  · subst hk0
    have : (nb : ℤ) = nb' := by linarith
    exact_mod_cast this
  · exfalso
    have : (f : ℤ) * 1 ≤ (f : ℤ) * k := by
      apply mul_le_mul_of_nonneg_left (by omega) (by omega)
    linarith

/-- **Sharpness of the pinning window (corpus).**  At `x = f·b` the words `b^f` and
`a^{f−e} c^{f−e}` (`Inflation.b_side_alt_word_at_f`) have `b`-counts `f` and `0`; so the window
`[0, f·b)` of `b_pinning` is exact, and R3's case `x₀ = f·b` needs a separate argument (§1(b)). -/
theorem b_pinning_window_sharp (e f b : ℕ) (hef : e ≤ f) (hb : b + e ^ 2 = f ^ 2) :
    0 * (e * f) + f * b + 0 * f ^ 2 = f * b ∧
    (f - e) * (e * f) + 0 * b + (f - e) * f ^ 2 = f * b :=
  ⟨by ring, Inflation.b_side_alt_word_at_f e f b hef hb⟩

/-! ## §1 R3 (b): `d*` — both forms, and `d* ∉ S` for `2 ≤ e ≤ f − 2` -/

theorem nStar_mul_le (f b : ℕ) : nStar f b * f ^ 2 ≤ f * b := Nat.div_mul_le_self _ _

/-- `d* = f·b mod c`. -/
theorem dStar_eq_mod (f b : ℕ) : dStar f b = f * b % f ^ 2 := by
  unfold dStar nStar
  have h := Nat.div_add_mod (f * b) (f ^ 2)
  rw [Nat.mul_comm (f ^ 2)] at h
  exact Nat.sub_eq_of_eq_add (by rw [Nat.add_comm]; exact h.symm)

/-- `d* = f·(b mod f)`. -/
theorem dStar_eq_f_mul_mod (f b : ℕ) : dStar f b = f * (b % f) := by
  rw [dStar_eq_mod, sq, Nat.mul_mod_mul_left]

/-- `b mod f = (−e²) mod f = ρ`. -/
theorem mod_f_eq_rho {e f b : ℕ} (hb : b + e ^ 2 = f ^ 2) : ((b % f : ℕ) : ℤ) = rho e f := by
  unfold rho
  have hbz : (b : ℤ) = -(e : ℤ) ^ 2 + (f : ℤ) * f := by
    have := congrArg (Nat.cast : ℕ → ℤ) hb
    push_cast at this; nlinarith
  rw [Int.natCast_mod, hbz, Int.add_mul_emod_self_left]

/-- **R3(b), the two forms agree:** `d* = f·b − ⌊f·b/c⌋·c = f·ρ`, `ρ = (−e²) mod f`. -/
theorem dStar_eq_f_rho {e f b : ℕ} (hb : b + e ^ 2 = f ^ 2) :
    (dStar f b : ℤ) = (f : ℤ) * rho e f := by
  rw [dStar_eq_f_mul_mod, ← mod_f_eq_rho hb]; push_cast; ring

/-- **R3(b), `d* ∉ S` for coprime `2 ≤ e ≤ f − 2`.**  Write `d* = f·r`, `r = b mod f < f`.  A
representation has `n_b = 0` (mod `f` gives `f ∣ n_b`, and `f·b > f·r`), then `n_c = 0` (size), so
`r = n_a·e`; `r ≡ −e² (mod f)` gives `f ∣ e·(n_a + e)`, so `n_a ≥ f − e` and
`r ≥ (f − e)·e ≥ f` (as `e ≥ 2`, `f ≥ e + 2`) — against `r < f`. -/
theorem dStar_not_mem {e f b : ℕ} (hcop : Nat.Coprime e f) (he : 2 ≤ e) (hef : e + 2 ≤ f)
    (hb : b + e ^ 2 = f ^ 2) : ¬ InS e f b (dStar f b) := by
  rintro ⟨na, nb, nc, h⟩
  rw [dStar_eq_f_mul_mod] at h
  have hf0 : 0 < f := by omega
  have hrf : b % f < f := Nat.mod_lt _ hf0
  have hdiv := Nat.mod_add_div b f
  have hbf : f < b := by nlinarith
  have hnb : nb = 0 := by
    have h3 : f ∣ na * (e * f) + nc * f ^ 2 :=
      Nat.dvd_add ⟨na * e, by ring⟩ ⟨nc * f, by ring⟩
    have h4 : f ∣ na * (e * f) + nc * f ^ 2 + nb * b := by
      have : na * (e * f) + nc * f ^ 2 + nb * b = f * (b % f) := by omega
      rw [this]; exact dvd_mul_right f _
    have h5 : f ∣ nb * b := (Nat.dvd_add_right h3).mp h4
    have h6 : f ∣ nb := Inflation.f_dvd_nb e f b nb hcop hb (by exact_mod_cast h5)
    rcases Nat.eq_zero_or_pos nb with h0 | h0
    · exact h0
    · exfalso
      have hge : f ≤ nb := Nat.le_of_dvd h0 h6
      have k1 : f * b ≤ nb * b := Nat.mul_le_mul_right _ hge
      have k2 : f * (b % f) < f * b := Nat.mul_lt_mul_of_pos_left (by omega) hf0
      omega
  subst hnb
  have hnc : nc = 0 := by
    by_contra hc
    have k1 : f ^ 2 ≤ nc * f ^ 2 := Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero hc)
    have k2 : f * (b % f) < f ^ 2 := by rw [sq]; exact Nat.mul_lt_mul_of_pos_left hrf hf0
    omega
  subst hnc
  have hr_eq : na * e = b % f := by
    have : f * (na * e) = f * (b % f) := by rw [← h]; ring
    exact Nat.eq_of_mul_eq_mul_left hf0 this
  have h9 : f * (b / f) + e * (na + e) = f * f := by
    have k1 : e * (na + e) = na * e + e ^ 2 := by ring
    have k2 : f ^ 2 = f * f := sq f
    omega
  have h8 : f ∣ e * (na + e) := by
    have : f ∣ f * (b / f) + e * (na + e) := by rw [h9]; exact dvd_mul_right f f
    exact (Nat.dvd_add_right (dvd_mul_right f _)).mp this
  have h10 : f ∣ na + e := Nat.Coprime.dvd_of_dvd_mul_left hcop.symm h8
  have h11 : f ≤ na + e := Nat.le_of_dvd (by omega) h10
  have hz1 : ((na : ℤ) * e) < f := by
    have : na * e < f := by omega
    exact_mod_cast this
  have hz2 : (f : ℤ) ≤ na + e := by exact_mod_cast h11
  have hz3 : (e : ℤ) + 2 ≤ f := by exact_mod_cast hef
  have hz4 : (2 : ℤ) ≤ e := by exact_mod_cast he
  nlinarith [mul_nonneg (sub_nonneg.mpr hz2) (by linarith : (0 : ℤ) ≤ e),
    mul_nonneg (by linarith : (0 : ℤ) ≤ f - e - 2) (by linarith : (0 : ℤ) ≤ e - 1)]

/-- **R3(b) sharpness: `d* ∈ S` at `e ∈ {1, f − 1}`** (instances `(1,5)`, `(4,5)`, `(1,7)`,
`(6,7)`): `d* = 20 = 4a`, `20 = a`, `42 = 6a`, `42 = a`.  So `2 ≤ e ≤ f − 2` is needed. -/
theorem dStar_mem_edge_cases :
    dStar 5 24 = 20 ∧ InS 1 5 24 20 ∧ dStar 5 9 = 20 ∧ InS 4 5 9 20 ∧
    dStar 7 48 = 42 ∧ InS 1 7 48 42 ∧ dStar 7 13 = 42 ∧ InS 6 7 13 42 := by
  refine ⟨by decide, ⟨4, 0, 0, by norm_num⟩, by decide, ⟨1, 0, 0, by norm_num⟩,
    by decide, ⟨6, 0, 0, by norm_num⟩, by decide, ⟨1, 0, 0, by norm_num⟩⟩

/-- `n < f` (so `c^n` is a sub-scale `c`-run and Lemma A applies to every chain point). -/
theorem nStar_lt {e f b : ℕ} (he : 1 ≤ e) (hef : e < f) (hb : b + e ^ 2 = f ^ 2) :
    nStar f b < f := by
  have h1 := nStar_mul_le f b
  have hbf : b < f ^ 2 := by have : 0 < e ^ 2 := by positivity
                             omega
  have hf0 : 0 < f := by omega
  have h2 : f * b < f * f ^ 2 := Nat.mul_lt_mul_of_pos_left hbf hf0
  have h3 : nStar f b * f ^ 2 < f * f ^ 2 := lt_of_le_of_lt h1 h2
  exact Nat.lt_of_mul_lt_mul_right h3

/-! ## §1 R3 (c): the kill -/

/-- **R3(c), `x₀ < f·b`.**  Near word `c^n · t`, far word `w` with `≥ 1` `b`, equal value
`x₀ < f·b`: b-pinning gives `n_b(t) = n_b(w) ≥ 1`, so `val t ≥ b`; but `val t = x₀ − n·c < d*`.
So `d* < b` kills it.  (Only coprime `e < f` used.) -/
theorem r3_kill_below {e f b n ta tb tc na nb nc x0 : ℕ} (hcop : Nat.Coprime e f) (hef : e < f)
    (hb : b + e ^ 2 = f ^ 2) (hn : n = nStar f b)
    (hnear : n * f ^ 2 + (ta * (e * f) + tb * b + tc * f ^ 2) = x0)
    (hfar : na * (e * f) + nb * b + nc * f ^ 2 = x0) (hfarb : 1 ≤ nb)
    (hx0 : x0 < f * b) (hd : dStar f b < b) : False := by
  have hpin : tb = nb := b_pinning (na := ta) (nb := tb) (nc := tc + n) (x := x0) hcop hef hb
    (by rw [← hnear]; ring) hfar hx0
  have hle := nStar_mul_le f b
  have hds : dStar f b = f * b - nStar f b * f ^ 2 := rfl
  subst hn
  have : b ≤ tb * b := Nat.le_mul_of_pos_left b (by omega)
  omega

/-- **R3(c), `x₀ = f·b`.**  The near word `c^n · t` reaching the base puts `val t = d*` in `S`,
against `dStar_not_mem`.  (The far side is not used.) -/
theorem r3_kill_at_base {e f b n ta tb tc : ℕ} (hcop : Nat.Coprime e f) (he : 2 ≤ e)
    (hef : e + 2 ≤ f) (hb : b + e ^ 2 = f ^ 2) (hn : n = nStar f b)
    (hnear : n * f ^ 2 + (ta * (e * f) + tb * b + tc * f ^ 2) = f * b) : False := by
  apply dStar_not_mem hcop he hef hb
  refine ⟨ta, tb, tc, ?_⟩
  have hle := nStar_mul_le f b
  unfold dStar; subst hn; omega

/-- **R3(c), the kill as one theorem.**  `m = 1`, coprime `2 ≤ e ≤ f − 2`, near side `c^n · t`,
far side `w` with `≥ 1` `b`, common value `x₀ ≤ f·b` (the ray's length), `d* < b`: impossible. -/
theorem r3_kill {e f b n ta tb tc na nb nc x0 : ℕ} (hcop : Nat.Coprime e f) (he : 2 ≤ e)
    (hef : e + 2 ≤ f) (hb : b + e ^ 2 = f ^ 2) (hn : n = nStar f b)
    (hnear : n * f ^ 2 + (ta * (e * f) + tb * b + tc * f ^ 2) = x0)
    (hfar : na * (e * f) + nb * b + nc * f ^ 2 = x0) (hfarb : 1 ≤ nb)
    (hx0 : x0 ≤ f * b) (hd : dStar f b < b) : False := by
  rcases Nat.lt_or_eq_of_le hx0 with h | h
  · exact r3_kill_below hcop (by omega) hb hn hnear hfar hfarb h hd
  · subst h; exact r3_kill_at_base hcop he hef hb hn hnear

/-- **R3(c), b-piercer version.**  Far side with `≥ 2` `b`-edges, `d* < 2b`: impossible. -/
theorem r3_kill_bpiercer {e f b n ta tb tc na nb nc x0 : ℕ} (hcop : Nat.Coprime e f)
    (he : 2 ≤ e) (hef : e + 2 ≤ f) (hb : b + e ^ 2 = f ^ 2) (hn : n = nStar f b)
    (hnear : n * f ^ 2 + (ta * (e * f) + tb * b + tc * f ^ 2) = x0)
    (hfar : na * (e * f) + nb * b + nc * f ^ 2 = x0) (hfarb : 2 ≤ nb)
    (hx0 : x0 ≤ f * b) (hd : dStar f b < 2 * b) : False := by
  rcases Nat.lt_or_eq_of_le hx0 with h | h
  · have hpin : tb = nb :=
      b_pinning (na := ta) (nb := tb) (nc := tc + n) (x := x0) hcop (by omega) hb
        (by rw [← hnear]; ring) hfar h
    have hle := nStar_mul_le f b
    have hds : dStar f b = f * b - nStar f b * f ^ 2 := rfl
    subst hn
    have : 2 * b ≤ tb * b := Nat.mul_le_mul_right b (by omega)
    omega
  · subst h; exact r3_kill_at_base hcop he hef hb hn hnear

/-- `d* < c` (the leftover after the longest `c`-run is shorter than `c`). -/
theorem dStar_lt_c (f b : ℕ) (hf : 0 < f) : dStar f b < f ^ 2 := by
  rw [dStar_eq_mod]; exact Nat.mod_lt _ (by positivity)

/-- **R3 (ii), the PROSE form (added 2026-09-24): the `b`-piercer kill at EVERY member, no
condition on `d*`.**  With a `b`-piercer, the far word up to the piercer's end is `b^{t+2}` and the
piercer contains `c` in its interior, so `(t+2)·b > c` (`prop:rung2`; its arithmetic core is
`rung2_core` below, its placement half is glue).  The far word up to `x₀` then
carries `n_b ≥ t+2` `b`-edges, pinning hands them to the near leftover `t_w`, whose value is `≥ (t+2)b
> c > d* > val t_w` (`x₀ < f·b`); `x₀ = f·b` is `r3_kill_at_base`.  This supersedes
`r3_kill_bpiercer` (which assumes `d* < 2b` and so misses e.g. `(11,13)`: `d* = 117 ≥ 2b = 96`,
`r3_rung2_witness_11_13`). -/
theorem r3_kill_bpiercer_rung2 {e f b n ta tb tc na nb nc x0 t : ℕ} (hcop : Nat.Coprime e f)
    (he : 2 ≤ e) (hef : e + 2 ≤ f) (hb : b + e ^ 2 = f ^ 2) (hn : n = nStar f b)
    (hnear : n * f ^ 2 + (ta * (e * f) + tb * b + tc * f ^ 2) = x0)
    (hfar : na * (e * f) + nb * b + nc * f ^ 2 = x0) (ht : t + 2 ≤ nb)
    (htc : f ^ 2 < (t + 2) * b) (hx0 : x0 ≤ f * b) : False := by
  rcases Nat.lt_or_eq_of_le hx0 with h | h
  · have hpin : tb = nb :=
      b_pinning (na := ta) (nb := tb) (nc := tc + n) (x := x0) hcop (by omega) hb
        (by rw [← hnear]; ring) hfar h
    have hdc := dStar_lt_c f b (by omega)
    have hle := nStar_mul_le f b
    have hds : dStar f b = f * b - nStar f b * f ^ 2 := rfl
    subst hn
    have : (t + 2) * b ≤ tb * b := Nat.mul_le_mul_right b (by omega)
    omega
  · subst h; exact r3_kill_at_base hcop he hef hb hn hnear

/-- **`prop:rung2`'s arithmetic core**: an edge length `∈ {a, b, c}` that fits in `[b, c]`
(length `≤ c − b = e²`) is `b` (`a = ef > e²`, `c = f² > e²`). -/
theorem rung2_core {e f b x : ℕ} (he : 1 ≤ e) (hef : e < f) (hb : b + e ^ 2 = f ^ 2)
    (hx : x = e * f ∨ x = b ∨ x = f ^ 2) (hle : x ≤ e ^ 2) : x = b := by
  have h1 : e ^ 2 < e * f := by rw [sq]; exact Nat.mul_lt_mul_of_pos_left hef (by omega)
  have h2 : e ^ 2 < f ^ 2 := Nat.pow_lt_pow_left hef (by norm_num)
  rcases hx with rfl | rfl | rfl <;> omega

/-- **Witness (vacuity rule + the gap the old form had)**: at `(e,f) = (11,13)` (`b = 48`, `c = 169`,
`n = 3`, `d* = 117`) the old hypothesis `d* < 2b` FAILS, while `r3_kill_bpiercer_rung2`'s count
hypothesis holds with `t = 2` (`4·48 = 192 > 169`); `f² > 2e²` fails there (`169 ≤ 242`), so the
`b`-run can have interior `b`s (`t = 2`: `b³` then the piercer `[144, 192] ∋ 169`). -/
theorem r3_rung2_witness_11_13 :
    Nat.Coprime 11 13 ∧ 48 + 11 ^ 2 = 13 ^ 2 ∧ nStar 13 48 = 3 ∧ dStar 13 48 = 117 ∧
      ¬ dStar 13 48 < 2 * 48 ∧ 13 ^ 2 < (2 + 2) * 48 ∧ (2 + 1) * 48 < 13 ^ 2 := by
  refine ⟨by decide, by norm_num, by decide, by decide, by decide, by norm_num, by norm_num⟩

/-- **R3(c) with the chain possibly stopping early**: the form the assembly consumes.  The near side
is `c^j · t` with `j ≤ n`, and `t` empty unless `j = n` (a near junction before `n·c` on a pure
`c`-run is a multiple of `c`).  `j < n`: the far word of value `j·c` has a `b`, against Lemma A
(`Inflation.c_side_no_b`, `j < f`).  `j = n`: `r3_kill`. -/
theorem r3_arith {e f b j ta tb tc na nb nc x0 : ℕ} (hcop : Nat.Coprime e f) (he : 2 ≤ e)
    (hef : e + 2 ≤ f) (hb : b + e ^ 2 = f ^ 2) (hj : j ≤ nStar f b)
    (hshort : j < nStar f b → ta = 0 ∧ tb = 0 ∧ tc = 0)
    (hnear : j * f ^ 2 + (ta * (e * f) + tb * b + tc * f ^ 2) = x0)
    (hfar : na * (e * f) + nb * b + nc * f ^ 2 = x0) (hfarb : 1 ≤ nb)
    (hx0 : x0 ≤ f * b) (hd : dStar f b < b) : False := by
  rcases Nat.lt_or_eq_of_le hj with hlt | heq
  · obtain ⟨rfl, rfl, rfl⟩ := hshort hlt
    have hjf : j < f := lt_of_lt_of_le hlt (nStar_lt (by omega) (by omega) hb).le
    have : nb = 0 := Inflation.c_side_no_b e f b j na nb nc (by omega) (by omega) hcop hb hjf
      (by rw [hfar, ← hnear]; ring)
    omega
  · exact r3_kill hcop he hef hb heq hnear hfar hfarb hx0 hd

/-! ### R3 witnesses (vacuity rule) -/

/-- The member-level hypotheses of `r3_kill` are satisfiable with `d* < b`: `(e,f) = (3,5)`,
`b = 16`, `n = 3`, `d* = 5`; also at `(7,10)` (`N = 251`): `b = 51`, `n = 5`, `d* = 10`. -/
theorem r3_member_hyps_satisfiable :
    Nat.Coprime 3 5 ∧ 2 ≤ 3 ∧ 3 + 2 ≤ 5 ∧ 16 + 3 ^ 2 = 5 ^ 2 ∧ nStar 5 16 = 3 ∧
      dStar 5 16 = 5 ∧ dStar 5 16 < 16 ∧
    Nat.Coprime 7 10 ∧ 51 + 7 ^ 2 = 10 ^ 2 ∧ nStar 10 51 = 5 ∧ dStar 10 51 = 10 ∧
      dStar 10 51 < 51 := by
  refine ⟨by decide, by norm_num, by norm_num, by norm_num, by decide, by decide, by decide,
    by decide, by norm_num, by decide, by decide, by decide⟩

/-- **`d* < b` is necessary** — every other hypothesis of `r3_kill` holds at `(4,7)` (`N = 131`,
`a,b,c = 28,33,49`, `n = 4`, `d* = 35 ≥ b`): near `c⁴·b`, far `b·c⁴`, `x₀ = 229 ≤ f·b = 231`
(the room's surviving c- and a-piercer value).  And the at-base case alone is not the obstruction there:
`229 < 231`. -/
theorem r3_dstar_hyp_necessary :
    Nat.Coprime 4 7 ∧ 33 + 4 ^ 2 = 7 ^ 2 ∧ nStar 7 33 = 4 ∧ dStar 7 33 = 35 ∧ ¬ dStar 7 33 < 33 ∧
    4 * 7 ^ 2 + (0 * (4 * 7) + 1 * 33 + 0 * 7 ^ 2) = 229 ∧
    0 * (4 * 7) + 1 * 33 + 4 * 7 ^ 2 = 229 ∧ 229 ≤ 7 * 33 := by
  refine ⟨by decide, by norm_num, by decide, by decide, by decide, by norm_num, by norm_num,
    by norm_num⟩

/-- The far-side `b` is necessary: without it, near `c³` and far `c³` agree at `75 ≤ 80`, `(3,5)`. -/
theorem r3_far_b_hyp_necessary :
    3 * 5 ^ 2 + (0 * (3 * 5) + 0 * 16 + 0 * 5 ^ 2) = 75 ∧ 0 * (3 * 5) + 0 * 16 + 3 * 5 ^ 2 = 75 ∧
    75 ≤ 5 * 16 := by
  refine ⟨by norm_num, by norm_num, by norm_num⟩

/-- **The `m = 2` failure at `(e,f) = (1,2)`, `N = 44`** (tile `(2,3,4)`; the ray has length
`m·f·b = 12`): near `c³`, far `b⁴`, common junction `x₀ = 12` (the base).  The b-counts are `0` and
`4 = 2f` — pinning fails because `12 ≥ f·b = 6` (the window is `m`-blind only below `f·b`) — and the
leftover `12 − ⌊12/4⌋·4 = 0 ∈ S`.  So both m = 1 steps are used. -/
theorem r3_fails_m2_N44 :
    3 * 2 ^ 2 = 12 ∧ 0 * (1 * 2) + 4 * 3 + 0 * 2 ^ 2 = 12 ∧ 12 = 2 * (2 * 3) ∧ ¬ (12 < 2 * 3) ∧
    12 - 12 / 2 ^ 2 * 2 ^ 2 = 0 ∧ InS 1 2 3 0 ∧ (0 : ℕ) ≠ 4 := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, ⟨0, 0, 0, by norm_num⟩,
    by norm_num⟩

/-! ## §2 R4 arithmetic -/

/-- **R4 repair (1), piercing of every chain point `k·V`, `k < f`** — a far word of value `k·c`
with a `b` is impossible.  This IS Lemma A = `Inflation.c_side_no_b` (corpus, VERIFIED). -/
theorem pierce_chain_point {e f b k na nb nc : ℕ} (he : 1 ≤ e) (hef : e < f)
    (hcop : Nat.Coprime e f) (hb : b + e ^ 2 = f ^ 2) (hk : k < f)
    (h : na * (e * f) + nb * b + nc * f ^ 2 = k * f ^ 2) : nb = 0 :=
  Inflation.c_side_no_b e f b k na nb nc he hef hcop hb hk h

/-- **R4 repair (1), the review's form: `k·c − b = w` forces `n_b(w) ≥ f − 1` and `k·c ≥ f·b`.**
Mod `f`: `f ∣ (n_b + 1)·b`, so `f ∣ n_b + 1`. -/
theorem chain_point_minus_b {e f b k na nb nc : ℕ} (hcop : Nat.Coprime e f)
    (hb : b + e ^ 2 = f ^ 2)
    (h : na * (e * f) + nb * b + nc * f ^ 2 + b = k * f ^ 2) :
    f ≤ nb + 1 ∧ f * b ≤ k * f ^ 2 := by
  have hcast : (na : ℤ) * ((e : ℤ) * f) + (nb : ℤ) * b + (nc : ℤ) * (f : ℤ) ^ 2 + b
      = (k : ℤ) * (f : ℤ) ^ 2 := by exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) h
  have hd : f ∣ nb + 1 := Inflation.f_dvd_nb e f b (nb + 1) hcop hb
    ⟨(k : ℤ) * f - na * e - nc * f, by push_cast; linear_combination hcast⟩
  have h1 : f ≤ nb + 1 := Nat.le_of_dvd (by omega) hd
  refine ⟨h1, ?_⟩
  have h2 : f * b ≤ (nb + 1) * b := Nat.mul_le_mul_right _ h1
  have h3 : (nb + 1) * b = nb * b + b := by ring
  omega

/-- The piercing in gap form: for `k·c < f·b`, `k·c − b ∉ S` (e.g. `2c − b` at every member
where `2c < f·b`; at `N = 44`, `2c − b = 5 = a + b`, `review_S7/out_n44.txt`). -/
theorem chain_point_minus_b_not_mem {e f b k : ℕ} (hcop : Nat.Coprime e f)
    (hb : b + e ^ 2 = f ^ 2) (hk : k * f ^ 2 < f * b) (hbk : b ≤ k * f ^ 2) :
    ¬ InS e f b (k * f ^ 2 - b) := by
  rintro ⟨na, nb, nc, h⟩
  have := (chain_point_minus_b (k := k) (na := na) (nb := nb) (nc := nc) hcop hb
    (by omega)).2
  omega

/-- **`2a` has only `a + a` for `f ≥ 3`** (R4 S6).  Corpus: `Inflation.a_side_no_b` (`k = 2 ≤ f`)
then `Inflation.a_side_rigid` (`k = 2 < f`).  Fails at `N = 44`: `2a = c` (`two_a_eq_c_N44`). -/
theorem two_a_rigid {e f b na nb nc : ℕ} (he : 1 ≤ e) (hef : e < f) (hf3 : 3 ≤ f)
    (hcop : Nat.Coprime e f) (hb : b + e ^ 2 = f ^ 2)
    (h : na * (e * f) + nb * b + nc * f ^ 2 = 2 * (e * f)) : na = 2 ∧ nb = 0 ∧ nc = 0 := by
  have hnb : nb = 0 := Inflation.a_side_no_b e f b 2 na nb nc he hef hcop hb (by omega) h
  subst hnb
  have h' : na * (e * f) + nc * f ^ 2 = 2 * (e * f) := by simpa using h
  obtain ⟨h1, h2⟩ := Inflation.a_side_rigid e f 2 na nc he hef hcop (by omega) h'
  exact ⟨h1, rfl, h2⟩

theorem two_a_eq_c_N44 : 2 * (1 * 2) = 2 ^ 2 := by norm_num

/-- **`c` has only the trivial representation for `e ≥ 2`.**  REDISCOVERY: this is
`CChord.c_chord_unique_thick` (corpus, VERIFIED); restated in the `b + e² = f²` convention. -/
theorem c_rigid {e f b na nb nc : ℕ} (he : 2 ≤ e) (hef : e < f) (hcop : Nat.Coprime e f)
    (hb : b + e ^ 2 = f ^ 2) (h : na * (e * f) + nb * b + nc * f ^ 2 = f ^ 2) :
    na = 0 ∧ nb = 0 ∧ nc = 1 := by
  have hb' : b = f * f - e * e := by rw [← sq, ← sq]; omega
  subst hb'
  exact CChord.c_chord_unique_thick he hef hcop (by rw [← sq]; simpa [sq] using h)

/-- `c = f²` at `e = 1` has the second representation `f·a` (`c_rigid` needs `e ≥ 2`). -/
theorem c_nonrigid_e1 (f : ℕ) : f * (1 * f) = f ^ 2 := by ring

/-- **R4 repair (2), the chain bound:** `k·c < (f−1)·b ⇒ k ≤ f − 2`. -/
theorem chain_bound {e f b k : ℕ} (hb : b + e ^ 2 = f ^ 2) (h : k * f ^ 2 < (f - 1) * b) :
    k ≤ f - 2 := by
  have h1 : (f - 1) * b ≤ (f - 1) * f ^ 2 := Nat.mul_le_mul_left _ (by omega)
  have h2 : k * f ^ 2 < (f - 1) * f ^ 2 := lt_of_lt_of_le h h1
  have h3 : k < f - 1 := Nat.lt_of_mul_lt_mul_right h2
  omega

/-! ### The angle catalogue on the θ-lattice

With `γ = 2α + β`, `3α + 2β = π` and `α ∉ ℚπ` (`BaseBetaE1.tile_alpha_irrational`, the corpus
convention), a wedge filled by `x` α-, `y` β-, `z` γ-corners and `p` straight angles has, in the
basis `(α, β)`, coordinates `(x + 2z + 3p, y + z + 2p)` (`Geometry.vertex_multiplicities`).  (Seat 7's
`θ`-lattice, `α = 2θ`, `β = π/2 − 3θ`, `γ = π/2 + θ`, is the same lattice: `(h, t) = (2s+y+z,
2x−3y+z)`.)  Targets: `γ = (2,1)`, `π + β = (3,3)`, `π = (3,2)`, `π − α = (2,2)`, `2α = (2,0)`,
`α = (1,0)`, `β = (0,1)`, `2π = (6,4)`. -/

/-- **Residual `γ` fills only as `{γ}` or `{2α, β}`** (R4 S1). -/
theorem gamma_fill (x y z p : ℕ) (h1 : x + 2 * z + 3 * p = 2) (h2 : y + z + 2 * p = 1) :
    (x = 0 ∧ y = 0 ∧ z = 1 ∧ p = 0) ∨ (x = 2 ∧ y = 1 ∧ z = 0 ∧ p = 0) := by omega

/-- **`π + β` fills only as `{α, 2β, γ}`, `{3α, 3β}`, or a straight angle `+ β`** (R4, `Q₁` in `L_c`). -/
theorem pi_add_beta_fill (x y z p : ℕ) (h1 : x + 2 * z + 3 * p = 3) (h2 : y + z + 2 * p = 3) :
    (x = 1 ∧ y = 2 ∧ z = 1 ∧ p = 0) ∨ (x = 3 ∧ y = 3 ∧ z = 0 ∧ p = 0) ∨
      (x = 0 ∧ y = 1 ∧ z = 0 ∧ p = 1) := by omega

/-- `π` fills as `{α,β,γ}`, `{3α,2β}` or one straight angle (S6: far side of the anti-diagonal). -/
theorem pi_fill (x y z p : ℕ) (h1 : x + 2 * z + 3 * p = 3) (h2 : y + z + 2 * p = 2) :
    (x = 1 ∧ y = 1 ∧ z = 1 ∧ p = 0) ∨ (x = 3 ∧ y = 2 ∧ z = 0 ∧ p = 0) ∨
      (x = 0 ∧ y = 0 ∧ z = 0 ∧ p = 1) := by omega

/-- `π − α` (= `2π − 2γ`, the rigid residual at `P′`) fills as `{2α, 2β}` or `{β, γ}`. -/
theorem pi_sub_alpha_fill (x y z p : ℕ) (h1 : x + 2 * z + 3 * p = 2) (h2 : y + z + 2 * p = 2) :
    (x = 2 ∧ y = 2 ∧ z = 0 ∧ p = 0) ∨ (x = 0 ∧ y = 1 ∧ z = 1 ∧ p = 0) := by omega

/-- `β` is indecomposable (`β − α` is not a sum of angles): a straight angle at `Q₁` lies along
`ℓ` or along the `a`-line only. -/
theorem beta_fill (x y z p : ℕ) (h1 : x + 2 * z + 3 * p = 0) (h2 : y + z + 2 * p = 1) :
    x = 0 ∧ y = 1 ∧ z = 0 ∧ p = 0 := by omega

/-- `2α` fills only as `{α, α}`. -/
theorem two_alpha_fill (x y z p : ℕ) (h1 : x + 2 * z + 3 * p = 2) (h2 : y + z + 2 * p = 0) :
    x = 2 ∧ y = 0 ∧ z = 0 ∧ p = 0 := by omega

/-- `α` is indecomposable (P31: the gap left by a `β` corner is a single `α`-corner). -/
theorem alpha_fill (x y z p : ℕ) (h1 : x + 2 * z + 3 * p = 1) (h2 : y + z + 2 * p = 0) :
    x = 1 ∧ y = 0 ∧ z = 0 ∧ p = 0 := by omega

/-- **R4's figure at `P′`, as counts.**  At an interior point (`2π = (6,4)`, `u` full turns) carrying
`≥ 2` γ-corners (`T₂`, `T₃`), `≥ 1` β-corner (`K`) and `≥ 1` α-corner (`T₂ + P′`, forced by S5), the
figure is exactly `{2α, 2β, 2γ}`, with no straight angle and no full turn. -/
theorem figure_at_pprime_counts (x y z p u : ℕ) (h1 : x + 2 * z + 3 * p + 6 * u = 6)
    (h2 : y + z + 2 * p + 4 * u = 4) (hx : 1 ≤ x) (hy : 1 ≤ y) (hz : 2 ≤ z) :
    x = 2 ∧ y = 2 ∧ z = 2 ∧ p = 0 ∧ u = 0 := by omega

/-- Without S5's `α` the count alone allows `{β, 3γ}` (the paper's `prop:figurePprime` figure). -/
theorem figure_at_pprime_without_alpha :
    0 + 2 * 3 + 3 * 0 + 6 * 0 = 6 ∧ 1 + 3 + 2 * 0 + 4 * 0 = 4 := by norm_num

/-- **Real bridge.**  A real angle identity `xα + yβ + zγ + pπ = sα + tβ` gives the integer
coordinates.  Corpus: `Geometry.vertex_multiplicities` after `π = 3α + 2β`. -/
theorem fill_counts_real {α β : ℝ} (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (x y z p : ℕ) (s t : ℤ)
    (h : (x : ℝ) * α + (y : ℝ) * β + (z : ℝ) * (2 * α + β) + (p : ℝ) * Real.pi
      = (s : ℝ) * α + (t : ℝ) * β) :
    (x : ℤ) + 2 * z + 3 * p = s ∧ (y : ℤ) + z + 2 * p = t := by
  have h' : ((x + 3 * p : ℕ) : ℝ) * α + ((y + 2 * p : ℕ) : ℝ) * β + (z : ℝ) * (2 * α + β)
      = (s : ℝ) * α + (t : ℝ) * β := by
    push_cast; linear_combination h + (p : ℝ) * hrel
  obtain ⟨h1, h2⟩ := Geometry.vertex_multiplicities hrel hirr _ _ _ s t h'
  push_cast at h1 h2
  constructor <;> linarith

/-- The residual-`γ` catalogue at the level of real angles. -/
theorem gamma_fill_real {α β : ℝ} (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (x y z p : ℕ)
    (h : (x : ℝ) * α + (y : ℝ) * β + (z : ℝ) * (2 * α + β) + (p : ℝ) * Real.pi = 2 * α + β) :
    (x = 0 ∧ y = 0 ∧ z = 1 ∧ p = 0) ∨ (x = 2 ∧ y = 1 ∧ z = 0 ∧ p = 0) := by
  obtain ⟨h1, h2⟩ := fill_counts_real hrel hirr x y z p 2 1 (by push_cast; linarith)
  exact gamma_fill x y z p (by omega) (by omega)

/-- The `π + β` catalogue at the level of real angles. -/
theorem pi_add_beta_fill_real {α β : ℝ} (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (x y z p : ℕ)
    (h : (x : ℝ) * α + (y : ℝ) * β + (z : ℝ) * (2 * α + β) + (p : ℝ) * Real.pi = Real.pi + β) :
    (x = 1 ∧ y = 2 ∧ z = 1 ∧ p = 0) ∨ (x = 3 ∧ y = 3 ∧ z = 0 ∧ p = 0) ∨
      (x = 0 ∧ y = 1 ∧ z = 0 ∧ p = 1) := by
  obtain ⟨h1, h2⟩ := fill_counts_real hrel hirr x y z p 3 3 (by push_cast; linarith)
  exact pi_add_beta_fill x y z p (by omega) (by omega)

/-- `2γ + π > 2π` (so two `γ` at a point forbid a straight angle there: `P′`, `2P′`); and
`γ > α + β` (moderator §3: the far corner at `Q₁` is `β`). -/
theorem two_gamma_add_pi_gt {α β : ℝ} (hrel : 3 * α + 2 * β = Real.pi) (hα : 0 < α) :
    2 * Real.pi < 2 * (2 * α + β) + Real.pi ∧ α + β < 2 * α + β := by
  constructor <;> linarith

/-! ## §3 P31 and the moderator's (M)₂ step -/

/-- `2a − c = f·(2e − f)` (for `f ≤ 2e`). -/
theorem two_a_sub_c_eq (e f : ℕ) (h : f ≤ 2 * e) : 2 * (e * f) - f ^ 2 = f * (2 * e - f) := by
  have h1 : f ^ 2 ≤ 2 * (e * f) := by nlinarith
  zify [h, h1]; ring

/-- **(M)₂: `2a − c = f(2e − f) ∉ S` when `f < 2e < 2f`** (moderator §3, hand derivation).  Size
kills `a` and `c` (`2e − f < e < f`); then `n_b·b = f(2e − f)`, `gcd(f, b) = 1` forces `f ∣ n_b`,
and `n_b ≥ f` overshoots while `n_b = 0` leaves `f(2e − f) = 0`. -/
theorem two_a_sub_c_not_mem {e f b : ℕ} (hcop : Nat.Coprime e f) (hef : e < f) (hfe : f < 2 * e)
    (hb : b + e ^ 2 = f ^ 2) : ¬ InS e f b (f * (2 * e - f)) := by
  rintro ⟨na, nb, nc, h⟩
  have hf0 : 0 < f := by omega
  have hd : 2 * e - f < e := by omega
  have hdpos : 0 < 2 * e - f := by omega
  have hna : na = 0 := by
    by_contra hc
    have k1 : e * f ≤ na * (e * f) := Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero hc)
    have k2 : f * (2 * e - f) < f * e := Nat.mul_lt_mul_of_pos_left hd hf0
    have k3 : f * e = e * f := Nat.mul_comm f e
    omega
  have hnc : nc = 0 := by
    by_contra hc
    have k1 : f ^ 2 ≤ nc * f ^ 2 := Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero hc)
    have k2 : f * (2 * e - f) < f * f := Nat.mul_lt_mul_of_pos_left (by omega) hf0
    have k3 : f ^ 2 = f * f := sq f
    omega
  subst hna; subst hnc
  have h' : nb * b = f * (2 * e - f) := by simpa using h
  have hdv : f ∣ nb := Inflation.f_dvd_nb e f b nb hcop hb
    (by rw [show ((nb : ℤ) * (b : ℤ)) = ((nb * b : ℕ) : ℤ) by push_cast; ring, h']
        exact_mod_cast dvd_mul_right f _)
  rcases Nat.eq_zero_or_pos nb with h0 | h0
  · subst h0
    have : f * (2 * e - f) = 0 := by omega
    rcases Nat.mul_eq_zero.mp this with h1 | h1 <;> omega
  · have hge : f ≤ nb := Nat.le_of_dvd h0 hdv
    have hbf : 2 * e - f < b := by nlinarith
    have k1 : f * b ≤ nb * b := Nat.mul_le_mul_right _ hge
    have k2 : f * (2 * e - f) < f * b := Nat.mul_lt_mul_of_pos_left hbf hf0
    omega

/-- **The same, as a corollary of `2a`-rigidity** (the moderator's citation, "a_side_rigid at
k = 2"): `2a = c + w` with `w ∈ S` is a representation of `2a` with a `c`, which `two_a_rigid`
forbids for `f ≥ 3`. -/
theorem two_a_ne_c_add {e f b na nb nc : ℕ} (he : 1 ≤ e) (hef : e < f) (hf3 : 3 ≤ f)
    (hcop : Nat.Coprime e f) (hb : b + e ^ 2 = f ^ 2) :
    na * (e * f) + nb * b + nc * f ^ 2 + f ^ 2 ≠ 2 * (e * f) := by
  intro h
  have := (two_a_rigid (na := na) (nb := nb) (nc := nc + 1) he hef hf3 hcop hb
    (by rw [← h]; ring)).2.2
  omega

/-- **The (M)₂ step dichotomy.**  For a member with `f ≥ 3`: `f ≠ 2e`, and either `c > 2a` (the
β-tile's `c` would exit the leg) or `c < 2a` with leftover `2a − c ∉ S`. -/
theorem m2_step_dichotomy {e f b : ℕ} (he : 1 ≤ e) (hcop : Nat.Coprime e f) (hef : e < f)
    (hf3 : 3 ≤ f) (hb : b + e ^ 2 = f ^ 2) :
    2 * (e * f) < f ^ 2 ∨ (f ^ 2 < 2 * (e * f) ∧ ¬ InS e f b (2 * (e * f) - f ^ 2)) := by
  have hne : f ≠ 2 * e := by
    intro h
    have : e ∣ f := ⟨2, by omega⟩
    have := Nat.Coprime.eq_one_of_dvd hcop this
    omega
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · right
    refine ⟨by nlinarith, ?_⟩
    rw [two_a_sub_c_eq e f h.le]
    exact two_a_sub_c_not_mem hcop hef h hb
  · left; nlinarith

/-- `(M)₂` step fails at `N = 44`: `(1,2)`, `2a − c = 0 ∈ S` (and `f = 2e`). -/
theorem m2_step_fails_N44 : 2 * (1 * 2) - 2 ^ 2 = 0 ∧ InS 1 2 3 0 ∧ 2 = 2 * 1 :=
  ⟨by norm_num, ⟨0, 0, 0, by norm_num⟩, rfl⟩

/-- Witness for `two_a_sub_c_not_mem`'s hypotheses: `(3,5)` (`f < 2e < 2f`, `2a − c = 5`),
`(7,10)` (`2a − c = 40`), `(4,7)` (`2a − c = 7`). -/
theorem two_a_sub_c_hyps_satisfiable :
    Nat.Coprime 3 5 ∧ 5 < 2 * 3 ∧ 3 < 5 ∧ 16 + 3 ^ 2 = 5 ^ 2 ∧ 5 * (2 * 3 - 5) = 5 ∧
    Nat.Coprime 7 10 ∧ 10 < 2 * 7 ∧ 10 * (2 * 7 - 10) = 40 ∧
    Nat.Coprime 4 7 ∧ 7 < 2 * 4 ∧ 7 * (2 * 4 - 7) = 7 := by
  refine ⟨by decide, by norm_num, by norm_num, by norm_num, by norm_num, by decide, by norm_num,
    by norm_num, by decide, by norm_num, by norm_num⟩

/-- **P31 threshold:** `a < b ⟺ e² + ef < f²`. -/
theorem a_lt_b_iff {e f b : ℕ} (hb : b + e ^ 2 = f ^ 2) : e * f < b ↔ e ^ 2 + e * f < f ^ 2 := by
  omega

/-- **P31 threshold, golden form:** for `0 ≤ t`, `t < (√5 − 1)/2 ⟺ t² + t < 1`; with `t = e/f`
this is `e² + ef < f²`, i.e. `a < b`. -/
theorem golden_threshold {t : ℝ} (ht : 0 ≤ t) : t < (Real.sqrt 5 - 1) / 2 ↔ t ^ 2 + t < 1 := by
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hs : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  constructor
  · intro h
    nlinarith
  · intro h
    by_contra hc
    push_neg at hc
    nlinarith

/-- **P31 flank step:** an `α`-corner's flanks are `b` and `c` (`Interface.flanks`); when `a < b`
both exceed `a` (`c > a` always), so an `α`-tile laid along `PJ₁′` (length `a`) overshoots `J₁′`. -/
theorem alpha_flanks_exceed_a {e f b : ℕ} (hef : e < f) (hab : e * f < b) :
    e * f < b ∧ e * f < f ^ 2 := by
  refine ⟨hab, ?_⟩
  have hf : 0 < f := by omega
  rw [sq]; exact Nat.mul_lt_mul_of_pos_right hef hf

/-- Witnesses for P31's threshold both ways: `(3,5)` has `a = 15 < b = 16`; `(7,10)` has
`a = 70 > b = 51` (P31 silent there, the room's `(7,10)` β-piercer kill is engine-only). -/
theorem p31_threshold_witnesses : 3 * 5 < 16 ∧ ¬ (7 * 10 < 51) := by norm_num

/-! ## §4 Witnesses for the remaining conditionals (vacuity rule) -/

/-- `b_pinning`: two different words of equal value below `f·b` exist — `(3,5)`, `75 = 3c = 5a`,
`75 < f·b = 80` (b-counts `0 = 0`). -/
theorem b_pinning_hyps_satisfiable :
    Nat.Coprime 3 5 ∧ 16 + 3 ^ 2 = 5 ^ 2 ∧ 0 * (3 * 5) + 0 * 16 + 3 * 5 ^ 2 = 75 ∧
    5 * (3 * 5) + 0 * 16 + 0 * 5 ^ 2 = 75 ∧ 75 < 5 * 16 := by
  refine ⟨by decide, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- `r3_kill_bpiercer`: its window `b ≤ d* < 2b` is non-empty (`(4,7)`: `33 ≤ 35 < 66`, where
`r3_kill` is silent), and `nb ≥ 2` is necessary there: near `c⁴·b`, far `b·c⁴` (`nb = 1`),
`x₀ = 229 ≤ 231`. -/
theorem r3_bpiercer_hyps :
    33 ≤ dStar 7 33 ∧ dStar 7 33 < 2 * 33 ∧
    4 * 7 ^ 2 + (0 * (4 * 7) + 1 * 33 + 0 * 7 ^ 2) = 229 ∧ 0 * (4 * 7) + 1 * 33 + 4 * 7 ^ 2 = 229 :=
  ⟨by decide, by decide, by norm_num, by norm_num⟩

/-- `chain_point_minus_b`: `(3,5)`, `5c = 3a + 4b + b` (`n_b = 4 = f − 1`, `5c = 125 ≥ f·b = 80`). -/
theorem chain_point_minus_b_hyps : 3 * (3 * 5) + 4 * 16 + 0 * 5 ^ 2 + 16 = 5 * 5 ^ 2 := by norm_num

/-- `chain_point_minus_b_not_mem`, `chain_bound`: `(3,5)`, `k = 2`: `b ≤ 2c = 50 < f·b = 80`,
`50 < (f−1)·b = 64`. -/
theorem chain_hyps : 16 ≤ 2 * 5 ^ 2 ∧ 2 * 5 ^ 2 < 5 * 16 ∧ 2 * 5 ^ 2 < (5 - 1) * 16 := by norm_num

/-- The real-angle bridges' hypotheses (`3α + 2β = π`, `α ∉ ℚπ`) are satisfiable
(`MarchSlots.angleData_f3`, corpus). -/
theorem angle_hyps_satisfiable :
    ∃ α β : ℝ, 3 * α + 2 * β = Real.pi ∧ ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi := by
  obtain ⟨α, β, γ, h⟩ := MarchSlots.angleData_f3
  exact ⟨α, β, h.hrel, h.hirr⟩

/-- `figure_at_pprime_counts`: `(2,2,2,0,0)` meets every hypothesis. -/
theorem figure_counts_hyps : 2 + 2 * 2 + 3 * 0 + 6 * 0 = 6 ∧ 2 + 2 + 2 * 0 + 4 * 0 = 4 := by
  norm_num

/-- `m2_step_dichotomy`: both branches occur — `(2,5)`: `2a = 20 < c = 25`; `(3,5)`: `c < 2a = 30`. -/
theorem m2_dichotomy_both_branches : 2 * (2 * 5) < 5 ^ 2 ∧ 5 ^ 2 < 2 * (3 * 5) := by norm_num

end Erdos634.Draft.HalfTurnR3R4

#print axioms Erdos634.Draft.HalfTurnR3R4.b_pinning
#print axioms Erdos634.Draft.HalfTurnR3R4.b_pinning_window_sharp
#print axioms Erdos634.Draft.HalfTurnR3R4.dStar_eq_mod
#print axioms Erdos634.Draft.HalfTurnR3R4.dStar_eq_f_mul_mod
#print axioms Erdos634.Draft.HalfTurnR3R4.mod_f_eq_rho
#print axioms Erdos634.Draft.HalfTurnR3R4.dStar_eq_f_rho
#print axioms Erdos634.Draft.HalfTurnR3R4.dStar_not_mem
#print axioms Erdos634.Draft.HalfTurnR3R4.dStar_mem_edge_cases
#print axioms Erdos634.Draft.HalfTurnR3R4.nStar_lt
#print axioms Erdos634.Draft.HalfTurnR3R4.r3_kill_below
#print axioms Erdos634.Draft.HalfTurnR3R4.r3_kill_at_base
#print axioms Erdos634.Draft.HalfTurnR3R4.r3_kill
#print axioms Erdos634.Draft.HalfTurnR3R4.r3_kill_bpiercer
#print axioms Erdos634.Draft.HalfTurnR3R4.r3_arith
#print axioms Erdos634.Draft.HalfTurnR3R4.r3_member_hyps_satisfiable
#print axioms Erdos634.Draft.HalfTurnR3R4.r3_dstar_hyp_necessary
#print axioms Erdos634.Draft.HalfTurnR3R4.r3_far_b_hyp_necessary
#print axioms Erdos634.Draft.HalfTurnR3R4.r3_fails_m2_N44
#print axioms Erdos634.Draft.HalfTurnR3R4.pierce_chain_point
#print axioms Erdos634.Draft.HalfTurnR3R4.chain_point_minus_b
#print axioms Erdos634.Draft.HalfTurnR3R4.chain_point_minus_b_not_mem
#print axioms Erdos634.Draft.HalfTurnR3R4.two_a_rigid
#print axioms Erdos634.Draft.HalfTurnR3R4.c_rigid
#print axioms Erdos634.Draft.HalfTurnR3R4.chain_bound
#print axioms Erdos634.Draft.HalfTurnR3R4.gamma_fill
#print axioms Erdos634.Draft.HalfTurnR3R4.pi_add_beta_fill
#print axioms Erdos634.Draft.HalfTurnR3R4.pi_fill
#print axioms Erdos634.Draft.HalfTurnR3R4.pi_sub_alpha_fill
#print axioms Erdos634.Draft.HalfTurnR3R4.beta_fill
#print axioms Erdos634.Draft.HalfTurnR3R4.two_alpha_fill
#print axioms Erdos634.Draft.HalfTurnR3R4.alpha_fill
#print axioms Erdos634.Draft.HalfTurnR3R4.figure_at_pprime_counts
#print axioms Erdos634.Draft.HalfTurnR3R4.fill_counts_real
#print axioms Erdos634.Draft.HalfTurnR3R4.gamma_fill_real
#print axioms Erdos634.Draft.HalfTurnR3R4.pi_add_beta_fill_real
#print axioms Erdos634.Draft.HalfTurnR3R4.two_gamma_add_pi_gt
#print axioms Erdos634.Draft.HalfTurnR3R4.two_a_sub_c_eq
#print axioms Erdos634.Draft.HalfTurnR3R4.two_a_sub_c_not_mem
#print axioms Erdos634.Draft.HalfTurnR3R4.two_a_ne_c_add
#print axioms Erdos634.Draft.HalfTurnR3R4.m2_step_dichotomy
#print axioms Erdos634.Draft.HalfTurnR3R4.m2_step_fails_N44
#print axioms Erdos634.Draft.HalfTurnR3R4.two_a_sub_c_hyps_satisfiable
#print axioms Erdos634.Draft.HalfTurnR3R4.a_lt_b_iff
#print axioms Erdos634.Draft.HalfTurnR3R4.golden_threshold
#print axioms Erdos634.Draft.HalfTurnR3R4.alpha_flanks_exceed_a
#print axioms Erdos634.Draft.HalfTurnR3R4.p31_threshold_witnesses
#print axioms Erdos634.Draft.HalfTurnR3R4.b_pinning_hyps_satisfiable
#print axioms Erdos634.Draft.HalfTurnR3R4.r3_bpiercer_hyps
#print axioms Erdos634.Draft.HalfTurnR3R4.chain_point_minus_b_hyps
#print axioms Erdos634.Draft.HalfTurnR3R4.chain_hyps
#print axioms Erdos634.Draft.HalfTurnR3R4.angle_hyps_satisfiable
#print axioms Erdos634.Draft.HalfTurnR3R4.figure_counts_hyps
#print axioms Erdos634.Draft.HalfTurnR3R4.m2_dichotomy_both_branches
#print axioms Erdos634.Draft.HalfTurnR3R4.dStar_lt_c
#print axioms Erdos634.Draft.HalfTurnR3R4.r3_kill_bpiercer_rung2
#print axioms Erdos634.Draft.HalfTurnR3R4.rung2_core
#print axioms Erdos634.Draft.HalfTurnR3R4.r3_rung2_witness_11_13
