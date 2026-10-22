import Mathlib

/-!
# BAD layer L3: the algebraic core of `prop:basealphadiv`

Written 2026-10-03.  Pure algebra over `ℤ[T;T⁻¹]`, no geometry.  Paper: `prop:basealphadiv`
(`paper/erdos-634.tex` ~l.1627-1683), steps "Division" and "Evaluation".

Tile `(a,b,c) = (ef, f²-e², f²)`.  `Φ = f t² - e t + f`, `p = (e t + f) Φ`, `q = (f t + e) Φ`.
Hypothesis: the boundary polynomial `B = Y + X (t² + t⁻²)` with `X = f² w`, `Y = (2f²-e²) w`
is a signed sum of shifted tile polynomials `± t^s p`, `± t^s q`.  Conclusion: `(f²-e²) ∣ w`.

NOT in this file: the geometric input that such a signed sum exists for a tiling (layers L1, L2).
-/

open LaurentPolynomial

namespace BAD

noncomputable section

abbrev L := LaurentPolynomial ℤ

def Phi (e f : ℤ) : L := C f * T 2 - C e * T 1 + C f
def pTile (e f : ℤ) : L := (C e * T 1 + C f) * Phi e f
def qTile (e f : ℤ) : L := (C f * T 1 + C e) * Phi e f
/-- boundary polynomial of the base-α isosceles target with `X = f² w`, `Y = (2f²-e²) w`. -/
def Bdry (e f w : ℤ) : L := C (f ^ 2 * w) * T 2 + C ((2 * f ^ 2 - e ^ 2) * w) + C (f ^ 2 * w) * T (-2)

/-- a signed shifted tile term: `(σ, s, true)` is `σ t^s p`, `(σ, s, false)` is `σ t^s q`. -/
def term (e f : ℤ) (x : ℤ × ℤ × Bool) : L :=
  C x.1 * T x.2.1 * (if x.2.2 then pTile e f else qTile e f)

def tsum (e f : ℤ) (l : List (ℤ × ℤ × Bool)) : L := (l.map (term e f)).sum

def gterm (e f : ℤ) (x : ℤ × ℤ × Bool) : L :=
  C x.1 * T x.2.1 * (if x.2.2 then (C e * T 1 + C f) else (C f * T 1 + C e))

def gsum (e f : ℤ) (l : List (ℤ × ℤ × Bool)) : L := (l.map (gterm e f)).sum

theorem tsum_eq (e f : ℤ) (l : List (ℤ × ℤ × Bool)) : tsum e f l = Phi e f * gsum e f l := by
  induction l with
  | nil => simp [tsum, gsum]
  | cons x l ih =>
    simp only [tsum, gsum, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih, mul_add]
    congr 1
    unfold term gterm pTile qTile
    split_ifs <;> ring

/-- `Bdry = Φ · B'` with `B' = u t⁰ + v t⁻¹ + u t⁻²`, `u = f w`, `v = e w`. -/
def Bq (e f w : ℤ) : L := C (f * w) + C (e * w) * T (-1) + C (f * w) * T (-2)

theorem Bdry_eq (e f w : ℤ) : Bdry e f w = Phi e f * Bq e f w := by
  have h1 : (T 2 : L) * T (-2) = 1 := by rw [← T_add]; simp
  have h2 : (T 1 : L) * T (-1) = 1 := by rw [← T_add]; simp
  have h3 : (T 2 : L) * T (-1) = T 1 := by rw [← T_add]; norm_num
  have h4 : (T 1 : L) * T (-2) = T (-1) := by rw [← T_add]; norm_num
  have h5 : (T 1 : L) * T (-1) * T (-1) = T (-1) := by rw [h2, one_mul]
  unfold Bdry Phi Bq
  simp only [map_mul, map_sub, map_pow, map_ofNat]
  have h : (T 1 : L) * T (-1) = 1 := h2
  have hx : (T 2 : L) = T 1 * T 1 := by rw [← T_add]; norm_num
  have hy : (T (-2) : L) = T (-1) * T (-1) := by rw [← T_add]; norm_num
  rw [hx, hy]
  linear_combination (-(C e * C f * C w * T 1 + C f ^ 2 * C w * (T 1 * T (-1) + 1)
      - C e ^ 2 * C w - C e * C f * C w * T (-1))) * h

instance : NoZeroDivisors L := inferInstanceAs (NoZeroDivisors (AddMonoidAlgebra ℤ ℤ))

theorem Phi_ne_zero (e f : ℤ) (h0 : 0 < e) (hef : e < f) : Phi e f ≠ 0 := by
  intro h
  have := congrArg (LaurentPolynomial.eval₂ (Int.castRingHom ℤ) (1 : ℤˣ)) h
  simp [Phi] at this
  omega

theorem Bq_eq_gsum (e f w : ℤ) (h0 : 0 < e) (hef : e < f) (l : List (ℤ × ℤ × Bool))
    (h : Bdry e f w = tsum e f l) : Bq e f w = gsum e f l := by
  rw [Bdry_eq, tsum_eq] at h
  exact mul_left_cancel₀ (Phi_ne_zero e f h0 hef) h

theorem basealpha_div_of_poly (e f w : ℤ) (h0 : 0 < e) (hef : e < f)
    (hcb : IsCoprime e (f ^ 2 - e ^ 2)) (hcf : IsCoprime f (f ^ 2 - e ^ 2))
    (l : List (ℤ × ℤ × Bool)) (h : Bdry e f w = tsum e f l) : (f ^ 2 - e ^ 2) ∣ w := by
  have hG := Bq_eq_gsum e f w h0 hef l h
  obtain ⟨u, v, huv⟩ := hcb
  set b : ℤ := f ^ 2 - e ^ 2 with hbdef
  set n : ℕ := b.natAbs with hn
  have hb0 : ((b : ℤ) : ZMod n) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd b n).2 (Int.natAbs_dvd_self)
  have hF2 : ((f : ℤ) : ZMod n) ^ 2 = ((e : ℤ) : ZMod n) ^ 2 := by
    have := hb0
    rw [hbdef] at this
    push_cast at this
    exact sub_eq_zero.1 this
  have hEU : ((e : ℤ) : ZMod n) * (u : ZMod n) = 1 := by
    have := congrArg (fun z : ℤ => (z : ZMod n)) huv
    simp only [Int.cast_add, Int.cast_mul, Int.cast_one, hb0, mul_zero, add_zero] at this
    rw [mul_comm]; exact this
  set τ : ZMod n := -((f : ℤ) : ZMod n) * (u : ZMod n) with hτ
  have hττ : τ * τ = 1 := by
    have : τ * τ = (((f : ℤ) : ZMod n) ^ 2) * (u : ZMod n) ^ 2 := by rw [hτ]; ring
    rw [this, hF2]
    calc ((e : ℤ) : ZMod n) ^ 2 * (u : ZMod n) ^ 2 = (((e : ℤ) : ZMod n) * (u : ZMod n)) ^ 2 := by ring
      _ = 1 := by rw [hEU]; norm_num
  let τu : (ZMod n)ˣ := ⟨τ, τ, hττ, hττ⟩
  have hinv : τu⁻¹ = τu := inv_eq_of_mul_eq_one_right (Units.ext hττ)
  have hτe : ((e : ℤ) : ZMod n) * τ + ((f : ℤ) : ZMod n) = 0 := by
    rw [hτ]
    calc _ = ((f : ℤ) : ZMod n) * (1 - ((e : ℤ) : ZMod n) * (u : ZMod n)) := by ring
      _ = 0 := by rw [hEU]; ring
  have hτf : ((f : ℤ) : ZMod n) * τ + ((e : ℤ) : ZMod n) = 0 := by
    rw [hτ]
    calc _ = ((e : ℤ) : ZMod n) * (1 - ((e : ℤ) : ZMod n) * (u : ZMod n)) +
        (((e : ℤ) : ZMod n) ^ 2 - ((f : ℤ) : ZMod n) ^ 2) * (u : ZMod n) := by ring
      _ = 0 := by rw [hEU, hF2]; ring
  have hφe : LaurentPolynomial.eval₂ (Int.castRingHom (ZMod n)) τu (C e * T 1 + C f) = 0 := by
    simpa [LaurentPolynomial.eval₂_C, LaurentPolynomial.eval₂_T, τu] using hτe
  have hφf : LaurentPolynomial.eval₂ (Int.castRingHom (ZMod n)) τu (C f * T 1 + C e) = 0 := by
    simpa [LaurentPolynomial.eval₂_C, LaurentPolynomial.eval₂_T, τu] using hτf
  have hgs : ∀ l' : List (ℤ × ℤ × Bool),
      LaurentPolynomial.eval₂ (Int.castRingHom (ZMod n)) τu (gsum e f l') = 0 := by
    intro l'
    induction l' with
    | nil => simp [gsum]
    | cons x l' ih =>
      simp only [gsum, List.map_cons, List.sum_cons, map_add] at ih ⊢
      rw [ih, add_zero]
      unfold gterm
      rw [map_mul]
      split_ifs
      · rw [hφe, mul_zero]
      · rw [hφf, mul_zero]
  have hBq : LaurentPolynomial.eval₂ (Int.castRingHom (ZMod n)) τu (Bq e f w) = ((f * w : ℤ) : ZMod n) := by
    simp only [Bq, map_add, map_mul, LaurentPolynomial.eval₂_C, LaurentPolynomial.eval₂_T,
      zpow_neg, zpow_one, hinv]
    have h2 : (τu ^ (2 : ℤ) : (ZMod n)ˣ) = 1 := by
      rw [zpow_two]; exact Units.ext hττ
    rw [h2]
    simp only [inv_one, Units.val_one, mul_one, eq_intCast, Int.coe_castRingHom]
    change _ + _ * τ + _ = _
    rw [hτ]
    push_cast
    linear_combination (-((f : ZMod n) * (w : ZMod n))) * hEU
  have key : ((f * w : ℤ) : ZMod n) = 0 := by
    rw [← hBq, hG, hgs]
  have hd : (n : ℤ) ∣ f * w := (ZMod.intCast_zmod_eq_zero_iff_dvd _ n).1 key
  have hd' : b ∣ f * w := Int.natAbs_dvd_natAbs.1 (Int.natCast_dvd.1 hd)
  exact hcf.symm.dvd_of_dvd_mul_left hd'

end

end BAD
