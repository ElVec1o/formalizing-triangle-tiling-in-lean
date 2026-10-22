import Mathlib

/-!
# Beeson-Rosu (arXiv 2607.23453 v2), Sect. 10: Lemmas 23-28 for the tile with 3 alpha + 2 beta = pi

NOTE, UNAUDITED.  Credit: Michael Beeson and Rosu (arXiv 2607.23453 v2), Beeson (arXiv 1206.2229 v4, Lemmas 2, 8),
Beeson-Zhang, Laczkovich (DCG 48 (2012)).  Formalization debt, not progress on the /goal outcomes.

H1 = "alpha is not a rational multiple of pi" is an explicit hypothesis of Lemma 23/24; it is WITNESSED for every
integer tile by `lemma27_h1` (printed Lemma 27, via Mathlib's Niven theorem), instance `(2,3,4)`.

* `lemma23_unique`, `lemma23_sector`, `lemma23_items` (R-L23): uniqueness of `p alpha + q beta`, sector filling.
* `lemma24_core`, `lemma24_rest` (R-L24): the ARITHMETIC half of the printed Lemma 24 (no gamma at a vertex of T).
  The geometric half (angles of a tiled T at its vertices are sums of tile angles) is NOT in this file.
* `lemma25` (R-L25): gamma = (pi + alpha)/2, beta = (pi - 3 alpha)/2, a/c = 2 sin(alpha/2), b/c = 2 cos alpha - 1,
  a^2 = c(c - b), cos alpha = (b + c)/(2c), from the law of sines (hypothesis in cross-multiplied form).
* `lemma26` (R-L26): `(a,b,c) = (mk, k^2 - m^2, k^2)`, `k = gcd(a,c)`, `m < k`.
* `lemma27_h1` (printed Lemma 27): alpha/pi irrational for an integer tile.  Shorter than the printed proof: cos alpha =
  (b+c)/(2c) lies strictly between 1/2 and 1, and Niven gives no such rational cosine.
* `lemma28` (R-L27 in the map; printed Lemma 28): the relation lattice has basis e1 = (k,0,-m), e2 = (m,k,-k),
  `k | y` and `m | y + z`.
-/

namespace Erdos634.BeesonRow

open Real

theorem lemma23_unique (α β : ℝ) (h3 : 3 * α + 2 * β = π) (H1 : ¬ ∃ r : ℚ, α = (r : ℝ) * π)
    (p q u v : ℤ) (h : (p : ℝ) * α + q * β = u * α + v * β) : p = u ∧ q = v := by
  have hβ : β = (π - 3 * α) / 2 := by linarith
  rw [hβ] at h
  have key : α * (2 * ((p : ℝ) - u) - 3 * ((q : ℝ) - v)) = -((q : ℝ) - v) * π := by
    linear_combination 2 * h
  by_cases hq : q = v
  · subst hq
    refine ⟨?_, rfl⟩
    by_contra hp
    have hne : (2 * ((p : ℝ) - u) - 3 * ((q : ℝ) - q)) ≠ 0 := by
      have : (p : ℝ) ≠ u := by exact_mod_cast hp
      intro h0; apply this; linarith
    have : α = 0 := by
      have := key; simp at this
      rcases this with h0 | h0
      · exact h0
      · exfalso; apply hne; simp; linarith
    exact H1 ⟨0, by simp [this]⟩
  · exfalso
    have hd : ((q : ℝ) - v) ≠ 0 := by
      intro h0; apply hq; have : (q : ℝ) = v := by linarith
      exact_mod_cast this
    have hc : (2 * ((p : ℝ) - u) - 3 * ((q : ℝ) - v)) ≠ 0 := by
      intro h0; rw [h0, mul_zero] at key
      have : ((q : ℝ) - v) * π = 0 := by linarith
      rcases mul_eq_zero.mp this with h1 | h1
      · exact hd h1
      · exact Real.pi_ne_zero h1
    apply H1
    have hα' : α = (-((q : ℝ) - v) * π) / (2 * ((p : ℝ) - u) - 3 * ((q : ℝ) - v)) := by
      rw [eq_div_iff hc]; exact key
    refine ⟨((-((q : ℚ) - v)) / (2 * ((p : ℚ) - u) - 3 * ((q : ℚ) - v))), ?_⟩
    push_cast
    rw [hα']; ring

theorem lemma23_sector (α β : ℝ) (h3 : 3 * α + 2 * β = π) (H1 : ¬ ∃ r : ℚ, α = (r : ℝ) * π)
    (x y z p q : ℕ) (h : (x : ℝ) * α + y * β + z * (2 * α + β) = p * α + q * β) :
    x + 2 * z = p ∧ y + z = q := by
  have := lemma23_unique α β h3 H1 ((x : ℤ) + 2 * z) ((y : ℤ) + z) p q (by push_cast; linarith)
  omega

theorem lemma23_items (α β : ℝ) (h3 : 3 * α + 2 * β = π) (H1 : ¬ ∃ r : ℚ, α = (r : ℝ) * π)
    (x y z : ℕ) :
    ((x : ℝ) * α + y * β + z * (2 * α + β) = α → x = 1 ∧ y = 0 ∧ z = 0) ∧
    ((x : ℝ) * α + y * β + z * (2 * α + β) = β → x = 0 ∧ y = 1 ∧ z = 0) ∧
    ((x : ℝ) * α + y * β + z * (2 * α + β) = α + β → x = 1 ∧ y = 1 ∧ z = 0) ∧
    ((x : ℝ) * α + y * β + z * (2 * α + β) = 3 * α → x = 3 ∧ y = 0 ∧ z = 0) ∧
    ((x : ℝ) * α + y * β + z * (2 * α + β) = α + 2 * β → x = 1 ∧ y = 2 ∧ z = 0) := by
  have s := fun p q : ℕ => lemma23_sector α β h3 H1 x y z p q
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
  · have := s 1 0 (by push_cast; linarith); omega
  · have := s 0 1 (by push_cast; linarith); omega
  · have := s 1 1 (by push_cast; linarith); omega
  · have := s 3 0 (by push_cast; linarith); omega
  · have := s 1 2 (by push_cast; linarith); omega

/-- Arithmetic core of printed Lemma 24: if a vertex of T carries `gamma + r alpha + s beta` and the other two vertices
carry `p alpha + q beta` with `p + q >= 2`, then `p = q = 1`, `r = s = 0`. -/
theorem lemma24_core (α β : ℝ) (h3 : 3 * α + 2 * β = π) (H1 : ¬ ∃ r : ℚ, α = (r : ℝ) * π)
    (p q r s : ℕ) (hpq : 2 ≤ p + q)
    (hsum : ((2 * α + β) + (r * α + s * β)) + (p * α + q * β) = π) :
    p = 1 ∧ q = 1 ∧ r = 0 ∧ s = 0 := by
  have := lemma23_unique α β h3 H1 ((p : ℤ) + r + 2) ((q : ℤ) + s + 1) 3 2 (by push_cast; linarith)
  omega

/-- The other two angles of T, each filled by at least one tile and adding up to `alpha + beta`, are `alpha` and `beta`. -/
theorem lemma24_rest (α β : ℝ) (h3 : 3 * α + 2 * β = π) (H1 : ¬ ∃ r : ℚ, α = (r : ℝ) * π)
    (u2 v2 u3 v3 : ℕ) (h2 : 1 ≤ u2 + v2) (h3' : 1 ≤ u3 + v3)
    (h : ((u2 : ℝ) * α + v2 * β) + (u3 * α + v3 * β) = α + β) :
    (u2 = 1 ∧ v2 = 0 ∧ u3 = 0 ∧ v3 = 1) ∨ (u2 = 0 ∧ v2 = 1 ∧ u3 = 1 ∧ v3 = 0) := by
  have := lemma23_unique α β h3 H1 ((u2 : ℤ) + u3) ((v2 : ℤ) + v3) 1 1 (by push_cast; linarith)
  omega

theorem lemma25 (α β γ a b c : ℝ) (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ) (hs : α + β + γ = π)
    (h3 : 3 * α + 2 * β = π) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (la : a * Real.sin γ = c * Real.sin α) (lb : b * Real.sin γ = c * Real.sin β) :
    γ = (π + α) / 2 ∧ β = (π - 3 * α) / 2 ∧ a / c = 2 * Real.sin (α / 2) ∧
    b / c = 2 * Real.cos α - 1 ∧ b / c = 1 - (a / c) ^ 2 ∧ a ^ 2 = c * (c - b) ∧
    Real.cos α = (b + c) / (2 * c) := by
  have hγe : γ = α / 2 + π / 2 := by linarith
  have hβe : β = π / 2 - 3 * (α / 2) := by linarith
  have hαlt : α < π / 3 := by linarith
  have hcp : 0 < Real.cos (α / 2) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have sγ : Real.sin γ = Real.cos (α / 2) := by rw [hγe, Real.sin_add_pi_div_two]
  have sβ : Real.sin β = Real.cos (3 * (α / 2)) := by rw [hβe, Real.sin_pi_div_two_sub]
  have sα : Real.sin α = 2 * Real.sin (α / 2) * Real.cos (α / 2) := by
    rw [← Real.sin_two_mul]; ring_nf
  have cα : Real.cos α = 2 * Real.cos (α / 2) ^ 2 - 1 := by
    rw [← Real.cos_two_mul]; ring_nf
  have hA : a = 2 * c * Real.sin (α / 2) := by
    rw [sγ, sα] at la
    apply mul_right_cancel₀ hcp.ne'
    linarith
  have hB : b = c * (4 * Real.cos (α / 2) ^ 2 - 3) := by
    rw [sγ, sβ, Real.cos_three_mul] at lb
    apply mul_right_cancel₀ hcp.ne'
    nlinarith [lb]
  have hB' : b = c * (2 * Real.cos α - 1) := by rw [hB, cα]; ring
  have sc : Real.sin (α / 2) ^ 2 = 1 - Real.cos (α / 2) ^ 2 := by
    linarith [Real.sin_sq_add_cos_sq (α / 2)]
  have hA2 : a ^ 2 = c * (c - b) := by
    rw [hA, hB]; linear_combination (4 * c ^ 2) * sc
  refine ⟨by linarith, by linarith, ?_, ?_, ?_, hA2, ?_⟩
  · rw [hA]; field_simp
  · rw [hB']; field_simp
  · have : b / c = 1 - (a / c) ^ 2 := by
      field_simp; nlinarith [hA2]
    exact this
  · rw [hB']; field_simp; ring

theorem lemma26 (a b c m k : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hk : 0 < k)
    (hmk : Nat.Coprime m k) (hr : a * k = m * c) (h : a ^ 2 + c * b = c ^ 2)
    (hg : Nat.gcd (Nat.gcd a b) c = 1) :
    c = k ^ 2 ∧ a = m * k ∧ b + m ^ 2 = k ^ 2 ∧ k = Nat.gcd a c ∧ m < k := by
  have e1 : b * k ^ 2 + c * m ^ 2 = c * k ^ 2 := by
    have h1 : c * (b * k ^ 2 + c * m ^ 2) = c * (c * k ^ 2) := by
      have : a ^ 2 * k ^ 2 = m ^ 2 * c ^ 2 := by
        have := congrArg (fun x => x ^ 2) hr; simp only [mul_pow] at this; exact this
      nlinarith [this, h]
    exact Nat.eq_of_mul_eq_mul_left hc h1
  have hd : k ^ 2 ∣ c := by
    have : k ^ 2 ∣ c * m ^ 2 := by
      have h2 : k ^ 2 ∣ b * k ^ 2 + c * m ^ 2 := by rw [e1]; exact Dvd.intro_left _ rfl
      exact (Nat.dvd_add_right (Dvd.intro_left _ rfl)).mp h2
    exact (Nat.Coprime.pow 2 2 hmk.symm).dvd_of_dvd_mul_right this
  obtain ⟨t, rfl⟩ := hd
  have hk2 : 0 < k ^ 2 := by positivity
  have e2 : b + t * m ^ 2 = t * k ^ 2 := by
    apply Nat.eq_of_mul_eq_mul_left hk2
    nlinarith [e1]
  have e3 : a = m * k * t := by
    apply Nat.eq_of_mul_eq_mul_left hk
    nlinarith [hr]
  have ht : t = 1 := by
    have h1 : t ∣ a := ⟨m * k, by rw [e3]; ring⟩
    have h2 : t ∣ b := by
      have : t ∣ b + t * m ^ 2 := by rw [e2]; exact Dvd.intro _ rfl
      exact (Nat.dvd_add_left (Dvd.intro _ rfl)).mp this
    have h3 : t ∣ k ^ 2 * t := Dvd.intro_left _ rfl
    have : t ∣ Nat.gcd (Nat.gcd a b) (k ^ 2 * t) := Nat.dvd_gcd (Nat.dvd_gcd h1 h2) h3
    rw [hg] at this; exact Nat.dvd_one.mp this
  subst ht
  have e3' : a = m * k := by simpa using e3
  have e2' : b + m ^ 2 = k ^ 2 := by simpa using e2
  refine ⟨mul_one _, e3', e2', ?_, ?_⟩
  · rw [e3', mul_one, show k ^ 2 = k * k by ring, Nat.gcd_mul_right, hmk.gcd_eq_one, one_mul]
  · have : m ^ 2 < k ^ 2 := by omega
    exact lt_of_pow_lt_pow_left₀ 2 (Nat.zero_le _) this

/-- H1 for an integer tile: for `cos alpha = (b+c)/(2c)` with `0 < b < c`, `0 <= alpha <= pi`, the angle `alpha` is not a rational multiple of `pi` (Niven).
This is NOT the printed Lemma 27 of Beeson's v4 (Lemma 27 there is a counting formula); the name `lemma27_h1` is historical. Credit: Beeson (arXiv 1206.2229 v4). -/
theorem lemma27_h1 (b c : ℕ) (hb : 0 < b) (hbc : b < c) (α : ℝ) (hα : Real.cos α = ((b : ℝ) + c) / (2 * c))
    (h0 : 0 ≤ α) (hπ : α ≤ π) : ¬ ∃ r : ℚ, α = (r : ℝ) * π := by
  rintro ⟨r, hr⟩
  have hc : (0 : ℝ) < c := by exact_mod_cast (by omega : 0 < c)
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have hbc' : (b : ℝ) < c := by exact_mod_cast hbc
  have hlt : 1 / 2 < Real.cos α := by rw [hα, lt_div_iff₀ (by positivity)]; linarith
  have hgt : Real.cos α < 1 := by rw [hα, div_lt_one (by positivity)]; linarith
  have hcos : ∃ q : ℚ, Real.cos α = q := ⟨((b : ℚ) + c) / (2 * c), by rw [hα]; push_cast; ring⟩
  have := niven_angle_eq ⟨r, hr⟩ hcos ⟨h0, hπ⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this
  have c23 : Real.cos (π * (2 / 3)) = -1 / 2 := by
    rw [show π * (2 / 3) = π - π / 3 by ring, Real.cos_pi_sub, Real.cos_pi_div_three]; norm_num
  rcases this with h | h | h | h | h <;> rw [h] at hlt hgt
  · simp at hgt
  · rw [Real.cos_pi_div_three] at hlt; norm_num at hlt
  · rw [Real.cos_pi_div_two] at hlt; norm_num at hlt
  · rw [c23] at hlt; norm_num at hlt
  · rw [Real.cos_pi] at hlt; norm_num at hlt

theorem lemma28 (m k : ℕ) (hm : 0 < m) (hmk : Nat.Coprime m k) (hlt : m < k) (x y z : ℤ)
    (h : x * ((m : ℤ) * k) + y * ((k : ℤ) ^ 2 - (m : ℤ) ^ 2) + z * (k : ℤ) ^ 2 = 0) :
    (∃! ξη : ℤ × ℤ, (x, y, z) = (ξη.1 * k + ξη.2 * m, ξη.2 * k, -ξη.1 * m - ξη.2 * k)) ∧
      (k : ℤ) ∣ y ∧ (m : ℤ) ∣ y + z := by
  have hk : (0 : ℤ) < k := by exact_mod_cast (by omega : 0 < k)
  have hcop : IsCoprime (k : ℤ) ((m : ℤ) ^ 2) := by
    have := Nat.isCoprime_iff_coprime.mpr (Nat.Coprime.pow_right 2 hmk.symm)
    exact_mod_cast this
  have hky : (k : ℤ) ∣ y := by
    have : (k : ℤ) ∣ y * (m : ℤ) ^ 2 := by
      have : y * (m : ℤ) ^ 2 = k * (x * m + y * k + z * k) - ( x * ((m : ℤ) * k) + y * ((k : ℤ) ^ 2 - (m : ℤ) ^ 2) + z * (k : ℤ) ^ 2) := by ring
      rw [this, h, sub_zero]; exact Dvd.intro _ rfl
    exact hcop.dvd_of_dvd_mul_right this
  obtain ⟨η, rfl⟩ := hky
  have e1 : (m : ℤ) * (x - η * m) = -(k * (z + η * k)) := by
    have : (k : ℤ) * ((m : ℤ) * (x - η * m) + k * (z + η * k)) = 0 := by linear_combination h
    rcases mul_eq_zero.mp this with h0 | h0
    · exact absurd h0 hk.ne'
    · linarith
  have hcop2 : IsCoprime (k : ℤ) (m : ℤ) := by
    exact_mod_cast Nat.isCoprime_iff_coprime.mpr hmk.symm
  have hkx : (k : ℤ) ∣ x - η * m := by
    have : (k : ℤ) ∣ (m : ℤ) * (x - η * m) := ⟨-(z + η * k), by linarith⟩
    exact hcop2.dvd_of_dvd_mul_left this
  obtain ⟨ξ, hξ⟩ := hkx
  have hz : z = -ξ * m - η * k := by
    have : (k : ℤ) * (m * ξ + (z + η * k)) = 0 := by
      rw [hξ] at e1; linear_combination e1
    rcases mul_eq_zero.mp this with h0 | h0
    · exact absurd h0 hk.ne'
    · linarith
  have hx : x = ξ * k + η * m := by linarith
  refine ⟨⟨(ξ, η), ?_, ?_⟩, ⟨η, rfl⟩, ?_⟩
  · simp only [Prod.mk.injEq]; exact ⟨hx, by ring, hz⟩
  · intro ⟨ξ', η'⟩ hh
    simp only [Prod.mk.injEq] at hh
    obtain ⟨h1, h2, h3⟩ := hh
    have hη : η' = η := by
      have : (η' - η) * k = 0 := by linarith
      rcases mul_eq_zero.mp this with h0 | h0
      · linarith
      · exact absurd h0 hk.ne'
    have hξ' : ξ' = ξ := by
      subst hη
      have : (ξ' - ξ) * k = 0 := by linarith
      rcases mul_eq_zero.mp this with h0 | h0
      · linarith
      · exact absurd h0 hk.ne'
    rw [hξ', hη]
  · exact ⟨-ξ, by rw [hz]; ring⟩

/-- Witness of the lattice basis: e1, e2 lie in K for the tile (2,3,4): (m,k) = (1,2). -/
theorem wit28 : (2 : ℤ) * (1 * 2) + 0 * 3 + (-1) * 4 = 0 ∧ 1 * (1 * 2) + 2 * 3 + (-2) * 4 = 0 := by norm_num

/-- H1 WITNESSED for the tile (2,3,4): alpha = arccos(7/8) is not a rational multiple of pi. -/
theorem wit_h1_234 : ¬ ∃ r : ℚ, Real.arccos (7 / 8) = (r : ℝ) * π := by
  apply lemma27_h1 3 4 (by norm_num) (by norm_num)
  · rw [Real.cos_arccos (by norm_num) (by norm_num)]; norm_num
  · exact Real.arccos_nonneg _
  · exact Real.arccos_le_pi _

end Erdos634.BeesonRow
