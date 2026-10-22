import Erdos634.Draft.BeesonIso4e

/-!
# Beeson, "Tilings of an isosceles triangle" (arXiv 1206.1974 v7), Lemma 11.10, "at least four": the arithmetic

NOTE, UNAUDITED.  Credit: Michael Beeson (arXiv 1206.1974 v7, Lemma 11.10), Laczkovich (DCG 48 (2012)), Beeson-Zhang, Herdt, Zhang.
Formalization debt, not progress on the /goal outcomes.

Tile `t (k^2, m^2-k^2, km)`, `k < m < 2k` coprime.  A base of exactly three tiles has `na + nb + nc = 3` edges with `nb, nc >= 1` (a b-edge and a c-edge exist on the base) and the leg is
`X = (a/c) Y`.
* `base_arith`: `k Y' = m X'` (`Y'`, `X'` the base and leg lengths in units of `t`) forces `(na, nb, nc) = (1,1,1)` and `X' = k (m+k)`, i.e. `Y = a+b+c`, `X = a+c`.
* `leg_arith`: a leg `X = a + c` containing a c-edge consists of exactly one a-edge and one c-edge.
* `sum_abc_cnt`: a list of lengths each equal to `a`, `b` or `c` (pairwise distinct) has counts; existence of an entry equal to `b` (`c`) gives `nb >= 1` (`nc >= 1`).
Witness: `(k,m) = (2,3)` (tile (4,5,6)): `wit_base_arith` (Y' = 15, X' = 10).
-/

open scoped Classical

namespace Erdos634.Draft.BeesonIso5a

theorem base_arith (k m : ℕ) (hcop : Nat.Coprime k m) (hlt : k < m) (hm2 : m < 2 * k) (na nb nc : ℕ) (hsum : na + nb + nc = 3)
    (hb : 1 ≤ nb) (hc : 1 ≤ nc) (Y' X' : ℕ) (hY : Y' = na * k ^ 2 + nb * (m ^ 2 - k ^ 2) + nc * (k * m))
    (hrel : k * Y' = m * X') : na = 1 ∧ nb = 1 ∧ nc = 1 ∧ X' = k * (m + k) := by
  have hk2 : 2 ≤ k := by omega
  have hm3 : 3 ≤ m := by omega
  have hmk : k ^ 2 < m ^ 2 := by nlinarith
  obtain ⟨B, hB⟩ : ∃ B, B = m ^ 2 - k ^ 2 := ⟨_, rfl⟩
  rw [← hB] at hY
  have hBeq : B + k ^ 2 = m ^ 2 := by omega
  have hmY : m ∣ Y' := by
    have h1 : m ∣ k * Y' := ⟨X', hrel⟩
    exact (Nat.Coprime.symm hcop).dvd_of_dvd_mul_left h1
  have hcop2 : Nat.Coprime m (k ^ 2) := Nat.Coprime.pow_right 2 (Nat.Coprime.symm hcop)
  have hm2k : m ∣ k ^ 2 → False := by
    intro h
    have := Nat.Coprime.eq_one_of_dvd hcop2 h
    omega
  have hmB : m ∣ B + k ^ 2 := by rw [hBeq]; exact dvd_pow_self m two_ne_zero
  -- the three possible shapes
  have hcases : (na = 1 ∧ nb = 1 ∧ nc = 1) ∨ (na = 0 ∧ nb = 1 ∧ nc = 2) ∨ (na = 0 ∧ nb = 2 ∧ nc = 1) := by omega
  rcases hcases with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · subst h1; subst h2; subst h3
    refine ⟨rfl, rfl, rfl, ?_⟩
    have hY' : Y' = m * (m + k) := by
      rw [hY]; nlinarith [hBeq]
    rw [hY'] at hrel
    have : m * (k * (m + k)) = m * X' := by rw [← hrel]; ring
    exact (Nat.eq_of_mul_eq_mul_left (by omega) this).symm
  · exfalso
    subst h1; subst h2; subst h3
    -- Y' + k^2 = m (m + 2k)
    have e : Y' + k ^ 2 = m * (m + 2 * k) := by rw [hY]; nlinarith [hBeq]
    have h1 : m ∣ Y' + k ^ 2 := ⟨m + 2 * k, e⟩
    have := (Nat.dvd_add_right hmY).mp h1
    exact hm2k this
  · exfalso
    subst h1; subst h2; subst h3
    have e : Y' + 2 * k ^ 2 = m * (2 * m + k) := by rw [hY]; nlinarith [hBeq]
    have h1 : m ∣ Y' + 2 * k ^ 2 := ⟨2 * m + k, e⟩
    have h2 := (Nat.dvd_add_right hmY).mp h1
    have h3 : m ∣ 2 := Nat.Coprime.dvd_of_dvd_mul_right hcop2 h2
    have := Nat.le_of_dvd (by omega) h3
    omega

theorem leg_arith (k m : ℕ) (hcop : Nat.Coprime k m) (hlt : k < m) (hm2 : m < 2 * k) (u v w : ℕ)
    (hX : u * k ^ 2 + v * (m ^ 2 - k ^ 2) + w * (k * m) = k * (m + k)) (hw : 1 ≤ w) : u = 1 ∧ v = 0 ∧ w = 1 := by
  have hk2 : 2 ≤ k := by omega
  have hmk : k ^ 2 < m ^ 2 := by nlinarith
  obtain ⟨B, hB⟩ : ∃ B, B = m ^ 2 - k ^ 2 := ⟨_, rfl⟩
  rw [← hB] at hX
  have hBeq : B + k ^ 2 = m ^ 2 := by omega
  have hBmk : m + k ≤ B := by
    have h1 : m ^ 2 - k ^ 2 = (m + k) * (m - k) := Nat.sq_sub_sq m k
    have h2 : 1 ≤ m - k := by omega
    rw [hB, h1]; nlinarith
  have hkB : Nat.Coprime k B := by
    have h : Nat.Coprime k (B + k * k) := by rw [show B + k * k = m ^ 2 by nlinarith [hBeq]]; exact Nat.Coprime.pow_right 2 hcop
    exact (Nat.coprime_add_mul_right_right k B k).mp h
  have hw1 : w = 1 := by
    by_contra hh
    have h2 : 2 ≤ w := by omega
    have : 2 * (k * m) ≤ w * (k * m) := Nat.mul_le_mul_right _ h2
    nlinarith
  subst hw1
  have hX' : u * k ^ 2 + v * B = k ^ 2 := by nlinarith
  have hv0 : v = 0 := by
    by_contra hv
    have hvpos : 0 < v := Nat.pos_of_ne_zero hv
    have hkd : k ∣ v * B := by
      have h2 : k ∣ k ^ 2 := dvd_pow_self k two_ne_zero
      have h3 : k ∣ u * k ^ 2 := Dvd.dvd.mul_left h2 u
      have h4 : k ∣ u * k ^ 2 + v * B := by rw [hX']; exact h2
      exact (Nat.dvd_add_right h3).mp h4
    have hkv : k ∣ v := hkB.dvd_of_dvd_mul_right hkd
    have hk_le : k ≤ v := Nat.le_of_dvd hvpos hkv
    have : k * B ≤ v * B := Nat.mul_le_mul_right B hk_le
    nlinarith
  subst hv0
  refine ⟨?_, rfl, rfl⟩
  have : u * k ^ 2 = 1 * k ^ 2 := by omega
  exact Nat.eq_of_mul_eq_mul_right (by positivity) this

/-- Counts of a list of lengths each equal to `a`, `b` or `c` (pairwise distinct). -/
theorem sum_abc_cnt (a b c : ℝ) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (ds : List ℝ) (h : ∀ x ∈ ds, x = a ∨ x = b ∨ x = c) :
    ∃ na nb nc : ℕ, na + nb + nc = ds.length ∧ ds.sum = na * a + nb * b + nc * c ∧
      ((∃ x ∈ ds, x = b) → 1 ≤ nb) ∧ ((∃ x ∈ ds, x = c) → 1 ≤ nc) := by
  induction ds with
  | nil => exact ⟨0, 0, 0, by simp, by simp, by simp, by simp⟩
  | cons x ds ih =>
    obtain ⟨na, nb, nc, hl, hs, hb, hc⟩ := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    rcases h x (List.mem_cons_self ..) with hx | hx | hx
    · refine ⟨na + 1, nb, nc, by simp only [List.length_cons]; omega, by simp only [List.sum_cons]; rw [hs, hx]; push_cast; ring, ?_, ?_⟩
      · rintro ⟨y, hy, hyb⟩
        rcases List.mem_cons.mp hy with rfl | hy'
        · exact absurd (hx.symm.trans hyb) hab
        · exact hb ⟨y, hy', hyb⟩
      · rintro ⟨y, hy, hyc⟩
        rcases List.mem_cons.mp hy with rfl | hy'
        · exact absurd (hx.symm.trans hyc) hac
        · exact hc ⟨y, hy', hyc⟩
    · refine ⟨na, nb + 1, nc, by simp only [List.length_cons]; omega, by simp only [List.sum_cons]; rw [hs, hx]; push_cast; ring, ?_, ?_⟩
      · intro _; omega
      · rintro ⟨y, hy, hyc⟩
        rcases List.mem_cons.mp hy with rfl | hy'
        · exact absurd (hx.symm.trans hyc) hbc
        · exact hc ⟨y, hy', hyc⟩
    · refine ⟨na, nb, nc + 1, by simp only [List.length_cons]; omega, by simp only [List.sum_cons]; rw [hs, hx]; push_cast; ring, ?_, ?_⟩
      · rintro ⟨y, hy, hyb⟩
        rcases List.mem_cons.mp hy with rfl | hy'
        · exact absurd (hx.symm.trans hyb) (Ne.symm hbc)
        · exact hb ⟨y, hy', hyb⟩
      · intro _; omega

/-- Witness: the tile (4,5,6) = (k^2, m^2-k^2, km) for (k,m) = (2,3): base `a+b+c` has `Y' = 15`, leg `X' = 10 = k (m+k)`, `k Y' = m X'`. -/
theorem wit_base_arith : Nat.Coprime 2 3 ∧ (1 + 1 + 1 = 3) ∧ 15 = 1 * 2 ^ 2 + 1 * (3 ^ 2 - 2 ^ 2) + 1 * (2 * 3) ∧ 2 * 15 = 3 * 10 ∧ 10 = 2 * (3 + 2) ∧
    10 = 1 * 2 ^ 2 + 0 * (3 ^ 2 - 2 ^ 2) + 1 * (2 * 3) := by decide

end Erdos634.Draft.BeesonIso5a

#print axioms Erdos634.Draft.BeesonIso5a.base_arith
#print axioms Erdos634.Draft.BeesonIso5a.leg_arith
#print axioms Erdos634.Draft.BeesonIso5a.sum_abc_cnt
