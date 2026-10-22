import Erdos634.Draft.BeesonIsoArith

/-!
# Beeson, "Tilings of an isosceles triangle" (arXiv 1206.1974 v7), Lemma 11.8: the arithmetic core (chord commensurability)

NOTE, UNAUDITED.  Credit: Michael Beeson (arXiv 1206.1974 v7, Sect. 11, Lemmas 11.2, 11.8, 11.9, 11.10; arXiv 1206.2229), Laczkovich
(DCG 48 (2012)), Beeson-Zhang, Herdt, Zhang.  Formalization debt, not progress on the /goal outcomes.

* `tile_param`: a real tile `(a,b,c)` with `c^2 = a^2 + ab`, triangle inequality `b < a + c` and `a/b`, `c/a` rational (Beeson Thm 10.7,
  `beeson_thm107_proved`) is `t * (k^2, m^2-k^2, km)` with `t > 0`, `k < m < 2k` coprime (Lemma 11.2 after scaling to integers with no common factor).
* `chord_arith`: the arithmetic content of the proof of Lemma 11.8: a tile edge `l` in `{a,b,c}` is NOT a sum of at least two tile edges.
  (Printed proof: "the north side of EF supports at least two tiles", then the cases `l = a, b, c`; the printed case `l = b` says "b is an integer multiple of a"
  which is not what the sides force; the argument below is mod k and is valid.)
Witness: the tile `(4,5,6)` of the 1125-tiling is `1 * (k^2, m^2-k^2, km)` with `(k,m) = (2,3)`: `wit_tile_param`; `chord_arith` has no false hypothesis (it concludes `False`
from `n >= 2` edges summing to an edge) so it is exercised by `wit_chord_one` (one edge CAN equal an edge: the `n = 1` boundary case) and `wit_chord_two_fails`.
-/

namespace Erdos634.Draft.BeesonIso3a

open Erdos634.Draft.BeesonIsoArith

/-- Positive rational multiples of a triple give an integer triple with no common factor. -/
theorem int_scale {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) {r s : ℚ} (hr : a = (r : ℝ) * b) (hs : c = (s : ℝ) * a) :
    ∃ t : ℝ, 0 < t ∧ ∃ A B C : ℕ, 0 < A ∧ 0 < B ∧ 0 < C ∧ Nat.gcd (Nat.gcd A B) C = 1 ∧
      a = t * A ∧ b = t * B ∧ c = t * C := by
  have hr0 : 0 < r := by
    have : (0 : ℝ) < (r : ℝ) := by
      by_contra h; push Not at h
      have := mul_nonpos_iff.mpr (Or.inr ⟨h, hb.le⟩)
      linarith
    exact_mod_cast this
  have hv0 : 0 < s * r := by
    have h1 : (0 : ℝ) < (s : ℝ) := by
      by_contra h; push Not at h
      have := mul_nonpos_iff.mpr (Or.inr ⟨h, ha.le⟩)
      linarith
    have : (0 : ℚ) < s := by exact_mod_cast h1
    exact mul_pos this hr0
  set v : ℚ := s * r with hv
  -- integer triple
  set A0 : ℕ := r.num.toNat * v.den with hA0
  set B0 : ℕ := r.den * v.den with hB0
  set C0 : ℕ := v.num.toNat * r.den with hC0
  have hrnpos : 0 < r.num := Rat.num_pos.mpr hr0
  have hvnpos : 0 < v.num := Rat.num_pos.mpr hv0
  have hrn : (r.num.toNat : ℤ) = r.num := Int.toNat_of_nonneg hrnpos.le
  have hvn : (v.num.toNat : ℤ) = v.num := Int.toNat_of_nonneg hvnpos.le
  have hA0p : 0 < A0 := Nat.mul_pos (by omega) v.den_pos
  have hB0p : 0 < B0 := Nat.mul_pos r.den_pos v.den_pos
  have hC0p : 0 < C0 := Nat.mul_pos (by omega) r.den_pos
  set g : ℕ := Nat.gcd (Nat.gcd A0 B0) C0 with hg
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left _ (Nat.gcd_pos_of_pos_left _ hA0p)
  obtain ⟨A, hA⟩ : g ∣ A0 := (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_left _ _)
  obtain ⟨B, hB⟩ : g ∣ B0 := (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_right _ _)
  obtain ⟨C, hC⟩ : g ∣ C0 := Nat.gcd_dvd_right _ _
  have hAp : 0 < A := by
    rcases Nat.eq_zero_or_pos A with h | h
    · rw [h] at hA; omega
    · exact h
  have hBp : 0 < B := by
    rcases Nat.eq_zero_or_pos B with h | h
    · rw [h] at hB; omega
    · exact h
  have hCp : 0 < C := by
    rcases Nat.eq_zero_or_pos C with h | h
    · rw [h] at hC; omega
    · exact h
  have hgcd : Nat.gcd (Nat.gcd A B) C = 1 := by
    have h1 : g = g * Nat.gcd (Nat.gcd A B) C := by
      conv_lhs => rw [hg, hA, hB, hC]
      rw [Nat.gcd_mul_left, Nat.gcd_mul_left]
    have := Nat.eq_of_mul_eq_mul_left hgpos (by linarith : g * 1 = g * Nat.gcd (Nat.gcd A B) C)
    exact this.symm
  refine ⟨b / B, div_pos hb (by exact_mod_cast hBp), A, B, C, hAp, hBp, hCp, hgcd, ?_, ?_, ?_⟩
  · -- a = (b/B) * A, using a/b = r = A0/B0 = A/B
    have hBr : (0 : ℝ) < B := by exact_mod_cast hBp
    have e1 : (r : ℝ) = (A : ℝ) / B := by
      have h1 : (r : ℚ) = (A0 : ℚ) / B0 := by
        have e1 : (r.num : ℚ) = r * r.den := (Rat.mul_den_eq_num r).symm
        have hn : ((r.num.toNat : ℕ) : ℚ) = r.num := by exact_mod_cast hrn
        have hd1 : (r.den : ℚ) ≠ 0 := by exact_mod_cast r.den_nz
        have hd2 : (v.den : ℚ) ≠ 0 := by exact_mod_cast v.den_nz
        rw [hA0, hB0]; push_cast
        rw [hn, e1]; field_simp
      have h2 : (A0 : ℝ) / B0 = (A : ℝ) / B := by
        rw [hA, hB]; push_cast
        have : (g : ℝ) ≠ 0 := by exact_mod_cast hgpos.ne'
        have hB' : (B : ℝ) ≠ 0 := hBr.ne'
        field_simp
      have h3 : ((r : ℚ) : ℝ) = ((A0 : ℚ) / B0 : ℚ) := by rw [h1]
      rw [h3]; push_cast; exact h2
    rw [hr, e1]; field_simp
  · field_simp
  · have hBr : (0 : ℝ) < B := by exact_mod_cast hBp
    have e2 : (v : ℝ) = (C : ℝ) / B := by
      have h1 : (v : ℚ) = (C0 : ℚ) / B0 := by
        have e1 : (v.num : ℚ) = v * v.den := (Rat.mul_den_eq_num v).symm
        have hn : ((v.num.toNat : ℕ) : ℚ) = v.num := by exact_mod_cast hvn
        have hd1 : (r.den : ℚ) ≠ 0 := by exact_mod_cast r.den_nz
        have hd2 : (v.den : ℚ) ≠ 0 := by exact_mod_cast v.den_nz
        rw [hC0, hB0]; push_cast
        rw [hn, e1]; field_simp
      have h2 : (C0 : ℝ) / B0 = (C : ℝ) / B := by
        rw [hC, hB]; push_cast
        have : (g : ℝ) ≠ 0 := by exact_mod_cast hgpos.ne'
        have hB' : (B : ℝ) ≠ 0 := hBr.ne'
        field_simp
      have h3 : ((v : ℚ) : ℝ) = ((C0 : ℚ) / B0 : ℚ) := by rw [h1]
      rw [h3]; push_cast; exact h2
    have : c = (v : ℝ) * b := by rw [hs, hr, hv]; push_cast; ring
    rw [this, e2]; field_simp

/-- Lemma 11.2 for a real tile with rational ratios (Beeson Thm 10.7). -/
theorem tile_param {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hrel : c ^ 2 = a ^ 2 + a * b) (htri : b < a + c)
    {r s : ℚ} (hr : a = (r : ℝ) * b) (hs : c = (s : ℝ) * a) :
    ∃ t : ℝ, 0 < t ∧ ∃ k m : ℕ, Nat.Coprime k m ∧ k < m ∧ m < 2 * k ∧
      a = t * (k : ℝ) ^ 2 ∧ b = t * ((m : ℝ) ^ 2 - (k : ℝ) ^ 2) ∧ c = t * ((k : ℝ) * m) := by
  obtain ⟨t, ht, A, B, C, hA, hB, hC, hgcd, ea, eb, ec⟩ := int_scale ha hb hc hr hs
  have hrelN : C ^ 2 = A ^ 2 + A * B := by
    have : (t * C) ^ 2 = (t * A) ^ 2 + (t * A) * (t * B) := by rw [← ea, ← eb, ← ec]; exact hrel
    have h2 : t ^ 2 * ((C : ℝ) ^ 2) = t ^ 2 * ((A : ℝ) ^ 2 + A * B) := by linear_combination this
    have h3 : ((C : ℝ) ^ 2) = (A : ℝ) ^ 2 + A * B := mul_left_cancel₀ (pow_pos ht 2).ne' h2
    exact_mod_cast h3
  have htriN : B < A + C := by
    have : t * (B : ℝ) < t * ((A : ℝ) + C) := by rw [← eb, mul_add, ← ea, ← ec]; exact htri
    have := lt_of_mul_lt_mul_left this ht.le
    exact_mod_cast this
  obtain ⟨k, m, hkm, hlt, hm2, hak, hbm, hckm⟩ := l11_2_fwd A B C hB hrelN hgcd htriN
  refine ⟨t, ht, k, m, hkm, hlt, hm2, ?_, ?_, ?_⟩
  · rw [ea, hak]; push_cast; ring
  · have : (B : ℝ) = (m : ℝ) ^ 2 - (k : ℝ) ^ 2 := by
      have := congrArg (fun x : ℕ => (x : ℝ)) hbm
      push_cast at this; linarith
    rw [eb, this]
  · rw [ec, hckm]; push_cast; ring

/-- **Chord arithmetic (Lemma 11.8).**  For the tile `(k^2, m^2-k^2, km)` (`k < m < 2k` coprime) an edge is never a sum of `na` a-edges, `nb` b-edges, `nc` c-edges
with `na + nb + nc >= 2`.  Natural-number form (`A = k^2`, `B = m^2-k^2`, `C = km`, all edges scaled to integers). -/
theorem chord_arith_nat (k m : ℕ) (hcop : Nat.Coprime k m) (hlt : k < m) (hm2 : m < 2 * k) (na nb nc : ℕ)
    (hn : 2 ≤ na + nb + nc) (l : ℕ) (hl : l = k ^ 2 ∨ l + k ^ 2 = m ^ 2 ∨ l = k * m)
    (hsum : l = na * k ^ 2 + nb * (m ^ 2 - k ^ 2) + nc * (k * m)) : False := by
  have hk2 : 2 ≤ k := by omega
  have hmk : k ^ 2 < m ^ 2 := by nlinarith
  obtain ⟨B, hB⟩ : ∃ B, B = m ^ 2 - k ^ 2 := ⟨_, rfl⟩
  rw [← hB] at hsum
  have hBeq : B + k * k = m ^ 2 := by rw [hB]; nlinarith [Nat.sub_add_cancel hmk.le]
  have hBmk : m + k ≤ B := by
    have h1 : m ^ 2 - k ^ 2 = (m + k) * (m - k) := Nat.sq_sub_sq m k
    have h2 : 1 ≤ m - k := by omega
    rw [hB, h1]; nlinarith
  have hkB : Nat.Coprime k B := by
    have h : Nat.Coprime k (B + k * k) := by rw [hBeq]; exact Nat.Coprime.pow_right 2 hcop
    exact (Nat.coprime_add_mul_right_right k B k).mp h
  have hkmpos : 0 < k * m := Nat.mul_pos (by omega) (by omega)
  have hk2pos : 0 < k * k := Nat.mul_pos (by omega) (by omega)
  have hBpos : 0 < B := by omega
  have hsq : k ^ 2 = k * k := by ring
  rw [hsq] at hsum hl
  have hdiv : ∀ x y : ℕ, k ∣ x * (k * k) + y * (k * m) := fun x y =>
    dvd_add (Dvd.dvd.mul_left (Dvd.intro _ rfl) _) (Dvd.dvd.mul_left (Dvd.intro _ rfl) _)
  have hz1 : 0 ≤ na * (k * k) := Nat.zero_le _
  have hz2 : 0 ≤ nc * (k * m) := Nat.zero_le _
  have hz3 : 0 ≤ nb * B := Nat.zero_le _
  -- common step for l = k*k and l = k*m: k | nb
  have hknb : (l = k * k ∨ l = k * m) → k ∣ nb := by
    intro h
    have h1 : k ∣ l := by rcases h with h | h <;> rw [h] <;> exact Dvd.intro _ rfl
    have h2 : l = nb * B + (na * (k * k) + nc * (k * m)) := by rw [hsum]; ring
    rw [h2] at h1
    exact Nat.Coprime.dvd_of_dvd_mul_right hkB ((Nat.dvd_add_left (hdiv na nc)).mp h1)
  have hbig : (l = k * k ∨ l = k * m) → 0 < nb → False := by
    intro h hpos
    have hk_le : k ≤ nb := Nat.le_of_dvd hpos (hknb h)
    have h1 : k * B ≤ nb * B := Nat.mul_le_mul_right B hk_le
    have h2 : k * m < k * B := Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
    have h3 : k * k ≤ k * m := Nat.mul_le_mul_left k (by omega)
    rcases h with h | h <;> omega
  rcases hl with hl | hl | hl
  · -- l = k^2
    rcases Nat.eq_zero_or_pos nb with h0 | hpos
    · subst h0
      rcases Nat.eq_zero_or_pos nc with hc0 | hc1
      · subst hc0
        have : na = 1 := by
          have h1 : k * k * 1 = k * k * na := by rw [mul_one]; nlinarith
          exact (Nat.eq_of_mul_eq_mul_left hk2pos h1).symm
        omega
      · have h1 : k * m ≤ nc * (k * m) := Nat.le_mul_of_pos_left _ hc1
        have h3 : k * k < k * m := Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
        omega
    · exact hbig (Or.inl hl) hpos
  · -- l = B
    have hlB : l = B := by omega
    rcases Nat.eq_zero_or_pos nb with h0 | hpos
    · subst h0
      have hkB' : k ∣ B := by
        have : B = k * (na * k + nc * m) := by rw [← hlB, hsum]; ring
        exact ⟨_, this⟩
      have hkm2 : k ∣ m ^ 2 := by rw [← hBeq]; exact dvd_add hkB' (Dvd.intro _ rfl)
      have : k ∣ 1 := by
        have h2 := Nat.dvd_gcd (dvd_refl k) hkm2
        rwa [(Nat.Coprime.pow_right 2 hcop).gcd_eq_one] at h2
      have := Nat.le_of_dvd one_pos this
      omega
    · rcases Nat.lt_or_ge nb 2 with h1 | h2
      · have hnb : nb = 1 := by omega
        subst hnb
        have ha : na * (k * k) = 0 := by omega
        have hc : nc * (k * m) = 0 := by omega
        have : na = 0 := by
          rcases Nat.eq_zero_or_pos na with h | h
          · exact h
          · exfalso; have := Nat.mul_pos h hk2pos; omega
        have : nc = 0 := by
          rcases Nat.eq_zero_or_pos nc with h | h
          · exact h
          · exfalso; have := Nat.mul_pos h hkmpos; omega
        omega
      · have : 2 * B ≤ nb * B := Nat.mul_le_mul_right B h2
        omega
  · -- l = k*m
    rcases Nat.eq_zero_or_pos nb with h0 | hpos
    · subst h0
      have hmeq : m = na * k + nc * m := by
        have : k * m = k * (na * k + nc * m) := by rw [← hl, hsum]; ring
        exact Nat.eq_of_mul_eq_mul_left (by omega) this
      rcases Nat.lt_or_ge nc 2 with h1 | h2
      · have hnc : nc = 0 ∨ nc = 1 := by omega
        rcases hnc with hnc | hnc
        · subst hnc
          have hkm : k ∣ m := ⟨na, by linarith⟩
          have : k ∣ 1 := by
            have h2 := Nat.dvd_gcd (dvd_refl k) hkm
            rwa [hcop.gcd_eq_one] at h2
          have := Nat.le_of_dvd one_pos this
          omega
        · subst hnc
          have : na * k = 0 := by omega
          have : na = 0 := by
            rcases Nat.eq_zero_or_pos na with h | h
            · exact h
            · exfalso; have := Nat.mul_pos h (by omega : 0 < k); omega
          omega
      · have : 2 * m ≤ nc * m := Nat.mul_le_mul_right m h2
        omega
    · exact hbig (Or.inr hl) hpos

/-- Real form: an edge of the tile `t * (k^2, m^2-k^2, km)` is not a sum of at least two tile edges. -/
theorem chord_arith {a b c t : ℝ} (ht : 0 < t) {k m : ℕ} (hcop : Nat.Coprime k m) (hlt : k < m) (hm2 : m < 2 * k)
    (ha : a = t * (k : ℝ) ^ 2) (hb : b = t * ((m : ℝ) ^ 2 - (k : ℝ) ^ 2)) (hc : c = t * ((k : ℝ) * m))
    {l : ℝ} (hl : l = a ∨ l = b ∨ l = c) {na nb nc : ℕ} (hn : 2 ≤ na + nb + nc)
    (hsum : l = na * a + nb * b + nc * c) : False := by
  have hmk : k ^ 2 < m ^ 2 := by nlinarith
  have hcast : ((m ^ 2 - k ^ 2 : ℕ) : ℝ) = (m : ℝ) ^ 2 - (k : ℝ) ^ 2 := by
    rw [Nat.cast_sub hmk.le]; push_cast; ring
  obtain ⟨l', hl'⟩ : ∃ l' : ℕ, l = t * (l' : ℝ) ∧ (l' = k ^ 2 ∨ l' + k ^ 2 = m ^ 2 ∨ l' = k * m) := by
    rcases hl with h | h | h
    · exact ⟨k ^ 2, by rw [h, ha]; push_cast; ring, Or.inl rfl⟩
    · exact ⟨m ^ 2 - k ^ 2, by rw [h, hb, hcast], Or.inr (Or.inl (by omega))⟩
    · exact ⟨k * m, by rw [h, hc]; push_cast; ring, Or.inr (Or.inr rfl)⟩
  obtain ⟨hl1, hl2⟩ := hl'
  refine chord_arith_nat k m hcop hlt hm2 na nb nc hn l' hl2 ?_
  have : t * (l' : ℝ) = t * ((na * k ^ 2 + nb * (m ^ 2 - k ^ 2) + nc * (k * m) : ℕ) : ℝ) := by
    rw [← hl1, hsum, ha, hb, hc]; push_cast
    rw [Nat.cast_sub hmk.le]; push_cast; ring
  have := mul_left_cancel₀ ht.ne' this
  exact_mod_cast this

/-- Witness: `(4,5,6) = 1 * (k^2, m^2-k^2, km)` with `(k,m) = (2,3)`. -/
theorem wit_tile_param : Nat.Coprime 2 3 ∧ 2 < 3 ∧ 3 < 2 * 2 ∧ (4 : ℝ) = 1 * (2 : ℝ) ^ 2 ∧ (5 : ℝ) = 1 * ((3 : ℝ) ^ 2 - (2 : ℝ) ^ 2) ∧
    (6 : ℝ) = 1 * ((2 : ℝ) * 3) := by norm_num

/-- A single edge CAN equal an edge (the case `n = 1` excluded by `hn`): `a = a`. -/
theorem wit_chord_one : (4 : ℝ) = 1 * 4 + 0 * 5 + 0 * 6 := by norm_num

/-- Two edges of the 1125-tile never sum to an edge (spot check of the conclusion): `4+4, 4+5, 4+6, 5+5, 5+6, 6+6 \notin {4,5,6}`. -/
theorem wit_chord_two_fails : ∀ x y : ℝ, (x = 4 ∨ x = 5 ∨ x = 6) → (y = 4 ∨ y = 5 ∨ y = 6) → x + y ≠ 4 ∧ x + y ≠ 5 ∧ x + y ≠ 6 := by
  rintro x y (rfl | rfl | rfl) (rfl | rfl | rfl) <;> norm_num

end Erdos634.Draft.BeesonIso3a

#print axioms Erdos634.Draft.BeesonIso3a.int_scale
#print axioms Erdos634.Draft.BeesonIso3a.tile_param
#print axioms Erdos634.Draft.BeesonIso3a.chord_arith_nat
#print axioms Erdos634.Draft.BeesonIso3a.chord_arith
