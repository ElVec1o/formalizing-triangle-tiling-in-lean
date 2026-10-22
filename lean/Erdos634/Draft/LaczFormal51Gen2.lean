-- Draft/LaczFormal51Gen2.lean -- Laczkovich (Discrete Math 140 (1995)) THEOREM 5.1 for the tile (alpha, beta, 2 alpha + beta), 3 alpha + 2 beta = pi, FOR EVERY DENOMINATOR:  `lacz51_all : BeesonH1.Lacz51`.
--   Route: write alpha, beta, gamma = a_i pi / n in lowest terms (`common_denom`).  If `Covered n`: `lacz51_cov` (certificates).  Otherwise: Lemma K on the dissection gives K1, K2 (`KConj.lemmaK`), hence `KStar`
--   (`LemmaKStar.lemmaKStar`); the corner counts P_l (sum of the corner figures) satisfy  sum_l P_l a_l = n.  If some P_l >= 3 then {k a_l/n} <= 1/3 or >= 2/3 for the units k (`kstar_frac`), Lemma 5.2 gives
--   n / gcd(a_l, n) in {3,4,6,10}, and the family relation forces n | 2*{3,4,6,10} or 3*{3,4,6,10}, which is Covered (`n_small`) -- contradiction.  Otherwise P_l <= 2 and the target angles are a permutation of the tile angles
--   (P = (1,1,1), (2,1,0)) or a tile angle is pi/2 (P = (2,2,0)) (`uncov_core`).  No new geometry beyond `lemmaK`; the vertex equations of Laczkovich's proof of Thm 4.1 (`tile_identity`) are not needed for this tile family.
-- NOTE, UNAUDITED.  Credit: Laczkovich (Discrete Math. 140 (1995) Thm 5.1, Lemma 5.2; Combinatorica 10 (1990)), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormal51Gen1
import Erdos634.Draft.KConjLemmaK
import Erdos634.Draft.LaczFormal51Id

open scoped BigOperators Classical

namespace Erdos634.Lacz51Gen2

open Erdos634 Erdos634.Geometry Erdos634.BeesonColoring Erdos634.BeesonH1 Erdos634.Draft.LaczFormal
  Erdos634.Draft.TheoremPConditional Erdos634.Lacz51Cov Erdos634.Lacz51Gen Erdos634.Geometry.CaseA.LemmaV

theorem common_denom {x y z : ℚ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hs : x + y + z = 1) :
    ∃ n a0 a1 a2 : ℕ, 0 < n ∧ a0 + a1 + a2 = n ∧ Nat.gcd a0 (Nat.gcd a1 a2) = 1 ∧
      x = (a0 : ℚ) / n ∧ y = (a1 : ℚ) / n ∧ z = (a2 : ℚ) / n := by
  have key : ∀ w : ℚ, 0 < w → ∃ m : ℕ, w = (m : ℚ) / w.den := by
    intro w hw
    refine ⟨w.num.toNat, ?_⟩
    have h1 : ((w.num.toNat : ℤ)) = w.num := Int.toNat_of_nonneg (Rat.num_pos.mpr hw).le
    have h2 : ((w.num.toNat : ℕ) : ℚ) = (w.num : ℚ) := by exact_mod_cast h1
    rw [h2]; exact (Rat.num_div_den w).symm
  obtain ⟨mx, hmx⟩ := key x hx
  obtain ⟨my, hmy⟩ := key y hy
  obtain ⟨mz, hmz⟩ := key z hz
  set dx := x.den; set dy := y.den; set dz := z.den
  have dxp : 0 < dx := x.den_pos
  have dyp : 0 < dy := y.den_pos
  have dzp : 0 < dz := z.den_pos
  set n0 := dx * dy * dz with hn0
  set A0 := mx * dy * dz
  set A1 := dx * my * dz
  set A2 := dx * dy * mz
  have n0p : 0 < n0 := by positivity
  have hA : A0 + A1 + A2 = n0 := by
    have : ((A0 + A1 + A2 : ℕ) : ℚ) = n0 := by
      have e0 : (A0 : ℚ) = x * n0 := by simp only [A0, n0]; push_cast; rw [hmx]; field_simp
      have e1 : (A1 : ℚ) = y * n0 := by simp only [A1, n0]; push_cast; rw [hmy]; field_simp
      have e2 : (A2 : ℚ) = z * n0 := by simp only [A2, n0]; push_cast; rw [hmz]; field_simp
      push_cast at e0 e1 e2 ⊢
      rw [e0, e1, e2]; linear_combination (n0 : ℚ) * hs
    exact_mod_cast this
  have Ae0 : (A0 : ℚ) = x * n0 := by simp only [A0, n0]; push_cast; rw [hmx]; field_simp
  have Ae1 : (A1 : ℚ) = y * n0 := by simp only [A1, n0]; push_cast; rw [hmy]; field_simp
  have Ae2 : (A2 : ℚ) = z * n0 := by simp only [A2, n0]; push_cast; rw [hmz]; field_simp
  set g := Nat.gcd A0 (Nat.gcd A1 A2) with hg
  have gp : 0 < g := by
    apply Nat.gcd_pos_of_pos_left
    simp only [A0]; have : 0 < mx := by
      by_contra h0; push Not at h0
      have : mx = 0 := by omega
      rw [this] at hmx; simp at hmx; linarith
    positivity
  obtain ⟨a0, ha0⟩ : g ∣ A0 := Nat.gcd_dvd_left _ _
  obtain ⟨a1, ha1⟩ : g ∣ A1 := (Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_left _ _)
  obtain ⟨a2, ha2⟩ : g ∣ A2 := (Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_right _ _)
  have hn : n0 = g * (a0 + a1 + a2) := by rw [← hA, ha0, ha1, ha2]; ring
  refine ⟨a0 + a1 + a2, a0, a1, a2, ?_, rfl, ?_, ?_, ?_, ?_⟩
  · by_contra h0
    have : a0 + a1 + a2 = 0 := by omega
    rw [this] at hn; omega
  · have e : Nat.gcd (g * a0) (Nat.gcd (g * a1) (g * a2)) = g := by
      rw [← ha0, ← ha1, ← ha2]
    rw [Nat.gcd_mul_left, Nat.gcd_mul_left] at e
    exact Nat.eq_of_mul_eq_mul_left gp (e.trans (mul_one g).symm)
  all_goals
    first
    | (have hgq : (g : ℚ) ≠ 0 := by exact_mod_cast gp.ne'
       have hq : ((a0 + a1 + a2 : ℕ) : ℚ) ≠ 0 := by
         have : 0 < a0 + a1 + a2 := by
           by_contra h0
           have : a0 + a1 + a2 = 0 := by omega
           rw [this] at hn; omega
         exact_mod_cast this.ne'
       first
       | (rw [eq_div_iff hq]
          have e := Ae0
          rw [ha0] at e
          have hn' : (n0 : ℚ) = g * ((a0 + a1 + a2 : ℕ) : ℚ) := by exact_mod_cast hn
          rw [hn'] at e
          apply mul_left_cancel₀ hgq
          push_cast at e ⊢
          linarith)
       | (rw [eq_div_iff hq]
          have e := Ae1
          rw [ha1] at e
          have hn' : (n0 : ℚ) = g * ((a0 + a1 + a2 : ℕ) : ℚ) := by exact_mod_cast hn
          rw [hn'] at e
          apply mul_left_cancel₀ hgq
          push_cast at e ⊢
          linarith)
       | (rw [eq_div_iff hq]
          have e := Ae2
          rw [ha2] at e
          have hn' : (n0 : ℚ) = g * ((a0 + a1 + a2 : ℕ) : ℚ) := by exact_mod_cast hn
          rw [hn'] at e
          apply mul_left_cancel₀ hgq
          push_cast at e ⊢
          linarith))

theorem six_perm (u a : Fin 3 → ℕ)
    (h : (u 0 = a 0 ∧ u 1 = a 1 ∧ u 2 = a 2) ∨ (u 0 = a 0 ∧ u 1 = a 2 ∧ u 2 = a 1) ∨
      (u 0 = a 1 ∧ u 1 = a 0 ∧ u 2 = a 2) ∨ (u 0 = a 1 ∧ u 1 = a 2 ∧ u 2 = a 0) ∨
      (u 0 = a 2 ∧ u 1 = a 0 ∧ u 2 = a 1) ∨ (u 0 = a 2 ∧ u 1 = a 1 ∧ u 2 = a 0)) :
    ∃ τ : Equiv.Perm (Fin 3), ∀ j, u j = a (τ j) := by
  have mk : ∀ r : Fin 3 → Fin 3, Function.Bijective r → (∀ j, u j = a (r j)) → ∃ τ : Equiv.Perm (Fin 3), ∀ j, u j = a (τ j) :=
    fun r hr hh => ⟨Equiv.ofBijective r hr, hh⟩
  rcases h with ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩
  · exact mk ![0, 1, 2] (by decide) (by intro j; fin_cases j <;> simp [h0, h1, h2])
  · exact mk ![0, 2, 1] (by decide) (by intro j; fin_cases j <;> simp [h0, h1, h2])
  · exact mk ![1, 0, 2] (by decide) (by intro j; fin_cases j <;> simp [h0, h1, h2])
  · exact mk ![1, 2, 0] (by decide) (by intro j; fin_cases j <;> simp [h0, h1, h2])
  · exact mk ![2, 0, 1] (by decide) (by intro j; fin_cases j <;> simp [h0, h1, h2])
  · exact mk ![2, 1, 0] (by decide) (by intro j; fin_cases j <;> simp [h0, h1, h2])

theorem sum_of_angles {n : ℕ} (hn : 0 < n) (T : Tri) (b : Fin 3 → ℕ) (hb : ∀ i, T.angleAt i = b i * Real.pi / n) :
    ∑ i, b i = n := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hs := T.angleAt_sum
  rw [hb 0, hb 1, hb 2] at hs
  have hnn : (n : ℝ) * (Real.pi / n) = Real.pi := by field_simp
  have key : (((b 0 + b 1 + b 2 : ℕ) : ℝ) - n) * (Real.pi / n) = 0 := by
    push_cast; linear_combination hs - hnn
  have := sub_eq_zero.mp ((mul_eq_zero.mp key).resolve_right (div_ne_zero Real.pi_ne_zero hn'))
  rw [Fin.sum_univ_three]; exact_mod_cast this

/-- **Laczkovich Theorem 5.1 for the tile `(alpha, beta, 2 alpha + beta)`, every denominator.** -/
theorem lacz51_all : Lacz51 := by
  intro N D α β a b c x y z hdata hα hβ hγ hns
  have hpi := Real.pi_pos
  obtain ⟨σ, h0, -, h1, -, h2, -⟩ := id hdata
  set vals : Fin 3 → ℝ := ![α, β, 2 * α + β] with hvals
  have hm : ∀ m, D.model.angleAt m = vals (σ.symm m) := by
    intro m
    obtain ⟨k, rfl⟩ := σ.surjective m
    rw [Equiv.symm_apply_apply]
    fin_cases k
    · simpa [hvals] using h0
    · simpa [hvals] using h1
    · simpa [hvals] using h2
  have hrel : 3 * α + 2 * β = Real.pi := by
    have hs := D.model.angleAt_sum
    rw [hm 0, hm 1, hm 2] at hs
    rcases perm_cases σ.symm with ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ |
      ⟨e0, e1, e2⟩ <;> rw [e0, e1, e2] at hs <;> simp [hvals] at hs <;> linarith
  have hq : ∀ w : ℚ, (w : ℝ) * Real.pi = Real.pi / 2 → w = 1 / 2 := by
    intro w hw
    have : (w : ℝ) = 1 / 2 := by
      apply mul_right_cancel₀ hpi.ne'
      rw [hw]; ring
    exact Rat.cast_injective (α := ℝ) (by push_cast; exact this)
  have hright : ∀ k, vals k = Real.pi / 2 → (x = 1 / 2 ∨ y = 1 / 2 ∨ z = 1 / 2) := by
    intro k hk
    fin_cases k
    · left; apply hq; rw [← hα]; simpa [hvals] using hk
    · right; left; apply hq; rw [← hβ]; simpa [hvals] using hk
    · right; right; apply hq; rw [← hγ]; simpa [hvals] using hk
  -- positivity and the rational relations
  have hαpos : 0 < α := h0 ▸ D.model.angleAt_pos' (σ 0)
  have hβpos : 0 < β := h1 ▸ D.model.angleAt_pos' (σ 1)
  have hxpos : 0 < x := by
    have : 0 < (x : ℝ) * Real.pi := hα ▸ hαpos
    exact_mod_cast pos_of_mul_pos_left this hpi.le
  have hypos : 0 < y := by
    have : 0 < (y : ℝ) * Real.pi := hβ ▸ hβpos
    exact_mod_cast pos_of_mul_pos_left this hpi.le
  have hzE : z = 2 * x + y := by
    have : (z : ℝ) * Real.pi = (2 * (x : ℝ) + y) * Real.pi := by rw [← hγ, hα, hβ]; ring
    have := mul_right_cancel₀ hpi.ne' this
    exact_mod_cast this
  have hxy : 3 * x + 2 * y = 1 := by
    have : (3 * (x : ℝ) + 2 * y) * Real.pi = 1 * Real.pi := by linear_combination hrel - 3 * hα - 2 * hβ
    have := mul_right_cancel₀ hpi.ne' this
    exact_mod_cast this
  have hzpos : 0 < z := by rw [hzE]; linarith
  obtain ⟨n, a0, a1, a2, hn, hsA, hg, hxe, hye, hze⟩ := common_denom hxpos hypos hzpos (by rw [hzE]; linarith)
  by_cases hcov : Covered n
  · exact lacz51_cov D x y z n a0 a1 a2 hn hcov hg hxe hye hze hdata hα hβ hγ hns
  -- uncovered denominators
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  have hr1 : 3 * a0 + 2 * a1 = n := by
    have : (3 * (a0 : ℚ) + 2 * a1) = n := by
      have e : 3 * ((a0 : ℚ) / n) + 2 * ((a1 : ℚ) / n) = 1 := by rw [← hxe, ← hye]; exact hxy
      field_simp at e; linarith
    exact_mod_cast this
  have hr2 : a2 = 2 * a0 + a1 := by
    have : (a2 : ℚ) = 2 * a0 + a1 := by
      have e : (a2 : ℚ) / n = 2 * ((a0 : ℚ) / n) + (a1 : ℚ) / n := by rw [← hxe, ← hye, ← hze]; exact hzE
      field_simp at e; linarith
    exact_mod_cast this
  set A : Fin 3 → ℕ := ![a0, a1, a2] with hA
  have hvq : ∀ k, vals k = (A k : ℕ) * Real.pi / n := by
    intro k
    fin_cases k
    · simp only [hvals, hA]; simp; rw [hα, hxe]; push_cast; ring
    · simp only [hvals, hA]; simp; rw [hβ, hye]; push_cast; ring
    · simp only [hvals, hA]; simp; rw [hγ, hze]; push_cast; ring
  set a' : Fin 3 → ℕ := fun m => A (σ.symm m) with ha'
  have ha : ∀ k, D.model.angleAt k = a' k * Real.pi / n := fun k => by rw [hm, hvq]
  have ha1 : ∀ k, 1 ≤ a' k := fun k => (nat_bounds hn (ha k) (angle_pos _ k) (angle_lt_pi _ k)).1
  have hsum' : ∑ k, a' k = n := sum_of_angles hn D.model a' ha
  have hd : ∀ d, (∀ i, d ∣ a' i) → d = 1 := by
    intro d hdd
    have h0' : d ∣ a0 := by simpa [ha', hA] using hdd (σ 0)
    have h1' : d ∣ a1 := by simpa [ha', hA] using hdd (σ 1)
    have h2' : d ∣ a2 := by simpa [ha', hA] using hdd (σ 2)
    have := Nat.dvd_gcd h0' (Nat.dvd_gcd h1' h2')
    rw [hg] at this; exact Nat.dvd_one.mp this
  obtain ⟨idx, hidx⟩ := KConj.exists_idx D a' ha
  obtain ⟨htarget, hK0⟩ := KConj.lemmaK D hn a' ha idx hidx
  set f := KConj.fig D idx with hf
  have hupos : ∀ j, 0 < LemmaKStar.uu a' f j := fun j =>
    (nat_bounds hn (htarget j) (angle_pos _ j) (angle_lt_pi _ j)).1
  have hfne : ∀ j, f j ≠ 0 := by
    intro j h0'
    have := hupos j
    simp [LemmaKStar.uu, h0'] at this
  have hu : ∑ j, LemmaKStar.uu a' f j = n := sum_of_angles hn D.target _ htarget
  have hn3 : 3 ≤ n := by rw [← hsum', Fin.sum_univ_three]; have := ha1 0; have := ha1 1; have := ha1 2; omega
  have hK := (LemmaKStar.lemmaKStar hn3 ha1 hsum' hfne hu).1.mp hK0
  have hr1' : 3 * a' (σ 0) + 2 * a' (σ 1) = n := by simpa [ha', hA] using hr1
  have hr2' : a' (σ 2) = 2 * a' (σ 0) + a' (σ 1) := by simpa [ha', hA] using hr2
  have tile : ∀ k, D.model.angleAt k = vals (σ.symm k) := hm
  rcases uncov_core ha1 hsum' hd σ hr1' hr2' hfne hu hK hcov with h6 | ⟨l, hl⟩
  · exfalso
    obtain ⟨τ, hτ⟩ := six_perm (fun j => LemmaKStar.uu a' f j) a' h6
    apply hns
    have e : ∀ k, D.target.angleAt k = vals ((τ.trans σ.symm) k) := fun k => by
      rw [htarget k, hτ k]
      simp only [Equiv.trans_apply]
      rw [← hm, ha]
    rw [e 0, e 1, e 2]
    simpa [hvals] using Lacz51Cov.triple3_perm vals (τ.trans σ.symm)
  · left
    apply hright (σ.symm l)
    rw [← hm, ha]
    have : (a' l : ℝ) = n / 2 := by
      have : (2 * a' l : ℝ) = n := by exact_mod_cast hl
      linarith
    rw [this]; field_simp

end Erdos634.Lacz51Gen2

#print axioms Erdos634.Lacz51Gen2.lacz51_all
