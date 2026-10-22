/-
Draft/CompositeS3Refined.lean — S3 (target (α,α,α+2β), tile with `ThreeAlphaData`) with `IsoQDvd N` replaced by the
weaker, equation-level hypothesis `IsoQRef N`: the reduced Row-11 equation `N d = m² (2e+d) Q`
(`Q = e²+4ed+2d²`, `gcd(e,e+d) = 1`) has no solution.  `IsoQDvd N` (every such Q | N equals N) is FALSE for
N = 14, 42, 62, 70 (Q = 7, 14 or 31 properly divides N), so the original leaf does not apply; the proper-Q cases
are killed here by the equation itself (N d = m² (2e+d) Q), proved by bounded check for N = 14, 42, 62, 70.
Proof of `excluded_isoQRef` is a copy of `Row11.excluded_isoQ` (Row11IsoQ.lean) with the last step replaced.
UNAUDITED.  Formalization debt, NOT /goal progress.  No sorry, no native_decide.
-/
import Erdos634.Draft.Row11IsoQ
import Erdos634.Draft.CompositeGen2

namespace Erdos634.Geometry

open Rows11_13AnyLabel

/-- The reduced Row-11 equation has no solution. -/
def IsoQRef (N : ℕ) : Prop :=
  ∀ e d m : ℕ, 1 ≤ e → 1 ≤ d → Nat.Coprime e (e + d) →
    N * d = m ^ 2 * ((2 * e + d) * (e ^ 2 + 4 * e * d + 2 * d ^ 2)) → False

/-- `IsoQRef N` from the divisibility-form: `Q ∣ N` (forced by `gcd(d,Q) = 1`) plus the equation has no solution. -/
theorem isoQRef_of_dvd_case (N : ℕ)
    (H : ∀ e d m : ℕ, 1 ≤ e → 1 ≤ d → e ^ 2 + 4 * e * d + 2 * d ^ 2 ∣ N →
      N * d = m ^ 2 * ((2 * e + d) * (e ^ 2 + 4 * e * d + 2 * d ^ 2)) → False) : IsoQRef N := by
  intro e d m he hd hcop heq
  set Q := e ^ 2 + 4 * e * d + 2 * d ^ 2 with hQdef
  have hged : Nat.gcd e (e + d) = 1 := hcop
  have hdQ : Nat.gcd d Q = 1 := by
    by_contra h
    obtain ⟨p, hp, hp1, hp2⟩ := Nat.Prime.not_coprime_iff_dvd.mp h
    have hQr : Q = d * (4 * e + 2 * d) + e ^ 2 := by rw [hQdef]; ring
    rw [hQr] at hp2
    have hpe2 : p ∣ e ^ 2 := (Nat.dvd_add_right (hp1.mul_right _)).mp hp2
    have hpe : p ∣ e := hp.dvd_of_dvd_pow hpe2
    have hped : p ∣ e + d := Nat.dvd_add hpe hp1
    have hg : p ∣ Nat.gcd e (e + d) := Nat.dvd_gcd hpe hped
    rw [hged, Nat.dvd_one] at hg
    exact hp.one_lt.ne' hg
  have hQNd : Q ∣ N * d := ⟨m ^ 2 * (2 * e + d), by rw [heq]; ring⟩
  have hQN : Q ∣ N := (Nat.Coprime.symm hdQ).dvd_of_dvd_mul_right hQNd
  exact H e d m he hd hQN heq

theorem Row11.excluded_isoQRef (D : CongruentDissection N) {α β a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hrel : 3 * α + 2 * β = Real.pi)
    (h : D.model.ThreeAlphaData α β a b c)
    (hP0 : D.target.angleAt 0 = α) (hP1 : D.target.angleAt 1 = α) (hN : IsoQRef N) : False := by
  obtain ⟨s, M, hs0, hs1, hc, ha, hb, hM1, hleg, harea⟩ := Row11.area D hα hrel h hP0 hP1
  obtain ⟨r, hr⟩ := Row11.rational D hα hrel h hP0 hP1
  have hsr : s = r := by
    have : c * (s - r) = 0 := by rw [ha] at hr; linear_combination hr
    linarith [(mul_eq_zero.mp this).resolve_left hc.ne']
  -- `s = e/f` in lowest terms, `f = e + d`, `e, d ≥ 1`
  have hr0 : 0 < r := by exact_mod_cast (hsr ▸ hs0 : (0 : ℝ) < r)
  obtain ⟨e, he⟩ : ∃ e : ℕ, r.num = e := ⟨r.num.toNat, (Int.toNat_of_nonneg (Rat.num_pos.mpr hr0).le).symm⟩
  obtain ⟨f, hfdef⟩ : ∃ f : ℕ, f = r.den := ⟨_, rfl⟩
  have hf0 : 0 < f := hfdef ▸ r.den_pos
  have hcop : Nat.Coprime e f := by
    have := r.reduced; rw [he, ← hfdef] at this; simpa using this
  have hsef : s = (e : ℝ) / f := by
    rw [hsr, ← Rat.num_div_den r, he, ← hfdef]
    push_cast <;> ring
  have hfR : (0 : ℝ) < f := by exact_mod_cast hf0
  have he1 : 1 ≤ e := by
    have : (0 : ℝ) < e := by
      have h1 := hs0; rw [hsef] at h1
      have h2 := mul_pos h1 hfR
      rwa [div_mul_cancel₀ _ hfR.ne'] at h2
    exact_mod_cast this
  have hef : e < f := by
    have : (e : ℝ) < f := by
      have := hs1; rw [hsef, div_lt_one hfR] at this; exact this
    exact_mod_cast this
  obtain ⟨d, hd⟩ : ∃ d, f = e + d := ⟨f - e, by omega⟩
  have hd1 : 1 ≤ d := by omega
  -- `M` natural
  obtain ⟨m', rfl⟩ := Int.eq_ofNat_of_zero_le (by linarith : (0 : ℤ) ≤ M)
  push_cast at hleg harea
  have hfd : (f : ℝ) = e + d := by rw [hd]; push_cast; ring
  -- the tiling equation over ℕ: `N·d·(3e+2d)² = m'²·(2e+d)·(e²+4ed+2d²)`
  have hNeq : N * d * (3 * e + 2 * d) ^ 2 = m' ^ 2 * ((2 * e + d) * (e ^ 2 + 4 * e * d + 2 * d ^ 2)) := by
    have hf' : (f : ℝ) ≠ 0 := hfR.ne'
    have key : (N : ℝ) * d * (3 * e + 2 * d) ^ 2 - (m' : ℝ) ^ 2 * ((2 * e + d) * (e ^ 2 + 4 * e * d + 2 * d ^ 2))
        = (f : ℝ) ^ 3 * ((N : ℝ) * (1 - s) * (2 + s) ^ 2 - (m' : ℝ) ^ 2 * (1 + s) * (2 - s ^ 2)) := by
      rw [hsef, hfd]
      have hed : (e : ℝ) + d ≠ 0 := by rw [← hfd]; exact hf'
      field_simp <;> ring
    rw [harea, sub_self, mul_zero, sub_eq_zero] at key
    exact_mod_cast key
  -- the leg word gives `X'·(2f+e) = m'·f²·(f+e)`
  obtain ⟨na, nb, nc, hw⟩ := D.side_word_threeAlpha h 0
  set X' : ℕ := na * (e * (e + d)) + nb * (d * (2 * e + d)) + nc * (e + d) ^ 2 with hX'def
  have hXeq : X' * (2 * (e + d) + e) = m' * ((e + d + e) * (e + d) ^ 2) := by
    have hf' : (f : ℝ) ≠ 0 := hfR.ne'
    have hX'R : (X' : ℝ) * c = D.target.oppLen 0 * (f : ℝ) ^ 2 := by
      rw [hw, ha, hb, hsef, hfd, hX'def]
      have hed : (e : ℝ) + d ≠ 0 := by rw [← hfd]; exact hf'
      push_cast
      field_simp <;> ring
    have hlegf : D.target.oppLen 0 * (2 * f + e) = m' * c * (f + e) := by
      have := hleg
      rw [hsef] at this
      field_simp at this
      linear_combination this
    have hc' : c ≠ 0 := hc.ne'
    have : c * ((X' : ℝ) * (2 * (e + d) + e) - m' * ((e + d + e) * (e + d) ^ 2)) = 0 := by
      rw [hfd] at hlegf hX'R
      linear_combination (2 * ((e : ℝ) + d) + e) * hX'R + ((e : ℝ) + d) ^ 2 * hlegf
    have h2 := sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hc')
    exact_mod_cast h2
  -- `(2f+e) ∣ M`
  have hcop' : Nat.Coprime e (e + d) := by rw [← hd]; exact hcop
  obtain ⟨m, hm⟩ := Erdos634.IsoAlpha.isoalpha_X_forces e (e + d) m' X' hcop' hXeq
  -- the reduced equation `N·d = m²·(2e+d)·(e²+4ed+2d²)`
  have hred : N * d = m ^ 2 * ((2 * e + d) * (e ^ 2 + 4 * e * d + 2 * d ^ 2)) := by
    rw [hm] at hNeq
    have h3 : 0 < (3 * e + 2 * d) ^ 2 := by positivity
    have e2 : 2 * (e + d) + e = 3 * e + 2 * d := by ring
    rw [e2] at hNeq
    have : (3 * e + 2 * d) ^ 2 * (N * d) = (3 * e + 2 * d) ^ 2 * (m ^ 2 * ((2 * e + d) * (e ^ 2 + 4 * e * d + 2 * d ^ 2))) := by
      calc (3 * e + 2 * d) ^ 2 * (N * d) = N * d * (3 * e + 2 * d) ^ 2 := by ring
        _ = ((3 * e + 2 * d) * m) ^ 2 * ((2 * e + d) * (e ^ 2 + 4 * e * d + 2 * d ^ 2)) := hNeq
        _ = _ := by ring
    exact Nat.eq_of_mul_eq_mul_left h3 this
  exact hN e d m he1 hd1 hcop' hred


theorem Row11.excluded_isoQRef_any_label {N : ℕ} (D : CongruentDissection N) {α β a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hrel : 3 * α + 2 * β = Real.pi)
    (h : D.model.ThreeAlphaData α β a b c) {t₀ t₁ : Fin 3} (ht : t₀ ≠ t₁)
    (hP0 : D.target.angleAt t₀ = α) (hP1 : D.target.angleAt t₁ = α) (hN : IsoQRef N) : False := by
  obtain ⟨σ, hm, h0, h1⟩ := transport D ht α hP0 hP1
  exact Row11.excluded_isoQRef (D.relabelTarget' σ) hα hrel (hm ▸ h) h0 h1 hN


end Erdos634.Geometry

#print axioms Erdos634.Geometry.isoQRef_of_dvd_case
#print axioms Erdos634.Geometry.Row11.excluded_isoQRef_any_label
