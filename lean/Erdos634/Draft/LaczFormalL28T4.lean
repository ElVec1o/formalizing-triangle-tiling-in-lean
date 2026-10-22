import Erdos634.Draft.LaczFormalL28Beeson
import Erdos634.Draft.LaczFormalL27Ang

/-!
# The fourth-triple triangle in the complementary range `N(a₀) < 0`: input `T4RSD` from Beeson's Theorem 24

NOTE, UNAUDITED.  Credit: Laczkovich (Discrete Math. 140 (1995) 79-94, Theorem 2.4, Fig. 5), Beeson (arXiv 1206.2229,
Theorem 24, Lemma 52), Beeson-Zhang, Zhang.

The fan constructions of `LaczFormalL27*` use the range condition `N(a₀) = a₀⁴ - (1-a₀²)³ > 0` only through the
dissection `T4RSD` of the chart triangle `T = L R P` (apex `P`, apex angle `α`, rational legs `R.c K/(1-a₀²)`).  For
`N(a₀) < 0` (which is `a⁴ < b³ c`, Beeson's hypothesis `a² c < b (a² + b²)` of Theorem 24) that dissection is
`ratsim_iso_beeson`.  `T4RSD_all` covers every `a₀ ∈ (0,1)` rational: `N(a₀) = 0` has no solution
(`N(a₀) = 0` is `u³ - 2u² + 3u - 1 = 0` for `u = a₀²`, no rational root; here it is excluded by Beeson's Lemma 52).
-/

namespace Erdos634.LaczL28

open Erdos634.Geometry Erdos634.CertCoord Erdos634.LaczL22 Erdos634.LaczL24 Erdos634.LaczL26 Erdos634.LaczL27
  Erdos634.DissectionMap Erdos634.Realizable EuclideanGeometry

theorem T4_eq0 {a : ℝ} (h : Hyp0 a) :
    (triT0 h).carrier = (hfan (sP a) (tP a) h.hK (show (0 : ℝ) ≠ sR a from (sR_pos0 h).ne)).carrier := by
  refine carrier_eq_of_range ?_
  rw [hfan_range]
  unfold triT0
  rw [mkTri_pts, range_mk3]
  ext z; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto

theorem T4RSD_of_neg (R : RTri) (a0 : ℚ) (ha0 : 0 < a0) (ha1 : a0 < 1)
    (hA : R.a = a0 * R.c) (hB : R.b = (1 - a0 ^ 2) * R.c) (hneg : a0 ^ 4 - (1 - a0 ^ 2) ^ 3 < 0) :
    T4RSD R a0 ha0 ha1 := by
  intro w d hdet hw hd hwd
  have h0 := hyp0_of_q a0 ha0 ha1
  unfold ChartRSD
  rw [← T4_eq0 h0, ← mapTri_carrier]
  obtain ⟨hiso, hap⟩ := T4_iso_apex R a0 ha0 ha1 hA hB w d hdet hw hd hwd
  have hrel : R.b * R.c = R.c ^ 2 - R.a ^ 2 := by rw [hA, hB]; ring
  have hlt : R.a ^ 4 < R.b ^ 3 * R.c := by
    have e : R.a ^ 4 - R.b ^ 3 * R.c = R.c ^ 4 * (a0 ^ 4 - (1 - a0 ^ 2) ^ 3) := by rw [hA, hB]; ring
    have : R.c ^ 4 * (a0 ^ 4 - (1 - a0 ^ 2) ^ 3) < 0 := mul_neg_of_pos_of_neg (by have := R.pc; positivity) hneg
    linarith
  have ha0r : (0 : ℝ) < a0 := by exact_mod_cast ha0
  have hb0q : (0 : ℚ) < 1 - a0 ^ 2 := by nlinarith
  have hb0r : (0 : ℝ) < 1 - (a0 : ℝ) ^ 2 := by exact_mod_cast hb0q
  have hcr : (0 : ℝ) < R.c := by exact_mod_cast R.pc
  have hupos : (0 : ℚ) < R.c / (a0 * (1 - a0 ^ 2)) := by have := R.pc; positivity
  set U : ℝ := (((R.c / (a0 * (1 - a0 ^ 2)) : ℚ) : ℝ)) with hUdef
  have hUpos : 0 < U := by rw [hUdef]; exact_mod_cast hupos
  have hKpos : 0 < gK (a0 : ℝ) := h0.hK
  have hwd' : inner ℝ w d = U ^ 2 * (2 - (a0 : ℝ) ^ 2) / 2 := hwd
  set ℓ : ℚ := R.c * (a0 ^ 2 + (1 - a0 ^ 2) ^ 2) / (1 - a0 ^ 2) with hℓdef
  have hℓ : 0 < ℓ := by have := R.pc; rw [hℓdef]; positivity
  have hKa : 0 ≤ U * gK (a0 : ℝ) * a0 := by positivity
  have hd1 : dist (chartEquiv 0 w d hdet (mkPt (sP (a0 : ℝ)) (tP (a0 : ℝ)))) (chartEquiv 0 w d hdet (mkPt 0 0))
      = U * gK (a0 : ℝ) * a0 := by
    refine chart_dist w d hdet (a0 : ℝ) U hw hd hwd' (sP (a0 : ℝ)) (tP (a0 : ℝ)) 0 0 _ hKa ?_
    unfold Erdos634.LaczL27.Qf sP tP gb gK; ring
  have hval : U * gK (a0 : ℝ) * a0 = (ℓ : ℝ) := by
    rw [hUdef, hℓdef]
    unfold gK
    push_cast
    have : (a0 : ℝ) ≠ 0 := ha0r.ne'
    have : (1 - (a0 : ℝ) ^ 2) ≠ 0 := hb0r.ne'
    field_simp
  exact ratsim_iso_beeson R hrel hlt (mapTri (chartEquiv 0 w d hdet) (triT0 h0)) hiso hap ℓ hℓ (by
    show dist (chartEquiv 0 w d hdet (mkPt (sP (a0 : ℝ)) (tP (a0 : ℝ)))) (chartEquiv 0 w d hdet (mkPt 0 0)) = _
    rw [hd1, hval])

/-- `N(a₀) ≠ 0` for rational `a₀ ∈ (0,1)`: with `x = 1 - a₀² = b/c` it is `c (c - b)² = b³`, which has no solution
(Beeson's Lemma 52, `no_rational_root`). -/
theorem N_ne_zero (a0 : ℚ) (ha0 : 0 < a0) (ha1 : a0 < 1) : a0 ^ 4 - (1 - a0 ^ 2) ^ 3 ≠ 0 := by
  intro hz
  have hx0 : 0 < 1 - a0 ^ 2 := by nlinarith
  have hx1 : 1 - a0 ^ 2 < 1 := by nlinarith
  have h1 : a0 ^ 4 = (1 - (1 - a0 ^ 2)) ^ 2 := by ring
  generalize hx : 1 - a0 ^ 2 = x at hx0 hx1 h1 hz
  rw [h1] at hz
  have hnum : 0 < x.num := Rat.num_pos.mpr hx0
  obtain ⟨b, hb⟩ : ∃ b : ℕ, x.num = b := ⟨x.num.toNat, (Int.toNat_of_nonneg hnum.le).symm⟩
  have hcpos : 0 < x.den := x.den_pos
  have hxe : x = (b : ℚ) / (x.den : ℚ) := by
    have := (Rat.num_div_den x).symm
    rw [hb] at this
    simpa using this
  have hbpos : 0 < b := by
    have : (0 : ℤ) < (b : ℤ) := hb ▸ hnum
    exact_mod_cast this
  have hcQ : (0 : ℚ) < (x.den : ℚ) := by exact_mod_cast hcpos
  have hbc : b < x.den := by
    have : (b : ℚ) / (x.den : ℚ) < 1 := hxe ▸ hx1
    rw [div_lt_one hcQ] at this
    exact_mod_cast this
  apply Erdos634.BeesonLemma52.no_rational_root b x.den hbpos hbc
  have e : (x.den : ℚ) * ((x.den : ℚ) - b) ^ 2 - (b : ℚ) ^ 3
      = (x.den : ℚ) ^ 3 * ((1 - (b : ℚ) / (x.den : ℚ)) ^ 2 - ((b : ℚ) / (x.den : ℚ)) ^ 3) := by
    field_simp
  rw [← hxe] at e
  rw [hz, mul_zero] at e
  have e2 : ((x.den * (x.den - b) ^ 2 : ℕ) : ℚ) = ((b ^ 3 : ℕ) : ℚ) := by
    push_cast [Nat.cast_sub hbc.le]
    linarith
  exact_mod_cast e2

/-- `T4RSD` for every rational `a₀ ∈ (0,1)` of a tile `R` with `R.a = a₀ R.c`, `R.b = (1-a₀²) R.c`
(Laczkovich's `N(a₀) > 0` range via `fourth_chart`; the complementary range via Beeson's Theorem 24). -/
theorem T4RSD_all (R : RTri) (a0 : ℚ) (ha0 : 0 < a0) (ha1 : a0 < 1)
    (hA : R.a = a0 * R.c) (hB : R.b = (1 - a0 ^ 2) * R.c) : T4RSD R a0 ha0 ha1 := by
  rcases lt_trichotomy (a0 ^ 4 - (1 - a0 ^ 2) ^ 3) 0 with hneg | hzero | hpos
  · exact T4RSD_of_neg R a0 ha0 ha1 hA hB hneg
  · exact absurd hzero (N_ne_zero a0 ha0 ha1)
  · exact T4RSD_of_N R a0 ha0 ha1 hA hB hpos

end Erdos634.LaczL28
