import Erdos634.Draft.LaczFormalL28T4
import Erdos634.Draft.LaczFormalL27Any

/-!
# Laczkovich Theorem 2.4: triples 2, 3, 4, 5 for EVERY rational `a₀ ∈ (0,1)` (both ranges of `N(a₀)`)

NOTE, UNAUDITED.  Credit: Laczkovich (Discrete Math. 140 (1995) 79-94, Theorem 2.4, Fig. 5), Beeson (arXiv 1206.2229,
Theorem 24, Lemma 52), Beeson-Zhang, Zhang.

Complementary range `N(a₀) = a₀⁴ - (1-a₀²)³ < 0`: the picture-1 triangle of each fan construction is dissected by Beeson's
Theorem 24 (`LaczFormalL28Beeson.ratsim_iso_beeson`, via `T4RSD_of_neg`), after the rational rescaling of the tile that the
`RatSimDiss`/Lemma 2.1 (`toCongruent`) vocabulary absorbs: all pieces are rational similar copies of `Δ`, and Lemma 2.1 then
produces congruent tiles.  `N(a₀) = 0` never occurs (`N_ne_zero`).  Printed gap: the paper says only "Similar constructions
apply for the other triples listed in (1); see Fig. 5"; the picture-1 triangle has apex `α` and is the fourth triple
(`thm24_fourth_all`).
-/

namespace Erdos634.LaczL28

open Erdos634.Geometry Erdos634.CertCoord Erdos634.LaczL22 Erdos634.LaczL24 Erdos634.LaczL26 Erdos634.LaczL27
  Erdos634.DissectionMap Erdos634.Realizable Erdos634.LaczTransport EuclideanGeometry

section all

variable (R : RTri) (a0 : ℚ) (ha0 : 0 < a0) (ha1 : a0 < 1)
  (hA : R.a = a0 * R.c) (hB : R.b = (1 - a0 ^ 2) * R.c)

include ha0 ha1 hA hB

/-- **Laczkovich Theorem 2.4, FOURTH triple `(α, α+β, α+β)`, every `a₀`.**  The chart triangle `L R P`. -/
theorem thm24_fourth_all :
    ∃ (T : Tri) (q : ℕ) (hq : 0 < q) (M : ℕ)
      (C : Erdos634.RegionDissection.CongruentRegionDissection M),
      C.region = T.carrier ∧
      C.model = scaleTri (1 / (q : ℝ)) (one_div_pos.mpr (Nat.cast_pos.mpr hq)).ne' R.Δ ∧
      dist (T.pts 2) (T.pts 0) = dist (T.pts 2) (T.pts 1) ∧
      cornerAngle (T.pts 0) (T.pts 2) (T.pts 1)
        = cornerAngle (R.Δ.pts 1) (R.Δ.pts 0) (R.Δ.pts 2) := by
  obtain ⟨w1, d1, hdet, hw, hd, hwd⟩ := std_chart_exists R a0 ha0 ha1
  have h0 := hyp0_of_q a0 ha0 ha1
  have key := T4RSD_all R a0 ha0 ha1 hA hB w1 d1 hdet hw hd hwd
  unfold ChartRSD at key
  rw [← T4_eq0 h0, ← mapTri_carrier] at key
  obtain ⟨q, hq, M, C, hC1, hC2⟩ := RatSimDiss.toCongruent R.rational key
  obtain ⟨hiso, hap⟩ := T4_iso_apex R a0 ha0 ha1 hA hB w1 d1 hdet hw hd hwd
  exact ⟨mapTri (chartEquiv 0 w1 d1 hdet) (triT0 h0), q, hq, M, C, hC1, hC2, hiso, hap⟩

/-- **Theorem 2.4, fourth triple, every `a₀`, for every triangle isosceles at `T'₂` with apex angle `α`.** -/
theorem thm24_fourth_any_all (T' : Tri) (hiso : dist (T'.pts 2) (T'.pts 0) = dist (T'.pts 2) (T'.pts 1))
    (hang : cornerAngle (T'.pts 0) (T'.pts 2) (T'.pts 1)
      = cornerAngle (R.Δ.pts 1) (R.Δ.pts 0) (R.Δ.pts 2)) :
    ∃ (s : ℝ) (hs : 0 < s) (M : ℕ) (D' : CongruentDissection M),
      D'.target.carrier = T'.carrier ∧ D'.model.Congruent (scaleTri s hs.ne' R.Δ) := by
  obtain ⟨T, q, hq, M, C, hC1, hC2, hiso0, hang0⟩ := thm24_fourth_all R a0 ha0 ha1 hA hB
  have hT := base_angle T hiso0
  have hT' := base_angle T' hiso
  obtain ⟨s, hs, D', e1, e2⟩ := transport_region R.Δ T q hq M C hC1 hC2 T' 0 2 1 (by decide) (by decide)
    (by decide) (hang0.trans hang.symm)
    (by
      have : ∠ (T.pts 2) (T.pts 1) (T.pts 0) = ∠ (T'.pts 2) (T'.pts 1) (T'.pts 0) := by
        have h1 : cornerAngle (T.pts 0) (T.pts 2) (T.pts 1)
          = cornerAngle (T'.pts 0) (T'.pts 2) (T'.pts 1) := hang0.trans hang.symm
        unfold cornerAngle at h1
        linarith
      exact this)
  exact ⟨s, hs, M, D', e1, e2⟩

theorem thm24_fifth_all :
    ∃ (T : Tri) (q : ℕ) (hq : 0 < q) (M : ℕ) (C : Erdos634.RegionDissection.CongruentRegionDissection M),
      C.region = T.carrier ∧
      C.model = scaleTri (1 / (q : ℝ)) (one_div_pos.mpr (Nat.cast_pos.mpr hq)).ne' R.Δ ∧
      ∠ (T.pts 0) (T.pts 1) (T.pts 2) = ∠ (R.Δ.pts 0) (R.Δ.pts 1) (R.Δ.pts 2) ∧
      ∠ (T.pts 1) (T.pts 2) (T.pts 0)
        = ∠ (R.Δ.pts 1) (R.Δ.pts 0) (R.Δ.pts 2) + ∠ (R.Δ.pts 0) (R.Δ.pts 1) (R.Δ.pts 2) := thm24_fifth_gen R a0 ha0 ha1 hA hB (T4RSD_all R a0 ha0 ha1 hA hB)

theorem thm24_second_all :
    ∃ (T : Tri) (q : ℕ) (hq : 0 < q) (M : ℕ) (C : Erdos634.RegionDissection.CongruentRegionDissection M),
      C.region = T.carrier ∧
      C.model = scaleTri (1 / (q : ℝ)) (one_div_pos.mpr (Nat.cast_pos.mpr hq)).ne' R.Δ ∧
      ∠ (T.pts 0) (T.pts 1) (T.pts 2) = ∠ (R.Δ.pts 0) (R.Δ.pts 1) (R.Δ.pts 2) ∧
      ∠ (T.pts 1) (T.pts 2) (T.pts 0) = ∠ (R.Δ.pts 0) (R.Δ.pts 1) (R.Δ.pts 2) := thm24_second_gen R a0 ha0 ha1 hA hB (T4RSD_all R a0 ha0 ha1 hA hB)

theorem thm24_third_all :
    ∃ (T : Tri) (q : ℕ) (hq : 0 < q) (M : ℕ) (C : Erdos634.RegionDissection.CongruentRegionDissection M),
      C.region = T.carrier ∧
      C.model = scaleTri (1 / (q : ℝ)) (one_div_pos.mpr (Nat.cast_pos.mpr hq)).ne' R.Δ ∧
      ∠ (T.pts 0) (T.pts 1) (T.pts 2)
        = ∠ (R.Δ.pts 1) (R.Δ.pts 0) (R.Δ.pts 2) + ∠ (R.Δ.pts 1) (R.Δ.pts 0) (R.Δ.pts 2) ∧
      ∠ (T.pts 1) (T.pts 2) (T.pts 0) = ∠ (R.Δ.pts 1) (R.Δ.pts 0) (R.Δ.pts 2) := thm24_third_gen R a0 ha0 ha1 hA hB (T4RSD_all R a0 ha0 ha1 hA hB)

theorem thm24_fifth_any_all (T' : Tri)
    (h1 : ∠ (T'.pts 0) (T'.pts 1) (T'.pts 2) = ∠ (R.Δ.pts 0) (R.Δ.pts 1) (R.Δ.pts 2))
    (h2 : ∠ (T'.pts 1) (T'.pts 2) (T'.pts 0)
      = ∠ (R.Δ.pts 1) (R.Δ.pts 0) (R.Δ.pts 2) + ∠ (R.Δ.pts 0) (R.Δ.pts 1) (R.Δ.pts 2)) :
    ∃ (s : ℝ) (hs : 0 < s) (M : ℕ) (D' : CongruentDissection M),
      D'.target.carrier = T'.carrier ∧ D'.model.Congruent (scaleTri s hs.ne' R.Δ) := thm24_fifth_any_gen R a0 ha0 ha1 hA hB (T4RSD_all R a0 ha0 ha1 hA hB) T' h1 h2

theorem thm24_second_any_all (T' : Tri)
    (h1 : ∠ (T'.pts 0) (T'.pts 1) (T'.pts 2) = ∠ (R.Δ.pts 0) (R.Δ.pts 1) (R.Δ.pts 2))
    (h2 : ∠ (T'.pts 1) (T'.pts 2) (T'.pts 0) = ∠ (R.Δ.pts 0) (R.Δ.pts 1) (R.Δ.pts 2)) :
    ∃ (s : ℝ) (hs : 0 < s) (M : ℕ) (D' : CongruentDissection M),
      D'.target.carrier = T'.carrier ∧ D'.model.Congruent (scaleTri s hs.ne' R.Δ) := thm24_second_any_gen R a0 ha0 ha1 hA hB (T4RSD_all R a0 ha0 ha1 hA hB) T' h1 h2

theorem thm24_third_any_all (T' : Tri)
    (h1 : ∠ (T'.pts 0) (T'.pts 1) (T'.pts 2)
      = ∠ (R.Δ.pts 1) (R.Δ.pts 0) (R.Δ.pts 2) + ∠ (R.Δ.pts 1) (R.Δ.pts 0) (R.Δ.pts 2))
    (h2 : ∠ (T'.pts 1) (T'.pts 2) (T'.pts 0) = ∠ (R.Δ.pts 1) (R.Δ.pts 0) (R.Δ.pts 2)) :
    ∃ (s : ℝ) (hs : 0 < s) (M : ℕ) (D' : CongruentDissection M),
      D'.target.carrier = T'.carrier ∧ D'.model.Congruent (scaleTri s hs.ne' R.Δ) := thm24_third_any_gen R a0 ha0 ha1 hA hB (T4RSD_all R a0 ha0 ha1 hA hB) T' h1 h2

/-- `T'` is the union of finitely many congruent triangles similar to `Δ` (tile scale `s > 0`). -/
def Dissectable (R : RTri) (T' : Tri) : Prop :=
  ∃ (s : ℝ) (hs : 0 < s) (M : ℕ) (D' : CongruentDissection M),
    D'.target.carrier = T'.carrier ∧ D'.model.Congruent (scaleTri s hs.ne' R.Δ)

/-- **Laczkovich Theorem 2.4 (all five triples of (1)), every rational tile with `sin(α/2)` rational.**  `R` is the tile
`(α, β, γ)` of sides `(a₀ c, (1-a₀²) c, c)`, `0 < a₀ = 2 sin(α/2) < 1` rational (`3α + 2β = π`).  A triangle `T'` with angles
(a) `(α, α, π-2α)` [apex `T'₁`], (b) `(α, α+β, α+β)` [apex `T'₂`], (c) `(β, β, 3α)`, (d) `(α, 2α, 2β)`, (e) `(β, 2α, α+β)`
is `Dissectable`.  Both ranges `N(a₀) > 0`, `N(a₀) < 0` (`N(a₀) = 0` does not occur). -/
theorem thm24_all_triples :
    (∀ T' : Tri, dist (T'.pts 1) (T'.pts 0) = dist (T'.pts 1) (T'.pts 2) →
      cornerAngle (T'.pts 1) (T'.pts 0) (T'.pts 2) = cornerAngle (R.Δ.pts 1) (R.Δ.pts 0) (R.Δ.pts 2) →
      Dissectable R T') ∧
    (∀ T' : Tri, dist (T'.pts 2) (T'.pts 0) = dist (T'.pts 2) (T'.pts 1) →
      cornerAngle (T'.pts 0) (T'.pts 2) (T'.pts 1) = cornerAngle (R.Δ.pts 1) (R.Δ.pts 0) (R.Δ.pts 2) →
      Dissectable R T') ∧
    (∀ T' : Tri, ∠ (T'.pts 0) (T'.pts 1) (T'.pts 2) = ∠ (R.Δ.pts 0) (R.Δ.pts 1) (R.Δ.pts 2) →
      ∠ (T'.pts 1) (T'.pts 2) (T'.pts 0) = ∠ (R.Δ.pts 0) (R.Δ.pts 1) (R.Δ.pts 2) → Dissectable R T') ∧
    (∀ T' : Tri, ∠ (T'.pts 0) (T'.pts 1) (T'.pts 2)
        = ∠ (R.Δ.pts 1) (R.Δ.pts 0) (R.Δ.pts 2) + ∠ (R.Δ.pts 1) (R.Δ.pts 0) (R.Δ.pts 2) →
      ∠ (T'.pts 1) (T'.pts 2) (T'.pts 0) = ∠ (R.Δ.pts 1) (R.Δ.pts 0) (R.Δ.pts 2) → Dissectable R T') ∧
    (∀ T' : Tri, ∠ (T'.pts 0) (T'.pts 1) (T'.pts 2) = ∠ (R.Δ.pts 0) (R.Δ.pts 1) (R.Δ.pts 2) →
      ∠ (T'.pts 1) (T'.pts 2) (T'.pts 0)
        = ∠ (R.Δ.pts 1) (R.Δ.pts 0) (R.Δ.pts 2) + ∠ (R.Δ.pts 0) (R.Δ.pts 1) (R.Δ.pts 2) → Dissectable R T') :=
  ⟨fun T' h1 h2 => Erdos634.LaczTransport.thm24_first_any R a0 ha0 ha1 hA hB T' h1 h2,
   fun T' h1 h2 => thm24_fourth_any_all R a0 ha0 ha1 hA hB T' h1 h2,
   fun T' h1 h2 => thm24_second_any_all R a0 ha0 ha1 hA hB T' h1 h2,
   fun T' h1 h2 => thm24_third_any_all R a0 ha0 ha1 hA hB T' h1 h2,
   fun T' h1 h2 => thm24_fifth_any_all R a0 ha0 ha1 hA hB T' h1 h2⟩

end all

/-! ### Witnesses in the NEW range `N(a₀) < 0`: tile `(2, 3, 4)`, `a₀ = 1/2`, `N(1/2) = 1/16 - 27/64 < 0`. -/

theorem R234_hyp : R234.a = (1 / 2 : ℚ) * R234.c ∧ R234.b = (1 - (1 / 2 : ℚ) ^ 2) * R234.c ∧
    (1 / 2 : ℚ) ^ 4 - (1 - (1 / 2 : ℚ) ^ 2) ^ 3 < 0 := by
  refine ⟨by simp [R234]; norm_num, by simp [R234]; norm_num, by norm_num⟩

theorem wit_fifth_234 :
    ∃ T' : Tri, ∠ (T'.pts 0) (T'.pts 1) (T'.pts 2) = ∠ (R234.Δ.pts 0) (R234.Δ.pts 1) (R234.Δ.pts 2) ∧
      ∠ (T'.pts 1) (T'.pts 2) (T'.pts 0)
        = ∠ (R234.Δ.pts 1) (R234.Δ.pts 0) (R234.Δ.pts 2) + ∠ (R234.Δ.pts 0) (R234.Δ.pts 1) (R234.Δ.pts 2) ∧
      Dissectable R234 T' := by
  obtain ⟨hA, hB, -⟩ := R234_hyp
  obtain ⟨T, q, hq, M, C, hC1, hC2, g1, g2⟩ := thm24_fifth_all R234 (1 / 2) (by norm_num) (by norm_num) hA hB
  exact ⟨T, g1, g2, thm24_fifth_any_all R234 (1 / 2) (by norm_num) (by norm_num) hA hB T g1 g2⟩

theorem wit_second_234 :
    ∃ T' : Tri, ∠ (T'.pts 0) (T'.pts 1) (T'.pts 2) = ∠ (R234.Δ.pts 0) (R234.Δ.pts 1) (R234.Δ.pts 2) ∧
      ∠ (T'.pts 1) (T'.pts 2) (T'.pts 0) = ∠ (R234.Δ.pts 0) (R234.Δ.pts 1) (R234.Δ.pts 2) ∧
      Dissectable R234 T' := by
  obtain ⟨hA, hB, -⟩ := R234_hyp
  obtain ⟨T, q, hq, M, C, hC1, hC2, g1, g2⟩ := thm24_second_all R234 (1 / 2) (by norm_num) (by norm_num) hA hB
  exact ⟨T, g1, g2, thm24_second_any_all R234 (1 / 2) (by norm_num) (by norm_num) hA hB T g1 g2⟩

theorem wit_third_234 :
    ∃ T' : Tri, ∠ (T'.pts 0) (T'.pts 1) (T'.pts 2)
        = ∠ (R234.Δ.pts 1) (R234.Δ.pts 0) (R234.Δ.pts 2) + ∠ (R234.Δ.pts 1) (R234.Δ.pts 0) (R234.Δ.pts 2) ∧
      ∠ (T'.pts 1) (T'.pts 2) (T'.pts 0) = ∠ (R234.Δ.pts 1) (R234.Δ.pts 0) (R234.Δ.pts 2) ∧
      Dissectable R234 T' := by
  obtain ⟨hA, hB, -⟩ := R234_hyp
  obtain ⟨T, q, hq, M, C, hC1, hC2, g1, g2⟩ := thm24_third_all R234 (1 / 2) (by norm_num) (by norm_num) hA hB
  exact ⟨T, g1, g2, thm24_third_any_all R234 (1 / 2) (by norm_num) (by norm_num) hA hB T g1 g2⟩

theorem wit_fourth_234 :
    ∃ T' : Tri, dist (T'.pts 2) (T'.pts 0) = dist (T'.pts 2) (T'.pts 1) ∧
      cornerAngle (T'.pts 0) (T'.pts 2) (T'.pts 1)
        = cornerAngle (R234.Δ.pts 1) (R234.Δ.pts 0) (R234.Δ.pts 2) ∧ Dissectable R234 T' := by
  obtain ⟨hA, hB, -⟩ := R234_hyp
  obtain ⟨T, q, hq, M, C, hC1, hC2, g1, g2⟩ := thm24_fourth_all R234 (1 / 2) (by norm_num) (by norm_num) hA hB
  exact ⟨T, g1, g2, thm24_fourth_any_all R234 (1 / 2) (by norm_num) (by norm_num) hA hB T g1 g2⟩

#print axioms thm24_fourth_all
#print axioms thm24_fifth_all
#print axioms thm24_second_all
#print axioms thm24_third_all
#print axioms thm24_all_triples
#print axioms wit_fifth_234
#print axioms wit_second_234
#print axioms wit_third_234
#print axioms wit_fourth_234

end Erdos634.LaczL28
