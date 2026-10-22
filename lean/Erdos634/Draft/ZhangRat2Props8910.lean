import Erdos634.Draft.ZhangRat

/-!
# Zhang Props 8, 9, 10 for rational tiles and EVERY admissible `m`

`ZhangRat.zhang_prop{8,9,10}_{1,2}_rational` fix `m = 3 M0` (the least `m` of Thm 4).  Here `m` is
universally quantified: for every natural `m > 0` for which `EquiConstr A B (m A B) (m^2 A B)` holds
(Zhang's hypothesis in the integer statements; by `ZhangThm4.zhang_thm4` this includes every
`m >= 3 M0`, see `equi_data_all`), the dilated triangle carries the stated number of model tiles.
UNAUDITED.  Credit Zhang (arXiv 2512.22696), Beeson, Beeson-Zhang, Laczkovich.
-/

namespace Erdos634.ZhangRat2

open Erdos634.Geometry Erdos634.CertCoord Erdos634.CertGeom Erdos634.RegionDissection
  Erdos634.SssCongruent Erdos634.ZhangL1 Erdos634.ZhangPara Erdos634.ZhangThm4
  Erdos634.LaczL22 Erdos634.ZhangPi3 Erdos634.Realizable Erdos634.BeesonCor5 Erdos634.ZhangRational
  Erdos634.ZhangSporadic Erdos634.ZhangRat

/-- every `m >= 3 M0` is admissible (Zhang Thm 4), so the `m`-free statements below are not vacuous. -/
theorem equi_data_all (A B C : ℕ) (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (hh : C * C = A * A + B * B + A * B) (hcop : Nat.Coprime A B) :
    ∃ M : ℕ, 0 < M ∧ ∀ m : ℕ, M ≤ m →
      EquiConstr A B hA hB ((m : ℝ) * ((A : ℝ) * B)) (m * m * (A * B)) := by
  refine ⟨3 * ((C * C - A - B) / (A * B) + 1), by positivity, fun m hm => ?_⟩
  exact zhang_thm4 A B C hA hB hC hh hcop m hm

section p8
variable (R : RTri) (hrel : R.c ^ 2 = R.a ^ 2 + R.b ^ 2 + R.a * R.b)
include hrel

theorem zhang_prop9_1_rational_all :
    ∃ (A B : ℕ) (k : ℚ) (hA : 0 < A) (hB : 0 < B), 0 < k ∧ R.a = k * A ∧ R.b = k * B ∧
      ∀ (m : ℕ) (hm : 0 < m)
        (hE : EquiConstr A B hA hB ((m : ℝ) * ((A : ℝ) * B)) (m * m * (A * B))),
      ∃ C1 : CongruentRegionDissection (m * m * (B * (A + B))),
        C1.region = dil (k : ℝ) (TriSet (((m : ℝ) * ((A : ℝ) * B)) / 2)
          (((m : ℝ) * ((A : ℝ) * B)) * zs / 2) (-((m : ℝ) * B * B)) 0 ((m : ℝ) * ((A : ℝ) * B)) 0) ∧
        C1.model.Congruent R.Δ := by
  obtain ⟨A, B, C, k, hk, hA, hB, hC, hh, hcop, ea, eb, ec⟩ := rat_data R hrel
  exact ⟨A, B, k, hA, hB, hk, ea, eb, fun m hm hE =>
    rat_dis R A B C k hk hA hB hh ea eb ec (zhang_prop9_1 A B m hA hB hm hE)⟩

theorem zhang_prop9_2_rational_all :
    ∃ (A B : ℕ) (k : ℚ) (hA : 0 < A) (hB : 0 < B), 0 < k ∧ R.a = k * A ∧ R.b = k * B ∧
      ∀ (m : ℕ) (hm : 0 < m)
        (hE : EquiConstr A B hA hB ((m : ℝ) * ((A : ℝ) * B)) (m * m * (A * B))),
      ∃ C1 : CongruentRegionDissection (m * m * (A * (A + B))),
        C1.region = dil (k : ℝ) (TriSet (((m : ℝ) * ((A : ℝ) * B)) / 2)
          (((m : ℝ) * ((A : ℝ) * B)) * zs / 2) (-((m : ℝ) * A * A)) 0 ((m : ℝ) * ((A : ℝ) * B)) 0) ∧
        C1.model.Congruent R.Δ := by
  obtain ⟨A, B, C, k, hk, hA, hB, hC, hh, hcop, ea, eb, ec⟩ := rat_data R hrel
  exact ⟨A, B, k, hA, hB, hk, ea, eb, fun m hm hE =>
    rat_dis R A B C k hk hA hB hh ea eb ec (zhang_prop9_2 A B m hA hB hm hE)⟩

theorem zhang_prop8_1_rational_all :
    ∃ (A B : ℕ) (k : ℚ) (hA : 0 < A) (hB : 0 < B), 0 < k ∧ R.a = k * A ∧ R.b = k * B ∧
      ∀ (m : ℕ) (hm : 0 < m)
        (hE : EquiConstr A B hA hB ((m : ℝ) * ((A : ℝ) * B)) (m * m * (A * B))),
      ∃ C1 : CongruentRegionDissection (m * m * (B * (A + 2 * B))),
        C1.region = dil (k : ℝ) (TriSet (((m : ℝ) * ((A : ℝ) * B)) / 2)
          (((m : ℝ) * ((A : ℝ) * B)) * zs / 2) (-((m : ℝ) * B * B)) 0
          (((m : ℝ) * ((A : ℝ) * B)) + (m : ℝ) * B * B) 0) ∧
        C1.model.Congruent R.Δ := by
  obtain ⟨A, B, C, k, hk, hA, hB, hC, hh, hcop, ea, eb, ec⟩ := rat_data R hrel
  exact ⟨A, B, k, hA, hB, hk, ea, eb, fun m hm hE =>
    rat_dis R A B C k hk hA hB hh ea eb ec (zhang_prop8_1 A B m hA hB hm hE)⟩

theorem zhang_prop8_2_rational_all :
    ∃ (A B : ℕ) (k : ℚ) (hA : 0 < A) (hB : 0 < B), 0 < k ∧ R.a = k * A ∧ R.b = k * B ∧
      ∀ (m : ℕ) (hm : 0 < m)
        (hE : EquiConstr A B hA hB ((m : ℝ) * ((A : ℝ) * B)) (m * m * (A * B))),
      ∃ C1 : CongruentRegionDissection (m * m * (A * (B + 2 * A))),
        C1.region = dil (k : ℝ) (TriSet (((m : ℝ) * ((A : ℝ) * B)) / 2)
          (((m : ℝ) * ((A : ℝ) * B)) * zs / 2) (-((m : ℝ) * A * A)) 0
          (((m : ℝ) * ((A : ℝ) * B)) + (m : ℝ) * A * A) 0) ∧
        C1.model.Congruent R.Δ := by
  obtain ⟨A, B, C, k, hk, hA, hB, hC, hh, hcop, ea, eb, ec⟩ := rat_data R hrel
  exact ⟨A, B, k, hA, hB, hk, ea, eb, fun m hm hE =>
    rat_dis R A B C k hk hA hB hh ea eb ec (zhang_prop8_2 A B m hA hB hm hE)⟩

theorem zhang_prop10_1_rational_all :
    ∃ (A B : ℕ) (k : ℚ) (hA : 0 < A) (hB : 0 < B), 0 < k ∧ R.a = k * A ∧ R.b = k * B ∧
      ∀ (m : ℕ) (hm : 0 < m)
        (hE : EquiConstr A B hA hB ((m : ℝ) * ((A : ℝ) * B)) (m * m * (A * B))),
      ∃ C1 : CongruentRegionDissection (m * m * ((A + B) * (2 * A + B))),
        C1.region = dil (k : ℝ) (TriSet (-((m : ℝ) * A * A)) 0
          (((m : ℝ) * ((A : ℝ) * B)) + (m : ℝ) * (A + B) * B / 2)
          (-((m : ℝ) * (A + B) * B * zs / 2))
          (((m : ℝ) * ((A : ℝ) * B)) / 2) (((m : ℝ) * ((A : ℝ) * B)) * zs / 2)) ∧
        C1.model.Congruent R.Δ := by
  obtain ⟨A, B, C, k, hk, hA, hB, hC, hh, hcop, ea, eb, ec⟩ := rat_data R hrel
  exact ⟨A, B, k, hA, hB, hk, ea, eb, fun m hm hE =>
    rat_dis R A B C k hk hA hB hh ea eb ec (zhang_prop10_1 A B m hA hB hm hE)⟩

theorem zhang_prop10_2_rational_all :
    ∃ (A B : ℕ) (k : ℚ) (hA : 0 < A) (hB : 0 < B), 0 < k ∧ R.a = k * A ∧ R.b = k * B ∧
      ∀ (m : ℕ) (hm : 0 < m)
        (hE : EquiConstr A B hA hB ((m : ℝ) * ((A : ℝ) * B)) (m * m * (A * B))),
      ∃ C1 : CongruentRegionDissection (m * m * ((A + B) * (A + 2 * B))),
        C1.region = dil (k : ℝ) (TriSet (-((m : ℝ) * B * B)) 0
          (((m : ℝ) * ((A : ℝ) * B)) + (m : ℝ) * (A + B) * A / 2)
          (-((m : ℝ) * (A + B) * A * zs / 2))
          (((m : ℝ) * ((A : ℝ) * B)) / 2) (((m : ℝ) * ((A : ℝ) * B)) * zs / 2)) ∧
        C1.model.Congruent R.Δ := by
  obtain ⟨A, B, C, k, hk, hA, hB, hC, hh, hcop, ea, eb, ec⟩ := rat_data R hrel
  exact ⟨A, B, k, hA, hB, hk, ea, eb, fun m hm hE =>
    rat_dis R A B C k hk hA hB hh ea eb ec (zhang_prop10_2 A B m hA hB hm hE)⟩

end p8

end Erdos634.ZhangRat2
