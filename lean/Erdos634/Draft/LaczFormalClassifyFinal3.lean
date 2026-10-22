-- Draft/LaczFormalClassifyFinal3.lean -- `classify_commensurable_final` with the coverage extended by the chunked certificates n = 160, 162, 180, 192, 200.
-- UNAUDITED (NOTE).  Credit: Laczkovich (DCG 48 (2012); Discrete Math 140 (1995) Thm 5.1/5.3), Beeson-Rosu, Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalClassifyFinal
import Erdos634.Draft.LaczFormalR2G_160
import Erdos634.Draft.LaczFormalR2G_162
import Erdos634.Draft.LaczFormalR2G_180
import Erdos634.Draft.LaczFormalR2G_192
import Erdos634.Draft.LaczFormalR2G_200

open scoped BigOperators Classical
open Erdos634.Geometry Erdos634.TilePlacement Erdos634.Draft.TheoremPConditional Erdos634.LemmaS Erdos634.CaseA.R0c
open Erdos634.Geometry.CaseA.LemmaV (nat_bounds angle_pos angle_lt_pi)

namespace Erdos634.Draft.LaczFormal

variable {N : ℕ}

/-- Further certified 5-smooth denominators (chunked light kernel certificates `LaczFormalR2G_n`, n = 160, 162, 180, 192, 200). -/
def CertN3 (n : ℕ) : Prop := n = 160 ∨ n = 162 ∨ n = 180 ∨ n = 192 ∨ n = 200

theorem lemmaS_smooth3 {n : ℕ} (hn : CertN3 n) (a : Fin 3 → ℕ) (hpos : ∀ i, 0 < a i) (hsum : ∑ i, a i = n)
    (hgcd : Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1) : LemmaS.relSpace n a = LemmaS.trivSpace n a := by
  rcases hn with rfl | rfl | rfl | rfl | rfl
  · exact of_allCert allCert_160 a hpos hsum hgcd
  · exact of_allCert allCert_162 a hpos hsum hgcd
  · exact of_allCert allCert_180 a hpos hsum hgcd
  · exact of_allCert allCert_192 a hpos hsum hgcd
  · exact of_allCert allCert_200 a hpos hsum hgcd

/-- Covered denominators, extended by `CertN3`. -/
def Covered3 (n : ℕ) : Prop := Covered n ∨ CertN3 n

/-- **Classification, extended coverage (`Covered3`), equilateral shapes excluded.** -/
theorem classify_commensurable_final3 (D : CongruentDissection N) {n : ℕ} (hn : 0 < n) (a : Fin 3 → ℕ)
    (ha : ∀ k, D.model.angleAt k = a k * Real.pi / n)
    (hgcd : Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1) (hcov : Covered3 n) :
    SimilarTM D ∨ (∃ k l : Fin 3, l ≠ k ∧ D.model.angleAt k = Real.pi / 2 ∧
        ∃ j₁ j₂ : Fin 3, j₁ ≠ j₂ ∧ D.target.angleAt j₁ = D.model.angleAt l ∧
          D.target.angleAt j₂ = D.model.angleAt l) ∨ ExcPair3 D := by
  rcases hcov with h | h
  · exact classify_commensurable_final D hn a ha hgcd h
  · have ha1 : ∀ i, 0 < a i := fun i => (nat_bounds hn (ha i) (angle_pos _ i) (angle_lt_pi _ i)).1
    rcases l9_of_S D hn a ha hgcd (lemmaS_smooth3 h a ha1 (Erdos634.CaseA.R0c.sum_of_angles hn ha) hgcd) with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)

end Erdos634.Draft.LaczFormal

#print axioms Erdos634.Draft.LaczFormal.classify_commensurable_final3
