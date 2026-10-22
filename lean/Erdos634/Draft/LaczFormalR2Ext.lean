-- Draft/LaczFormalR2Ext.lean -- R(a) = R0(a) at the further certified 5-smooth denominators n = 5, 80, 81, 90, 96, 100, 108, 120, 125, 128, 135, 144, 150 (chunked light kernel certificates, `LaczFormalR2G_n`);
-- extends `CertN` / `lemmaS_smooth` / `l9_smooth` of `LaczFormalR2`.  UNAUDITED.  Credit: Laczkovich (1995, Lemma S, Thm 5.1/5.3); our CaseACorF, `Lite` chunking.
import Erdos634.Draft.LaczFormalR2
import Erdos634.Draft.LaczFormalR2G_5
import Erdos634.Draft.LaczFormalR2G_80
import Erdos634.Draft.LaczFormalR2G_81
import Erdos634.Draft.LaczFormalR2G_90
import Erdos634.Draft.LaczFormalR2G_96
import Erdos634.Draft.LaczFormalR2G_100
import Erdos634.Draft.LaczFormalR2G_108
import Erdos634.Draft.LaczFormalR2G_120
import Erdos634.Draft.LaczFormalR2G_125
import Erdos634.Draft.LaczFormalR2G_128
import Erdos634.Draft.LaczFormalR2G_135
import Erdos634.Draft.LaczFormalR2G_144
import Erdos634.Draft.LaczFormalR2G_150

open scoped BigOperators Classical
open Erdos634.Geometry Erdos634.LemmaS Erdos634.LemmaKStar Erdos634.Draft.TheoremPConditional
open Erdos634.Geometry.CaseA.LemmaV (nat_bounds angle_pos angle_lt_pi)

namespace Erdos634.Draft.LaczFormal

/-- Certified denominators: the 16 of `CertN` and the further ones. -/
def CertN2 (n : ℕ) : Prop := CertN n ∨ n = 5 ∨ n = 80 ∨ n = 81 ∨ n = 90 ∨ n = 96 ∨ n = 100 ∨ n = 108 ∨ n = 120 ∨ n = 125 ∨ n = 128 ∨ n = 135 ∨ n = 144 ∨ n = 150

theorem lemmaS_smooth2 {n : ℕ} (hn : CertN2 n) (a : Fin 3 → ℕ) (hpos : ∀ i, 0 < a i) (hsum : ∑ i, a i = n)
    (hgcd : Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1) : relSpace n a = trivSpace n a := by
  rcases hn with h | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lemmaS_smooth h a hpos hsum hgcd
  · exact of_allCert allCert_5 a hpos hsum hgcd
  · exact of_allCert allCert_80 a hpos hsum hgcd
  · exact of_allCert allCert_81 a hpos hsum hgcd
  · exact of_allCert allCert_90 a hpos hsum hgcd
  · exact of_allCert allCert_96 a hpos hsum hgcd
  · exact of_allCert allCert_100 a hpos hsum hgcd
  · exact of_allCert allCert_108 a hpos hsum hgcd
  · exact of_allCert allCert_120 a hpos hsum hgcd
  · exact of_allCert allCert_125 a hpos hsum hgcd
  · exact of_allCert allCert_128 a hpos hsum hgcd
  · exact of_allCert allCert_135 a hpos hsum hgcd
  · exact of_allCert allCert_144 a hpos hsum hgcd
  · exact of_allCert allCert_150 a hpos hsum hgcd

/-- L9 at the certified smooth denominators of `CertN2`. -/
theorem l9_smooth2 {N : ℕ} (D : CongruentDissection N) {n : ℕ} (hn : 0 < n) (a : Fin 3 → ℕ)
    (ha : ∀ k, D.model.angleAt k = a k * Real.pi / n)
    (hgcd : Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1) (hC : CertN2 n) :
    SimilarTM D ∨
      ∃ k l : Fin 3, l ≠ k ∧ D.model.angleAt k = Real.pi / 2 ∧
        ∃ j₁ j₂ : Fin 3, j₁ ≠ j₂ ∧ D.target.angleAt j₁ = D.model.angleAt l ∧
          D.target.angleAt j₂ = D.model.angleAt l := by
  have ha1 : ∀ i, 0 < a i := fun i => (nat_bounds hn (ha i) (angle_pos _ i) (angle_lt_pi _ i)).1
  exact l9_of_S D hn a ha hgcd (lemmaS_smooth2 hC a ha1 (Erdos634.CaseA.R0c.sum_of_angles hn ha) hgcd)

end Erdos634.Draft.LaczFormal
