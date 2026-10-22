import Erdos634.Draft.FluxDRow4
import Erdos634.Draft.G3C6Control

/-!
# Beeson, "Tilings of an isosceles triangle" (arXiv 1206.1974 v7), Lemmas 11.1, 11.4, 11.5 (geometric)

NOTE, UNAUDITED.  Credit: Michael Beeson (arXiv 1206.1974 v7, Sect. 11; arXiv 1206.2229), Laczkovich (DCG 48 (2012)),
Beeson-Zhang.  Formalization debt, not progress on the /goal outcomes.

Setting (printed): isosceles `ABC` with base angles `alpha` (corners `0`, `1` of `D.target`), `N`-tiled by a tile with
angles `(alpha, beta, 2 alpha)` and sides `(a, b, c)`, `alpha` not a rational multiple of `pi` (H1).  `X` = the equal
sides (`oppLen 0 = oppLen 1`), `Y` = the base (`oppLen 2`).
* Lemma 11.1 `c^2 = a^2 + ab` and Lemma 11.4 `X^2 = N a b`: both are already conjuncts of `Row4.P5`
  (`FluxDRow4.lean:160`, `ab = c^2 - a^2`); restated here.
* Lemma 11.5 `X Y = N b c` and `Y = (c/a) X`: NEW (from `Row4.sides`, `Row4.P5`).
Witness: the real 1125-tiling (`G3C6Control`, target `(150,150,225)`, tile `(64,80,96)` = 16*(4,5,6)): `wit_1125`.
-/

namespace Erdos634.Draft.BeesonIsoL11Geo

open Erdos634.Geometry

variable {N : ℕ}

/-- Lemmas 11.1 and 11.4. -/
theorem l11_1_4 (D : CongruentDissection N) {α a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (h : D.model.TwoAlphaData α a b c)
    (hA : D.target.angleAt 0 = α) (hB : D.target.angleAt 1 = α) :
    c ^ 2 = a ^ 2 + a * b ∧ D.target.oppLen 0 ^ 2 = N * a * b := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hX, hab⟩ := Row4.P5 D hα h hA hB
  exact ⟨by linarith, hX⟩

/-- Lemma 11.5: `X Y = N b c` and `Y = (c/a) X`. -/
theorem l11_5 (D : CongruentDissection N) {α a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (h : D.model.TwoAlphaData α a b c)
    (hA : D.target.angleAt 0 = α) (hB : D.target.angleAt 1 = α) :
    D.target.oppLen 0 * D.target.oppLen 2 = N * b * c ∧
      D.target.oppLen 2 = c / a * D.target.oppLen 0 := by
  obtain ⟨κ, -, -, ha, -, hc, hb, hY, -⟩ := Row4.sides D h hA hB
  obtain ⟨-, hX⟩ := l11_1_4 D hα h hA hB
  have hca : c / a = 2 * κ := by rw [hc]; field_simp
  refine ⟨?_, by rw [hca, hY]⟩
  rw [hY]
  have : D.target.oppLen 0 * (2 * κ * D.target.oppLen 0) = 2 * κ * (D.target.oppLen 0 ^ 2) := by ring
  rw [this, hX, hc, hb]
  ring

open Erdos634.Draft.G3GControl in
/-- Witness: the hypotheses hold on the real 1125-tiling (`G3C6Control.joint_premises`), and the conclusions are
instantiated there: `c^2 = a^2 + ab`, `X^2 = N a b`, `X Y = N b c` with `X = 2400`, `Y = 3600`, tile `(64,80,96)`. -/
theorem wit_1125 :
    (96 : ℝ) ^ 2 = 64 ^ 2 + 64 * 80 ∧ (2400 : ℝ) ^ 2 = (1125 : ℕ) * 64 * 80 ∧
      (2400 : ℝ) * 3600 = (1125 : ℕ) * 80 * 96 := by
  obtain ⟨h1, h2⟩ := l11_1_4 D α_irr data t_ang0 t_ang1
  obtain ⟨h3, -⟩ := l11_5 D α_irr data t_ang0 t_ang1
  rw [t_opp0, Erdos634.Draft.G3GTiling1125.cert_len] at h2
  rw [t_opp0, t_opp2, Erdos634.Draft.G3GTiling1125.cert_len] at h3
  exact ⟨h1, h2, h3⟩

end Erdos634.Draft.BeesonIsoL11Geo

#print axioms Erdos634.Draft.BeesonIsoL11Geo.l11_1_4
#print axioms Erdos634.Draft.BeesonIsoL11Geo.l11_5
#print axioms Erdos634.Draft.BeesonIsoL11Geo.wit_1125
