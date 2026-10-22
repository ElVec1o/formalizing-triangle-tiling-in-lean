import Erdos634.Draft.ISUMain

/-!
# Beeson, "Tilings of an isosceles triangle" (arXiv 1206.1974 v7), Theorem 12.11 (no 37-tiling, `gamma = 2 pi/3`)

NOTE, UNAUDITED.  Credit: Michael Beeson (arXiv 1206.1974 v7, Thm 12.11; arXiv 1206.2229), Laczkovich (DCG 48 (2012)),
Beeson-Zhang, Paliy (primes).  Formalization debt, not progress on the /goal outcomes.

Printed statement: there is no `37`-tiling of an isosceles triangle with base angles `alpha` using a tile with
`gamma = 2 pi/3` (`alpha` not a rational multiple of `pi`, the standing hypothesis H1 of the isosceles paper).
Beeson proves it by Theorem 12.10 and a boundary argument at `B`.  Here it is a CORNER of the project's
`ISUMain.thmIso_unrestricted_angles` (every PRIME `N`, any non-equilateral target with two equal angles, tile
`(alpha, pi/3 - alpha, 2 pi/3)`, `alpha` not in `Q pi`): `37` is prime.  So this is NOT Beeson's proof.
Hypotheses witnessed (all but primality) by the certified 2673-tiling (`G3CIsoControl`, `2673 = 3^5 * 11`): `witness_hyps`.
Uses H1 (`IrrPi alpha`), as the printed theorem does.
-/

namespace Erdos634.Draft.BeesonIsoT1211

open Erdos634.Geometry Erdos634.Draft.TheoremPConditional Erdos634.Draft.ISUMain

/-- Every prime `N`: no `N`-tiling of the isosceles triangle with base angles `alpha` (corners `0`, `1`) by the
tile `(alpha, pi/3 - alpha, 2 pi/3)`, `alpha` not in `Q pi` (H1). -/
theorem no_prime_tiling_twoPiThree {N : ℕ} (hN : N.Prime) (D : CongruentDissection N) {α a b c : ℝ}
    (hα : IrrPi α) (hm : D.model.TwoPiThreeData α a b c)
    (hA : D.target.angleAt 0 = α) (hB : D.target.angleAt 1 = α) : False := by
  refine thmIso_unrestricted_angles D hN hα hm ⟨0, 1, by decide, by rw [hA, hB]⟩ ?_
  intro hE
  have h0 := hE 0
  rw [hA] at h0
  exact hα ⟨1 / 3, by rw [h0]; push_cast; ring⟩

/-- Beeson Theorem 12.11: no `37`-tiling of an isosceles triangle with base angles `alpha` by a `gamma = 2 pi/3`
tile (H1: `alpha` not in `Q pi`). -/
theorem beeson_12_11 (D : CongruentDissection 37) {α a b c : ℝ}
    (hα : IrrPi α) (hm : D.model.TwoPiThreeData α a b c)
    (hA : D.target.angleAt 0 = α) (hB : D.target.angleAt 1 = α) : False :=
  no_prime_tiling_twoPiThree (by norm_num) D hα hm hA hB

open Erdos634.Draft.G3CIsoControl Erdos634.Draft.G3CAng in
/-- Witness: on the real 2673-tiling every hypothesis of `no_prime_tiling_twoPiThree` except primality holds
(tile angle `beta` is the base angle of the target), so the primality hypothesis is the only one that can fail. -/
theorem witness_hyps :
    IrrPi β ∧ D.model.TwoPiThreeData β (1890 * 5) (1890 * 3) (1890 * 7) ∧
      D.target.angleAt 0 = β ∧ D.target.angleAt 1 = β := by
  refine ⟨?_, ?_, angle_eq_of_cos 0 (σm 1) (t_cos0.trans cos_β.symm),
    angle_eq_of_cos 1 (σm 1) (t_cos1.trans cos_β.symm)⟩
  · rintro ⟨r, hr⟩
    apply α_irr
    refine ⟨1 / 3 - r, ?_⟩
    have h1 := hβ
    push_cast
    linarith
  · obtain ⟨σ, h0, o0', h1, o1', h2, o2'⟩ := data
    have e0 : Equiv.swap (0 : Fin 3) 1 0 = 1 := by decide
    have e1 : Equiv.swap (0 : Fin 3) 1 1 = 0 := by decide
    have e2 : Equiv.swap (0 : Fin 3) 1 2 = 2 := by decide
    refine ⟨σ * Equiv.swap 0 1, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [Equiv.Perm.mul_apply, e0]; exact h1.trans hβ.symm
    · rw [Equiv.Perm.mul_apply, e0]; exact o1'
    · rw [Equiv.Perm.mul_apply, e1, h0]; linarith [hβ]
    · rw [Equiv.Perm.mul_apply, e1]; exact o0'
    · rw [Equiv.Perm.mul_apply, e2]; exact h2
    · rw [Equiv.Perm.mul_apply, e2]; exact o2'

end Erdos634.Draft.BeesonIsoT1211

#print axioms Erdos634.Draft.BeesonIsoT1211.no_prime_tiling_twoPiThree
#print axioms Erdos634.Draft.BeesonIsoT1211.beeson_12_11
#print axioms Erdos634.Draft.BeesonIsoT1211.witness_hyps
