import Erdos634.Draft.LaczFormalJunctionRules

/-!
# Band junction rules: the instance conditions from the isosceles band target

Erdős #634, base-`β` band.  Credit: AI assistant (band lemma / item-3 proposal), Beeson–Roșu, Beeson,
Laczkovich, Paliy.

The census target of the instance `T_M(e,f)` (`gram.rs`: `total = M·e·(3f²−e²)` for the base word;
`TARGET` line of the instance file: base `Bs`, legs `L`) is the isosceles triangle with base
`M·e·(3f²−e²)` and legs `M·f³` in units where the tile is `(a,b,c) = (ef, f²−e², f²)`
(`BaseBetaTargetCoord.baseBetaTarget`: base `eN`, legs `f³`, `N = 3f²−e²`, scaled by `M`).  Note the
base is `M e (3f²−e²)` and the *legs* are `M f³`; "`L > a`" in the hand proof is about a leg.

* `base_gt_c`, `leg_gt_a`: `c < M e (3f²−e²)` and `a < M f³` for `M ≥ 1`.
* `cos_beta_identity`: base`/`(2·leg) = cos β`, i.e. `(a²+c²−b²)·(2 M f³) = 2ac·(M e N)`.
* `band_S_target`, `band_E_target`, `band_I_target`, `band_Im_target`: the rules with the
  hypotheses `c < base`, `a < leg`, `a < b` *derived* from the dimensions of `D.target` and from the
  band inequality `2Me < f+e`, `M ≥ 2`.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.LaczJunction

open Erdos634.Geometry Erdos634.TilePlacement

variable {N : ℕ}

theorem base_gt_c (e f M : ℕ) (he : 1 ≤ e) (hef : e < f) (hM : 1 ≤ M) :
    tc e f < M * e * (3 * f ^ 2 - e ^ 2) := by
  unfold tc
  have hle : e ^ 2 ≤ f ^ 2 := Nat.pow_le_pow_left hef.le 2
  have h1 : 2 * f ^ 2 ≤ 3 * f ^ 2 - e ^ 2 := by omega
  have hf2 : 0 < f ^ 2 := pow_pos (by omega) 2
  have h2 : e * (3 * f ^ 2 - e ^ 2) ≤ M * e * (3 * f ^ 2 - e ^ 2) := by
    have : e ≤ M * e := Nat.le_mul_of_pos_left _ (by omega)
    exact Nat.mul_le_mul_right _ this
  have h3 : 1 * (3 * f ^ 2 - e ^ 2) ≤ e * (3 * f ^ 2 - e ^ 2) := Nat.mul_le_mul_right _ he
  omega

theorem leg_gt_a (e f M : ℕ) (he : 1 ≤ e) (hef : e < f) (hM : 1 ≤ M) :
    ta e f < M * f ^ 3 := by
  unfold ta
  have hf0 : 0 < f := by omega
  have h0 : e * f < f * f := Nat.mul_lt_mul_of_pos_right hef hf0
  have h3 : f * f ≤ f ^ 3 :=
    calc f * f = f * f * 1 := by ring
      _ ≤ f * f * f := Nat.mul_le_mul_left _ hf0
      _ = f ^ 3 := by ring
  have h1 : e * f < f ^ 3 := lt_of_lt_of_le h0 h3
  have h2 : f ^ 3 ≤ M * f ^ 3 := Nat.le_mul_of_pos_left _ (by omega)
  omega

/-- The base is `2·leg·cos β`: `(a²+c²−b²)(2 M f³) = (2ac)(M e (3f²−e²))` (law of cosines for the
tile, in the isosceles target of base `M e (3f²−e²)` and legs `M f³`). -/
theorem cos_beta_identity (e f M : ℝ) :
    ((e * f) ^ 2 + (f ^ 2) ^ 2 - (f ^ 2 - e ^ 2) ^ 2) * (2 * (M * f ^ 3)) =
      (2 * (e * f) * f ^ 2) * (M * e * (3 * f ^ 2 - e ^ 2)) := by ring

theorem band_h2 (e f M : ℕ) (he : 1 ≤ e) (hM : 2 ≤ M) (h2 : 2 * M * e < f + e) :
    ta e f < tb e f := band_a_lt_b e f M he hM h2

/-- **Rule S from the target dimensions**: base `M e (3f²−e²)`, left leg `M f³`. -/
theorem band_S_target (D : CongruentDissection N) (e f M : ℕ) (he : 1 ≤ e)
    (hef : e < f) (hcop : Nat.Coprime e f) (hM : 1 ≤ M) (α β γ : ℝ)
    (hγdef : γ = 2 * α + β) (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hα0 : 0 < α) (hβ0 : 0 < β)
    (hα' : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hβ' : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hγ' : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    (hsa : sideOpp D.model 0 = (ta e f : ℝ)) (hsb : sideOpp D.model 1 = (tb e f : ℝ))
    (hsc : sideOpp D.model 2 = (tc e f : ℝ))
    {p q r : Fin 3} (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (hbase : dist (D.target.pts p) (D.target.pts q) = ((M * e * (3 * f ^ 2 - e ^ 2) : ℕ) : ℝ))
    (hleg : dist (D.target.pts p) (D.target.pts r) = ((M * f ^ 3 : ℕ) : ℝ))
    {P G E Z2 : Plane} (i1 i2 : Fin N) (hne : i2 ≠ i1)
    (t1 : BaseTok D p q (angOf α β γ) (lenOf (ta e f) (tb e f) (tc e f)) .c .B .A i1
      (D.target.pts p) P G)
    (hGl : G ∈ segment ℝ (D.target.pts p) (D.target.pts r))
    (t2 : BaseTok D p q (angOf α β γ) (lenOf (ta e f) (tb e f) (tc e f)) .b .G .A i2 P E Z2) :
    False :=
  band_S_tok D e f he hef hcop α β γ hγdef hrel hirr hα0 hβ0 hα' hβ' hγ' hsa hsb hsc hpq hpr hqr
    (by rw [hbase]; exact_mod_cast base_gt_c e f M he hef hM)
    (by rw [hleg]; exact_mod_cast leg_gt_a e f M he hef hM) i1 i2 hne t1 hGl t2

/-- **Rule E from the target dimensions** (the right leg of the isosceles target is also `M f³`). -/
theorem band_E_target (D : CongruentDissection N) (e f M : ℕ) (he : 1 ≤ e)
    (hef : e < f) (hcop : Nat.Coprime e f) (hM : 1 ≤ M) (α β γ : ℝ)
    (hγdef : γ = 2 * α + β) (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hα0 : 0 < α) (hβ0 : 0 < β)
    (hα' : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hβ' : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hγ' : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    (hsa : sideOpp D.model 0 = (ta e f : ℝ)) (hsb : sideOpp D.model 1 = (tb e f : ℝ))
    (hsc : sideOpp D.model 2 = (tc e f : ℝ))
    {p q r : Fin 3} (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (hbase : dist (D.target.pts p) (D.target.pts q) = ((M * e * (3 * f ^ 2 - e ^ 2) : ℕ) : ℝ))
    (hlegR : dist (D.target.pts q) (D.target.pts r) = ((M * f ^ 3 : ℕ) : ℝ))
    {P G E Z2 : Plane} (i1 i2 : Fin N) (hne : i2 ≠ i1)
    (t2 : BaseTok D p q (angOf α β γ) (lenOf (ta e f) (tb e f) (tc e f)) .b .A .G i2 E P Z2)
    (t1 : BaseTok D p q (angOf α β γ) (lenOf (ta e f) (tb e f) (tc e f)) .c .A .B i1
      P (D.target.pts q) G)
    (hGr : G ∈ segment ℝ (D.target.pts q) (D.target.pts r)) : False :=
  band_E_tok D e f he hef hcop α β γ hγdef hrel hirr hα0 hβ0 hα' hβ' hγ' hsa hsb hsc hpq hpr hqr
    (by rw [hbase]; exact_mod_cast base_gt_c e f M he hef hM)
    (by rw [hlegR]; exact_mod_cast leg_gt_a e f M he hef hM) i1 i2 hne t2 t1 hGr

/-- **Rule I from the band inequality** `2Me < f+e`, `M ≥ 2`. -/
theorem band_I_target (D : CongruentDissection N) (e f M : ℕ) (he : 1 ≤ e) (hef : e < f)
    (hcop : Nat.Coprime e f) (hM : 2 ≤ M) (hbandM : 2 * M * e < f + e) (α β γ : ℝ)
    (hγdef : γ = 2 * α + β) (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hα0 : 0 < α) (hβ0 : 0 < β)
    (hα' : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hβ' : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hγ' : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    (hsa : sideOpp D.model 0 = (ta e f : ℝ)) (hsb : sideOpp D.model 1 = (tb e f : ℝ))
    (hsc : sideOpp D.model 2 = (tc e f : ℝ))
    {p q r : Fin 3} (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    {Y Q P G E Zx Z2 : Plane} (i1 i2 iX : Fin N) (hne2 : i2 ≠ i1) (hneX : iX ≠ i1)
    (xs : Side) (lX rX : Corner) (hrX : rX = .B ∨ rX = .G)
    (tX : BaseTok D p q (angOf α β γ) (lenOf (ta e f) (tb e f) (tc e f)) xs lX rX iX Y Q Zx)
    (t1 : BaseTok D p q (angOf α β γ) (lenOf (ta e f) (tb e f) (tc e f)) .c .B .A i1 Q P G)
    (t2 : BaseTok D p q (angOf α β γ) (lenOf (ta e f) (tb e f) (tc e f)) .b .G .A i2 P E Z2) :
    False :=
  band_I_tok D e f he hef hcop (band_h2 e f M he hM hbandM) α β γ hγdef hrel hirr hα0 hβ0 hα' hβ' hγ'
    hsa hsb hsc hpq hpr hqr i1 i2 iX hne2 hneX xs lX rX hrX tX t1 t2

/-- **Rule Im from the band inequality.** -/
theorem band_Im_target (D : CongruentDissection N) (e f M : ℕ) (he : 1 ≤ e) (hef : e < f)
    (hcop : Nat.Coprime e f) (hM : 2 ≤ M) (hbandM : 2 * M * e < f + e) (α β γ : ℝ)
    (hγdef : γ = 2 * α + β) (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hα0 : 0 < α) (hβ0 : 0 < β)
    (hα' : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hβ' : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hγ' : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    (hsa : sideOpp D.model 0 = (ta e f : ℝ)) (hsb : sideOpp D.model 1 = (tb e f : ℝ))
    (hsc : sideOpp D.model 2 = (tc e f : ℝ))
    {p q r : Fin 3} (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    {Y Q P G E Zy Z2 : Plane} (i1 i2 iY : Fin N) (hne2 : i2 ≠ i1) (hneY : iY ≠ i1)
    (ys : Side) (lY rY : Corner) (hlY : lY = .B ∨ lY = .G)
    (t2 : BaseTok D p q (angOf α β γ) (lenOf (ta e f) (tb e f) (tc e f)) .b .A .G i2 E P Z2)
    (t1 : BaseTok D p q (angOf α β γ) (lenOf (ta e f) (tb e f) (tc e f)) .c .A .B i1 P Q G)
    (tY : BaseTok D p q (angOf α β γ) (lenOf (ta e f) (tb e f) (tc e f)) ys lY rY iY Q Y Zy) :
    False :=
  band_Im_tok D e f he hef hcop (band_h2 e f M he hM hbandM) α β γ hγdef hrel hirr hα0 hβ0 hα' hβ'
    hγ' hsa hsb hsc hpq hpr hqr i1 i2 iY hne2 hneY ys lY rY hlY t2 t1 tY

/-- Sanity check of the band arithmetic on a grid: for every coprime `(e,f)` with `f < 60`, and
`M ∈ [2,10]` in the band `f ≤ 2Me < f+e`, the three derived instance conditions hold. -/
def checkInstance : Bool :=
  (List.range 60).all fun f => (List.range f).all fun e =>
    (List.range 11).all fun M =>
      e < 1 || M < 2 || !(f ≤ 2 * M * e && 2 * M * e < f + e && Nat.gcd e f == 1) ||
        (decide (tc e f < M * e * (3 * f ^ 2 - e ^ 2)) && decide (ta e f < M * f ^ 3) &&
          decide (ta e f < tb e f))

#eval checkInstance

#print axioms band_S_target
#print axioms band_E_target
#print axioms band_I_target
#print axioms band_Im_target

end Erdos634.LaczJunction
