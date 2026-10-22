import Erdos634.Draft.LaczFormalL33Chart
import Erdos634.Draft.LaczFormalL30Trap

/-!
# Laczkovich Theorem 2.5, triple `(α+β, α+β, α+β)`: the trapezoid `N V R Q` and the equilateral triangle

NOTE, UNAUDITED.  Credit: Laczkovich (Discrete Math. 140 (1995) 79-94, Lemma 2.2 (ii), Theorem 2.5, Fig. 7), Beeson,
Beeson-Zhang, Zhang.
-/

namespace Erdos634.LaczL33

open Erdos634.Geometry Erdos634.CertCoord Erdos634.LaczL22 Erdos634.LaczL21 Erdos634.LaczL24 Erdos634.Realizable
  Erdos634.DissectionMap Erdos634.LaczL30
open Erdos634.LaczL27 (carrier_eq_of_range range_mk3)

private theorem htri'' : ∀ i : Fin 3, i = 0 ∨ i = 1 ∨ i = 2 := by decide

theorem Wdc (R : RTri) (hγ : R.a ^ 2 + R.a * R.b + R.b ^ 2 = R.c ^ 2) :
    R.c * Ddq2 R * R.sw01.cos1 = R.a ^ 2 * (1 - kq R ^ 3) * (2 * kq R + 1) / 2 := by
  have ha := R.pa; have hb := R.pb; have hc := R.pc
  have e : R.b ^ 2 + R.c ^ 2 - R.a ^ 2 = R.b * (2 * R.b + R.a) := by linear_combination (-1 : ℚ) * hγ
  rw [cos1_sw01, e]
  unfold Ddq2 kq
  field_simp

section chart

variable (R : RTri) (hγ : R.a ^ 2 + R.a * R.b + R.b ^ 2 = R.c ^ 2) (hab : R.b < R.a)
  (w d : Plane) (hdet : w 0 * d 1 - w 1 * d 0 ≠ 0)
  (hw : inner ℝ w w = (R.a : ℝ) ^ 2) (hd : inner ℝ d d = (R.a : ℝ) ^ 2)
  (hwd : inner ℝ w d = (R.a : ℝ) * (R.a : ℝ) * (-1 / 2))

include hγ hab hdet hw hd hwd

set_option maxHeartbeats 8000000 in
theorem chart_strapE :
    ChartRSD R 0 w d hdet ((tU1 (hK0 R) (hK1 R hab)).carrier ∪ (tU2 (hK0 R) (hK1 R hab)).carrier) := by
  obtain ⟨hb, hc2⟩ := real_facts R hγ
  have hk0 := hK0 R
  have hk1 := hK1 R hab
  set K : ℝ := ((kq R : ℚ) : ℝ) with hKdef
  have h3 : K ^ 3 < 1 := pow_lt_one₀ hk0.le hk1 (by norm_num)
  have h3' : (0 : ℝ) < 1 - K ^ 3 := by linarith
  have ha : (0 : ℝ) < R.a := by exact_mod_cast R.pa
  have hdet' : (((-K) • w + (1 : ℝ) • d) : Plane) 0 * (((K ^ 3 - 1) • w + (0 : ℝ) • d) : Plane) 1
      - (((-K) • w + (1 : ℝ) • d) : Plane) 1 * (((K ^ 3 - 1) • w + (0 : ℝ) • d) : Plane) 0 ≠ 0 := by
    rw [Erdos634.LaczL25.det_comb]
    refine mul_ne_zero ?_ hdet
    intro h; nlinarith
  have hwG : inner ℝ ((-K) • w + (1 : ℝ) • d) ((-K) • w + (1 : ℝ) • d) = ((R.c : ℚ) : ℝ) ^ 2 := by
    rw [Erdos634.LaczL26.gram2, hw, hd, hwd, hc2]; ring
  have hdG : inner ℝ ((K ^ 3 - 1) • w + (0 : ℝ) • d) ((K ^ 3 - 1) • w + (0 : ℝ) • d) = ((Ddq2 R : ℚ) : ℝ) ^ 2 := by
    rw [Erdos634.LaczL26.gram2, hw, hd, hwd]
    unfold Ddq2; push_cast; ring
  have hwdG : inner ℝ ((-K) • w + (1 : ℝ) • d) ((K ^ 3 - 1) • w + (0 : ℝ) • d)
      = ((R.c : ℚ) : ℝ) * ((Ddq2 R : ℚ) : ℝ) * ((R.sw01.cos1 : ℚ) : ℝ) := by
    have e : ((R.c : ℚ) : ℝ) * ((Ddq2 R : ℚ) : ℝ) * ((R.sw01.cos1 : ℚ) : ℝ)
        = (((R.c * Ddq2 R * R.sw01.cos1 : ℚ)) : ℝ) := by push_cast; ring
    rw [e, Wdc R hγ, Erdos634.LaczL26.gram2, hw, hd, hwd]
    push_cast
    rw [← hKdef]; ring
  have hτ : (0 : ℚ) < kq R ^ 2 := by have := kq_pos R; positivity
  have ct := RatSimDiss.relabel (Δ := R.Δ) (Equiv.swap 0 1)
    (trap_ii R.sw01 ((1 : ℝ) • w + (0 : ℝ) • d) ((-K) • w + (1 : ℝ) • d) ((K ^ 3 - 1) • w + (0 : ℝ) • d) hdet' R.c
      (Ddq2 R) R.pc (Ddq2_pos R hab) hwG hdG hwdG (kq R ^ 2) (tTau2 R hγ).symm hτ)
  have hτR : (0 : ℝ) < ((kq R ^ 2 : ℚ) : ℝ) := by exact_mod_cast hτ
  have hτK : ((kq R ^ 2 : ℚ) : ℝ) = K ^ 2 := by push_cast; rfl
  have sub : ∀ x y : ℝ, chartEquiv ((1 : ℝ) • w + (0 : ℝ) • d) ((-K) • w + (1 : ℝ) • d) ((K ^ 3 - 1) • w + (0 : ℝ) • d)
      hdet' (mkPt x y) = chartEquiv 0 w d hdet (mkPt (1 - K * x + (K ^ 3 - 1) * y) x) := by
    intro x y
    rw [chartEquiv_apply, chartEquiv_apply]
    simp only [mkPt_zero, mkPt_one]
    module
  unfold ChartRSD at ct ⊢
  rw [trapSet_split _ hτR, Set.image_union] at ct
  rw [Set.image_union]
  have eY : chartEquiv ((1 : ℝ) • w + (0 : ℝ) • d) ((-K) • w + (1 : ℝ) • d) ((K ^ 3 - 1) • w + (0 : ℝ) • d) hdet' ''
        (mkTri 0 0 1 0 0 1 (by simp only [det3]; norm_num)).carrier
      = chartEquiv 0 w d hdet '' (tU1 hk0 hk1).carrier := by
    refine image_tri_eq _ _ _ _ (finRotate 3) (fun i => ?_)
    rcases htri'' i with rfl | rfl | rfl
    · show chartEquiv _ _ _ hdet' (mkPt 0 0) = chartEquiv 0 w d hdet (mkPt 1 0)
      rw [sub]; congr 2 <;> ring
    · show chartEquiv _ _ _ hdet' (mkPt 1 0) = chartEquiv 0 w d hdet (mkPt (1 - K) 1)
      rw [sub]; congr 2 <;> ring
    · show chartEquiv _ _ _ hdet' (mkPt 0 1) = chartEquiv 0 w d hdet (mkPt (K ^ 3) 0)
      rw [sub]; congr 2 <;> ring
  have eX : chartEquiv ((1 : ℝ) • w + (0 : ℝ) • d) ((-K) • w + (1 : ℝ) • d) ((K ^ 3 - 1) • w + (0 : ℝ) • d) hdet' ''
        (mkTri 1 0 ((kq R ^ 2 : ℚ) : ℝ) 1 0 1 (by simp only [det3]; nlinarith)).carrier
      = chartEquiv 0 w d hdet '' (tU2 hk0 hk1).carrier := by
    refine image_tri_eq _ _ _ _ (finRotate 3) (fun i => ?_)
    rcases htri'' i with rfl | rfl | rfl
    · show chartEquiv _ _ _ hdet' (mkPt 1 0) = chartEquiv 0 w d hdet (mkPt (1 - K) 1)
      rw [sub]; congr 2 <;> ring
    · show chartEquiv _ _ _ hdet' (mkPt ((kq R ^ 2 : ℚ) : ℝ) 1) = chartEquiv 0 w d hdet (mkPt 0 (K ^ 2))
      rw [sub, hτK]; congr 2 <;> ring
    · show chartEquiv _ _ _ hdet' (mkPt 0 1) = chartEquiv 0 w d hdet (mkPt (K ^ 3) 0)
      rw [sub]; congr 2 <;> ring
  rw [eX, eY] at ct
  -- `ct` is the union in the order `U2 ∪ U1`
  rw [Set.union_comm]
  exact ct

end chart

#print axioms chart_strapE

end Erdos634.LaczL33
