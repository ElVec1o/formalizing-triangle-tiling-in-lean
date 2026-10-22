-- Draft/LaczFormalIIcWN29.lean -- Laczkovich (DCG 48 (2012)), Sect. 6.2, "u = v + N" (printed `u(alpha+beta) + v(alpha+beta+2 gamma) = (u+v-2) pi`) for a cycle of Gamma_kite.
-- Combines the interior angle sum of a simple polygon (WN24, discrete Hopf), simplicity of a Gamma_kite cycle (WN18) and the turning angle at its vertices (WN28):
-- for a cycle `C` of Gamma_kite with distinct vertices there are `rho = +-1` and `t_k in {0,1,2}` with `rho * gamma * sum_k (t_k - 1) = 2 pi`
-- (`t_k = 0`: turn `-gamma`, interior angle `pi +- gamma`; `t_k = 1`: straight; `t_k = 2`: turn `+gamma`).  With u = #{rho (t_k-1) = 1}, v = #{rho (t_k-1) = -1}: `(u - v) gamma = 2 pi`, i.e. `u = v + N` for `gamma = 2 pi/N`.
-- NOTE, UNAUDITED.  CONDITIONAL on the Case IIc block and on the existence of a closed Gamma_kite chain (NOT witnessed: no tiling with a closed Gamma_kite chain is exhibited; Lemma 6.2 asserts there is none).
-- Credit: Laczkovich (DCG 48 (2012), Sect. 6.2), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcWN28
import Erdos634.Draft.LaczFormalIIcWN25
import Erdos634.Draft.LaczFormalIIcWN13
import Erdos634.Draft.LaczFormalIIcWN18

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ}

theorem toC_apply (x : EuclideanSpace ℝ (Fin 2)) :
    Erdos634.Draft.LaczFormal.WN.toC x = (x 0 : ℂ) + (x 1 : ℂ) * Complex.I := rfl

theorem toC_rot {u w : Plane} {θ : ℝ} (h : toV2 u = Graph.rot θ (toV2 w)) :
    Erdos634.Draft.LaczFormal.WN.toC u = Complex.exp ((θ : ℂ) * Complex.I) * Erdos634.Draft.LaczFormal.WN.toC w := by
  have h0 : u 0 = Real.cos θ * w 0 - Real.sin θ * w 1 := by
    have := congrArg Prod.fst h; simpa [toV2, Graph.rot] using this
  have h1 : u 1 = Real.sin θ * w 0 + Real.cos θ * w 1 := by
    have := congrArg Prod.snd h; simpa [toV2, Graph.rot] using this
  rw [toC_apply, toC_apply, Complex.exp_mul_I, h0, h1]
  push_cast
  rw [← Complex.ofReal_cos, ← Complex.ofReal_sin]
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

theorem toC_sub (a b : EuclideanSpace ℝ (Fin 2)) :
    Erdos634.Draft.LaczFormal.WN.toC (a - b) = Erdos634.Draft.LaczFormal.WN.toC a - Erdos634.Draft.LaczFormal.WN.toC b :=
  map_sub _ _ _

/-- Turning ratio at a vertex of a Gamma_kite chain: `(Z-Y)/(Y-X) = exp(i (t-1) gamma)`. -/
theorem gkite_ratio [NeZero N] [NeZero M] (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hC : CaseC D idx)
    (h1 : D.model.angleAt 2 < Real.pi / 2) (h3 : D.model.angleAt 2 ≠ Real.pi / 3) (G : AngGen (fun l => D.model.angleAt l)) {X Y Z : Plane}
    (hXY : GKite D idx X Y) (hYZ : GKite D idx Y Z) :
    ∃ t : ℕ, t ≤ 2 ∧
      (Erdos634.Draft.LaczFormal.WN.toC Z - Erdos634.Draft.LaczFormal.WN.toC Y) / (Erdos634.Draft.LaczFormal.WN.toC Y - Erdos634.Draft.LaczFormal.WN.toC X) =
        Complex.exp ((((t : ℝ) - 1) * D.model.angleAt 2 : ℝ) * Complex.I) := by
  obtain ⟨t, ht, hrot⟩ := gkite_turn D P hreg idx hC h1 h3 G hXY hYZ
  refine ⟨t, ht, ?_⟩
  have hc := toC_rot hrot
  rw [toC_sub, toC_sub] at hc
  have hne : Erdos634.Draft.LaczFormal.WN.toC Y - Erdos634.Draft.LaczFormal.WN.toC X ≠ 0 := by
    intro h
    have : X = Y := (Erdos634.Draft.LaczFormal.WN.toC.injective (sub_eq_zero.1 h)).symm
    exact gkite_ne D idx hXY this
  have hsum := G.sum
  have e : Erdos634.Draft.LaczFormal.WN.toC X - Erdos634.Draft.LaczFormal.WN.toC Y =
      -(Erdos634.Draft.LaczFormal.WN.toC Y - Erdos634.Draft.LaczFormal.WN.toC X) := by ring
  rw [hc, e, mul_neg, neg_div, mul_div_assoc, div_self hne, mul_one]
  have hθ : (((D.model.angleAt 1 + D.model.angleAt 0 + (t : ℝ) * D.model.angleAt 2 : ℝ)) : ℂ) =
      ((((t : ℝ) - 1) * D.model.angleAt 2 : ℝ) : ℂ) + (Real.pi : ℂ) := by
    have : D.model.angleAt 1 + D.model.angleAt 0 + (t : ℝ) * D.model.angleAt 2 =
        ((t : ℝ) - 1) * D.model.angleAt 2 + Real.pi := by
      simp only at hsum; linarith
    rw [this]; push_cast; ring
  rw [hθ, add_mul, Complex.exp_add, Complex.exp_pi_mul_I]
  ring

theorem arg_exp_real_mul_I {x : ℝ} (hx : x ∈ Set.Ioc (-Real.pi) Real.pi) : Complex.arg (Complex.exp ((x : ℂ) * Complex.I)) = x := by
  rw [Complex.exp_mul_I]
  exact Complex.arg_cos_add_sin_mul_I hx

/-- **`u = v + N` for a cycle of Gamma_kite** (Laczkovich, Lemma 6.2): `rho * gamma * sum_k (t_k - 1) = 2 pi`, `t_k in {0,1,2}`, `rho = +-1`. -/
theorem gkite_cycle_count [NeZero N] [NeZero M] (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hC : CaseC D idx)
    (h1 : D.model.angleAt 2 < Real.pi / 2) (h3 : D.model.angleAt 2 ≠ Real.pi / 3) (G : AngGen (fun l => D.model.angleAt l))
    {m : ℕ} [NeZero m] (C : Fin m → Plane) (hCy : ∀ k : Fin m, GKite D idx (C k) (C (k + 1))) (hinj : Function.Injective C) :
    3 ≤ m ∧ ∃ ρ : ℝ, (ρ = 1 ∨ ρ = -1) ∧ ∃ t : Fin m → ℕ, (∀ k, t k ≤ 2) ∧
      ρ * D.model.angleAt 2 * ∑ k : Fin m, (((t k : ℕ) : ℝ) - 1) = 2 * Real.pi := by
  obtain ⟨hm, hs⟩ := gkite_cycle_simple D idx C hCy hinj
  have hsC := (Erdos634.Draft.LaczFormal.WN.simplePolyP_iff C).1 hs
  have hinjC : Function.Injective (fun k => Erdos634.Draft.LaczFormal.WN.toC (C k)) :=
    fun a b h => hinj (Erdos634.Draft.LaczFormal.WN.toC.injective h)
  obtain ⟨ρ, hρ, -, hsum⟩ := Erdos634.Draft.LaczFormal.WN.interior_angle_sum hsC hinjC hm
  have hγ0 : 0 < D.model.angleAt 2 := G.pos 2
  have hk : ∀ k : Fin m, ∃ t : ℕ, t ≤ 2 ∧ Erdos634.Draft.LaczFormal.WN.extAng (fun k => Erdos634.Draft.LaczFormal.WN.toC (C k)) k =
      ((t : ℝ) - 1) * D.model.angleAt 2 := by
    intro k
    have hXY : GKite D idx (C (k - 1)) (C k) := by simpa using hCy (k - 1)
    obtain ⟨t, ht, hr⟩ := gkite_ratio D P hreg idx hC h1 h3 G hXY (hCy k)
    refine ⟨t, ht, ?_⟩
    unfold Erdos634.Draft.LaczFormal.WN.extAng
    simp only
    rw [hr]
    apply arg_exp_real_mul_I
    have ht' : (t : ℝ) ≤ 2 := by exact_mod_cast ht
    have ht0 : (0 : ℝ) ≤ t := Nat.cast_nonneg t
    have hpi := Real.pi_pos
    constructor <;> nlinarith
  choose t ht he using hk
  refine ⟨hm, ρ, hρ, t, ht, ?_⟩
  have : ∑ k : Fin m, (Real.pi - ρ * Erdos634.Draft.LaczFormal.WN.extAng (fun k => Erdos634.Draft.LaczFormal.WN.toC (C k)) k) =
      m * Real.pi - ρ * D.model.angleAt 2 * ∑ k : Fin m, (((t k : ℕ) : ℝ) - 1) := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    simp only [he, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    congr 1
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun k _ => by ring)
  rw [this] at hsum
  linarith

end Erdos634.Draft.LaczFormal.RG
