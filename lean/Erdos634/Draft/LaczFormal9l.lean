import Erdos634.Draft.LaczFormalRG4Geo
import Erdos634.Draft.LaczFormalRG4AngleSum
import Erdos634.Draft.LaczFormalRGCaseVb

/-!
# A strictly convex equiangular `2k`-gon with equal opposite sides is centrally symmetric

NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Thm 2.1 (v), (vi): "centrally symmetric"; used in Thm 2.4), Beeson-Zhang.
Formalization debt, not progress on the /goal outcomes.

For `P : ConvPoly M` with all interior angles `theta` (so, by the angle sum, `M theta = (M - 2) pi`), `M = 2 k` and `side i = side (i + k)`:
the edge vectors satisfy `e_{i+k} = - e_i` (the direction turns by the exterior angle `phi = pi - theta` at every vertex, `k phi = pi`,
and `|e_{i+k}| = |e_i|`), so `v_{i+k} + v_i` is constant and the carrier is symmetric about `c = (v_0 + v_k)/2`.

* `CentSym P`: `exists c, forall x in P.carrier, 2 c - x in P.carrier` (central symmetry of the polygon).
* `csym_of_equiangular`: the statement above.
-/

open scoped Classical
open Erdos634.Geometry Erdos634.CertCoord Erdos634.Draft.LaczFormal.Thm21 Erdos634.Draft.LaczFormal.RG

namespace Erdos634.Laczkovich9

variable {M : ℕ} [NeZero M]

/-- Central symmetry of the polygon. -/
def CentSym (P : ConvPoly M) : Prop := ∃ c : Plane, ∀ x ∈ P.carrier, (2 : ℝ) • c - x ∈ P.carrier

/-- Rotation of the plane by `phi`. -/
noncomputable def rot (φ : ℝ) (x : Plane) : Plane :=
  mkPt (Real.cos φ * x 0 - Real.sin φ * x 1) (Real.sin φ * x 0 + Real.cos φ * x 1)

@[simp] theorem rot_0 (φ : ℝ) (x : Plane) : rot φ x 0 = Real.cos φ * x 0 - Real.sin φ * x 1 := by simp [rot]
@[simp] theorem rot_1 (φ : ℝ) (x : Plane) : rot φ x 1 = Real.sin φ * x 0 + Real.cos φ * x 1 := by simp [rot]

theorem rot_add (α β : ℝ) (x : Plane) : rot α (rot β x) = rot (α + β) x := by
  ext i; fin_cases i
  · simp [Real.cos_add, Real.sin_add]; ring
  · simp [Real.cos_add, Real.sin_add]; ring

theorem rot_smul (α c : ℝ) (x : Plane) : rot α (c • x) = c • rot α x := by
  ext i; fin_cases i
  · simp; ring
  · simp; ring

theorem rot_zero (x : Plane) : rot 0 x = x := by
  ext i; fin_cases i <;> simp

theorem rot_pi (x : Plane) : rot Real.pi x = -x := by
  ext i; fin_cases i <;> simp

/-- **The next edge is the rotated previous edge**, scaled by the ratio of lengths: the exterior angle at `v_i` is `pi - theta`. -/
theorem next_edge (P : ConvPoly M) (i : Fin M) :
    P.e i = (‖P.e i‖ / ‖P.e (i - 1)‖) • rot (Real.pi - P.angle i) (P.e (i - 1)) := by
  obtain ⟨hc, hd⟩ := turn_of_angle P i
  have hLpos : 0 < ‖P.e (i - 1)‖ := norm_pos_iff.mpr (P.e_ne_zero P.three_le _)
  have hL2 : ‖P.e (i - 1)‖ ^ 2 = P.e (i - 1) 0 ^ 2 + P.e (i - 1) 1 ^ 2 := norm_sq_plane _
  rw [inner_plane] at hd
  unfold cross2 at hc
  have w0 : P.e i 0 = (‖P.e i‖ / ‖P.e (i - 1)‖) *
      (-Real.cos (P.angle i) * P.e (i - 1) 0 - Real.sin (P.angle i) * P.e (i - 1) 1) := by
    have h1 : ‖P.e (i - 1)‖ ^ 2 * P.e i 0 = P.e (i - 1) 0 * (-(‖P.e (i - 1)‖ * ‖P.e i‖ * Real.cos (P.angle i))) -
        P.e (i - 1) 1 * (‖P.e (i - 1)‖ * ‖P.e i‖ * Real.sin (P.angle i)) := by
      have : (P.e (i - 1) 0 ^ 2 + P.e (i - 1) 1 ^ 2) * P.e i 0 =
          P.e (i - 1) 0 * (P.e (i - 1) 0 * P.e i 0 + P.e (i - 1) 1 * P.e i 1) -
            P.e (i - 1) 1 * (P.e (i - 1) 0 * P.e i 1 - P.e (i - 1) 1 * P.e i 0) := by ring
      rw [hL2, this, hd, hc]
    field_simp
    nlinarith [h1]
  have w1 : P.e i 1 = (‖P.e i‖ / ‖P.e (i - 1)‖) *
      (Real.sin (P.angle i) * P.e (i - 1) 0 - Real.cos (P.angle i) * P.e (i - 1) 1) := by
    have h1 : ‖P.e (i - 1)‖ ^ 2 * P.e i 1 = P.e (i - 1) 1 * (-(‖P.e (i - 1)‖ * ‖P.e i‖ * Real.cos (P.angle i))) +
        P.e (i - 1) 0 * (‖P.e (i - 1)‖ * ‖P.e i‖ * Real.sin (P.angle i)) := by
      have : (P.e (i - 1) 0 ^ 2 + P.e (i - 1) 1 ^ 2) * P.e i 1 =
          P.e (i - 1) 1 * (P.e (i - 1) 0 * P.e i 0 + P.e (i - 1) 1 * P.e i 1) +
            P.e (i - 1) 0 * (P.e (i - 1) 0 * P.e i 1 - P.e (i - 1) 1 * P.e i 0) := by ring
      rw [hL2, this, hd, hc]
    field_simp
    nlinarith [h1]
  ext j; fin_cases j
  · show P.e i 0 = ((‖P.e i‖ / ‖P.e (i - 1)‖) • rot (Real.pi - P.angle i) (P.e (i - 1))) 0
    rw [PiLp.smul_apply, smul_eq_mul, rot_0, Real.cos_pi_sub, Real.sin_pi_sub, w0] <;> ring
  · show P.e i 1 = ((‖P.e i‖ / ‖P.e (i - 1)‖) • rot (Real.pi - P.angle i) (P.e (i - 1))) 1
    rw [PiLp.smul_apply, smul_eq_mul, rot_1, Real.cos_pi_sub, Real.sin_pi_sub, w1] <;> ring

theorem ofNat_succ (m : ℕ) : (Fin.ofNat M (m + 1) : Fin M) = Fin.ofNat M m + 1 := by
  apply Fin.ext
  rw [Fin.val_add]
  simp [Fin.val_ofNat, fin_val_one, Nat.add_mod]

/-- Iterating `next_edge`: `e_{i+m} = (|e_{i+m}| / |e_i|) rot(m phi) e_i`, all angles equal `theta`. -/
theorem edge_iter (P : ConvPoly M) (θ : ℝ) (hang : ∀ j, P.angle j = θ) (i : Fin M) (m : ℕ) :
    P.e (i + Fin.ofNat M m) = (‖P.e (i + Fin.ofNat M m)‖ / ‖P.e i‖) • rot ((m : ℝ) * (Real.pi - θ)) (P.e i) := by
  have hnz : ∀ j : Fin M, ‖P.e j‖ ≠ 0 := fun j => (norm_pos_iff.mpr (P.e_ne_zero P.three_le j)).ne'
  induction m with
  | zero =>
    have h0 : (Fin.ofNat M 0 : Fin M) = 0 := Fin.ext (by simp [Fin.val_ofNat])
    rw [h0, add_zero]
    simp [rot_zero, div_self (hnz i)]
  | succ m ih =>
    have hs : i + Fin.ofNat M (m + 1) = (i + Fin.ofNat M m) + 1 := by rw [ofNat_succ, add_assoc]
    set a := i + Fin.ofNat M m with ha
    have hn : P.e (a + 1) = (‖P.e (a + 1)‖ / ‖P.e a‖) • rot (Real.pi - θ) (P.e a) := by
      have := next_edge P (a + 1)
      rwa [hang, add_sub_cancel_right] at this
    have hr := congrArg (rot (Real.pi - θ)) ih
    rw [hs]
    calc P.e (a + 1) = (‖P.e (a + 1)‖ / ‖P.e a‖) • rot (Real.pi - θ) (P.e a) := hn
      _ = (‖P.e (a + 1)‖ / ‖P.e a‖) • rot (Real.pi - θ) ((‖P.e a‖ / ‖P.e i‖) • rot ((m : ℝ) * (Real.pi - θ)) (P.e i)) := by
          rw [← ih]
      _ = (‖P.e (a + 1)‖ / ‖P.e i‖) • rot (((m + 1 : ℕ) : ℝ) * (Real.pi - θ)) (P.e i) := by
          rw [rot_smul, rot_add, smul_smul]
          have hna := hnz a
          have : (‖P.e (a + 1)‖ / ‖P.e a‖) * (‖P.e a‖ / ‖P.e i‖) = ‖P.e (a + 1)‖ / ‖P.e i‖ := by
            field_simp
          rw [this]
          congr 2
          push_cast; ring

/-- **`e_{i+k} = - e_i`** for an equiangular polygon with `k (pi - theta) = pi` and `|e_{i+k}| = |e_i|`. -/
theorem edge_opposite (P : ConvPoly M) (θ : ℝ) (hang : ∀ j, P.angle j = θ) (k : ℕ) (hk : (k : ℝ) * (Real.pi - θ) = Real.pi)
    (hside : ∀ i, P.side i = P.side (i + Fin.ofNat M k)) (i : Fin M) :
    P.e (i + Fin.ofNat M k) = -P.e i := by
  have h := edge_iter P θ hang i k
  have hn : ‖P.e (i + Fin.ofNat M k)‖ = ‖P.e i‖ := by
    have e1 : ∀ j, ‖P.e j‖ = P.side j := by
      intro j; unfold ConvPoly.e ConvPoly.side; rw [dist_comm, dist_eq_norm]
    rw [e1, e1, ← hside]
  have hnz : ‖P.e i‖ ≠ 0 := (norm_pos_iff.mpr (P.e_ne_zero P.three_le i)).ne'
  rw [hk, hn, div_self hnz, one_smul, rot_pi] at h
  exact h

/-- `v_{i+k} + v_i` is constant. -/
theorem sum_const (P : ConvPoly M) (K : Fin M) (hopp : ∀ i, P.e (i + K) = -P.e i) (i : Fin M) :
    P.v (i + K) + P.v i = P.v K + P.v 0 := by
  have step : ∀ j : Fin M, P.v (j + 1 + K) + P.v (j + 1) = P.v (j + K) + P.v j := by
    intro j
    have h := hopp j
    unfold ConvPoly.e at h
    have e1 : j + 1 + K = j + K + 1 := add_right_comm j 1 K
    rw [e1]
    have : P.v (j + K + 1) - P.v (j + K) = -(P.v (j + 1) - P.v j) := h
    have h2 : P.v (j + K + 1) + P.v (j + 1) = P.v (j + K) + P.v j := by
      have := congrArg (fun x => x + P.v (j + K) + P.v (j + 1)) this
      simp only at this
      rw [sub_add_cancel] at this
      linear_combination (norm := module) this
    exact h2
  have key : ∀ n : ℕ, P.v (Fin.ofNat M n + K) + P.v (Fin.ofNat M n) = P.v K + P.v 0 := by
    intro n
    induction n with
    | zero =>
      have h0 : (Fin.ofNat M 0 : Fin M) = 0 := Fin.ext (by simp [Fin.val_ofNat])
      rw [h0, zero_add]
    | succ n ih => rw [ofNat_succ, step, ih]
  have : (Fin.ofNat M i.val : Fin M) = i := Fin.ext (by simp [Fin.val_ofNat, Nat.mod_eq_of_lt i.isLt])
  have := key i.val
  rwa [‹(Fin.ofNat M i.val : Fin M) = i›] at this

theorem csym_of_opp (P : ConvPoly M) (K : Fin M) (hopp : ∀ i, P.e (i + K) = -P.e i)
    (hv : ∀ i, P.v (i + K) + P.v i = P.v K + P.v 0) : CentSym P := by
  refine ⟨(1 / 2 : ℝ) • (P.v K + P.v 0), fun x hx j => ?_⟩
  have hxj := hx (j + K)
  have e1 : (2 : ℝ) • ((1 / 2 : ℝ) • (P.v K + P.v 0)) = P.v K + P.v 0 := by rw [smul_smul]; norm_num
  have hvj : P.v j = P.v K + P.v 0 - P.v (j + K) := by rw [← hv j]; abel
  have hej : P.e j = -P.e (j + K) := by rw [hopp]; simp
  rw [e1]
  set c2 := P.v K + P.v 0 with hc2
  -- the j-th edge constraint at y = c2 - x equals the (j+K)-th constraint at x
  have hrel : cross2 (P.e j) (c2 - x - P.v j) = cross2 (P.e (j + K)) (x - P.v (j + K)) := by
    have a : c2 - x - P.v j = -(x - P.v (j + K)) := by rw [hvj]; abel
    rw [a, hej]
    unfold cross2; simp; ring
  show 0 ≤ cross2 (P.e j) (c2 - x - P.v j)
  rw [hrel]; exact hxj

/-- **A strictly convex equiangular `2k`-gon with equal opposite sides is centrally symmetric.** -/
theorem csym_of_equiangular (P : ConvPoly M) (k : ℕ) (hM : M = 2 * k) (hang : ∀ i, P.angle i = P.angle 0)
    (hside : ∀ i, P.side i = P.side (i + Fin.ofNat M k)) : CentSym P := by
  have hpi := Real.pi_pos
  have hM3 : 3 ≤ M := P.three_le
  have hsum := poly_angle_sum P
  have hconst : ∑ i : Fin M, P.angle i = M * P.angle 0 := by
    rw [Finset.sum_congr rfl (fun i _ => hang i)]; simp
  have hcast : (((M - 2 : ℕ) : ℝ)) = (M : ℝ) - 2 := by
    rw [Nat.cast_sub (by omega)]; norm_num
  rw [hconst, hcast] at hsum
  have hMR : (M : ℝ) = 2 * k := by rw [hM]; push_cast; ring
  have hk : (k : ℝ) * (Real.pi - P.angle 0) = Real.pi := by
    rw [hMR] at hsum
    nlinarith [hsum]
  have hopp := edge_opposite P (P.angle 0) hang k hk hside
  have hv := sum_const P (Fin.ofNat M k) hopp
  exact csym_of_opp P (Fin.ofNat M k) hopp hv

end Erdos634.Laczkovich9

#print axioms Erdos634.Laczkovich9.next_edge
#print axioms Erdos634.Laczkovich9.edge_opposite
#print axioms Erdos634.Laczkovich9.csym_of_equiangular
