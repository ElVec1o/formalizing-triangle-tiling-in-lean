-- Draft/LaczFormalRG4AngleSum.lean -- the angle sum of a strictly convex polygon: `sum_i angle_i = (M-2) pi`.  (Fan triangulation from `v_0`; additivity of the unoriented angle for three vectors in
-- strictly positive angular order, proved by cosine/sine addition from the 2D identities.)  No hypothesis beyond `ConvPoly`.
-- UNAUDITED.  Credit: classical; the project's `abs_cross2` (Thm21Area) is used.
import Erdos634.Draft.LaczFormalThm21Def

open scoped Classical Fin.NatCast Fin.CommRing
open Erdos634.Geometry Erdos634.Draft.LaczFormal.Thm21

namespace Erdos634.Draft.LaczFormal.RG

/-- **Additivity of the angle**: if `x, y, z` are in strictly counterclockwise order (`cross x y, cross y z, cross x z > 0`) then `∠(x,z) = ∠(x,y) + ∠(y,z)`. -/
theorem angle_add_of_cross (x y z : Plane) (h1 : 0 < cross2 x y) (h2 : 0 < cross2 y z) (h3 : 0 < cross2 x z) :
    InnerProductGeometry.angle x z = InnerProductGeometry.angle x y + InnerProductGeometry.angle y z := by
  have hx : x ≠ 0 := by rintro rfl; simp [cross2] at h1
  have hy : y ≠ 0 := by rintro rfl; simp [cross2] at h1
  have hz : z ≠ 0 := by rintro rfl; simp [cross2] at h2
  have nx := norm_pos_iff.mpr hx
  have ny := norm_pos_iff.mpr hy
  have nz := norm_pos_iff.mpr hz
  set A := InnerProductGeometry.angle x y with hA
  set B := InnerProductGeometry.angle y z with hB
  set C := InnerProductGeometry.angle x z with hC
  have cA := InnerProductGeometry.cos_angle_mul_norm_mul_norm x y
  have cB := InnerProductGeometry.cos_angle_mul_norm_mul_norm y z
  have cC := InnerProductGeometry.cos_angle_mul_norm_mul_norm x z
  have sA := abs_cross2 x y
  have sB := abs_cross2 y z
  have sC := abs_cross2 x z
  rw [abs_of_pos h1] at sA
  rw [abs_of_pos h2] at sB
  rw [abs_of_pos h3] at sC
  rw [inner_plane] at cA cB cC
  rw [← hA] at cA sA
  rw [← hB] at cB sB
  rw [← hC] at cC sC
  have hnx : ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 := norm_sq_plane x
  have hny : ‖y‖ ^ 2 = y 0 ^ 2 + y 1 ^ 2 := norm_sq_plane y
  have hnz : ‖z‖ ^ 2 = z 0 ^ 2 + z 1 ^ 2 := norm_sq_plane z
  -- sin A, sin B > 0, so A, B in (0, pi)
  have sApos : 0 < Real.sin A := by
    have : 0 < ‖x‖ * ‖y‖ * Real.sin A := by rw [← sA]; exact h1
    exact (pos_iff_pos_of_mul_pos this |>.mp (by positivity))
  have sBpos : 0 < Real.sin B := by
    have : 0 < ‖y‖ * ‖z‖ * Real.sin B := by rw [← sB]; exact h2
    exact (pos_iff_pos_of_mul_pos this |>.mp (by positivity))
  have hA0 : 0 ≤ A := InnerProductGeometry.angle_nonneg x y
  have hApi : A ≤ Real.pi := InnerProductGeometry.angle_le_pi x y
  have hB0 : 0 ≤ B := InnerProductGeometry.angle_nonneg y z
  have hBpi : B ≤ Real.pi := InnerProductGeometry.angle_le_pi y z
  have hC0 : 0 ≤ C := InnerProductGeometry.angle_nonneg x z
  have hCpi : C ≤ Real.pi := InnerProductGeometry.angle_le_pi x z
  -- cos (A + B) = cos C
  have hcos : Real.cos (A + B) = Real.cos C := by
    rw [Real.cos_add]
    have key : (Real.cos A * Real.cos B - Real.sin A * Real.sin B) * (‖x‖ * ‖y‖ ^ 2 * ‖z‖) = Real.cos C * (‖x‖ * ‖z‖) * ‖y‖ ^ 2 := by
      have e1 : (Real.cos A * (‖x‖ * ‖y‖)) * (Real.cos B * (‖y‖ * ‖z‖)) - (‖x‖ * ‖y‖ * Real.sin A) * (‖y‖ * ‖z‖ * Real.sin B)
          = ((Real.cos A * Real.cos B - Real.sin A * Real.sin B) * (‖x‖ * ‖y‖ ^ 2 * ‖z‖)) := by ring
      rw [← e1, cA, cB, ← sA, ← sB, cC]
      unfold cross2
      have : (x 0 * y 0 + x 1 * y 1) * (y 0 * z 0 + y 1 * z 1) - (x 0 * y 1 - x 1 * y 0) * (y 0 * z 1 - y 1 * z 0)
          = (y 0 ^ 2 + y 1 ^ 2) * (x 0 * z 0 + x 1 * z 1) := by ring
      rw [this, hny]; ring
    have hne : ‖x‖ * ‖y‖ ^ 2 * ‖z‖ ≠ 0 := by positivity
    apply mul_right_cancel₀ hne
    rw [key]
    have : Real.cos C * (‖x‖ * ‖z‖) * ‖y‖ ^ 2 = Real.cos C * (‖x‖ * ‖y‖ ^ 2 * ‖z‖) := by ring
    rw [this]
  -- sin (A + B) > 0
  have hsin : 0 < Real.sin (A + B) := by
    rw [Real.sin_add]
    have key : (Real.sin A * Real.cos B + Real.cos A * Real.sin B) * (‖x‖ * ‖y‖ ^ 2 * ‖z‖) = (‖x‖ * ‖z‖ * Real.sin C) * ‖y‖ ^ 2 := by
      have e1 : (‖x‖ * ‖y‖ * Real.sin A) * (Real.cos B * (‖y‖ * ‖z‖)) + (Real.cos A * (‖x‖ * ‖y‖)) * (‖y‖ * ‖z‖ * Real.sin B)
          = (Real.sin A * Real.cos B + Real.cos A * Real.sin B) * (‖x‖ * ‖y‖ ^ 2 * ‖z‖) := by ring
      rw [← e1, cA, cB, ← sA, ← sB, ← sC]
      unfold cross2
      have : (x 0 * y 1 - x 1 * y 0) * (y 0 * z 0 + y 1 * z 1) + (x 0 * y 0 + x 1 * y 1) * (y 0 * z 1 - y 1 * z 0)
          = (y 0 ^ 2 + y 1 ^ 2) * (x 0 * z 1 - x 1 * z 0) := by ring
      rw [this, ← hny]; ring
    have hpos : 0 < (‖x‖ * ‖z‖ * Real.sin C) * ‖y‖ ^ 2 := by
      have : 0 < ‖x‖ * ‖z‖ * Real.sin C := by rw [← sC]; exact h3
      positivity
    have hne : 0 < ‖x‖ * ‖y‖ ^ 2 * ‖z‖ := by positivity
    rw [← key] at hpos
    exact (pos_iff_pos_of_mul_pos hpos |>.mpr hne)
  have hlt : A + B < Real.pi := by
    by_contra hnot
    push Not at hnot
    have h2pi : A + B ≤ 2 * Real.pi := by linarith
    have : Real.sin (A + B) ≤ 0 := by
      have e : Real.sin (A + B) = - Real.sin (A + B - Real.pi) := by rw [Real.sin_sub_pi]; ring
      rw [e]
      have : 0 ≤ Real.sin (A + B - Real.pi) := Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
      linarith
    linarith
  have hAB0 : 0 ≤ A + B := by linarith
  exact (Real.injOn_cos ⟨hC0, hCpi⟩ ⟨hAB0, hlt.le⟩ hcos.symm)

section PolySum

variable {M : ℕ} [NeZero M] (P : ConvPoly M)

/-- The vertices indexed by naturals (cyclically). -/
noncomputable def vv (j : ℕ) : Plane := P.v (j : Fin M)

theorem cast_ne {M : ℕ} [NeZero M] {a b : ℕ} (ha : a < M) (hb : b < M) (h : a ≠ b) : (a : Fin M) ≠ (b : Fin M) := by
  intro e
  have := congrArg Fin.val e
  rw [Fin.val_natCast, Fin.val_natCast, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this
  exact h this

theorem vv_succ (j : ℕ) : vv P (j + 1) = P.v ((j : Fin M) + 1) := by
  unfold vv; rw [Nat.cast_succ]

/-- Left-of-edge condition in natural-number indexing. -/
theorem leftN {a b : ℕ} (ha : a + 1 < M) (hb : b < M) (h1 : b ≠ a) (h2 : b ≠ a + 1) :
    0 < cross2 (vv P (a + 1) - vv P a) (vv P b - vv P a) := by
  have := P.left (a : Fin M) (b : Fin M) (cast_ne hb (by omega) h1) (by
    rw [← Nat.cast_succ]; exact cast_ne hb ha h2)
  rw [vv_succ]
  unfold vv
  exact this

noncomputable def rr (j : ℕ) : Plane := vv P j - vv P 0
noncomputable def aa (j : ℕ) : ℝ := InnerProductGeometry.angle (rr P j) (rr P (j + 1))
noncomputable def bb (j : ℕ) : ℝ := InnerProductGeometry.angle (vv P 0 - vv P j) (vv P (j + 1) - vv P j)
noncomputable def cc (j : ℕ) : ℝ := InnerProductGeometry.angle (vv P j - vv P (j + 1)) (vv P 0 - vv P (j + 1))

theorem cross_cyc (p q s : Plane) : cross2 (q - p) (s - p) = cross2 (s - q) (p - q) := by
  unfold cross2; simp; ring

theorem F1 {j : ℕ} (h1 : 1 ≤ j) (h2 : j + 1 < M) : 0 < cross2 (rr P j) (rr P (j + 1)) := by
  have hM : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  have := leftN P (a := j) (b := 0) h2 (by omega) (by omega) (by omega)
  have e : cross2 (rr P j) (rr P (j + 1)) = cross2 (vv P (j + 1) - vv P j) (vv P 0 - vv P j) := by
    unfold rr cross2; simp; ring
  rw [e]; exact this

theorem F2 {j : ℕ} (h1 : 2 ≤ j) (h2 : j < M) : 0 < cross2 (rr P 1) (rr P j) := by
  have := leftN P (a := 0) (b := j) (by omega) h2 (by omega) (by omega)
  simpa [rr] using this

theorem sum_a : ∀ k : ℕ, 1 ≤ k → k + 1 < M →
    InnerProductGeometry.angle (rr P 1) (rr P (k + 1)) = ∑ j ∈ Finset.range k, InnerProductGeometry.angle (rr P (j + 1)) (rr P (j + 2)) := by
  intro k
  induction k with
  | zero => intro h; omega
  | succ k ih =>
    intro hk hk2
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · subst hk0; simp
    · rw [Finset.sum_range_succ, ← ih hk0 (by omega)]
      exact angle_add_of_cross (rr P 1) (rr P (k + 1)) (rr P (k + 1 + 1)) (F2 P (by omega) (by omega)) (F1 P (by omega) (by omega))
        (F2 P (by omega) (by omega))

/-- Triangle `(v_0, v_j, v_{j+1})`: its three angles add up to `π`. -/
theorem tri_sum {j : ℕ} (h1 : 1 ≤ j) (h2 : j + 1 < M) :
    InnerProductGeometry.angle (rr P j) (rr P (j + 1)) + InnerProductGeometry.angle (vv P 0 - vv P j) (vv P (j + 1) - vv P j) +
      InnerProductGeometry.angle (vv P j - vv P (j + 1)) (vv P 0 - vv P (j + 1)) = Real.pi := by
  have hc := F1 P h1 h2
  have hne1 : vv P j ≠ vv P 0 := by
    intro e
    have : rr P j = 0 := by unfold rr; rw [e]; simp
    rw [this] at hc; simp [cross2] at hc
  have hne2 : vv P (j + 1) ≠ vv P 0 := by
    intro e
    have : rr P (j + 1) = 0 := by unfold rr; rw [e]; simp
    rw [this] at hc; simp [cross2] at hc
  have := EuclideanGeometry.angle_add_angle_add_angle_eq_pi (p₁ := vv P 0) (p₂ := vv P j) (vv P (j + 1)) hne1
  unfold EuclideanGeometry.angle at this
  simp only [vsub_eq_sub] at this
  rw [InnerProductGeometry.angle_comm (rr P j)]
  have e : InnerProductGeometry.angle (vv P (j + 1) - vv P 0) (vv P j - vv P 0) = InnerProductGeometry.angle (rr P (j + 1)) (rr P j) := rfl
  rw [e] at this
  linarith

theorem angle_nat {n : ℕ} (h1 : 1 ≤ n) (h2 : n + 1 < M) :
    P.angle (n : Fin M) = InnerProductGeometry.angle (vv P (n - 1) - vv P n) (vv P (n + 1) - vv P n) := by
  unfold ConvPoly.angle cornerAngle EuclideanGeometry.angle
  simp only [vsub_eq_sub]
  have e1 : ((n - 1 : ℕ) : Fin M) = (n : Fin M) - 1 := by rw [Nat.cast_sub h1]; simp
  have e2 : P.v ((n : Fin M) - 1) = vv P (n - 1) := by unfold vv; rw [e1]
  have e3 : P.v ((n : Fin M) + 1) = vv P (n + 1) := (vv_succ P n).symm
  have e4 : P.v (n : Fin M) = vv P n := rfl
  rw [e2, e3, e4]

theorem angle_zero (hM : 3 ≤ M) :
    P.angle 0 = InnerProductGeometry.angle (vv P (M - 1) - vv P 0) (vv P 1 - vv P 0) := by
  unfold ConvPoly.angle cornerAngle EuclideanGeometry.angle
  simp only [vsub_eq_sub]
  have e1 : (((M - 1 : ℕ) : Fin M)) = (0 : Fin M) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  have e2 : P.v ((0 : Fin M) - 1) = vv P (M - 1) := by unfold vv; rw [e1]
  have e3 : P.v ((0 : Fin M) + 1) = vv P 1 := by unfold vv; simp
  have e4 : P.v (0 : Fin M) = vv P 0 := by unfold vv; simp
  rw [e2, e3, e4]

theorem angle_last (hM : 3 ≤ M) :
    P.angle ((M - 1 : ℕ) : Fin M) = InnerProductGeometry.angle (vv P (M - 2) - vv P (M - 1)) (vv P 0 - vv P (M - 1)) := by
  unfold ConvPoly.angle cornerAngle EuclideanGeometry.angle
  simp only [vsub_eq_sub]
  have e1 : (((M - 2 : ℕ) : Fin M)) = ((M - 1 : ℕ) : Fin M) - 1 := by
    rw [show M - 2 = (M - 1) - 1 by omega, Nat.cast_sub (by omega)]; simp
  have e2 : P.v (((M - 1 : ℕ) : Fin M) - 1) = vv P (M - 2) := by unfold vv; rw [e1]
  have e3 : P.v (((M - 1 : ℕ) : Fin M) + 1) = vv P 0 := by
    unfold vv
    have : ((M - 1 : ℕ) : Fin M) + 1 = 0 := by
      rw [← Nat.cast_succ, Nat.succ_eq_add_one, show M - 1 + 1 = M by omega]; simp
    rw [this]; simp
  have e4 : P.v ((M - 1 : ℕ) : Fin M) = vv P (M - 1) := rfl
  rw [e2, e3, e4]

theorem ang_mid {k : ℕ} (h1 : 1 ≤ k) (h2 : k + 2 < M) :
    P.angle ((k + 1 : ℕ) : Fin M) = InnerProductGeometry.angle (vv P k - vv P (k + 1)) (vv P 0 - vv P (k + 1)) +
      InnerProductGeometry.angle (vv P 0 - vv P (k + 1)) (vv P (k + 1 + 1) - vv P (k + 1)) := by
  have hM : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  rw [angle_nat P (by omega) (by omega)]
  simp only [Nat.add_sub_cancel]
  set x := vv P (k + 1 + 1) - vv P (k + 1) with hx
  set y := vv P 0 - vv P (k + 1) with hy
  set z := vv P k - vv P (k + 1) with hz
  have cxy : 0 < cross2 x y := by
    have := leftN P (a := k + 1) (b := 0) (by omega) (by omega) (by omega) (by omega)
    exact this
  have cyz : 0 < cross2 y z := by
    have := leftN P (a := k) (b := 0) (by omega) (by omega) (by omega) (by omega)
    rw [cross_cyc] at this
    exact this
  have cxz : 0 < cross2 x z := by
    have := leftN P (a := k) (b := k + 2) (by omega) (by omega) (by omega) (by omega)
    rw [cross_cyc] at this
    exact this
  have hadd := angle_add_of_cross x y z cxy cyz cxz
  calc InnerProductGeometry.angle z x = InnerProductGeometry.angle x z := InnerProductGeometry.angle_comm z x
    _ = InnerProductGeometry.angle x y + InnerProductGeometry.angle y z := hadd
    _ = InnerProductGeometry.angle z y + InnerProductGeometry.angle y x := by
      rw [InnerProductGeometry.angle_comm x y, InnerProductGeometry.angle_comm y z]; ring

theorem angle_one (h : 2 < M) : P.angle ((1 : ℕ) : Fin M) = InnerProductGeometry.angle (vv P 0 - vv P 1) (vv P (1 + 1) - vv P 1) := by
  have := angle_nat P (n := 1) (by omega) (by omega)
  simpa using this

/-- **The angle sum of a strictly convex polygon**: `∑ angle_i = (M-2) π`. -/
theorem poly_angle_sum (P : ConvPoly M) : ∑ i : Fin M, P.angle i = ((M - 2 : ℕ) : ℝ) * Real.pi := by
  have hM3 : 3 ≤ M := P.three_le
  obtain ⟨L, rfl⟩ : ∃ L, M = L + 2 := ⟨M - 2, by omega⟩
  have hL1 : 1 ≤ L := by omega
  simp only [Nat.add_sub_cancel]
  set ang : ℕ → ℝ := fun n => P.angle (n : Fin (L + 2)) with hang
  have hsum : ∑ i : Fin (L + 2), P.angle i = ∑ n ∈ Finset.range (L + 2), ang n := by
    rw [← Fin.sum_univ_eq_sum_range ang]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [hang, Fin.cast_val_eq_self]
  rw [hsum, Finset.sum_range_succ', Finset.sum_range_succ]
  -- the pieces
  have a_zero : ang 0 = ∑ n ∈ Finset.range L, aa P (n + 1) := by
    simp only [hang, Nat.cast_zero]
    rw [angle_zero P hM3, InnerProductGeometry.angle_comm]
    have := sum_a P L hL1 (by omega)
    simpa [aa, rr, show L + 2 - 1 = L + 1 by omega] using this
  have a_one : ang 1 = bb P 1 := by
    simp only [hang, Nat.cast_one]
    have := angle_one P (M := L + 2) (by omega)
    simpa [bb] using this
  have a_mid : ∀ k, 1 ≤ k → k < L → ang (k + 1) = cc P k + bb P (k + 1) := by
    intro k hk1 hk2
    simp only [hang]
    exact ang_mid P hk1 (by omega)
  have a_last : ang (L + 1) = cc P L := by
    simp only [hang]
    have := angle_last P hM3
    simpa [cc, show L + 2 - 1 = L + 1 by omega, show L + 2 - 2 = L by omega] using this
  have key : ∀ k, 1 ≤ k → k ≤ L → ∑ n ∈ Finset.range k, ang (n + 1) + cc P k = ∑ n ∈ Finset.range k, (bb P (n + 1) + cc P (n + 1)) := by
    intro k
    induction k with
    | zero => intro h; omega
    | succ k ih =>
      intro hk1 hk2
      rcases Nat.eq_zero_or_pos k with hk0 | hk0
      · subst hk0
        simp [a_one]
      · rw [Finset.sum_range_succ, Finset.sum_range_succ (fun n => bb P (n + 1) + cc P (n + 1))]
        have := ih hk0 (by omega)
        rw [a_mid k hk0 (by omega)]
        linarith
  have hk := key L hL1 le_rfl
  have htri : ∑ n ∈ Finset.range L, (aa P (n + 1) + bb P (n + 1) + cc P (n + 1)) = ∑ n ∈ Finset.range L, Real.pi := by
    refine Finset.sum_congr rfl (fun n hn => ?_)
    have hn' := Finset.mem_range.mp hn
    exact tri_sum P (j := n + 1) (by omega) (by omega)
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at htri
  rw [a_zero, a_last]
  have e1 : ∑ n ∈ Finset.range L, (aa P (n + 1) + bb P (n + 1) + cc P (n + 1)) =
      ∑ n ∈ Finset.range L, aa P (n + 1) + ∑ n ∈ Finset.range L, (bb P (n + 1) + cc P (n + 1)) := by
    rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl (fun n _ => ?_); ring
  linarith

end PolySum


end Erdos634.Draft.LaczFormal.RG
