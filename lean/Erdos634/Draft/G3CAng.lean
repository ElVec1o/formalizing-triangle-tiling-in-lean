-- Draft/G3CAng.lean — G3C (room FINISH, seat HILBERT). UNAUDITED. No sorry/native_decide/axioms.
-- Generic angle/side bookkeeping for lattice certificates (G3CCert) and the 2π/3 / π/3 tile data.
import Erdos634.Draft.G3CCert
import Erdos634.Draft.FluxPaperWitness
import Erdos634.Draft.TheoremPConditional

open scoped Classical

namespace Erdos634.Draft.G3CAng

open Erdos634.Geometry Erdos634.Draft.G3CCert Erdos634.Draft.TheoremPConditional
open Erdos634.Draft.FluxPaperWitness (cos_cornerAngle' cornerAngle_mem')

theorem dist_toPt_nat (p q : LP) (s : ℕ) (h : d2 p q = (s : ℤ) ^ 2) :
    dist (toPt p) (toPt q) = (s : ℝ) := by
  have h1 := dist_sq_toPt p q
  rw [h] at h1
  push_cast at h1
  exact (pow_left_inj₀ dist_nonneg (Nat.cast_nonneg s) two_ne_zero).mp h1

theorem oppLen_triOf (t : LT) (h : 0 < cross t.1 t.2.1 t.2.2) (k : Fin 3) :
    (triOf t h).oppLen k = dist (toPt (vtx t (k + 1))) (toPt (vtx t (k + 2))) := by
  unfold Tri.oppLen
  rw [triOf_pts, triOf_pts]

theorem oppLen_pos (T : Tri) (k : Fin 3) : 0 ≤ T.oppLen k := dist_nonneg

theorem cos_angleAt_opp (T : Tri) (j : Fin 3) (h1 : 0 < T.oppLen (j + 1)) (h2 : 0 < T.oppLen (j + 2)) :
    Real.cos (T.angleAt j) =
      (T.oppLen (j + 1) ^ 2 + T.oppLen (j + 2) ^ 2 - T.oppLen j ^ 2) / (2 * T.oppLen (j + 1) * T.oppLen (j + 2)) := by
  have key : ∀ p q r : Plane, 0 < dist q r → 0 < dist p q → 
      Real.cos (cornerAngle p q r) = (dist q r ^ 2 + dist p q ^ 2 - dist p r ^ 2) / (2 * dist q r * dist p q) := by
    intro p q r hqr hpq
    have hp : p ≠ q := dist_pos.mp hpq
    have hr : r ≠ q := by intro e; rw [e, dist_self] at hqr; exact lt_irrefl _ hqr
    rw [cos_cornerAngle' hp hr, dist_comm r q]
    have : dist q r = dist r q := dist_comm q r
    rw [this]; ring_nf
  have c01 : dist (T.pts 1) (T.pts 0) = dist (T.pts 0) (T.pts 1) := dist_comm _ _
  have c02 : dist (T.pts 2) (T.pts 0) = dist (T.pts 0) (T.pts 2) := dist_comm _ _
  have c12 : dist (T.pts 2) (T.pts 1) = dist (T.pts 1) (T.pts 2) := dist_comm _ _
  fin_cases j <;> simp only [Tri.angleAt, Tri.oppLen] at h1 h2 ⊢ <;>
    simp only [show (0:Fin 3) + 1 = 1 from rfl, show (0:Fin 3) + 2 = 2 from rfl,
      show (1:Fin 3) + 1 = 2 from rfl, show (1:Fin 3) + 2 = 0 from rfl,
      show (2:Fin 3) + 1 = 0 from rfl, show (2:Fin 3) + 2 = 1 from rfl,
      Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] at h1 h2 ⊢
  · rw [key (T.pts 1) (T.pts 0) (T.pts 2) (by rwa [dist_comm]) (by rwa [c01, dist_comm] at *), c01, dist_comm (T.pts 0) (T.pts 2), c02]
  · rw [key (T.pts 2) (T.pts 1) (T.pts 0) (by rwa [dist_comm]) (by rwa [c12, dist_comm] at *), c12, c01]
  · rw [key (T.pts 0) (T.pts 2) (T.pts 1) (by rwa [dist_comm]) (by rwa [c02, dist_comm] at *), c02, c12]


theorem angle_eq_of_cos {T U : Tri} (j k : Fin 3) (h : Real.cos (T.angleAt j) = Real.cos (U.angleAt k)) :
    T.angleAt j = U.angleAt k :=
  Real.injOn_cos (cornerAngle_mem' _ _ _) (cornerAngle_mem' _ _ _) h

theorem perm_cases (σ : Equiv.Perm (Fin 3)) :
    ((σ 0 + 1 = σ 1 ∧ σ 0 + 2 = σ 2) ∨ (σ 0 + 1 = σ 2 ∧ σ 0 + 2 = σ 1)) ∧
    ((σ 1 + 1 = σ 0 ∧ σ 1 + 2 = σ 2) ∨ (σ 1 + 1 = σ 2 ∧ σ 1 + 2 = σ 0)) ∧
    ((σ 2 + 1 = σ 0 ∧ σ 2 + 2 = σ 1) ∨ (σ 2 + 1 = σ 1 ∧ σ 2 + 2 = σ 0)) := by
  revert σ; decide

theorem cos_s0 (T : Tri) (σ : Equiv.Perm (Fin 3)) (h1 : 0 < T.oppLen (σ 1)) (h2 : 0 < T.oppLen (σ 2)) :
    Real.cos (T.angleAt (σ 0)) =
      (T.oppLen (σ 1) ^ 2 + T.oppLen (σ 2) ^ 2 - T.oppLen (σ 0) ^ 2) / (2 * T.oppLen (σ 1) * T.oppLen (σ 2)) := by
  rcases (perm_cases σ).1 with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · have := cos_angleAt_opp T (σ 0) (by rw [e1]; exact h1) (by rw [e2]; exact h2)
    rw [e1, e2] at this; exact this
  · have := cos_angleAt_opp T (σ 0) (by rw [e1]; exact h2) (by rw [e2]; exact h1)
    rw [e1, e2] at this; rw [this]; ring

theorem cos_s1 (T : Tri) (σ : Equiv.Perm (Fin 3)) (h0 : 0 < T.oppLen (σ 0)) (h2 : 0 < T.oppLen (σ 2)) :
    Real.cos (T.angleAt (σ 1)) =
      (T.oppLen (σ 0) ^ 2 + T.oppLen (σ 2) ^ 2 - T.oppLen (σ 1) ^ 2) / (2 * T.oppLen (σ 0) * T.oppLen (σ 2)) := by
  rcases (perm_cases σ).2.1 with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · have := cos_angleAt_opp T (σ 1) (by rw [e1]; exact h0) (by rw [e2]; exact h2)
    rw [e1, e2] at this; exact this
  · have := cos_angleAt_opp T (σ 1) (by rw [e1]; exact h2) (by rw [e2]; exact h0)
    rw [e1, e2] at this; rw [this]; ring

theorem cos_s2 (T : Tri) (σ : Equiv.Perm (Fin 3)) (h0 : 0 < T.oppLen (σ 0)) (h1 : 0 < T.oppLen (σ 1)) :
    Real.cos (T.angleAt (σ 2)) =
      (T.oppLen (σ 0) ^ 2 + T.oppLen (σ 1) ^ 2 - T.oppLen (σ 2) ^ 2) / (2 * T.oppLen (σ 0) * T.oppLen (σ 1)) := by
  rcases (perm_cases σ).2.2 with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · have := cos_angleAt_opp T (σ 2) (by rw [e1]; exact h0) (by rw [e2]; exact h1)
    rw [e1, e2] at this; exact this
  · have := cos_angleAt_opp T (σ 2) (by rw [e1]; exact h1) (by rw [e2]; exact h0)
    rw [e1, e2] at this; rw [this]; ring

theorem irrPi_of_cos (α : ℝ) (q : ℚ) (hc : Real.cos α = q) (h0 : q ≠ 0) (h1 : q ≠ 1) (h2 : q ≠ -1)
    (h3 : q ≠ 1 / 2) (h4 : q ≠ -1 / 2) : IrrPi α := by
  intro hr
  have hmem := niven hr ⟨q, hc⟩
  rw [hc] at hmem
  have h0' : (q : ℝ) ≠ 0 := by exact_mod_cast h0
  have h1' : (q : ℝ) ≠ 1 := by exact_mod_cast h1
  have h2' : (q : ℝ) ≠ -1 := by exact_mod_cast h2
  have h3' : (q : ℝ) ≠ 1 / 2 := fun e => h3 (by exact_mod_cast (show ((q:ℚ):ℝ) = ((1/2:ℚ):ℝ) by rw [e]; norm_num))
  have h4' : (q : ℝ) ≠ -1 / 2 := fun e => h4 (by exact_mod_cast (show ((q:ℚ):ℝ) = ((-1/2:ℚ):ℝ) by rw [e]; norm_num))
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  rcases hmem with h | h | h | h | h
  all_goals first | exact h0' h | exact h1' h | exact h2' h | exact h3' h | exact h4' h |
    (apply h4'; linarith) | (apply h3'; linarith)

theorem sum_perm (T : Tri) (σ : Equiv.Perm (Fin 3)) :
    T.angleAt (σ 0) + T.angleAt (σ 1) + T.angleAt (σ 2) = Real.pi := by
  have hs := T.angleAt_sum
  have := Equiv.sum_comp σ (fun x => T.angleAt x)
  simp only [Fin.sum_univ_three] at this
  linarith

/-- A `2π/3` tile `(a,b,c)·lam` (c² = a²+ab+b²) presented with `σ`: opposite sides `lam a, lam b, lam c`. -/
theorem tp_angles (T : Tri) (σ : Equiv.Perm (Fin 3)) (lam a b c : ℝ) (hl : 0 < lam) (ha : 0 < a) (hb : 0 < b)
    (hc2 : c ^ 2 = a ^ 2 + a * b + b ^ 2)
    (o0 : T.oppLen (σ 0) = lam * a) (o1 : T.oppLen (σ 1) = lam * b) (o2 : T.oppLen (σ 2) = lam * c) :
    T.angleAt (σ 2) = 2 * Real.pi / 3 ∧ T.angleAt (σ 1) = Real.pi / 3 - T.angleAt (σ 0) := by
  have a2 : T.angleAt (σ 2) = 2 * Real.pi / 3 := by
    have hcos : Real.cos (T.angleAt (σ 2)) = -1 / 2 := by
      rw [cos_s2 T σ (by rw [o0]; positivity) (by rw [o1]; positivity), o0, o1, o2]
      have : (lam * a) ^ 2 + (lam * b) ^ 2 - (lam * c) ^ 2 = lam ^ 2 * (-(a * b)) := by
        have : (lam * c) ^ 2 = lam ^ 2 * c ^ 2 := by ring
        rw [this, hc2]; ring
      rw [this]; field_simp
    have hc' : Real.cos (2 * Real.pi / 3) = -1 / 2 := by
      rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring, Real.cos_pi_sub, Real.cos_pi_div_three]
      norm_num
    have hpi := Real.pi_pos
    exact Real.injOn_cos (cornerAngle_mem' _ _ _) ⟨by positivity, by linarith⟩ (hcos.trans hc'.symm)
  have hsum := sum_perm T σ
  exact ⟨a2, by rw [a2] at hsum; linarith⟩

theorem tp_data (T : Tri) (σ : Equiv.Perm (Fin 3)) (lam a b c : ℝ) (hl : 0 < lam) (ha : 0 < a) (hb : 0 < b)
    (hc2 : c ^ 2 = a ^ 2 + a * b + b ^ 2)
    (o0 : T.oppLen (σ 0) = lam * a) (o1 : T.oppLen (σ 1) = lam * b) (o2 : T.oppLen (σ 2) = lam * c) :
    T.TwoPiThreeData (T.angleAt (σ 0)) (lam * a) (lam * b) (lam * c) := by
  obtain ⟨h2, h1⟩ := tp_angles T σ lam a b c hl ha hb hc2 o0 o1 o2
  exact ⟨σ, rfl, o0, h1, o1, h2, o2⟩

/-- A `π/3` tile `(a,b,c)·lam` (c² = a²+b²−ab): angles `α, 2π/3 − α, π/3` opposite `a, b, c`. -/
theorem sixty_angles (T : Tri) (σ : Equiv.Perm (Fin 3)) (lam a b c : ℝ) (hl : 0 < lam) (ha : 0 < a) (hb : 0 < b)
    (hc2 : c ^ 2 = a ^ 2 + b ^ 2 - a * b)
    (o0 : T.oppLen (σ 0) = lam * a) (o1 : T.oppLen (σ 1) = lam * b) (o2 : T.oppLen (σ 2) = lam * c) :
    T.angleAt (σ 2) = Real.pi / 3 ∧ T.angleAt (σ 1) = 2 * Real.pi / 3 - T.angleAt (σ 0) := by
  have a2 : T.angleAt (σ 2) = Real.pi / 3 := by
    have hcos : Real.cos (T.angleAt (σ 2)) = 1 / 2 := by
      rw [cos_s2 T σ (by rw [o0]; positivity) (by rw [o1]; positivity), o0, o1, o2]
      have : (lam * a) ^ 2 + (lam * b) ^ 2 - (lam * c) ^ 2 = lam ^ 2 * (a * b) := by
        have : (lam * c) ^ 2 = lam ^ 2 * c ^ 2 := by ring
        rw [this, hc2]; ring
      rw [this]; field_simp
    have hpi := Real.pi_pos
    exact Real.injOn_cos (cornerAngle_mem' _ _ _) ⟨by positivity, by linarith⟩
      (hcos.trans Real.cos_pi_div_three.symm)
  have hsum := sum_perm T σ
  exact ⟨a2, by rw [a2] at hsum; linarith⟩

theorem sixty_data (T : Tri) (σ : Equiv.Perm (Fin 3)) (lam a b c : ℝ) (hl : 0 < lam) (ha : 0 < a) (hb : 0 < b)
    (hc2 : c ^ 2 = a ^ 2 + b ^ 2 - a * b)
    (o0 : T.oppLen (σ 0) = lam * a) (o1 : T.oppLen (σ 1) = lam * b) (o2 : T.oppLen (σ 2) = lam * c) :
    T.SixtyData (T.angleAt (σ 0)) (lam * a) (lam * b) (lam * c) := by
  obtain ⟨h2, h1⟩ := sixty_angles T σ lam a b c hl ha hb hc2 o0 o1 o2
  exact ⟨σ, rfl, o0, h1, o1, h2, o2⟩

end Erdos634.Draft.G3CAng
