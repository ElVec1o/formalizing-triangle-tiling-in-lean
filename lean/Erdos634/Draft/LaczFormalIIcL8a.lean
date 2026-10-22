-- Draft/LaczFormalIIcL8a.lean -- Laczkovich (DCG 48 (2012)), Sect. 6.3, two exceptional points, index split (G10), step 1: PURE PLANE GEOMETRY.
-- `poly_orient`: in a strictly convex polygon `ConvPoly M` any three vertices a < p < q (in the cyclic order starting at a) are positively oriented.
-- (The structure `ConvPoly` only records that every vertex is strictly left of every EDGE.)  Proof: with `Q_m = cross(a_1, a_m) > 0` and the three-term plane identity
-- `Q_q cross(a_p, a_{q+1}) = Q_{q+1} cross(a_p, a_q) + Q_p cross(a_q, a_{q+1})`, induction on q from consecutive triples.
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalThm21Loc

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.Draft.LaczFormal.Thm21

namespace Erdos634.Draft.LaczFormal.RG

variable {M : ℕ} [NeZero M]

theorem natCast_ne_zero_fin {q : ℕ} (h0 : 0 < q) (h : q < M) : ((q : ℕ) : Fin M) ≠ 0 := by
  intro h'
  have := (Fin.natCast_eq_zero).mp h'
  have := Nat.le_of_dvd h0 this
  omega

/-- Three vertices `a`, `a + p`, `a + q` (`0 < p < q < M`) of a strictly convex polygon are positively oriented. -/
theorem poly_orient (P : ConvPoly M) (a : Fin M) : ∀ p q : ℕ, 0 < p → p < q → q < M →
    0 < cross2 (P.v (a + (p : Fin M)) - P.v a) (P.v (a + (q : Fin M)) - P.v a) := by
  have hQ : ∀ m : ℕ, 2 ≤ m → m < M → 0 < cross2 (P.v (a + ((1 : ℕ) : Fin M)) - P.v a) (P.v (a + (m : Fin M)) - P.v a) := by
    intro m h2 hm
    have h1 : (a + (m : Fin M)) ≠ a := by
      intro h; apply natCast_ne_zero_fin (q := m) (by omega) hm; simpa using h
    have h2' : (a + (m : Fin M)) ≠ a + 1 := by
      intro h
      have : (m : Fin M) = ((1 : ℕ) : Fin M) := by simpa using add_left_cancel h
      have := congrArg Fin.val this
      rw [Fin.val_natCast, Fin.val_natCast, Nat.mod_eq_of_lt hm] at this
      have h1M : 1 < M := by omega
      rw [Nat.mod_eq_of_lt h1M] at this; omega
    have := P.left a (a + (m : Fin M)) h1 h2'
    simpa using this
  have hC : ∀ p : ℕ, 1 ≤ p → p + 1 < M →
      0 < cross2 (P.v (a + (p : Fin M)) - P.v a) (P.v (a + ((p + 1 : ℕ) : Fin M)) - P.v a) := by
    intro p hp hpM
    have h1 : a ≠ a + (p : Fin M) := by
      intro h; apply natCast_ne_zero_fin (M := M) (q := p) (by omega) (by omega)
      have : a + (p : Fin M) = a + 0 := by rw [add_zero]; exact h.symm
      exact add_left_cancel this
    have h2 : a ≠ a + (p : Fin M) + 1 := by
      intro h; apply natCast_ne_zero_fin (M := M) (q := p + 1) (by omega) hpM
      have : a + ((p + 1 : ℕ) : Fin M) = a + 0 := by rw [add_zero, Nat.cast_succ, ← add_assoc]; exact h.symm
      exact add_left_cancel this
    have := P.left (a + (p : Fin M)) a h1 h2
    have e : a + (p : Fin M) + 1 = a + ((p + 1 : ℕ) : Fin M) := by rw [Nat.cast_succ, add_assoc]
    rw [e] at this
    unfold cross2 at this ⊢
    simp only [PiLp.sub_apply] at this ⊢
    nlinarith [this]
  intro p q hp hpq hq
  induction q, hpq using Nat.le_induction with
  | base => exact hC p hp hq
  | succ q hpq ih =>
    have ih := ih (by omega)
    have hq1 := hQ q (by omega) (by omega)
    have hq2 := hQ (q + 1) (by omega) hq
    have hcc := hC q (by omega) hq
    have hQp : 0 ≤ cross2 (P.v (a + ((1 : ℕ) : Fin M)) - P.v a) (P.v (a + (p : Fin M)) - P.v a) := by
      by_cases hp1 : p = 1
      · subst hp1; unfold cross2; simp; ring_nf; exact le_refl _
      · exact (hQ p (by omega) (by omega)).le
    set x1 := P.v (a + ((1 : ℕ) : Fin M)) - P.v a
    set xp := P.v (a + (p : Fin M)) - P.v a
    set xq := P.v (a + (q : Fin M)) - P.v a
    set xr := P.v (a + ((q + 1 : ℕ) : Fin M)) - P.v a
    have key : cross2 x1 xq * cross2 xp xr = cross2 x1 xr * cross2 xp xq + cross2 x1 xp * cross2 xq xr := by
      unfold cross2; ring
    have : 0 < cross2 x1 xq * cross2 xp xr := by
      rw [key]; nlinarith [mul_pos hq2 ih, mul_nonneg hQp hcc.le]
    exact (mul_pos_iff_of_pos_left hq1).1 this

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.poly_orient
