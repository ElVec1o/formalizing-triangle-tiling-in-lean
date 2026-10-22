import Erdos634.Draft.LaczFormal53Shapes

/-!
# Laczkovich Thm 5.3, case (vii): dispatch over the target angle triples

NOTE, UNAUDITED.  Credit: Laczkovich (Discrete Math. 140 (1995), Thm 5.1/5.3), Beeson, Beeson-Zhang.  Formalization debt.

`main_alg`: target angles `(U0, U1, U2) pi/8` (positive integers, sum 8), not a permutation of `(2,1,5)`; sides
`L_i = n_i w + m_i u + k_i v` (nonnegative rationals, positive), law-of-sines proportionality to `sin (U_j pi/8)`, area `Hh(L) = N^2/4`
==> `False`.
-/

namespace Erdos634.Lacz53

open E4

/-- `sin (U pi / 8)` as a coefficient tuple, `U = 1..6`. -/
def sE : ℕ → E4
  | 1 => uE
  | 2 => wE
  | 3 => vE
  | 4 => oneE
  | 5 => vE
  | 6 => wE
  | _ => oneE

set_option maxHeartbeats 4000000 in
theorem main_alg {U0 U1 U2 : ℕ} {n0 m0 k0 n1 m1 k1 n2 m2 k2 N : ℚ}
    (hn0 : 0 ≤ n0) (hm0 : 0 ≤ m0) (hk0 : 0 ≤ k0) (hn1 : 0 ≤ n1) (hm1 : 0 ≤ m1) (hk1 : 0 ≤ k1)
    (hn2 : 0 ≤ n2) (hm2 : 0 ≤ m2) (hk2 : 0 ≤ k2)
    (hpos0 : 0 < n0 + m0 + k0) (hpos1 : 0 < n1 + m1 + k1) (hpos2 : 0 < n2 + m2 + k2)
    (u0 : 1 ≤ U0) (u1 : 1 ≤ U1) (u2 : 1 ≤ U2) (hsum : U0 + U1 + U2 = 8)
    (hnot : ¬ ((U0 = 1 ∨ U1 = 1 ∨ U2 = 1) ∧ (U0 = 2 ∨ U1 = 2 ∨ U2 = 2) ∧ (U0 = 5 ∨ U1 = 5 ∨ U2 = 5)))
    (p01 : (sideE n0 m0 k0).mul (sE U1) = (sideE n1 m1 k1).mul (sE U0))
    (p02 : (sideE n0 m0 k0).mul (sE U2) = (sideE n2 m2 k2).mul (sE U0))
    (p12 : (sideE n1 m1 k1).mul (sE U2) = (sideE n2 m2 k2).mul (sE U1))
    (hH0 : hhE (sideE n0 m0 k0) (sideE n1 m1 k1) (sideE n2 m2 k2) = ofQ (N ^ 2 / 4)) : False := by
  have p10 := p01.symm
  have p20 := p02.symm
  have p21 := p12.symm
  rcases (by omega : U0 = 1 ∨ U0 = 2 ∨ U0 = 3 ∨ U0 = 4 ∨ U0 = 5 ∨ U0 = 6) with rfl | rfl | rfl | rfl | rfl | rfl
  · rcases (by omega : U1 = 1 ∨ U1 = 2 ∨ U1 = 3 ∨ U1 = 4 ∨ U1 = 5 ∨ U1 = 6) with rfl | rfl | rfl | rfl | rfl | rfl
    · obtain rfl : U2 = 6 := by omega
      exact shape116 hn0 hm0 hk0 hn1 hm1 hk1 hn2 hm2 hk2 p01 p02 p12 (by first | exact hH0 | (rw [← hH0]; apply E4.ev_inj; rw [E4.ev_hhE, E4.ev_hhE]; ring)) hpos0
    · obtain rfl : U2 = 5 := by omega
      exact hnot (by decide)
    · obtain rfl : U2 = 4 := by omega
      exact shape134 hn0 hm0 hk0 hn1 hm1 hk1 hn2 hm2 hk2 p01 p02 p12 hpos0
    · obtain rfl : U2 = 3 := by omega
      exact shape134 hn0 hm0 hk0 hn2 hm2 hk2 hn1 hm1 hk1 p02 p01 p21 hpos0
    · obtain rfl : U2 = 2 := by omega
      exact hnot (by decide)
    · obtain rfl : U2 = 1 := by omega
      exact shape116 hn0 hm0 hk0 hn2 hm2 hk2 hn1 hm1 hk1 p02 p01 p21 (by first | exact hH0 | (rw [← hH0]; apply E4.ev_inj; rw [E4.ev_hhE, E4.ev_hhE]; ring)) hpos0
  · rcases (by omega : U1 = 1 ∨ U1 = 2 ∨ U1 = 3 ∨ U1 = 4 ∨ U1 = 5) with rfl | rfl | rfl | rfl | rfl
    · obtain rfl : U2 = 5 := by omega
      exact hnot (by decide)
    · obtain rfl : U2 = 4 := by omega
      exact shape224 hn0 hm0 hk0 hn1 hm1 hk1 hn2 hm2 hk2 p01 p02 p12 (by first | exact hH0 | (rw [← hH0]; apply E4.ev_inj; rw [E4.ev_hhE, E4.ev_hhE]; ring)) hpos0
    · obtain rfl : U2 = 3 := by omega
      exact shape233 hn0 hm0 hk0 hn1 hm1 hk1 hn2 hm2 hk2 p01 p02 p12 (by first | exact hH0 | (rw [← hH0]; apply E4.ev_inj; rw [E4.ev_hhE, E4.ev_hhE]; ring)) hpos0
    · obtain rfl : U2 = 2 := by omega
      exact shape224 hn0 hm0 hk0 hn2 hm2 hk2 hn1 hm1 hk1 p02 p01 p21 (by first | exact hH0 | (rw [← hH0]; apply E4.ev_inj; rw [E4.ev_hhE, E4.ev_hhE]; ring)) hpos0
    · obtain rfl : U2 = 1 := by omega
      exact hnot (by decide)
  · rcases (by omega : U1 = 1 ∨ U1 = 2 ∨ U1 = 3 ∨ U1 = 4) with rfl | rfl | rfl | rfl
    · obtain rfl : U2 = 4 := by omega
      exact shape134 hn1 hm1 hk1 hn0 hm0 hk0 hn2 hm2 hk2 p10 p12 p02 hpos1
    · obtain rfl : U2 = 3 := by omega
      exact shape233 hn1 hm1 hk1 hn0 hm0 hk0 hn2 hm2 hk2 p10 p12 p02 (by first | exact hH0 | (rw [← hH0]; apply E4.ev_inj; rw [E4.ev_hhE, E4.ev_hhE]; ring)) hpos1
    · obtain rfl : U2 = 2 := by omega
      exact shape233 hn2 hm2 hk2 hn0 hm0 hk0 hn1 hm1 hk1 p20 p21 p01 (by first | exact hH0 | (rw [← hH0]; apply E4.ev_inj; rw [E4.ev_hhE, E4.ev_hhE]; ring)) hpos2
    · obtain rfl : U2 = 1 := by omega
      exact shape134 hn2 hm2 hk2 hn0 hm0 hk0 hn1 hm1 hk1 p20 p21 p01 hpos2
  · rcases (by omega : U1 = 1 ∨ U1 = 2 ∨ U1 = 3) with rfl | rfl | rfl
    · obtain rfl : U2 = 3 := by omega
      exact shape134 hn1 hm1 hk1 hn2 hm2 hk2 hn0 hm0 hk0 p12 p10 p20 hpos1
    · obtain rfl : U2 = 2 := by omega
      exact shape224 hn1 hm1 hk1 hn2 hm2 hk2 hn0 hm0 hk0 p12 p10 p20 (by first | exact hH0 | (rw [← hH0]; apply E4.ev_inj; rw [E4.ev_hhE, E4.ev_hhE]; ring)) hpos1
    · obtain rfl : U2 = 1 := by omega
      exact shape134 hn2 hm2 hk2 hn1 hm1 hk1 hn0 hm0 hk0 p21 p20 p10 hpos2
  · rcases (by omega : U1 = 1 ∨ U1 = 2) with rfl | rfl
    · obtain rfl : U2 = 2 := by omega
      exact hnot (by decide)
    · obtain rfl : U2 = 1 := by omega
      exact hnot (by decide)
  · obtain rfl : U1 = 1 := by omega
    obtain rfl : U2 = 1 := by omega
    exact shape116 hn1 hm1 hk1 hn2 hm2 hk2 hn0 hm0 hk0 p12 p10 p20 (by first | exact hH0 | (rw [← hH0]; apply E4.ev_inj; rw [E4.ev_hhE, E4.ev_hhE]; ring)) hpos1

end Erdos634.Lacz53
