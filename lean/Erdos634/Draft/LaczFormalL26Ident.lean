import Erdos634.Draft.LaczFormalL26Chart

/-!
# Laczkovich Theorem 2.4, fourth triple: the polynomial identities for the five tiles

NOTE, UNAUDITED.  Credit: Laczkovich (Discrete Math. 140 (1995) 79-94), Beeson, Beeson-Zhang, Zhang.
Squared chart sides of the tiles `PVX, VXZ, XLZ, QZV, SQZ` (order `(α, β, γ)`-vertex) against `k²a²b²`, `k²a⁴b²`, `k²a²b⁴`.
-/

namespace Erdos634.LaczL26

open Erdos634.Geometry Erdos634.CertCoord Erdos634.LaczL22 Erdos634.LaczL21 Erdos634.LaczL24

set_option maxHeartbeats 2000000 in
theorem idA01 (a : ℝ) (ha : a ≠ 0) (hb : 1 - a ^ 2 ≠ 0) :
    ((sP a) - (sV a)) ^ 2 + (2 - a ^ 2) * (((sP a) - (sV a)) * ((tP a) - (tV a))) + ((tP a) - (tV a)) ^ 2
      = 1 ^ 2 * a ^ 2 * (1 - a ^ 2) ^ 2 := by
  unf; field_simp; ring

set_option maxHeartbeats 2000000 in
theorem idA12 (a : ℝ) (ha : a ≠ 0) (hb : 1 - a ^ 2 ≠ 0) :
    ((sV a) - (sX a)) ^ 2 + (2 - a ^ 2) * (((sV a) - (sX a)) * ((tV a) - (tX a))) + ((tV a) - (tX a)) ^ 2
      = 1 ^ 2 * a ^ 4 * (1 - a ^ 2) ^ 2 := by
  unf; field_simp; ring

set_option maxHeartbeats 2000000 in
theorem idA20 (a : ℝ) (ha : a ≠ 0) (hb : 1 - a ^ 2 ≠ 0) :
    ((sX a) - (sP a)) ^ 2 + (2 - a ^ 2) * (((sX a) - (sP a)) * ((tX a) - (tP a))) + ((tX a) - (tP a)) ^ 2
      = 1 ^ 2 * a ^ 2 * (1 - a ^ 2) ^ 4 := by
  unf; field_simp; ring

set_option maxHeartbeats 2000000 in
theorem idB01 (a : ℝ) (ha : a ≠ 0) (hb : 1 - a ^ 2 ≠ 0) :
    ((sV a) - (sX a)) ^ 2 + (2 - a ^ 2) * (((sV a) - (sX a)) * ((tV a) - (tX a))) + ((tV a) - (tX a)) ^ 2
      = a ^ 2 * a ^ 2 * (1 - a ^ 2) ^ 2 := by
  unf; field_simp; ring

set_option maxHeartbeats 2000000 in
theorem idB12 (a : ℝ) (ha : a ≠ 0) (hb : 1 - a ^ 2 ≠ 0) :
    ((sX a) - 0) ^ 2 + (2 - a ^ 2) * (((sX a) - 0) * ((tX a) - (tZ a))) + ((tX a) - (tZ a)) ^ 2
      = a ^ 2 * a ^ 4 * (1 - a ^ 2) ^ 2 := by
  unf; field_simp; ring

set_option maxHeartbeats 2000000 in
theorem idB20 (a : ℝ) (ha : a ≠ 0) (hb : 1 - a ^ 2 ≠ 0) :
    (0 - (sV a)) ^ 2 + (2 - a ^ 2) * ((0 - (sV a)) * ((tZ a) - (tV a))) + ((tZ a) - (tV a)) ^ 2
      = a ^ 2 * a ^ 2 * (1 - a ^ 2) ^ 4 := by
  unf; field_simp; ring

set_option maxHeartbeats 2000000 in
theorem idC01 (a : ℝ) (ha : a ≠ 0) (hb : 1 - a ^ 2 ≠ 0) :
    ((sX a) - 0) ^ 2 + (2 - a ^ 2) * (((sX a) - 0) * ((tX a) - 0)) + ((tX a) - 0) ^ 2
      = (a ^ 2 / (1 - a ^ 2)) ^ 2 * a ^ 2 * (1 - a ^ 2) ^ 2 := by
  unf; field_simp; ring

set_option maxHeartbeats 2000000 in
theorem idC12 (a : ℝ) (ha : a ≠ 0) (hb : 1 - a ^ 2 ≠ 0) :
    (0 - 0) ^ 2 + (2 - a ^ 2) * ((0 - 0) * (0 - (tZ a))) + (0 - (tZ a)) ^ 2
      = (a ^ 2 / (1 - a ^ 2)) ^ 2 * a ^ 4 * (1 - a ^ 2) ^ 2 := by
  unf; field_simp; ring

set_option maxHeartbeats 2000000 in
theorem idC20 (a : ℝ) (ha : a ≠ 0) (hb : 1 - a ^ 2 ≠ 0) :
    (0 - (sX a)) ^ 2 + (2 - a ^ 2) * ((0 - (sX a)) * ((tZ a) - (tX a))) + ((tZ a) - (tX a)) ^ 2
      = (a ^ 2 / (1 - a ^ 2)) ^ 2 * a ^ 2 * (1 - a ^ 2) ^ 4 := by
  unf; field_simp; ring

set_option maxHeartbeats 2000000 in
theorem idD01 (a : ℝ) (ha : a ≠ 0) (hb : 1 - a ^ 2 ≠ 0) :
    ((sQ a) - 0) ^ 2 + (2 - a ^ 2) * (((sQ a) - 0) * ((tQ a) - (tZ a))) + ((tQ a) - (tZ a)) ^ 2
      = (1 - a ^ 2) ^ 2 * a ^ 2 * (1 - a ^ 2) ^ 2 := by
  unf; field_simp; ring

set_option maxHeartbeats 2000000 in
theorem idD12 (a : ℝ) (ha : a ≠ 0) (hb : 1 - a ^ 2 ≠ 0) :
    (0 - (sV a)) ^ 2 + (2 - a ^ 2) * ((0 - (sV a)) * ((tZ a) - (tV a))) + ((tZ a) - (tV a)) ^ 2
      = (1 - a ^ 2) ^ 2 * a ^ 4 * (1 - a ^ 2) ^ 2 := by
  unf; field_simp; ring

set_option maxHeartbeats 2000000 in
theorem idD20 (a : ℝ) (ha : a ≠ 0) (hb : 1 - a ^ 2 ≠ 0) :
    ((sV a) - (sQ a)) ^ 2 + (2 - a ^ 2) * (((sV a) - (sQ a)) * ((tV a) - (tQ a))) + ((tV a) - (tQ a)) ^ 2
      = (1 - a ^ 2) ^ 2 * a ^ 2 * (1 - a ^ 2) ^ 4 := by
  unf; field_simp; ring

set_option maxHeartbeats 2000000 in
theorem idE01 (a : ℝ) (ha : a ≠ 0) (hb : 1 - a ^ 2 ≠ 0) :
    (0 - (sQ a)) ^ 2 + (2 - a ^ 2) * ((0 - (sQ a)) * ((tS a) - (tQ a))) + ((tS a) - (tQ a)) ^ 2
      = ((1 - a ^ 2) / a) ^ 2 * a ^ 2 * (1 - a ^ 2) ^ 2 := by
  unf; field_simp; ring

set_option maxHeartbeats 2000000 in
theorem idE12 (a : ℝ) (ha : a ≠ 0) (hb : 1 - a ^ 2 ≠ 0) :
    ((sQ a) - 0) ^ 2 + (2 - a ^ 2) * (((sQ a) - 0) * ((tQ a) - (tZ a))) + ((tQ a) - (tZ a)) ^ 2
      = ((1 - a ^ 2) / a) ^ 2 * a ^ 4 * (1 - a ^ 2) ^ 2 := by
  unf; field_simp; ring

set_option maxHeartbeats 2000000 in
theorem idE20 (a : ℝ) (ha : a ≠ 0) (hb : 1 - a ^ 2 ≠ 0) :
    (0 - 0) ^ 2 + (2 - a ^ 2) * ((0 - 0) * ((tZ a) - (tS a))) + ((tZ a) - (tS a)) ^ 2
      = ((1 - a ^ 2) / a) ^ 2 * a ^ 2 * (1 - a ^ 2) ^ 4 := by
  unf; field_simp; ring

end Erdos634.LaczL26
