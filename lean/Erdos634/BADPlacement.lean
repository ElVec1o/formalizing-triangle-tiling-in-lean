import Erdos634.BADAlgebra

/-!
# BAD layer L1: a placed tile has boundary polynomial `± t^s p` or `± t^s q`

Written 2026-10-03.  Single-tile lemma only (no dissection; that is layer L2).

Direction coordinates: with `ζ = e^{iα}`, `ω = e^{iβ}`, `3α+2β = π` (so `ζ³ω² = -1`), a direction is
written `ζ^i ω^j`, `(i,j) ∈ ℤ²` (unique modulo `(6,4)` when `α/π` is irrational: NOT proved here).
Letter index `k = 2i-3j`, sign `ε = (-1)^(i-j)`; both are invariant (resp. the sign flips by `(3,2)`)
consistently under `(6,4)`.  A directed side of length `len` and coordinate `(i,j)` contributes
`ε · len · t^k`.  Model tile ccw from `A`: sides `c` (0,0), `a` (3,1), `b` (-2,-2), `(a,b,c)=(ef,f²-e²,f²)`.
-/

open LaurentPolynomial

namespace BAD

noncomputable section

def kk (i j : ℤ) : ℤ := 2 * i - 3 * j
def ee (i j : ℤ) : ℤ := (((i - j).negOnePow : ℤˣ) : ℤ)

/-- a directed side: `(length, i, j)`. -/
abbrev Side := ℤ × ℤ × ℤ
def sideTerm (x : Side) : L := C (ee x.2.1 x.2.2 * x.1) * T (kk x.2.1 x.2.2)
/-- boundary polynomial of a list of directed sides. -/
def bp (l : List Side) : L := (l.map sideTerm).sum

theorem kk_period (i j : ℤ) : kk (i + 6) (j + 4) = kk i j := by unfold kk; ring
theorem ee_shift (i j m n : ℤ) : ee (i + m) (j + n) = ee i j * ee m n := by
  unfold ee
  have : i + m - (j + n) = (i - j) + (m - n) := by ring
  rw [this, Int.negOnePow_add]; push_cast; rfl
theorem ee_pi (i j : ℤ) : ee (i + 3) (j + 2) = - ee i j := by
  rw [ee_shift]; simp [ee]
theorem ee_period (i j : ℤ) : ee (i + 6) (j + 4) = ee i j := by
  rw [ee_shift]; simp [ee]; decide

theorem ee32 : ee 3 1 = 1 := by simp [ee]; decide
theorem ee22 : ee (-2) (-2) = 1 := by simp [ee]
theorem ee54 : ee 5 4 = -1 := by simp [ee]
theorem ee01 : ee 0 1 = -1 := by simp [ee]
theorem ee32' : ee 3 2 = -1 := by simp [ee]
theorem ee00 : ee 0 0 = 1 := by simp [ee]

theorem T2 : (T 2 : L) = T 1 * T 1 := by rw [← T_add]; norm_num
theorem T3 : (T 3 : L) = T 1 * T 1 * T 1 := by rw [← T_add, ← T_add]; norm_num

/-- the three side terms in the model orientation: `c + b t² + a t³ = p`. -/
theorem p_form (e f : ℤ) : C (f ^ 2) + C (f ^ 2 - e ^ 2) * T 2 + C (e * f) * (T 3 : L) = pTile e f := by
  unfold pTile Phi; rw [T2, T3]; simp only [map_mul, map_pow, map_sub]; ring
theorem q_form (e f : ℤ) : C (f ^ 2) * (T 3 : L) + C (f ^ 2 - e ^ 2) * T 1 + C (e * f) = qTile e f := by
  unfold qTile Phi; rw [T2, T3]; simp only [map_mul, map_pow, map_sub]; ring

/-- orientation-preserving placement by rotation `(i,j)`. -/
theorem bp_rot (e f i j : ℤ) :
    bp [(f ^ 2, i, j), (e * f, i + 3, j + 1), (f ^ 2 - e ^ 2, i - 2, j - 2)]
      = C (ee i j) * T (kk i j) * pTile e f := by
  have k1 : kk (i + 3) (j + 1) = kk i j + 3 := by unfold kk; ring
  have k2 : kk (i - 2) (j - 2) = kk i j + 2 := by unfold kk; ring
  have e2 : ee (i - 2) (j - 2) = ee i j := by
    have := ee_shift i j (-2) (-2); simp only [← sub_eq_add_neg] at this; rw [this, ee22, mul_one]
  have e1 : ee (i + 3) (j + 1) = ee i j := by rw [ee_shift, ee32, mul_one]
  rw [← p_form]
  simp only [bp, sideTerm, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, k1, k2, e1, e2,
    T_add, map_mul]
  have : (T 2 : L) = T 2 := rfl
  rw [show (T 3 : L) = T 3 from rfl]
  ring

/-- reflected placement (sides read counterclockwise). -/
theorem bp_mir (e f i j : ℤ) :
    bp [(f ^ 2 - e ^ 2, i + 5, j + 4), (e * f, i, j + 1), (f ^ 2, i + 3, j + 2)]
      = C (-ee i j) * T (kk i j - 3) * qTile e f := by
  have k1 : kk (i + 5) (j + 4) = (kk i j - 3) + 1 := by unfold kk; ring
  have k2 : kk i (j + 1) = kk i j - 3 := by unfold kk; ring
  have k3 : kk (i + 3) (j + 2) = (kk i j - 3) + 3 := by unfold kk; ring
  have e1 : ee (i + 5) (j + 4) = - ee i j := by rw [ee_shift, ee54]; ring
  have e2 : ee i (j + 1) = - ee i j := by
    have := ee_shift i j 0 1; simp only [add_zero] at this; rw [this, ee01]; ring
  rw [← q_form]
  simp only [bp, sideTerm, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, k1, k2, k3, e1, e2,
    ee_pi, T_add, map_mul, map_neg]
  rw [T3] 
  have h1 : (T 1 : L) = T 1 := rfl
  ring

end

end BAD
