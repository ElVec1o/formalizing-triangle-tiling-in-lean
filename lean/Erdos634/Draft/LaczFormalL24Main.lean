import Erdos634.Draft.LaczFormalL24Disj

/-!
# Laczkovich Theorem 2.4, first triple `(α, α, π - 2α)`: the similarity part and the assembly

NOTE, UNAUDITED.  Credit: Laczkovich (Discrete Math. 140 (1995) 79-94, Theorem 2.4, Fig. 4), Beeson,
Beeson-Zhang, Zhang.

`Δ` is a rational triangle with `a = a₀ c`, `b = (1 - a₀²) c` (`a₀ = 2 sin(α/2) ∈ (0,1)`, `c = |Δ₀Δ₁|`).
Chart `(G; w = GB, d = GF)` with `|w| = W = c N/a₀²`, `|d| = c`, `⟨w,d⟩ = W c cos α`,
`cos α = (2 - a₀²)/2` (`N = a₀² + (1-a₀²)²`).  The tiles `BCA, ACD, ADE, CDF` of Fig. 4 are
`Δ`-similar with ratios `1, b₀/a₀, b₀/a₀², b₀²/a₀²` (`t1_alg`, rational arithmetic); the trapezoid `GBCF` is
Lemma 2.2 (ii) (`trap_ii`) for the relabelled triangle (`RTri.sw01`).
-/

namespace Erdos634.LaczL24

open Erdos634.Geometry Erdos634.CertCoord Erdos634.LaczL22 Erdos634.LaczL21 Erdos634.Realizable

def q1N (a0 : ℚ) : ℚ := a0 ^ 2 + (1 - a0 ^ 2) ^ 2
def q1Tau (a0 : ℚ) : ℚ := (1 - a0 ^ 2) ^ 2 / q1N a0
def q1Del (a0 : ℚ) : ℚ := 1 + (1 - a0 ^ 2) ^ 3 / a0 ^ 2
def q1E (a0 : ℚ) : ℚ := q1Del a0 + (1 - a0 ^ 2) / a0 ^ 2
def q1W (a0 c : ℚ) : ℚ := c * q1N a0 / a0 ^ 2
def q1G (a0 c : ℚ) : ℚ := q1W a0 c * c * ((2 - a0 ^ 2) / 2)
def Qf (a0 c x y : ℚ) : ℚ := x ^ 2 * (q1W a0 c) ^ 2 + 2 * (x * y) * q1G a0 c + y ^ 2 * c ^ 2

theorem cast_gTau (a0 : ℚ) : gTau (a0 : ℝ) = ((q1Tau a0 : ℚ) : ℝ) := by
  simp only [gTau, gN, q1Tau, q1N]; push_cast; rfl
theorem cast_gDel (a0 : ℚ) : gDel (a0 : ℝ) = ((q1Del a0 : ℚ) : ℝ) := by
  simp only [gDel, q1Del]; push_cast; rfl
theorem cast_gE (a0 : ℚ) : gE (a0 : ℝ) = ((q1E a0 : ℚ) : ℝ) := by
  simp only [gE, q1E, cast_gDel, q1Del]; push_cast; rfl

theorem t1_alg (a0 c : ℚ) (ha : 0 < a0) (hb : a0 < 1) (hc : 0 < c) :
    let a := a0 * c; let b := (1 - a0 ^ 2) * c
    let τ := q1Tau a0; let δ := q1Del a0; let e := q1E a0
    Qf a0 c (1 - τ) (0 - 1) = 1 ^ 2 * a ^ 2 ∧ Qf a0 c (τ - τ) (1 - (2 - a0 ^ 2)) = 1 ^ 2 * b ^ 2 ∧
    Qf a0 c (τ - 1) ((2 - a0 ^ 2) - 0) = 1 ^ 2 * c ^ 2 ∧
    Qf a0 c (τ - τ) ((2 - a0 ^ 2) - 1) = ((1 - a0 ^ 2) / a0) ^ 2 * a ^ 2 ∧
    Qf a0 c (τ - 0) (1 - δ) = ((1 - a0 ^ 2) / a0) ^ 2 * b ^ 2 ∧
    Qf a0 c (0 - τ) (δ - (2 - a0 ^ 2)) = ((1 - a0 ^ 2) / a0) ^ 2 * c ^ 2 ∧
    Qf a0 c (τ - 0) ((2 - a0 ^ 2) - δ) = ((1 - a0 ^ 2) / a0 ^ 2) ^ 2 * a ^ 2 ∧
    Qf a0 c (0 - 0) (δ - e) = ((1 - a0 ^ 2) / a0 ^ 2) ^ 2 * c ^ 2 ∧
    Qf a0 c (0 - τ) (e - (2 - a0 ^ 2)) = ((1 - a0 ^ 2) / a0 ^ 2) ^ 2 * b ^ 2 ∧
    Qf a0 c (τ - 0) (1 - δ) = ((1 - a0 ^ 2) ^ 2 / a0 ^ 2) ^ 2 * a ^ 2 ∧
    Qf a0 c (0 - 0) (δ - 1) = ((1 - a0 ^ 2) ^ 2 / a0 ^ 2) ^ 2 * b ^ 2 ∧
    Qf a0 c (0 - τ) (1 - 1) = ((1 - a0 ^ 2) ^ 2 / a0 ^ 2) ^ 2 * c ^ 2 := by
  intro a b τ δ e
  have ha' := ha.ne'
  have hN : q1N a0 ≠ 0 := by
    unfold q1N; have : 0 < 1 - a0 ^ 2 := by nlinarith
    positivity
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [a, b, τ, δ, e, Qf, q1W, q1G, q1Tau, q1Del, q1E, q1N] at * <;> field_simp <;> ring


section tiles
variable (R : RTri) (a0 : ℚ) (ha0q : 0 < a0) (ha1q : a0 < 1)
  (hA : R.a = a0 * R.c) (hB : R.b = (1 - a0 ^ 2) * R.c)
  (A w d : Plane) (h : w 0 * d 1 - w 1 * d 0 ≠ 0)
  (hw : inner ℝ w w = ((q1W a0 R.c : ℚ) : ℝ) ^ 2) (hd : inner ℝ d d = (R.c : ℝ) ^ 2)
  (hwd : inner ℝ w d = ((q1G a0 R.c : ℚ) : ℝ))

private theorem hrot0 : (finRotate 3) 0 = 1 := by decide
private theorem hrot1 : (finRotate 3) 1 = 2 := by decide
private theorem hrot2 : (finRotate 3) 2 = 0 := by decide
private theorem hsw0 : (Equiv.swap (0 : Fin 3) 2) 0 = 2 := by decide
private theorem hsw1 : (Equiv.swap (0 : Fin 3) 2) 1 = 1 := by decide
private theorem hsw2 : (Equiv.swap (0 : Fin 3) 2) 2 = 0 := by decide

include ha0q ha1q hA hB hw hd hwd

theorem tile_BCA (ha0 : 0 < (a0 : ℝ)) (ha1 : (a0 : ℝ) < 1) :
    RatSimTile R.Δ (Erdos634.DissectionMap.mapTri (chartEquiv A w d h) (triBCA (a0 : ℝ) ha0 ha1)) := by
  obtain ⟨k1, k2, k3, -⟩ := t1_alg a0 R.c ha0q ha1q R.pc
  unfold triBCA
  refine chart_tile R A w d h (q1W a0 R.c) R.c hw hd _ hwd _ _ _ _ _ _ _ (finRotate 3) 1 one_pos
    ?_ ?_ ?_
  · rw [hrot0, hrot1, R.ha, hA, cast_gTau]
    have := congrArg (Rat.cast : ℚ → ℝ) k1; simp only [Qf] at this; push_cast at this
    push_cast; linear_combination this
  · rw [hrot1, hrot2, R.hb, hB, cast_gTau]
    have := congrArg (Rat.cast : ℚ → ℝ) k2; simp only [Qf] at this; push_cast at this
    push_cast; linear_combination this
  · rw [hrot2, hrot0, R.hc, cast_gTau]
    have := congrArg (Rat.cast : ℚ → ℝ) k3; simp only [Qf] at this; push_cast at this
    push_cast; linear_combination this


theorem tile_ACD (ha0 : 0 < (a0 : ℝ)) (ha1 : (a0 : ℝ) < 1) :
    RatSimTile R.Δ (Erdos634.DissectionMap.mapTri (chartEquiv A w d h) (triACD (a0 : ℝ) ha0 ha1)) := by
  obtain ⟨-, -, -, k4, k5, k6, -⟩ := t1_alg a0 R.c ha0q ha1q R.pc
  have hb0 : 0 < 1 - a0 ^ 2 := by nlinarith
  unfold triACD
  refine chart_tile R A w d h (q1W a0 R.c) R.c hw hd _ hwd _ _ _ _ _ _ _ (finRotate 3)
    ((1 - a0 ^ 2) / a0) (by positivity) ?_ ?_ ?_
  · rw [hrot0, hrot1, R.ha, hA, cast_gTau]
    have := congrArg (Rat.cast : ℚ → ℝ) k4; simp only [Qf] at this; push_cast at this
    push_cast; linear_combination this
  · rw [hrot1, hrot2, R.hb, hB, cast_gTau, cast_gDel]
    have := congrArg (Rat.cast : ℚ → ℝ) k5; simp only [Qf] at this; push_cast at this
    push_cast; linear_combination this
  · rw [hrot2, hrot0, R.hc, cast_gTau, cast_gDel]
    have := congrArg (Rat.cast : ℚ → ℝ) k6; simp only [Qf] at this; push_cast at this
    push_cast; linear_combination this

theorem tile_ADE (ha0 : 0 < (a0 : ℝ)) (ha1 : (a0 : ℝ) < 1) :
    RatSimTile R.Δ (Erdos634.DissectionMap.mapTri (chartEquiv A w d h) (triADE (a0 : ℝ) ha0 ha1)) := by
  obtain ⟨-, -, -, -, -, -, k7, k8, k9, -⟩ := t1_alg a0 R.c ha0q ha1q R.pc
  have hb0 : 0 < 1 - a0 ^ 2 := by nlinarith
  unfold triADE
  refine chart_tile R A w d h (q1W a0 R.c) R.c hw hd _ hwd _ _ _ _ _ _ _ (Equiv.swap 0 2)
    ((1 - a0 ^ 2) / a0 ^ 2) (by positivity) ?_ ?_ ?_
  · rw [hsw0, hsw1, dist_comm (R.Δ.pts 2) (R.Δ.pts 1), R.ha, hA, cast_gTau, cast_gDel]
    have := congrArg (Rat.cast : ℚ → ℝ) k7; simp only [Qf] at this; push_cast at this
    push_cast; linear_combination this
  · rw [hsw1, hsw2, dist_comm (R.Δ.pts 1) (R.Δ.pts 0), R.hc, cast_gDel, cast_gE]
    have := congrArg (Rat.cast : ℚ → ℝ) k8; simp only [Qf] at this; push_cast at this
    push_cast; linear_combination this
  · rw [hsw2, hsw0, dist_comm (R.Δ.pts 0) (R.Δ.pts 2), R.hb, hB, cast_gTau, cast_gE]
    have := congrArg (Rat.cast : ℚ → ℝ) k9; simp only [Qf] at this; push_cast at this
    push_cast; linear_combination this

theorem tile_CDF (ha0 : 0 < (a0 : ℝ)) (ha1 : (a0 : ℝ) < 1) :
    RatSimTile R.Δ (Erdos634.DissectionMap.mapTri (chartEquiv A w d h) (triCDF (a0 : ℝ) ha0 ha1)) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, k10, k11, k12⟩ := t1_alg a0 R.c ha0q ha1q R.pc
  have hb0 : 0 < 1 - a0 ^ 2 := by nlinarith
  unfold triCDF
  refine chart_tile R A w d h (q1W a0 R.c) R.c hw hd _ hwd _ _ _ _ _ _ _ (finRotate 3)
    ((1 - a0 ^ 2) ^ 2 / a0 ^ 2) (by positivity) ?_ ?_ ?_
  · rw [hrot0, hrot1, R.ha, hA, cast_gTau, cast_gDel]
    have := congrArg (Rat.cast : ℚ → ℝ) k10; simp only [Qf] at this; push_cast at this
    push_cast; linear_combination this
  · rw [hrot1, hrot2, R.hb, hB, cast_gDel]
    have := congrArg (Rat.cast : ℚ → ℝ) k11; simp only [Qf] at this; push_cast at this
    push_cast; linear_combination this
  · rw [hrot2, hrot0, R.hc, cast_gTau]
    have := congrArg (Rat.cast : ℚ → ℝ) k12; simp only [Qf] at this; push_cast at this
    push_cast; linear_combination this

end tiles

/-- Swap the labels `0 ↔ 1` of `Δ`: the angle at `Δ₀` becomes the angle at vertex `1`. -/
noncomputable def _root_.Erdos634.LaczL22.RTri.sw01 (R : RTri) : RTri where
  Δ := R.Δ.relabel (Equiv.swap 0 1)
  a := R.b
  b := R.a
  c := R.c
  ha := by
    have e1 : (Equiv.swap (0 : Fin 3) 1) 1 = 0 := by decide
    have e2 : (Equiv.swap (0 : Fin 3) 1) 2 = 2 := by decide
    simp only [Tri.relabel_pts, e1, e2]
    rw [dist_comm]; exact R.hb
  hb := by
    have e0 : (Equiv.swap (0 : Fin 3) 1) 0 = 1 := by decide
    have e2 : (Equiv.swap (0 : Fin 3) 1) 2 = 2 := by decide
    simp only [Tri.relabel_pts, e0, e2]
    rw [dist_comm]; exact R.ha
  hc := by
    have e0 : (Equiv.swap (0 : Fin 3) 1) 0 = 1 := by decide
    have e1 : (Equiv.swap (0 : Fin 3) 1) 1 = 0 := by decide
    simp only [Tri.relabel_pts, e0, e1]
    rw [dist_comm]; exact R.hc
  pa := R.pb
  pb := R.pa
  pc := R.pc

section trap
variable (R : RTri) (a0 : ℚ) (ha0q : 0 < a0) (ha1q : a0 < 1)
  (hA : R.a = a0 * R.c) (hB : R.b = (1 - a0 ^ 2) * R.c)
  (A w d : Plane) (h : w 0 * d 1 - w 1 * d 0 ≠ 0)
  (hw : inner ℝ w w = ((q1W a0 R.c : ℚ) : ℝ) ^ 2) (hd : inner ℝ d d = (R.c : ℝ) ^ 2)
  (hwd : inner ℝ w d = ((q1G a0 R.c : ℚ) : ℝ))

include ha0q ha1q hA hB hw hd hwd

theorem t1_trap : ChartRSD R A w d h (trapSet (gTau (a0 : ℝ))) := by
  have hb0 : 0 < 1 - a0 ^ 2 := by nlinarith
  have hc := R.pc
  have hWpos : 0 < q1W a0 R.c := by
    unfold q1W q1N; positivity
  have hcos : R.sw01.cos1 = (2 - a0 ^ 2) / 2 := by
    simp only [RTri.cos1, RTri.sw01, hA, hB]
    field_simp; ring
  have hwd' : inner ℝ w d = ((q1W a0 R.c : ℚ) : ℝ) * (R.c : ℝ) * (R.sw01.cos1 : ℝ) := by
    rw [hwd, hcos]; simp only [q1G]; push_cast; ring
  have hτ : q1Tau a0 = tTau R.sw01.a R.sw01.b R.sw01.c (q1W a0 R.c) R.c := by
    simp only [tTau, RTri.sw01, hA, hB, q1Tau, q1N, q1W]
    have ha' := ha0q.ne'
    have hN : a0 ^ 2 + (1 - a0 ^ 2) ^ 2 ≠ 0 := by positivity
    have hc' := hc.ne'
    have hb' : (1 - a0 ^ 2) ≠ 0 := hb0.ne'
    field_simp
    ring
  have hτpos : 0 < q1Tau a0 := by unfold q1Tau q1N; positivity
  have key := trap_ii R.sw01 A w d h (q1W a0 R.c) R.c hWpos hc hw hd hwd' (q1Tau a0) hτ hτpos
  rw [cast_gTau]
  exact RatSimDiss.relabel (Δ := R.Δ) (Equiv.swap 0 1) key


end trap

section chart
variable (R : RTri) (a0 : ℚ) (ha0q : 0 < a0) (ha1q : a0 < 1)
  (hA : R.a = a0 * R.c) (hB : R.b = (1 - a0 ^ 2) * R.c)
  (A w d : Plane) (h : w 0 * d 1 - w 1 * d 0 ≠ 0)
  (hw : inner ℝ w w = ((q1W a0 R.c : ℚ) : ℝ) ^ 2) (hd : inner ℝ d d = (R.c : ℝ) ^ 2)
  (hwd : inner ℝ w d = ((q1G a0 R.c : ℚ) : ℝ))

include ha0q ha1q hA hB hw hd hwd

/-- **Fig. 4 in the chart**: the target triangle `GBE` is a union of finitely many rational triangles
similar to `Δ`. -/
theorem t1_chart (ha0 : 0 < (a0 : ℝ)) (ha1 : (a0 : ℝ) < 1) :
    ChartRSD R A w d h (triT1 (a0 : ℝ) ha0 ha1).carrier := by
  have hcT : ∀ T : Tri, IsClosed T.carrier := fun T => T.isCompact.isClosed
  have c1 := t1_trap R a0 ha0q ha1q hA hB A w d h hw hd hwd
  have c2 := chart_single (R := R) (A := A) (w := w) (d := d) (h := h) _
    (tile_BCA R a0 ha0q ha1q hA hB A w d h hw hd hwd ha0 ha1)
  have c3 := chart_single (R := R) (A := A) (w := w) (d := d) (h := h) _
    (tile_ACD R a0 ha0q ha1q hA hB A w d h hw hd hwd ha0 ha1)
  have c4 := chart_single (R := R) (A := A) (w := w) (d := d) (h := h) _
    (tile_ADE R a0 ha0q ha1q hA hB A w d h hw hd hwd ha0 ha1)
  have c5 := chart_single (R := R) (A := A) (w := w) (d := d) (h := h) _
    (tile_CDF R a0 ha0q ha1q hA hB A w d h hw hd hwd ha0 ha1)
  have hcl1 := isClosed_trapSet (gTau (a0 : ℝ))
  have hcl2 := hcl1.union (hcT (triBCA (a0 : ℝ) ha0 ha1))
  have hcl3 := hcl2.union (hcT (triACD (a0 : ℝ) ha0 ha1))
  have u2 := chart_union c1 c2 (trap_BCA ha0 ha1)
  have d3 : Disjoint (interior (trapSet (gTau (a0 : ℝ)) ∪ (triBCA (a0 : ℝ) ha0 ha1).carrier))
      (interior (triACD (a0 : ℝ) ha0 ha1).carrier) :=
    disjoint_interior_union hcl1 (trap_ACD ha0 ha1) (ACD_BCA ha0 ha1).symm
  have u3 := chart_union u2 c3 d3
  have d4 : Disjoint (interior (trapSet (gTau (a0 : ℝ)) ∪ (triBCA (a0 : ℝ) ha0 ha1).carrier
        ∪ (triACD (a0 : ℝ) ha0 ha1).carrier)) (interior (triADE (a0 : ℝ) ha0 ha1).carrier) :=
    disjoint_interior_union hcl2
      (disjoint_interior_union hcl1 (trap_ADE ha0 ha1) (ADE_BCA ha0 ha1).symm)
      (ACD_ADE ha0 ha1)
  have u4 := chart_union u3 c4 d4
  have d5 : Disjoint (interior (trapSet (gTau (a0 : ℝ)) ∪ (triBCA (a0 : ℝ) ha0 ha1).carrier
        ∪ (triACD (a0 : ℝ) ha0 ha1).carrier ∪ (triADE (a0 : ℝ) ha0 ha1).carrier))
      (interior (triCDF (a0 : ℝ) ha0 ha1).carrier) :=
    disjoint_interior_union hcl3
      (disjoint_interior_union hcl2
        (disjoint_interior_union hcl1 (trap_CDF ha0 ha1) (CDF_BCA ha0 ha1).symm)
        (CDF_ACD ha0 ha1).symm)
      (CDF_ADE ha0 ha1).symm
  have u5 := chart_union u4 c5 d5
  refine chart_mono_eq u5 ?_
  rw [T1_carrier ha0 ha1]
  exact (Set.Subset.antisymm (pieces_sub_T1 ha0 ha1) (T1_sub_pieces ha0 ha1))

end chart

/-- Existence of a chart with prescribed Gram data. -/
theorem exists_gram_chart (W Dd cosv : ℝ) (hW : 0 < W) (hD : 0 < Dd) (hc : cosv ^ 2 < 1) :
    ∃ w d : Plane, inner ℝ w w = W ^ 2 ∧ inner ℝ d d = Dd ^ 2 ∧ inner ℝ w d = W * Dd * cosv ∧
      w 0 * d 1 - w 1 * d 0 ≠ 0 := by
  have hs : 0 < Real.sqrt (1 - cosv ^ 2) := Real.sqrt_pos.mpr (by linarith)
  have hs2 : Real.sqrt (1 - cosv ^ 2) ^ 2 = 1 - cosv ^ 2 := Real.sq_sqrt (by linarith)
  refine ⟨mkPt W 0, mkPt (Dd * cosv) (Dd * Real.sqrt (1 - cosv ^ 2)), ?_, ?_, ?_, ?_⟩
  · simp only [PiLp.inner_apply, Fin.sum_univ_two, mkPt_zero, mkPt_one, RCLike.inner_apply,
      conj_trivial]
    ring
  · simp only [PiLp.inner_apply, Fin.sum_univ_two, mkPt_zero, mkPt_one, RCLike.inner_apply,
      conj_trivial]
    nlinarith [hs2]
  · simp only [PiLp.inner_apply, Fin.sum_univ_two, mkPt_zero, mkPt_one, RCLike.inner_apply,
      conj_trivial]
    ring
  · simp only [mkPt_zero, mkPt_one]
    have : W * (Dd * Real.sqrt (1 - cosv ^ 2)) - 0 * (Dd * cosv) ≠ 0 := by
      have := mul_pos hW (mul_pos hD hs); nlinarith
    exact this


theorem q1_EC (a0 c : ℚ) (ha : 0 < a0) :
    q1E a0 * c = 2 * q1W a0 c * ((2 - a0 ^ 2) / 2) := by
  have ha' := ha.ne'
  simp only [q1E, q1Del, q1W, q1N]
  field_simp
  ring

/-- **Laczkovich Theorem 2.4, first triple `(α, α, π - 2α)`** (Fig. 4).  `Δ` a rational triangle with
`a = a₀ c`, `b = (1 - a₀²) c`, `0 < a₀ < 1` (i.e. `sin(α/2) = a₀/2` rational and
`β = (π - 3α)/2`, `γ = (π + α)/2`, in the form of the side ratios `a/c = 2 sin(α/2)`,
`b/c = 1 - 4 sin²(α/2)`).  Then the explicit isosceles triangle `T = G B E` (`|BG| = |BE|`,
angle `α` at `G`) is the union of finitely many congruent triangles, each similar to `Δ`
(model `scaleTri (1/q) Δ`): a `CongruentRegionDissection` of `T`. -/
theorem thm24_first (R : RTri) (a0 : ℚ) (ha0q : 0 < a0) (ha1q : a0 < 1)
    (hA : R.a = a0 * R.c) (hB : R.b = (1 - a0 ^ 2) * R.c) :
    ∃ (T : Tri) (q : ℕ) (hq : 0 < q) (M : ℕ)
      (C : Erdos634.RegionDissection.CongruentRegionDissection M),
      C.region = T.carrier ∧
      C.model = scaleTri (1 / (q : ℝ)) (one_div_pos.mpr (Nat.cast_pos.mpr hq)).ne' R.Δ ∧
      dist (T.pts 1) (T.pts 0) = dist (T.pts 1) (T.pts 2) ∧
      cornerAngle (T.pts 1) (T.pts 0) (T.pts 2)
        = cornerAngle (R.Δ.pts 1) (R.Δ.pts 0) (R.Δ.pts 2) := by
  have hc := R.pc
  have ha0 : (0 : ℝ) < a0 := by exact_mod_cast ha0q
  have ha1 : (a0 : ℝ) < 1 := by exact_mod_cast ha1q
  have hb0 : 0 < 1 - a0 ^ 2 := by nlinarith
  have hWpos : 0 < q1W a0 R.c := by unfold q1W q1N; positivity
  have hW' : (0 : ℝ) < ((q1W a0 R.c : ℚ) : ℝ) := by exact_mod_cast hWpos
  have hc' : (0 : ℝ) < (R.c : ℝ) := by exact_mod_cast hc
  have hcos2 : (((2 - a0 ^ 2) / 2 : ℚ) : ℝ) ^ 2 < 1 := by
    have h1 : ((2 - a0 ^ 2) / 2 : ℚ) < 1 := by nlinarith
    have h2 : 0 < ((2 - a0 ^ 2) / 2 : ℚ) := by nlinarith
    have : (((2 - a0 ^ 2) / 2 : ℚ) : ℝ) < 1 := by exact_mod_cast h1
    have : (0 : ℝ) < (((2 - a0 ^ 2) / 2 : ℚ) : ℝ) := by exact_mod_cast h2
    nlinarith
  obtain ⟨w, d, hw0, hd0, hwd0, hdet⟩ := exists_gram_chart ((q1W a0 R.c : ℚ) : ℝ) (R.c : ℝ)
    (((2 - a0 ^ 2) / 2 : ℚ) : ℝ) hW' hc' hcos2
  have hw : inner ℝ w w = ((q1W a0 R.c : ℚ) : ℝ) ^ 2 := hw0
  have hd : inner ℝ d d = (R.c : ℝ) ^ 2 := hd0
  have hwd : inner ℝ w d = ((q1G a0 R.c : ℚ) : ℝ) := by
    rw [hwd0]; simp only [q1G]; push_cast; ring
  set Φ := chartEquiv 0 w d hdet with hΦ
  have key := t1_chart R a0 ha0q ha1q hA hB 0 w d hdet hw hd hwd ha0 ha1
  obtain ⟨q, hq, M, C, hC1, hC2⟩ := RatSimDiss.toCongruent R.rational key
  refine ⟨Erdos634.DissectionMap.mapTri Φ (triT1 (a0 : ℝ) ha0 ha1), q, hq, M, C, ?_, hC2, ?_, ?_⟩
  · rw [hC1, Erdos634.DissectionMap.mapTri_carrier]
  · -- isosceles
    have hE : gE (a0 : ℝ) = ((q1E a0 : ℚ) : ℝ) := cast_gE a0
    have hEC := congrArg (Rat.cast : ℚ → ℝ) (q1_EC a0 R.c ha0q)
    push_cast at hEC
    refine eq_of_sq_eq' dist_nonneg dist_nonneg ?_
    show dist (Φ (mkPt 1 0)) (Φ (mkPt 0 0)) ^ 2 = dist (Φ (mkPt 1 0)) (Φ (mkPt 0 (gE (a0 : ℝ)))) ^ 2
    rw [dist_chart_sq, dist_chart_sq]
    simp only [mkPt_zero, mkPt_one]
    rw [hw, hd, hwd]
    rw [hE]
    simp only [q1G]
    push_cast
    linear_combination (-(((q1E a0 : ℚ) : ℝ) * (R.c : ℝ))) * hEC
  · -- the angle at G
    have he : (0 : ℝ) < gE (a0 : ℝ) := by
      have := gE_gt ha0 ha1; have := gDel_gt ha0 ha1; linarith
    have e1 : Φ (mkPt 1 0) - Φ (mkPt 0 0) = w := by
      rw [hΦ, chartEquiv_apply, chartEquiv_apply]; simp only [mkPt_zero, mkPt_one]; module
    have e2 : Φ (mkPt 0 (gE (a0 : ℝ))) - Φ (mkPt 0 0) = gE (a0 : ℝ) • d := by
      rw [hΦ, chartEquiv_apply, chartEquiv_apply]; simp only [mkPt_zero, mkPt_one]; module
    have hwn : ‖w‖ = ((q1W a0 R.c : ℚ) : ℝ) := by
      refine eq_of_sq_eq' (norm_nonneg _) hW'.le ?_
      rw [← real_inner_self_eq_norm_sq]; exact hw
    have hdn : ‖d‖ = (R.c : ℝ) := by
      refine eq_of_sq_eq' (norm_nonneg _) hc'.le ?_
      rw [← real_inner_self_eq_norm_sq]; exact hd
    have h1 : ‖R.Δ.pts 1 - R.Δ.pts 0‖ = R.c := by rw [← dist_eq_norm, dist_comm]; exact R.hc
    have h2 : ‖R.Δ.pts 2 - R.Δ.pts 0‖ = R.b := by rw [← dist_eq_norm]; exact R.hb
    show EuclideanGeometry.angle (Φ (mkPt 1 0)) (Φ (mkPt 0 0)) (Φ (mkPt 0 (gE (a0 : ℝ))))
      = EuclideanGeometry.angle (R.Δ.pts 1) (R.Δ.pts 0) (R.Δ.pts 2)
    unfold EuclideanGeometry.angle
    simp only [vsub_eq_sub]
    rw [e1, e2, InnerProductGeometry.angle_smul_right_of_pos _ _ he]
    unfold InnerProductGeometry.angle
    rw [R.inner_uv, h1, h2, hwd0, hwn, hdn, hA, hB]
    congr 1
    have hW0 : ((q1W a0 R.c : ℚ) : ℝ) ≠ 0 := hW'.ne'
    have hc0 : (R.c : ℝ) ≠ 0 := hc'.ne'
    have hb00 : (1 - (a0 : ℝ) ^ 2) ≠ 0 := by
      have : (0 : ℝ) < 1 - (a0 : ℝ) ^ 2 := by nlinarith
      exact this.ne'
    push_cast
    field_simp
    ring

end Erdos634.LaczL24
