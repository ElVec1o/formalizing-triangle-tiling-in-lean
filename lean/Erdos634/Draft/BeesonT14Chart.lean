import Erdos634.Draft.ZhangThm7

/-!
# Beeson Theorem 14, general parameters: affine chart and gluing in chart coordinates

A point `(X, W)` of the chart `CS alpha beta` is the plane point `(alpha * X, beta * W)`.
`CS alpha beta p` is the set of plane points whose chart pair satisfies `p`.
Credit Beeson (arXiv 1206.2229), Beeson-Zhang, Zhang (arXiv 2512.22696), Laczkovich.  UNAUDITED.
-/

namespace Erdos634.BeesonT14Chart

open Erdos634.Geometry Erdos634.CertCoord Erdos634.CertGeom Erdos634.RegionDissection
  Erdos634.GlueCut Erdos634.SssCongruent Erdos634.ZhangL1 Erdos634.ZhangPara
  Erdos634.ZhangSporadic Erdos634.ZhangThm4

noncomputable def detR (x0 w0 x1 w1 x2 w2 : ℝ) : ℝ := (x1 - x0) * (w2 - w0) - (x2 - x0) * (w1 - w0)

noncomputable def lnR (px pw qx qw X W : ℝ) : ℝ := (qx - px) * (W - pw) - (X - px) * (qw - pw)

def CS (α β : ℝ) (p : ℝ → ℝ → Prop) : Set Plane := {q | p (q 0 / α) (q 1 / β)}

variable {α β : ℝ}

theorem det3_chart (hα : α ≠ 0) (hβ : β ≠ 0) (x1 w1 x2 w2 : ℝ) (q : Plane) :
    det3 (q 0) (q 1) (α * x1) (β * w1) (α * x2) (β * w2) =
      α * β * detR (q 0 / α) (q 1 / β) x1 w1 x2 w2 := by
  simp only [det3, detR]; field_simp

theorem det3_chart2 (hα : α ≠ 0) (hβ : β ≠ 0) (x0 w0 x2 w2 : ℝ) (q : Plane) :
    det3 (α * x0) (β * w0) (q 0) (q 1) (α * x2) (β * w2) =
      α * β * detR x0 w0 (q 0 / α) (q 1 / β) x2 w2 := by
  simp only [det3, detR]; field_simp

theorem det3_chart3 (hα : α ≠ 0) (hβ : β ≠ 0) (x0 w0 x1 w1 : ℝ) (q : Plane) :
    det3 (α * x0) (β * w0) (α * x1) (β * w1) (q 0) (q 1) =
      α * β * detR x0 w0 x1 w1 (q 0 / α) (q 1 / β) := by
  simp only [det3, detR]; field_simp

theorem TriSet_CS (hα : 0 < α) (hβ : 0 < β) (x0 w0 x1 w1 x2 w2 : ℝ) :
    TriSet (α * x0) (β * w0) (α * x1) (β * w1) (α * x2) (β * w2) =
      CS α β (fun X W => 0 ≤ detR X W x1 w1 x2 w2 ∧ 0 ≤ detR x0 w0 X W x2 w2 ∧
        0 ≤ detR x0 w0 x1 w1 X W) := by
  ext q
  simp only [TriSet, CS, Set.mem_setOf_eq]
  have hp : 0 < α * β := mul_pos hα hβ
  rw [det3_chart hα.ne' hβ.ne', det3_chart2 hα.ne' hβ.ne', det3_chart3 hα.ne' hβ.ne',
    mul_nonneg_iff_of_pos_left hp, mul_nonneg_iff_of_pos_left hp, mul_nonneg_iff_of_pos_left hp]

theorem lineFun_chart (hα : α ≠ 0) (hβ : β ≠ 0) (px pw qx qw : ℝ) (q : Plane) :
    lineFun (α * px) (β * pw) (α * qx) (β * qw) q =
      α * β * lnR px pw qx qw (q 0 / α) (q 1 / β) := by
  simp only [lineFun_apply, lnR]; field_simp

theorem glueR {R : Tri} {p1 p2 : ℝ → ℝ → Prop} {n1 n2 : ℕ} (hα : 0 < α) (hβ : 0 < β)
    (h1 : Dis R (CS α β p1) n1) (h2 : Dis R (CS α β p2) n2) (px pw qx qw : ℝ)
    (hne : px ≠ qx ∨ pw ≠ qw)
    (hS1 : ∀ X W, p1 X W → lnR px pw qx qw X W ≤ 0)
    (hS2 : ∀ X W, p2 X W → 0 ≤ lnR px pw qx qw X W) :
    Dis R (CS α β (fun X W => p1 X W ∨ p2 X W)) (n1 + n2) := by
  have hp : 0 < α * β := mul_pos hα hβ
  have hne' : α * px ≠ α * qx ∨ β * pw ≠ β * qw := by
    rcases hne with h | h
    · exact Or.inl (fun e => h (mul_left_cancel₀ hα.ne' e))
    · exact Or.inr (fun e => h (mul_left_cancel₀ hβ.ne' e))
  refine (Dis.glue_line h1 h2 (α * px) (β * pw) (α * qx) (β * qw) hne' ?_ ?_).congr ?_ rfl
  · intro q hq
    rw [lineFun_chart hα.ne' hβ.ne']
    have := hS1 _ _ hq
    nlinarith
  · intro q hq
    rw [lineFun_chart hα.ne' hβ.ne']
    have := hS2 _ _ hq
    nlinarith
  · ext q; rfl

theorem glueQ {R : Tri} {p1 p2 : ℝ → ℝ → Prop} {n1 n2 : ℕ} (hα : 0 < α) (hβ : 0 < β)
    (h1 : Dis R (CS α β p1) n1) (h2 : Dis R (CS α β p2) n2) (px pw qx qw rx rw' sx sw : ℝ)
    (hne : px ≠ qx ∨ pw ≠ qw) (hne2 : rx ≠ sx ∨ rw' ≠ sw)
    (hS1 : ∀ X W, p1 X W → lnR px pw qx qw X W ≤ 0)
    (hS1' : ∀ X W, p1 X W → lnR rx rw' sx sw X W ≤ 0)
    (hS2 : ∀ X W, p2 X W → 0 ≤ lnR px pw qx qw X W ∨ 0 ≤ lnR rx rw' sx sw X W) :
    Dis R (CS α β (fun X W => p1 X W ∨ p2 X W)) (n1 + n2) := by
  have hp : 0 < α * β := mul_pos hα hβ
  have hne' : α * px ≠ α * qx ∨ β * pw ≠ β * qw := by
    rcases hne with h | h
    · exact Or.inl (fun e => h (mul_left_cancel₀ hα.ne' e))
    · exact Or.inr (fun e => h (mul_left_cancel₀ hβ.ne' e))
  have hne2' : α * rx ≠ α * sx ∨ β * rw' ≠ β * sw := by
    rcases hne2 with h | h
    · exact Or.inl (fun e => h (mul_left_cancel₀ hα.ne' e))
    · exact Or.inr (fun e => h (mul_left_cancel₀ hβ.ne' e))
  have hd : Disjoint (interior (CS α β p1)) (interior (CS α β p2)) := by
    refine (disjoint_quadrant (S := CS α β p2) (T := CS α β p1)
      (lineFun (α * px) (β * pw) (α * qx) (β * qw)) (lineFun (α * rx) (β * rw') (α * sx) (β * sw))
      (lineFun_linear_ne_zero hne') (lineFun_linear_ne_zero hne2') ?_ ?_ ?_).symm
    · intro q hq; rw [lineFun_chart hα.ne' hβ.ne']; have := hS1 _ _ hq; nlinarith
    · intro q hq; rw [lineFun_chart hα.ne' hβ.ne']; have := hS1' _ _ hq; nlinarith
    · intro q hq
      rcases hS2 _ _ hq with h | h
      · left; rw [lineFun_chart hα.ne' hβ.ne']; nlinarith
      · right; rw [lineFun_chart hα.ne' hβ.ne']; nlinarith
  refine (Dis.glue_disj h1 h2 hd).congr ?_ rfl
  ext q; rfl

end Erdos634.BeesonT14Chart
