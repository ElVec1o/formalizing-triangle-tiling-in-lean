import Erdos634.Draft.LaczFormalL24Main

/-!
# Laczkovich Theorem 2.5, first triple `(α, α+β, α+2β)`: chart geometry of Fig. 6

NOTE, UNAUDITED.  Credit: Laczkovich (Discrete Math. 140 (1995) 79-94, Theorem 2.5, Fig. 6), Beeson,
Beeson-Zhang, Zhang.

Setting: `Δ = (a, b, c)` rational with `γ = 2π/3` (`c² = a² + ab + b²`, so `α + β = π/3`).  The paper's points
`D, E, F` (Fig. 6) with the free rational length `CF` chosen as `CF = a`.  In the chart
`(D; w = F - D, d = A - D)` (`|w| = W = a + 2b`, `|d| = c`, `⟨w,d⟩ = W²/2`) put `τ = b/W`, `ρ = 1 - τ = (a+b)/W`:

* `D = (0,0)`, `F = (1,0)`, `A = (0,1)`, `B = (0,2)`, `C = (τ,1)`, `E = (2ρ,0)`;
* target `T = E B D`;  `T = FDAC ∪ ABC ∪ BEFC`, where `FDAC = trapSet τ` (Lemma 2.2 (ii)),
  `ABC` is the tile, `BEFC` is the isosceles trapezoid of Lemma 2.2 (iii).

This file: pure real geometry of the cover and of the pairwise disjointness (parameter `0 < τ < 1/2`).
-/

namespace Erdos634.LaczL25

open Erdos634.Geometry Erdos634.CertCoord Erdos634.LaczL22 Erdos634.LaczL24

/-- The tile `ABC`: `A = (0,1)`, `B = (0,2)`, `C = (τ,1)`. -/
def SA (τ : ℝ) : Set Plane := {z | 0 ≤ z 0 ∧ 1 ≤ z 1 ∧ z 0 + τ * z 1 ≤ 2 * τ}

/-- The isosceles trapezoid `BEFC`. -/
def SB (τ : ℝ) : Set Plane :=
  {z | 0 ≤ z 1 ∧ 2 * τ ≤ z 0 + τ * z 1 ∧ 1 ≤ z 0 + (1 - τ) * z 1 ∧ z 0 + (1 - τ) * z 1 ≤ 2 * (1 - τ)}

/-- The target `T = E B D` in the chart. -/
def ST (τ : ℝ) : Set Plane := {z | 0 ≤ z 0 ∧ 0 ≤ z 1 ∧ z 0 + (1 - τ) * z 1 ≤ 2 * (1 - τ)}

private theorem htri5 : ∀ k : Fin 3, k = 0 ∨ k = 1 ∨ k = 2 := by decide

section geo
variable {τ : ℝ} (h0 : 0 < τ) (h1 : τ < 1 / 2)
include h0 h1

theorem cover_sub (z : Plane) (hz : z ∈ ST τ) : z ∈ (trapSet τ ∪ SA τ) ∪ SB τ := by
  obtain ⟨hs, ht, hh⟩ := hz
  have hd : 0 < 1 - 2 * τ := by linarith
  by_cases e1 : z 1 ≤ 1
  · by_cases e2 : z 0 + (1 - τ) * z 1 ≤ 1
    · left; left
      refine ⟨ht, e1, hs, ?_⟩
      nlinarith
    · right
      push_neg at e2
      refine ⟨ht, ?_, e2.le, hh⟩
      nlinarith [mul_nonneg hd.le (sub_nonneg.2 e1)]
  · push_neg at e1
    by_cases e2 : z 0 + τ * z 1 ≤ 2 * τ
    · left; right; exact ⟨hs, e1.le, e2⟩
    · right
      push_neg at e2
      refine ⟨ht, e2.le, ?_, hh⟩
      nlinarith [mul_nonneg hd.le (sub_nonneg.2 e1.le)]

theorem pieces_sub (z : Plane) (hz : z ∈ (trapSet τ ∪ SA τ) ∪ SB τ) : z ∈ ST τ := by
  have hd : 0 < 1 - 2 * τ := by linarith
  rcases hz with (hz | hz) | hz
  · obtain ⟨a1, a2, a3, a4⟩ := hz
    refine ⟨a3, a1, ?_⟩
    nlinarith
  · obtain ⟨a1, a2, a3⟩ := hz
    refine ⟨a1, by linarith, ?_⟩
    nlinarith [mul_nonneg hd.le (sub_nonneg.2 a2)]
  · obtain ⟨a1, a2, a3, a4⟩ := hz
    refine ⟨?_, a1, a4⟩
    -- from `z 0 + (1-τ) z 1 ≤ 2(1-τ)` and `z 0 + τ z 1 ≥ 2 τ`: subtract
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 - τ) (sub_nonneg.2 a2),
      mul_nonneg h0.le (by nlinarith : (0:ℝ) ≤ 2 * (1 - τ) - (z 0 + (1 - τ) * z 1))]

theorem cover_eq : (trapSet τ ∪ SA τ) ∪ SB τ = ST τ :=
  Set.Subset.antisymm (fun z hz => pieces_sub h0 h1 z hz) (fun z hz => cover_sub h0 h1 z hz)

theorem disj_FA : Disjoint (interior (trapSet τ)) (interior (SA τ)) :=
  sepY 1 (fun z hz => hz.2.1) (fun z hz => hz.2.1)

theorem disj_AB : Disjoint (interior (SA τ)) (interior (SB τ)) :=
  disjoint_interior_of_sep (coordFun 1 τ 0) (coordFun_linear_ne_zero 0 (Or.inl one_ne_zero)) (2 * τ)
    (fun z hz => by show 1 * z 0 + τ * z 1 + 0 ≤ 2 * τ; linarith [hz.2.2])
    (fun z hz => by show 2 * τ ≤ 1 * z 0 + τ * z 1 + 0; linarith [hz.2.1])

theorem disj_FB : Disjoint (interior (trapSet τ)) (interior (SB τ)) :=
  disjoint_interior_of_sep (coordFun 1 (1 - τ) 0) (coordFun_linear_ne_zero 0 (Or.inl one_ne_zero)) 1
    (fun z hz => by
      show 1 * z 0 + (1 - τ) * z 1 + 0 ≤ 1
      obtain ⟨_, _, _, a4⟩ := hz
      nlinarith)
    (fun z hz => by show 1 ≤ 1 * z 0 + (1 - τ) * z 1 + 0; linarith [hz.2.2.1])

theorem convex_ST : Convex ℝ (ST τ) := by
  intro x hx y hy p q hp hq hpq
  obtain ⟨hx1, hx2, hx3⟩ := hx
  obtain ⟨hy1, hy2, hy3⟩ := hy
  simp only [ST, Set.mem_setOf_eq, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  obtain rfl : q = 1 - p := by linarith
  refine ⟨?_, ?_, ?_⟩
  · nlinarith [mul_nonneg hp hx1, mul_nonneg hq hy1]
  · nlinarith [mul_nonneg hp hx2, mul_nonneg hq hy2]
  · nlinarith [mul_nonneg hp (sub_nonneg.2 hx3), mul_nonneg hq (sub_nonneg.2 hy3)]

theorem convex_SA : Convex ℝ (SA τ) := by
  intro x hx y hy p q hp hq hpq
  obtain ⟨hx1, hx2, hx3⟩ := hx
  obtain ⟨hy1, hy2, hy3⟩ := hy
  simp only [SA, Set.mem_setOf_eq, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  obtain rfl : q = 1 - p := by linarith
  refine ⟨?_, ?_, ?_⟩
  · nlinarith [mul_nonneg hp hx1, mul_nonneg hq hy1]
  · nlinarith [mul_nonneg hp (sub_nonneg.2 hx2), mul_nonneg hq (sub_nonneg.2 hy2)]
  · nlinarith [mul_nonneg hp (sub_nonneg.2 hx3), mul_nonneg hq (sub_nonneg.2 hy3)]

/-- The target triangle `D E B`: chart vertices `(0,0), (2ρ,0), (0,2)`. -/
noncomputable def triTT : Tri :=
  mkTri 0 0 (2 * (1 - τ)) 0 0 2 (by simp only [det3]; nlinarith)

/-- The tile `A B C`: chart vertices `(0,1), (0,2), (τ,1)`. -/
noncomputable def triAB : Tri :=
  mkTri 0 1 0 2 τ 1 (by simp only [det3]; nlinarith)

theorem triTT_carrier : (triTT (τ := τ) h0 h1).carrier = ST τ := by
  have hr : 0 < 1 - τ := by linarith
  apply Set.Subset.antisymm
  · refine convexHull_min (Set.range_subset_iff.mpr ?_) (convex_ST h0 h1)
    intro k
    rcases htri5 k with rfl | rfl | rfl
    · show (mkPt 0 0) ∈ ST τ; simp [ST]; linarith
    · show (mkPt (2 * (1 - τ)) 0) ∈ ST τ; simp [ST]; linarith
    · show (mkPt 0 2) ∈ ST τ; simp [ST]; linarith
  · intro z hz
    obtain ⟨hs, ht, hh⟩ := hz
    rw [← mkPt_self z]
    refine mem_mkTri_of_dets (x0 := 0) (y0 := 0) (x1 := 2 * (1 - τ)) (y1 := 0) (x2 := 0) (y2 := 2) _ ?_ ?_ ?_
    · simp only [det3]; apply div_nonneg <;> nlinarith
    · simp only [det3]; apply div_nonneg <;> nlinarith
    · simp only [det3]; apply div_nonneg <;> nlinarith

theorem triAB_carrier : (triAB (τ := τ) h0).carrier = SA τ := by
  apply Set.Subset.antisymm
  · refine convexHull_min (Set.range_subset_iff.mpr ?_) (convex_SA h0 h1)
    intro k
    rcases htri5 k with rfl | rfl | rfl
    · show (mkPt 0 1) ∈ SA τ; simp [SA]; linarith
    · show (mkPt 0 2) ∈ SA τ; simp [SA]; linarith
    · show (mkPt τ 1) ∈ SA τ; refine ⟨?_, ?_, ?_⟩ <;> simp <;> linarith
  · intro z hz
    obtain ⟨hs, ht, hh⟩ := hz
    rw [← mkPt_self z]
    refine mem_mkTri_of_dets (x0 := 0) (y0 := 1) (x1 := 0) (y1 := 2) (x2 := τ) (y2 := 1) _ ?_ ?_ ?_
    · simp only [det3]; apply div_nonneg_of_nonpos <;> nlinarith
    · simp only [det3]; apply div_nonneg_of_nonpos <;> nlinarith
    · simp only [det3]; apply div_nonneg_of_nonpos <;> nlinarith

end geo

end Erdos634.LaczL25
