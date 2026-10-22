-- Draft/LaczFormalIVcRatB7d.lean -- Laczkovich DCG 48 (2012), Sect. 8.3 (Subcase IVc, rational branch), BLUEPRINT Part B, item B7, stage d: the FRAME (U; p, q) and the CELL WEDGE.
--   `Frame b`: a point U and vectors p, q with |p|^2 = |q|^2 = b^2, p.q = b^2/2 (so the triangle U, U+p, U+q is equilateral of side b); coordinates `fa`, `fb` (y = U + fa p + fb q), `Frame.pt a beta`.
--   `cell_wedge`: an equilateral cell c (congruent to eqT b) with a vertex at U that lies in the half plane {fb >= 0} and misses the open box (-1,0) x (0,1) of the frame is the triangle (U, U+p, U+q):
--   its other two vertices are F.pt 1 0 and F.pt 0 1 (in either order).  Route: unit vectors e1, e2 of the two other vertices (Q = 1), e1.e2 = b^2/2 (B = 1/2), `wedge_basis` (B7a).
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 8.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIVcRatB7c
import Erdos634.Draft.LaczFormalIVcRatB7a

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement Erdos634.CertCoord

namespace Erdos634.Draft.LaczFormal.RG

theorem dist_sq7 (x y : Plane) : dist x y ^ 2 = (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 := by
  rw [EuclideanSpace.dist_eq, Real.sq_sqrt (by positivity)]
  simp [Fin.sum_univ_two, Real.dist_eq, sq_abs]

theorem fin3_ne7 (j : Fin 3) : j + 1 ≠ j ∧ j + 2 ≠ j ∧ j + 1 ≠ j + 2 := by revert j; decide

/-- A frame: origin `U`, vectors `p`, `q` with `|p| = |q| = b`, `p.q = b^2/2`. -/
structure Frame (b : ℝ) where
  U0 : ℝ
  U1 : ℝ
  p0 : ℝ
  p1 : ℝ
  q0 : ℝ
  q1 : ℝ
  hp : p0 ^ 2 + p1 ^ 2 = b ^ 2
  hq : q0 ^ 2 + q1 ^ 2 = b ^ 2
  hpq : p0 * q0 + p1 * q1 = b ^ 2 / 2

namespace Frame
variable {b : ℝ} (F : Frame b)

noncomputable def D : ℝ := F.p0 * F.q1 - F.p1 * F.q0

theorem D_ne (hb : 0 < b) : F.D ≠ 0 := by
  intro h
  have h1 : (F.p0 * F.q1 - F.p1 * F.q0) ^ 2 + (F.p0 * F.q0 + F.p1 * F.q1) ^ 2 = (F.p0 ^ 2 + F.p1 ^ 2) * (F.q0 ^ 2 + F.q1 ^ 2) := by ring
  rw [show F.p0 * F.q1 - F.p1 * F.q0 = 0 from h, F.hpq, F.hp, F.hq] at h1
  have : 0 < b ^ 4 := by positivity
  nlinarith

/-- The point `U + a p + beta q`. -/
noncomputable def pt (a β : ℝ) : Plane := mkPt (F.U0 + a * F.p0 + β * F.q0) (F.U1 + a * F.p1 + β * F.q1)

noncomputable def fa (y : Plane) : ℝ := ((y 0 - F.U0) * F.q1 - (y 1 - F.U1) * F.q0) / F.D
noncomputable def fb (y : Plane) : ℝ := (F.p0 * (y 1 - F.U1) - F.p1 * (y 0 - F.U0)) / F.D

theorem pt_zero (a β : ℝ) : F.pt a β 0 = F.U0 + a * F.p0 + β * F.q0 := by simp [pt]
theorem pt_one (a β : ℝ) : F.pt a β 1 = F.U1 + a * F.p1 + β * F.q1 := by simp [pt]

theorem fa_pt (hb : 0 < b) (a β : ℝ) : F.fa (F.pt a β) = a := by
  have hD := F.D_ne hb
  unfold fa; rw [pt_zero, pt_one, div_eq_iff hD]; unfold D; ring

theorem fb_pt (hb : 0 < b) (a β : ℝ) : F.fb (F.pt a β) = β := by
  have hD := F.D_ne hb
  unfold fb; rw [pt_zero, pt_one, div_eq_iff hD]; unfold D; ring

theorem recon (hb : 0 < b) (y : Plane) : y = F.pt (F.fa y) (F.fb y) := by
  have hD := F.D_ne hb
  apply plane_ext'
  · rw [pt_zero]; unfold fa fb; field_simp; unfold D; ring
  · rw [pt_one]; unfold fa fb; field_simp; unfold D; ring

end Frame

/-- A convex combination of three points of a convex set. -/
theorem convex3 {S : Set Plane} (hS : Convex ℝ S) {u v w : Plane} (hu : u ∈ S) (hv : v ∈ S) (hw : w ∈ S) {s t : ℝ}
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s + t ≤ 1) :
    ∃ y ∈ S, y 0 = (1 - s - t) * u 0 + s * v 0 + t * w 0 ∧ y 1 = (1 - s - t) * u 1 + s * v 1 + t * w 1 := by
  have h := hS.sum_mem (t := (Finset.univ : Finset (Fin 3))) (w := ![1 - s - t, s, t]) (z := ![u, v, w])
    (by intro i _; fin_cases i <;> simp <;> linarith) (by simp [Fin.sum_univ_three]; ring)
    (by intro i _; fin_cases i <;> simp [hu, hv, hw])
  refine ⟨_, h, ?_, ?_⟩ <;> simp [Fin.sum_univ_three]

theorem Frame.coords {b : ℝ} (F : Frame b) (hb : 0 < b) (y : Plane) :
    ∃ a β : ℝ, y 0 = F.U0 + a * F.p0 + β * F.q0 ∧ y 1 = F.U1 + a * F.p1 + β * F.q1 :=
  ⟨F.fa y, F.fb y, by rw [(F.recon hb y)]; simp [Frame.pt_zero, Frame.fa_pt F hb, Frame.fb_pt F hb],
    by rw [(F.recon hb y)]; simp [Frame.pt_one, Frame.fa_pt F hb, Frame.fb_pt F hb]⟩

theorem Frame.fa_fb_of {b : ℝ} (F : Frame b) (hb : 0 < b) {y : Plane} {a β : ℝ} (h0 : y 0 = F.U0 + a * F.p0 + β * F.q0)
    (h1 : y 1 = F.U1 + a * F.p1 + β * F.q1) : F.fa y = a ∧ F.fb y = β := by
  have : y = F.pt a β := plane_ext' (by rw [F.pt_zero]; exact h0) (by rw [F.pt_one]; exact h1)
  rw [this]; exact ⟨F.fa_pt hb a β, F.fb_pt hb a β⟩

/-- **B7d (cell wedge).** -/
theorem cell_wedge {b : ℝ} (F : Frame b) (hb : 0 < b) (c : Tri) (hc : c.Congruent (eqT b hb)) (j : Fin 3)
    (hU : c.pts j = F.pt 0 0) (hbel : ∀ y ∈ c.carrier, 0 ≤ F.fb y)
    (hmiss : ∀ y ∈ c.carrier, ¬ (-1 < F.fa y ∧ F.fa y < 0 ∧ 0 < F.fb y ∧ F.fb y < 1)) :
    (c.pts (j + 1) = F.pt 1 0 ∧ c.pts (j + 2) = F.pt 0 1) ∨ (c.pts (j + 1) = F.pt 0 1 ∧ c.pts (j + 2) = F.pt 1 0) := by
  obtain ⟨h1, h2, h3⟩ := fin3_ne7 j
  have d1 : dist (c.pts (j + 1)) (c.pts j) = b := congr_dist_eqT hb hc h1
  have d2 : dist (c.pts (j + 2)) (c.pts j) = b := congr_dist_eqT hb hc h2
  have d12 : dist (c.pts (j + 1)) (c.pts (j + 2)) = b := congr_dist_eqT hb hc h3
  have hU0 : (c.pts j) 0 = F.U0 := by rw [hU, F.pt_zero]; ring
  have hU1 : (c.pts j) 1 = F.U1 := by rw [hU, F.pt_one]; ring
  obtain ⟨a1, b1, e10, e11⟩ := F.coords hb (c.pts (j + 1))
  obtain ⟨a2, b2, e20, e21⟩ := F.coords hb (c.pts (j + 2))
  have hb2 : 0 < b ^ 2 := by positivity
  have fn := fun x y x' y' => frame_norm F.hp F.hq F.hpq x y x' y'
  have n1 : (a1 * F.p0 + b1 * F.q0) ^ 2 + (a1 * F.p1 + b1 * F.q1) ^ 2 = b ^ 2 := by
    have := dist_sq7 (c.pts (j + 1)) (c.pts j)
    rw [d1, e10, e11, hU0, hU1] at this
    linear_combination (-1 : ℝ) * this
  have n2 : (a2 * F.p0 + b2 * F.q0) ^ 2 + (a2 * F.p1 + b2 * F.q1) ^ 2 = b ^ 2 := by
    have := dist_sq7 (c.pts (j + 2)) (c.pts j)
    rw [d2, e20, e21, hU0, hU1] at this
    linear_combination (-1 : ℝ) * this
  have n12 : ((a1 - a2) * F.p0 + (b1 - b2) * F.q0) ^ 2 + ((a1 - a2) * F.p1 + (b1 - b2) * F.q1) ^ 2 = b ^ 2 := by
    have := dist_sq7 (c.pts (j + 1)) (c.pts (j + 2))
    rw [d12, e10, e11, e20, e21] at this
    linear_combination (-1 : ℝ) * this
  have Q1 : a1 ^ 2 + a1 * b1 + b1 ^ 2 = 1 := by
    have h := fn a1 b1 a1 b1
    have : b ^ 2 * (a1 ^ 2 + a1 * b1 + b1 ^ 2) = b ^ 2 * 1 := by linear_combination (-1 : ℝ) * h + n1
    exact mul_left_cancel₀ hb2.ne' this
  have Q2 : a2 ^ 2 + a2 * b2 + b2 ^ 2 = 1 := by
    have h := fn a2 b2 a2 b2
    have : b ^ 2 * (a2 ^ 2 + a2 * b2 + b2 ^ 2) = b ^ 2 * 1 := by linear_combination (-1 : ℝ) * h + n2
    exact mul_left_cancel₀ hb2.ne' this
  have Q12 : (a1 - a2) ^ 2 + (a1 - a2) * (b1 - b2) + (b1 - b2) ^ 2 = 1 := by
    have h := fn (a1 - a2) (b1 - b2) (a1 - a2) (b1 - b2)
    have : b ^ 2 * ((a1 - a2) ^ 2 + (a1 - a2) * (b1 - b2) + (b1 - b2) ^ 2) = b ^ 2 * 1 := by linear_combination (-1 : ℝ) * h + n12
    exact mul_left_cancel₀ hb2.ne' this
  have hB : a1 * a2 + b1 * b2 + (a1 * b2 + a2 * b1) / 2 = 1 / 2 := by linear_combination (1 / 2 : ℝ) * Q1 + (1 / 2 : ℝ) * Q2 - (1 / 2 : ℝ) * Q12
  have hβ1 : 0 ≤ b1 := by
    have := hbel _ (pts_mem c (j + 1))
    rwa [(F.fa_fb_of hb e10 e11).2] at this
  have hβ2 : 0 ≤ b2 := by
    have := hbel _ (pts_mem c (j + 2))
    rwa [(F.fa_fb_of hb e20 e21).2] at this
  have hO : ∀ s t : ℝ, 0 ≤ s → 0 ≤ t → s + t ≤ 1 →
      ¬ (-1 < s * a1 + t * a2 ∧ s * a1 + t * a2 < 0 ∧ 0 < s * b1 + t * b2 ∧ s * b1 + t * b2 < 1) := by
    intro s t hs ht hst hcon
    obtain ⟨y, hy, y0, y1⟩ := convex3 c.convex (pts_mem c j) (pts_mem c (j + 1)) (pts_mem c (j + 2)) hs ht hst
    rw [hU0, e10, e20] at y0
    rw [hU1, e11, e21] at y1
    have hfy := F.fa_fb_of hb (a := s * a1 + t * a2) (β := s * b1 + t * b2) (by rw [y0]; ring) (by rw [y1]; ring)
    exact hmiss y hy (by rw [hfy.1, hfy.2]; exact hcon)
  rcases wedge_basis Q1 Q2 hB hβ1 hβ2 hO with ⟨ha1, hb1, ha2, hb2'⟩ | ⟨ha1, hb1, ha2, hb2'⟩
  · left
    exact ⟨plane_ext' (by rw [e10, F.pt_zero, ha1, hb1]) (by rw [e11, F.pt_one, ha1, hb1]),
      plane_ext' (by rw [e20, F.pt_zero, ha2, hb2']) (by rw [e21, F.pt_one, ha2, hb2'])⟩
  · right
    exact ⟨plane_ext' (by rw [e10, F.pt_zero, ha1, hb1]) (by rw [e11, F.pt_one, ha1, hb1]),
      plane_ext' (by rw [e20, F.pt_zero, ha2, hb2']) (by rw [e21, F.pt_one, ha2, hb2'])⟩

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.cell_wedge
