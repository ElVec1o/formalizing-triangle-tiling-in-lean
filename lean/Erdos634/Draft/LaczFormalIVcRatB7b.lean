-- Draft/LaczFormalIVcRatB7b.lean -- Laczkovich DCG 48 (2012), Sect. 8.3 (Subcase IVc, rational branch), BLUEPRINT Part B, item B7, stage b: a KITE cannot lie along a supporting line.
--   `kite_support`: if an affine functional f (f y = a0 y_0 + a1 y_1 + c) is >= 0 on the kite K (kiteSet = triangle V, V+2s, V+2w, W = V+s+w) and vanishes at two distinct points of K,
--   then f(V) = 0 or f(W) = 0.  (Route: f on K is (1-l-m) f(V) + l f(E1) + m f(E2); two distinct zeros force f(V) = 0, or f(E1) = f(E2) = 0, i.e. f(W) = (f(E1)+f(E2))/2 = 0.)
--   With `vw_not_boundary` (B5: no V, no W of a kite of a convex region lies on the frontier) this is the printed step P3 of the blueprint: a kite never has a side along a side of A.
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 8.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIVcRatB6

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement Erdos634.CertCoord

namespace Erdos634.Draft.LaczFormal.RG

/-- The real-variable core. -/
theorem kite_zero {f0 F1 F2 l1 m1 l2 m2 : ℝ} (h0 : 0 ≤ f0) (hF1 : 0 ≤ F1) (hF2 : 0 ≤ F2)
    (hl1 : 0 ≤ l1) (hm1 : 0 ≤ m1) (hs1 : l1 + m1 ≤ 1) (hl2 : 0 ≤ l2) (hm2 : 0 ≤ m2) (hs2 : l2 + m2 ≤ 1)
    (e1 : (1 - l1 - m1) * f0 + l1 * F1 + m1 * F2 = 0) (e2 : (1 - l2 - m2) * f0 + l2 * F1 + m2 * F2 = 0)
    (hne : l1 ≠ l2 ∨ m1 ≠ m2) : f0 = 0 ∨ F1 + F2 = 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hf0, hFF⟩ := hcon
  have hf0p : 0 < f0 := lt_of_le_of_ne h0 (Ne.symm hf0)
  have t1 : 0 ≤ (1 - l1 - m1) * f0 := mul_nonneg (by linarith) h0
  have t2 : 0 ≤ l1 * F1 := mul_nonneg hl1 hF1
  have t3 : 0 ≤ m1 * F2 := mul_nonneg hm1 hF2
  have s1 : 1 - l1 - m1 = 0 := by
    have : (1 - l1 - m1) * f0 = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · exact h
    · exact absurd h hf0
  have u2 : 0 ≤ (1 - l2 - m2) * f0 := mul_nonneg (by linarith) h0
  have u3 : 0 ≤ l2 * F1 := mul_nonneg hl2 hF1
  have u4 : 0 ≤ m2 * F2 := mul_nonneg hm2 hF2
  have s2 : 1 - l2 - m2 = 0 := by
    have : (1 - l2 - m2) * f0 = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · exact h
    · exact absurd h hf0
  have z1 : l1 * F1 = 0 := by rw [s1] at e1; linarith
  have z1' : m1 * F2 = 0 := by rw [s1] at e1; linarith
  have z2 : l2 * F1 = 0 := by rw [s2] at e2; linarith
  have z2' : m2 * F2 = 0 := by rw [s2] at e2; linarith
  have hF : 0 < F1 ∨ 0 < F2 := by
    by_contra h
    push Not at h
    apply hFF; linarith [h.1, h.2]
  rcases hF with hF | hF
  · have a1 : l1 = 0 := by
      rcases mul_eq_zero.mp z1 with h | h
      · exact h
      · linarith
    have a2 : l2 = 0 := by
      rcases mul_eq_zero.mp z2 with h | h
      · exact h
      · linarith
    rcases hne with h | h
    · exact h (by rw [a1, a2])
    · exact h (by linarith)
  · have a1 : m1 = 0 := by
      rcases mul_eq_zero.mp z1' with h | h
      · exact h
      · linarith
    have a2 : m2 = 0 := by
      rcases mul_eq_zero.mp z2' with h | h
      · exact h
      · linarith
    rcases hne with h | h
    · exact h (by linarith)
    · exact h (by rw [a1, a2])

/-- **B7b.** A kite on one side of a line touches it in at most one point unless `V` or `W` lies on the line. -/
theorem kite_support {b : ℝ} (K : KiteData b) (α0 α1 c : ℝ) (hK : ∀ y ∈ K.set, 0 ≤ α0 * y 0 + α1 * y 1 + c)
    {y1 y2 : Plane} (h1 : y1 ∈ K.set) (h2 : y2 ∈ K.set) (hne : y1 ≠ y2)
    (e1 : α0 * y1 0 + α1 * y1 1 + c = 0) (e2 : α0 * y2 0 + α1 * y2 1 + c = 0) :
    α0 * K.V 0 + α1 * K.V 1 + c = 0 ∨ α0 * K.W 0 + α1 * K.W 1 + c = 0 := by
  have hD := hD4 K.hD
  have mem : ∀ y, y ∈ K.set ↔ ∃ l m : ℝ, 0 ≤ l ∧ 0 ≤ m ∧ l + m ≤ 1 ∧ y 0 = K.v0 + l * (2 * K.s0) + m * (2 * K.w0) ∧
      y 1 = K.v1 + l * (2 * K.s1) + m * (2 * K.w1) := fun y => ct_carrier hD y
  obtain ⟨l1, m1, hl1, hm1, hs1, a1, b1⟩ := (mem y1).mp h1
  obtain ⟨l2, m2, hl2, hm2, hs2, a2, b2⟩ := (mem y2).mp h2
  have hV : mkPt K.v0 K.v1 ∈ K.set := (mem _).mpr ⟨0, 0, le_rfl, le_rfl, by norm_num, by simp [mkPt_zero], by simp [mkPt_one]⟩
  have hE1 : mkPt (K.v0 + 2 * K.s0) (K.v1 + 2 * K.s1) ∈ K.set :=
    (mem _).mpr ⟨1, 0, by norm_num, le_rfl, by norm_num, by simp [mkPt_zero], by simp [mkPt_one]⟩
  have hE2 : mkPt (K.v0 + 2 * K.w0) (K.v1 + 2 * K.w1) ∈ K.set :=
    (mem _).mpr ⟨0, 1, le_rfl, by norm_num, by norm_num, by simp [mkPt_zero], by simp [mkPt_one]⟩
  have gV := hK _ hV
  have gE1 := hK _ hE1
  have gE2 := hK _ hE2
  simp only [mkPt_zero, mkPt_one] at gV gE1 gE2
  set f0 := α0 * K.v0 + α1 * K.v1 + c with hf0
  set F1 := α0 * (K.v0 + 2 * K.s0) + α1 * (K.v1 + 2 * K.s1) + c with hF1
  set F2 := α0 * (K.v0 + 2 * K.w0) + α1 * (K.v1 + 2 * K.w1) + c with hF2
  have ee1 : (1 - l1 - m1) * f0 + l1 * F1 + m1 * F2 = 0 := by
    rw [a1, b1] at e1; rw [hf0, hF1, hF2]; linarith
  have ee2 : (1 - l2 - m2) * f0 + l2 * F1 + m2 * F2 = 0 := by
    rw [a2, b2] at e2; rw [hf0, hF1, hF2]; linarith
  have hne' : l1 ≠ l2 ∨ m1 ≠ m2 := by
    by_contra hcon
    push Not at hcon
    apply hne
    exact plane_ext' (by rw [a1, a2, hcon.1, hcon.2]) (by rw [b1, b2, hcon.1, hcon.2])
  rcases kite_zero gV gE1 gE2 hl1 hm1 hs1 hl2 hm2 hs2 ee1 ee2 hne' with h | h
  · left; simp only [KiteData.V, mkPt_zero, mkPt_one]; exact h
  · right; simp only [KiteData.W, mkPt_zero, mkPt_one]; rw [hF1, hF2] at h; linarith

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.kite_support
