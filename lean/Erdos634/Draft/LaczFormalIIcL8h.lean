-- Draft/LaczFormalIIcL8h.lean -- Laczkovich (DCG 48 (2012)), Sect. 6.3, L8 `gexc_disjoint`, local geometry of tiles, step 1: points of a tile given by positive barycentric weights are interior points
-- (`tri_interior_comb`), the Cramer coordinates of a point in a tile frame (`cramer_interior`).
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.NearBaseVertex
import Erdos634.Draft.LaczFormalThm21Area

open Erdos634.Geometry

namespace Erdos634.Draft.LaczFormal.RG

theorem pl_ext2 {u w : Plane} (h0 : u 0 = w 0) (h1 : u 1 = w 1) : u = w := by
  ext i; fin_cases i <;> simpa

/-- the cross product of two sides at a vertex of a tile is `± det`, hence nonzero. -/
theorem kappa_ne (T : Tri) {a b g : Fin 3} (hab : a ≠ b) (hag : a ≠ g) (hbg : b ≠ g) :
    cross (T.pts b - T.pts a) (T.pts g - T.pts a) ≠ 0 := by
  have hd := T.det_ne_zero
  have hcases : (b = a + 1 ∧ g = a + 2) ∨ (b = a + 2 ∧ g = a + 1) := by
    revert hab hag hbg; fin_cases a <;> fin_cases b <;> fin_cases g <;> decide
  rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [T.det_cyclic]; exact hd
  · have h2 : cross (T.pts (a + 2) - T.pts a) (T.pts (a + 1) - T.pts a) = - cross (T.pts (a + 1) - T.pts a) (T.pts (a + 2) - T.pts a) := by
      simp only [cross]; ring
    rw [h2, T.det_cyclic]; simpa using hd

/-- **Points with positive barycentric weights are interior.** -/
theorem tri_interior_comb (T : Tri) {a b g : Fin 3} (hab : a ≠ b) (hag : a ≠ g) (hbg : b ≠ g) {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1) :
    T.pts a + s • (T.pts b - T.pts a) + t • (T.pts g - T.pts a) ∈ interior T.carrier := by
  have key : ∀ (k : Fin 3) (s t : ℝ), 0 < s → 0 < t → s + t < 1 →
      T.pts k + s • (T.pts (k + 1) - T.pts k) + t • (T.pts (k + 2) - T.pts k) ∈ interior T.carrier := by
    intro k s t hs ht hst
    have := Erdos634.Draft.NearBaseVertex.corner_interior T k rfl hs ht (ε := 1) one_pos (by linarith)
    simpa [add_assoc] using this
  have hcases : (b = a + 1 ∧ g = a + 2) ∨ (b = a + 2 ∧ g = a + 1) := by
    revert hab hag hbg; fin_cases a <;> fin_cases b <;> fin_cases g <;> decide
  rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact key a s t hs ht hst
  · have := key a t s ht hs (by linarith)
    convert this using 1
    abel

theorem cramer_real (z0 z1 a0 a1 b0 b1 g0 g1 : ℝ) (hk : (b0 - a0) * (g1 - a1) - (b1 - a1) * (g0 - a0) ≠ 0) :
    z0 = a0 + ((z0 - a0) * (g1 - a1) - (z1 - a1) * (g0 - a0)) / ((b0 - a0) * (g1 - a1) - (b1 - a1) * (g0 - a0)) * (b0 - a0) +
      ((b0 - a0) * (z1 - a1) - (b1 - a1) * (z0 - a0)) / ((b0 - a0) * (g1 - a1) - (b1 - a1) * (g0 - a0)) * (g0 - a0) ∧
    z1 = a1 + ((z0 - a0) * (g1 - a1) - (z1 - a1) * (g0 - a0)) / ((b0 - a0) * (g1 - a1) - (b1 - a1) * (g0 - a0)) * (b1 - a1) +
      ((b0 - a0) * (z1 - a1) - (b1 - a1) * (z0 - a0)) / ((b0 - a0) * (g1 - a1) - (b1 - a1) * (g0 - a0)) * (g1 - a1) := by
  obtain ⟨k, hkd⟩ : ∃ k, k = (b0 - a0) * (g1 - a1) - (b1 - a1) * (g0 - a0) := ⟨_, rfl⟩
  rw [← hkd] at hk ⊢
  have e0 : ((z0 - a0) * (g1 - a1) - (z1 - a1) * (g0 - a0)) * (b0 - a0) + ((b0 - a0) * (z1 - a1) - (b1 - a1) * (z0 - a0)) * (g0 - a0) = (z0 - a0) * k := by
    rw [hkd]; ring
  have e1 : ((z0 - a0) * (g1 - a1) - (z1 - a1) * (g0 - a0)) * (b1 - a1) + ((b0 - a0) * (z1 - a1) - (b1 - a1) * (z0 - a0)) * (g1 - a1) = (z1 - a1) * k := by
    rw [hkd]; ring
  constructor
  · have : a0 + ((z0 - a0) * (g1 - a1) - (z1 - a1) * (g0 - a0)) / k * (b0 - a0) + ((b0 - a0) * (z1 - a1) - (b1 - a1) * (z0 - a0)) / k * (g0 - a0)
        = a0 + (((z0 - a0) * (g1 - a1) - (z1 - a1) * (g0 - a0)) * (b0 - a0) + ((b0 - a0) * (z1 - a1) - (b1 - a1) * (z0 - a0)) * (g0 - a0)) / k := by ring
    rw [this, e0]; field_simp; ring
  · have : a1 + ((z0 - a0) * (g1 - a1) - (z1 - a1) * (g0 - a0)) / k * (b1 - a1) + ((b0 - a0) * (z1 - a1) - (b1 - a1) * (z0 - a0)) / k * (g1 - a1)
        = a1 + (((z0 - a0) * (g1 - a1) - (z1 - a1) * (g0 - a0)) * (b1 - a1) + ((b0 - a0) * (z1 - a1) - (b1 - a1) * (z0 - a0)) * (g1 - a1)) / k := by ring
    rw [this, e1]; field_simp; ring

/-- Cramer coordinates: a point whose coordinates in the frame `(A; B - A, G - A)` of a tile are positive with sum below one is interior. -/
theorem cramer_interior (T : Tri) {a b g : Fin 3} (hab : a ≠ b) (hag : a ≠ g) (hbg : b ≠ g) {Z : Plane}
    (hs : 0 < cross (Z - T.pts a) (T.pts g - T.pts a) / cross (T.pts b - T.pts a) (T.pts g - T.pts a))
    (ht : 0 < cross (T.pts b - T.pts a) (Z - T.pts a) / cross (T.pts b - T.pts a) (T.pts g - T.pts a))
    (hst : cross (Z - T.pts a) (T.pts g - T.pts a) / cross (T.pts b - T.pts a) (T.pts g - T.pts a) +
      cross (T.pts b - T.pts a) (Z - T.pts a) / cross (T.pts b - T.pts a) (T.pts g - T.pts a) < 1) :
    Z ∈ interior T.carrier := by
  have hk := kappa_ne T hab hag hbg
  have hk' : (T.pts b 0 - T.pts a 0) * (T.pts g 1 - T.pts a 1) - (T.pts b 1 - T.pts a 1) * (T.pts g 0 - T.pts a 0) ≠ 0 := by simpa [cross] using hk
  have := tri_interior_comb T hab hag hbg hs ht hst
  have hr := cramer_real (Z 0) (Z 1) (T.pts a 0) (T.pts a 1) (T.pts b 0) (T.pts b 1) (T.pts g 0) (T.pts g 1) hk'
  convert this using 1
  apply pl_ext2
  · simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, cross]
    exact hr.1
  · simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, cross]
    exact hr.2

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.cramer_interior
