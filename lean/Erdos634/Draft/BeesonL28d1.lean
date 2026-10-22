import Erdos634.Draft.BeesonL28c4

/-!
# Beeson (arXiv 1206.2229v4) Lemma 28, step 3a: the tile signs `eps_i` are `(-1)^{n+eps}` resp. `(-1)^{eps}`

NOTE, UNAUDITED.  Credit: Michael Beeson (arXiv 1206.2229 v4, Def. 6, Lemmas 19-23, Thm 3, Thm 4, Lemma 28), Laczkovich
(DCG 48 (2012)), Beeson-Zhang.  Formalization debt, not progress on the /goal outcomes.

Printed: a direction `theta = n delta + eps pi` (`delta = alpha + beta`, measured from the base direction = the direction of
`AB`) has `Phi_1(theta) = (-1)^eps`, `Phi_2(theta) = (-1)^{n+eps}`; a tile `t` has `Phi_2(t) = (-1)^{n+eps} (a-b-c)`
where `n, eps` are the coordinates of the direction of its edge `a` (Lemma 21).  The orientation of the tile (reflected or
not) only changes the indices of the OTHER two edges (`n-1, n-3` instead of `n+1, n+3`) and never enters the computation
on the edge `a`; so no determinant is used, and the result holds for every tile, reflected or not.
The Lean character `chiAt alpha _ 0 anc` is `j pi + k theta -> (-1)^j`, `theta = alpha/2 + pi/2 = pi - delta`, and
`n delta + eps pi = (n+eps) pi + (-n) theta`, so `Phi_2 = (-1)^{n+eps}` exactly; `chiAt .. 1` gives `(-1)^{eps}`.

HYPOTHESIS, NAMED EXACTLY (`AnchorCoset`): every tile edge direction lies in the coset `anchor + L` of the base direction
(`anchor` = direction of `AB`, `L = Z pi + Z theta`).  This is Beeson's Lemma 19; it is what makes `n, eps` exist at all.
It is NOT proved here for a general dissection (the Lean flux argument never needs it); the proof is connectivity of the
dissection through shared segments.  It is not checked here for the 77-tiling.
-/

open scoped Classical

namespace Erdos634.BeesonColoring

open Erdos634.Geometry Erdos634.Geometry.A1Field

variable {N : ℕ}

/-- Beeson Lemma 19 as a hypothesis: every tile edge direction is in the coset of the base direction. -/
def AnchorCoset (D : CongruentDissection N) (α : ℝ) (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) : Prop :=
  ∀ (i : Fin N) (k : Fin 3), ((D.tile i).leftUnit k).angle - (D.target.leftUnit 0).angle
    ∈ (chiAt α hα 0 (D.target.leftUnit 0).angle).L

theorem weight_of_coset (G : GridChar ℝ) (d : Dir) (h : d.angle - G.anchor ∈ G.L) :
    G.weight d = G.chi (d.angle - G.anchor) := by
  unfold GridChar.weight GridChar.val GridChar.rep
  rw [if_pos h]

theorem zsign (j : ℤ) : (if (j : ZMod 2) + 0 * (0 : ZMod 2) = 0 then (1 : ℝ) else -1) = (-1 : ℝ) ^ j := by
  rcases Int.even_or_odd' j with ⟨m, rfl | rfl⟩
  · have : ((2 * m : ℤ) : ZMod 2) = 0 := by
      push_cast; rw [show (2 : ZMod 2) = 0 by decide]; ring
    rw [this, zpow_mul]; norm_num
  · have : ((2 * m + 1 : ℤ) : ZMod 2) = 1 := by
      push_cast; rw [show (2 : ZMod 2) = 0 by decide]; ring
    rw [this, zpow_add₀ (by norm_num), zpow_mul]; norm_num

/-- **Tile sign = weight of the `alpha`-opposite edge.**  For any anchor and parity `bb`, the sign `eps_i` of the
`chiAt` flux of tile `i` equals the weight of the left-directed edge `k` opposite a vertex of angle `alpha`. -/
theorem eps_eq_edgeWeight (D : CongruentDissection N) {α β a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hrel : 3 * α + 2 * β = Real.pi)
    (h : D.model.ThreeAlphaData α β a b c) (bb : ZMod 2) (anc : Real.Angle)
    (hK : (chiAt α hα bb anc).tileValue D.model ≠ 0) (ε : Fin N → ℤ)
    (hε : SignsFor D (chiAt α hα bb anc) ε) (i : Fin N) (k : Fin 3)
    (hk : (D.tile i).angleAt (k + 2) = α) :
    (ε i : ℝ) = (chiAt α hα bb anc).weight ((D.tile i).leftUnit k) := by
  set G := chiAt α hα bb anc with hG
  have hsq := chiAt_sq α hα bb anc
  have hmodel : ∀ k, ((D.model.angleAt k : ℝ) : Real.Angle) ∈ G.L :=
    D.model.threeAlpha_angles_mem hα hrel h bb
  obtain ⟨σ, hσ⟩ := (D.tiles_congruent i).exists_perm
  have hi : ∀ k, (((D.tile i).angleAt k : ℝ) : Real.Angle) ∈ G.L := fun k => by
    rw [(hσ k).1]; exact hmodel _
  have h1 := (D.tile i).flux_eq_edgeSign G hsq hi k
  rw [G.tileValue_congr (D.tiles_congruent i)] at h1
  have h2 := hε i
  have h3 : (ε i : ℝ) * G.tileValue D.model = G.edgeSign (D.tile i) k * G.tileValue D.model := by
    rw [← h2, h1]
  have h4 := mul_right_cancel₀ hK h3
  rw [h4]
  unfold GridChar.edgeSign
  rw [hk, show Real.pi - α = ((2 : ℤ) : ℝ) * Real.pi + ((-2 : ℤ) : ℝ) * (α / 2 + Real.pi / 2) by
      push_cast; ring, hG, chiAt_chi, if_pos (by push_cast; rw [show (2 : ZMod 2) = 0 by decide]; ring), one_mul]

end Erdos634.BeesonColoring

#print axioms Erdos634.BeesonColoring.eps_eq_edgeWeight
