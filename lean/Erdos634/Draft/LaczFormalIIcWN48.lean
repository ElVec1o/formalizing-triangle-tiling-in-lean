-- Draft/LaczFormalIIcWN48.lean -- Laczkovich (DCG 48 (2012)), Sect. 6.3, Lemma 6.2 (`IIcNoKites`), step (h), part 9:
-- `pocket_concave`: if the arc polygon Q = arcPoly p a d has orientation opposite to that of p, then some interior arc vertex of p is concave
-- (sigma * extAng p < 0).  Angle sum (d-1) pi of Q against the angles pi + sigma ext >= pi it would have at convex vertices.
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcWN47

open scoped Classical Fin.NatCast
open Complex Filter Topology

namespace Erdos634.Draft.LaczFormal.WN

variable {n : ℕ} [NeZero n]

theorem pocket_concave (p : Fin n → ℂ) (a : Fin n) {d : ℕ} (hd : 2 ≤ d) {σ σQ : ℝ}
    (OQ : OrientOK (arcPoly p a d) σQ) (hopp : σQ = -σ) :
    ∃ k : ℕ, 1 ≤ k ∧ k + 1 ≤ d ∧ σ * extAng p (phi a k) < 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨-, hbd, hsum, -⟩ := OQ
  set Q := arcPoly p a d with hQ
  have hg : ∑ u : Fin (d + 1), (Real.pi - σQ * extAng Q u - Real.pi) = -(2 * Real.pi) := by
    rw [Finset.sum_sub_distrib]
    have : ∑ u : Fin (d + 1), (Real.pi - σQ * extAng Q u) = ((((d + 1 : ℕ) : ℝ)) - 2) * Real.pi := hsum
    rw [this]
    simp
    ring
  have h0 : (0 : Fin (d + 1)) ≠ Fin.last d := by
    intro h
    have := congrArg Fin.val h
    simp at this
    omega
  have hmem : (Fin.last d) ∈ (Finset.univ : Finset (Fin (d + 1))).erase 0 := by
    simp [Finset.mem_erase, h0.symm]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : Fin (d + 1))), ← Finset.add_sum_erase _ _ hmem] at hg
  have hmid : 0 ≤ ∑ u ∈ ((Finset.univ : Finset (Fin (d + 1))).erase 0).erase (Fin.last d), (Real.pi - σQ * extAng Q u - Real.pi) := by
    apply Finset.sum_nonneg
    intro u hu
    simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hu
    obtain ⟨hul, hu0⟩ := hu
    have hu1 : 1 ≤ u.val := by
      by_contra h; apply hu0; ext; simp only [Fin.val_zero]; omega
    have hu2 : u.val + 1 ≤ d := by
      have := u.isLt
      by_contra h; apply hul; ext; simp only [Fin.val_last]; omega
    rw [arc_ext p a u hu1 hu2, hopp]
    have := hcon u.val hu1 hu2
    linarith
  have b0 := (hbd 0).1
  have bl := (hbd (Fin.last d)).1
  linarith

end Erdos634.Draft.LaczFormal.WN
