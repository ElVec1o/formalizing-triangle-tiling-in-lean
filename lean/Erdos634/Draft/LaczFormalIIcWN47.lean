-- Draft/LaczFormalIIcWN47.lean -- Laczkovich (DCG 48 (2012)), Sect. 6.3, Lemma 6.2 (`IIcNoKites`), step (h), part 8:
-- exterior angles of `arcPoly` at interior arc vertices equal those of p; `pocket_concave`: an arc polygon whose orientation is OPPOSITE to that of p
-- has a vertex of p in its arc with sigma * extAng < 0 (a concave vertex), by the angle sum.
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcWN46

open scoped Classical Fin.NatCast
open Complex Filter Topology

namespace Erdos634.Draft.LaczFormal.WN

variable {n : ℕ} [NeZero n]

theorem arc_nbrs (p : Fin n → ℂ) (a : Fin n) {d : ℕ} (u : Fin (d + 1)) (h1 : 1 ≤ u.val) (h2 : u.val + 1 ≤ d) :
    arcPoly p a d (u - 1) = p (phi a (u.val - 1)) ∧ arcPoly p a d u = p (phi a u.val) ∧ arcPoly p a d (u + 1) = p (phi a (u.val + 1)) := by
  refine ⟨?_, rfl, ?_⟩
  · have hv : u = (⟨u.val - 1, by omega⟩ : Fin (d + 1)) + 1 := by
      apply Fin.ext
      rw [Fin.val_add_one_of_lt (by rw [Fin.lt_def]; simp; omega)]
      simp; omega
    have : (u - 1 : Fin (d + 1)) = ⟨u.val - 1, by omega⟩ := by
      conv_lhs => rw [hv]
      simp
    rw [this]; rfl
  · have e : u = ⟨u.val, u.isLt⟩ := rfl
    have := arcPoly_succ p a (d := d) u.val (by omega)
    rw [← e] at this
    exact this

theorem arc_ext (p : Fin n → ℂ) (a : Fin n) {d : ℕ} (u : Fin (d + 1)) (h1 : 1 ≤ u.val) (h2 : u.val + 1 ≤ d) :
    extAng (arcPoly p a d) u = extAng p (phi a u.val) := by
  obtain ⟨e0, e1, e2⟩ := arc_nbrs p a u h1 h2
  unfold extAng
  rw [e0, e1, e2]
  have hs1 : phi a (u.val + 1) = phi a u.val + 1 := phi_succ a u.val
  have hs0 : phi a (u.val - 1) = phi a u.val - 1 := by
    have : phi a u.val = phi a (u.val - 1 + 1) := by congr 1; omega
    rw [this, phi_succ]; simp
  rw [hs1, hs0]

end Erdos634.Draft.LaczFormal.WN
