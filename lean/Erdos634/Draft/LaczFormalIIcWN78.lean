-- Draft/LaczFormalIIcWN78.lean -- Laczkovich (DCG 48 (2012), Sect. 6.3), Lemma 6.2: the OUTER polygon A of the ring, from `ConvPoly`.
-- For a `ConvPoly M` `P` and `A i = toC (P.v i)`: `A` is injective, `SC A 1` (strictly convex, counter-clockwise) and every interior point `Y` of `P.carrier` lies strictly inside every edge half-plane:
-- `0 < 1 * sideFn (A j) (A (j+1) - A j) (toC Y)` (`RingSetup.SA`, `Ainj`, `inside`).  Bridge `sideFn_toC`: the side function is `cross2 / |edge|^2`.
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcWN77
import Erdos634.Draft.LaczFormalIIcG11d
import Erdos634.Draft.LaczFormalIIcWN66

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.Draft.LaczFormal.Thm21 Erdos634.Draft.LaczFormal.RG

namespace Erdos634.Draft.LaczFormal.WN

variable {M : ℕ} [NeZero M]

theorem sideFn_toC (a b x : Plane) :
    sideFn (toC a) (toC b - toC a) (toC x) = cross2 (b - a) (x - a) / Complex.normSq (toC b - toC a) := by
  rw [sideFn_ri]
  simp only [Erdos634.Draft.LaczFormal.RG.toC_apply, cross2, Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, PiLp.sub_apply]
  ring

theorem convPoly_e_ne (P : ConvPoly M) (j : Fin M) : P.v (j + 1) ≠ P.v j := by
  obtain ⟨f1, f2, f3, f4, f5, f6⟩ := ConvPoly.fin_facts P.three_le j
  have hpos : 0 < P.c j (P.v (j + 2)) := P.c_vertex_pos f2 f3
  intro h
  have : P.e j = 0 := by simp [ConvPoly.e, h]
  rw [ConvPoly.c, this] at hpos
  simp [cross2] at hpos

theorem convPoly_inj (P : ConvPoly M) : Function.Injective (fun i => toC (P.v i)) := by
  intro i j hij
  have h : P.v i = P.v j := toC.injective hij
  by_contra hne
  by_cases h1 : j = i + 1
  · exact convPoly_e_ne P i (by rw [← h1, ← h])
  · have := P.c_vertex_pos (j := i) (m := j) (Ne.symm hne) h1
    rw [← h, P.c_self] at this
    exact lt_irrefl _ this

theorem convPoly_SC (P : ConvPoly M) : SC (fun i => toC (P.v i)) 1 := by
  intro j m h1 h2
  rw [one_mul, sideFn_toC]
  have hn : 0 < Complex.normSq (toC (P.v (j + 1)) - toC (P.v j)) := by
    apply Complex.normSq_pos.2
    intro h
    exact convPoly_e_ne P j (toC.injective (sub_eq_zero.1 h))
  apply div_pos _ hn
  exact P.c_vertex_pos h1 h2

theorem convPoly_inside (P : ConvPoly M) {Y : Plane} (hY : Y ∈ interior P.carrier) (j : Fin M) :
    0 < 1 * sideFn (toC (P.v j)) (toC (P.v (j + 1)) - toC (P.v j)) (toC Y) := by
  rw [one_mul, sideFn_toC]
  have hn : 0 < Complex.normSq (toC (P.v (j + 1)) - toC (P.v j)) := by
    apply Complex.normSq_pos.2
    intro h
    exact convPoly_e_ne P j (toC.injective (sub_eq_zero.1 h))
  apply div_pos _ hn
  exact c_pos_of_interior P hY j

#print axioms convPoly_SC
#print axioms convPoly_inside

end Erdos634.Draft.LaczFormal.WN
