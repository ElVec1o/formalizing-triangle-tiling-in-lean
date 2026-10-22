import Erdos634.Draft.FDBBaseBetaE1
import Erdos634.Draft.GapE120Dis

/-!
# `HasSides` under relabelling

`FDBBaseBetaE1.HasSides T a b c`: the sides of `T` are `a, b, c` in some order of the vertices.  Here: it follows from
`oppLen` data (in the given labelling, or up to a permutation), and it is invariant under permuting `(a, b, c)`.
With `congruent_of_hasSides` this turns any certificate's `TGT`/`MODEL` (whatever their labelling) into the hypotheses
of the leaf instances (`S1Inst`, `S4Inst`, `S5Inst`, ...).  No sorry.
-/

namespace Erdos634.Draft.FDBBaseBetaE1

open Erdos634.Geometry

theorem hasSides_of_oppLen {T : Erdos634.Geometry.Tri} {a b c : ℝ} (h0 : T.oppLen 0 = a) (h1 : T.oppLen 1 = b)
    (h2 : T.oppLen 2 = c) : HasSides T a b c :=
  ⟨Equiv.refl _, h0, h1, h2⟩

open Erdos634.Geometry.GapE120Dis in
theorem hasSides_of_sigma {T : Erdos634.Geometry.Tri} {a b c : ℝ} (σ : Equiv.Perm (Fin 3))
    (m0 : T.oppLen (σ 0) = a) (m1 : T.oppLen (σ 1) = b) (m2 : T.oppLen (σ 2) = c) : HasSides T a b c := by
  obtain ⟨s1, s2, s3⟩ := sides_of_perm T σ
  exact ⟨σ, by rw [s1, m0], by rw [dist_comm, s2, m1], by rw [s3, m2]⟩

/-- cyclic rotation -/
theorem hasSides_rot {T : Erdos634.Geometry.Tri} {a b c : ℝ} (h : HasSides T a b c) : HasSides T b c a := by
  obtain ⟨τ, h1, h2, h3⟩ := h
  have e0 : ((finRotate 3).trans τ) 0 = τ 1 := by rw [Equiv.trans_apply]; rfl
  have e1 : ((finRotate 3).trans τ) 1 = τ 2 := by rw [Equiv.trans_apply]; rfl
  have e2 : ((finRotate 3).trans τ) 2 = τ 0 := by rw [Equiv.trans_apply]; rfl
  exact ⟨(finRotate 3).trans τ, by rw [e1, e2]; exact h2, by rw [e2, e0]; exact h3, by rw [e0, e1]; exact h1⟩

/-- transposition of the first two sides -/
theorem hasSides_swap {T : Erdos634.Geometry.Tri} {a b c : ℝ} (h : HasSides T a b c) : HasSides T b a c := by
  obtain ⟨τ, h1, h2, h3⟩ := h
  have e0 : ((Equiv.swap (0 : Fin 3) 1).trans τ) 0 = τ 1 := by rw [Equiv.trans_apply]; rfl
  have e1 : ((Equiv.swap (0 : Fin 3) 1).trans τ) 1 = τ 0 := by rw [Equiv.trans_apply]; rfl
  have e2 : ((Equiv.swap (0 : Fin 3) 1).trans τ) 2 = τ 2 := by rw [Equiv.trans_apply]; rfl
  exact ⟨(Equiv.swap (0 : Fin 3) 1).trans τ, by rw [e1, e2, dist_comm]; exact h2, by rw [e2, e0, dist_comm]; exact h1,
    by rw [e0, e1, dist_comm]; exact h3⟩

/-- a certificate target/model `U` with sides `dist 01 = c`, `dist 12 = a`, `dist 02 = b` -/
theorem congruent_of_hasSides' {T U : Erdos634.Geometry.Tri} {a b c : ℝ} (hT : HasSides T a b c)
    (h01 : dist (U.pts 0) (U.pts 1) = c) (h12 : dist (U.pts 1) (U.pts 2) = a) (h02 : dist (U.pts 0) (U.pts 2) = b) :
    T.Congruent U :=
  congruent_of_hasSides hT h12 (by rw [dist_comm]; exact h02) h01

end Erdos634.Draft.FDBBaseBetaE1
