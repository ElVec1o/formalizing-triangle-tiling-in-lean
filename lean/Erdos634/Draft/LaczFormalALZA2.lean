import Erdos634.Draft.LaczFormalALZA

/-!
# The hypotenuse points D_s, the environment, the chain cover (a-lattice)

Erdős \#634, base-`β` row, thick analogue of `M(j)` (Lemma A(j)).  Credit: AI assistant (Lemma A(k) proposal), Beeson–Roșu,
Beeson, Laczkovich, Paliy.  UNAUDITED.  Axiom-clean; no `sorry`.  Port of `LaczFormalMJZA2.lean` to the exchanged frame
`AF` (`e0` of length `a` along the base, `v` of length `c` along the left leg).
-/

namespace Erdos634.LaczAL

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.LaczJunction Erdos634.LaczJunction.Walk
  Erdos634.LaczJunction.Grammar Erdos634.Draft.TraceCovering Erdos634.LaczMJ Set

variable {N : ℕ} {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ} {p q r : Fin 3}

namespace AF

variable (F : AF D e f α β γ p q r)

/-- The point `D_j = (m+1-j, lv+j)` of the hypotenuse. -/
def Dp (m lv : ℕ) (j : ℝ) : Plane := F.pt ((m : ℝ) + 1 - j) ((lv : ℝ) + j)

theorem Dp_eq' (m lv : ℕ) (j : ℝ) :
    F.Dp m lv j = F.pt ((m : ℝ) + 1) (lv : ℝ) + j • (F.v - F.e0) := F.Dp_eq j (m : ℝ) (lv : ℝ)

theorem Dp_inj {m lv : ℕ} {a b : ℝ} (h : F.Dp m lv a = F.Dp m lv b) : a = b := by
  rw [F.Dp_eq', F.Dp_eq'] at h
  exact lm_injective (X := F.pt ((m : ℝ) + 1) (lv : ℝ)) F.u_ne h

/-- The environment of one stage of the induction. -/
structure Env (H m lv : ℕ) : Prop where
  hB : F.Bnd H
  hrH : lv + m + 1 ≤ H
  hme : m + 1 ≤ f - 1
  IHT : ∀ i, i < m → F.TRule H i
  IHA : ∀ i, i < m → F.ARule H i
  hnsJ : ¬ F.StrL ((m : ℝ) + 1) (lv : ℝ) (F.pt ((m : ℝ) + 1) (lv : ℝ))

/-- `l_cover` for the stage `s'+1`, written with `Dp`. -/
theorem lcov {H m lv s' : ℕ} (E : F.Env H m lv) (hs : s' + 1 ≤ m + 1) (hStd : F.Std lv m s')
    (hnsD : ¬ F.StrL ((m : ℝ) + 1) (lv : ℝ) (F.Dp m lv ((s' : ℝ) + 1))) :
    (∀ e' ∈ D.lineChain (crossL (F.v - F.e0)) (cross (F.v - F.e0) (F.pt ((m : ℝ) + 1) (lv : ℝ))),
        (D.tile e'.1).edge e'.2 ⊆ segment ℝ (F.pt ((m : ℝ) + 1) (lv : ℝ)) (F.Dp m lv ((s' : ℝ) + 1)) →
        ∃ k : ℕ, k < s' + 1 ∧
        (((D.tile e'.1).pts e'.2 = F.Dp m lv (k : ℝ) ∧
          (D.tile e'.1).pts (e'.2 + 1) = F.Dp m lv ((k : ℝ) + 1)) ∨
         ((D.tile e'.1).pts e'.2 = F.Dp m lv ((k : ℝ) + 1) ∧
          (D.tile e'.1).pts (e'.2 + 1) = F.Dp m lv (k : ℝ)))) ∧
    ∀ k : ℕ, k < s' + 1 →
      ∃ e' ∈ D.lineChain (crossL (F.v - F.e0)) (cross (F.v - F.e0) (F.pt ((m : ℝ) + 1) (lv : ℝ))),
        (((D.tile e'.1).pts e'.2 = F.Dp m lv (k : ℝ) ∧
          (D.tile e'.1).pts (e'.2 + 1) = F.Dp m lv ((k : ℝ) + 1)) ∨
         ((D.tile e'.1).pts e'.2 = F.Dp m lv ((k : ℝ) + 1) ∧
          (D.tile e'.1).pts (e'.2 + 1) = F.Dp m lv (k : ℝ))) := by
  have hc : ((s' + 1 : ℕ) : ℝ) = (s' : ℝ) + 1 := by push_cast; ring
  have h := F.l_cover (s := s' + 1) E.hB E.hrH E.hme (by omega) hs (by simpa using hStd) E.hnsJ
    (by rw [hc]; exact hnsD)
  rw [hc] at h
  obtain ⟨-, h2, h3⟩ := h
  exact ⟨h2, h3⟩

end AF

end Erdos634.LaczAL
