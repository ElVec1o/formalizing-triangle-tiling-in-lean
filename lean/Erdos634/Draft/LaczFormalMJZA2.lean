import Erdos634.Draft.LaczFormalMJZA

/-!
# Claims Z and A of the induction `M(j)`: definitions and wrappers

Erdős #634, base-`β` band, rule `M(j)`.  Credit: AI assistant (item 3, band program, Claims Z and A), Beeson–Roșu,
Beeson, Laczkovich, Paliy.  UNAUDITED.  Axiom-clean; no `sorry`.
-/

namespace Erdos634.LaczMJ

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.LaczJunction Erdos634.LaczJunction.Walk
  Erdos634.LaczJunction.Grammar Erdos634.Draft.TraceCovering Set

variable {N : ℕ} {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ} {p q r : Fin 3}

/-- No two distinct tiles present `γ` at a point of the frontier which is not a target vertex. -/
theorem no_double_gamma_S (S : BandSetup D e f α β γ p q r) {w : Plane} (hw : w ∈ frontier D.target.carrier)
    (hnw : w ∉ Set.range D.target.pts) {i j : Fin N} (hij : i ≠ j)
    (h1 : (D.tile i).localAngle w = γ) (h2 : (D.tile j).localAngle w = γ) : False := by
  obtain ⟨hapi, hbpi, hgpi, ha2, hb2, hg2, ha0, hb0, hg0⟩ := ang_ne S
  obtain ⟨hαβ, hβγ, hαγ, -, -, -⟩ := BandSetup.distinct S
  exact Erdos634.Geometry.Dissection.congruentDissection_no_double_gamma D α β γ hαβ hαγ hapi ha0 hβγ hbpi hb0 hgpi
    hg0 Real.pi_ne_zero S.hγdef S.hrel S.hirr S.hα' S.hβ' S.hγ' hw hnw i j hij h1 h2

namespace LFrame

variable (F : LFrame D e f α β γ p q r)

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
  hme : m + 1 ≤ e
  IHT : ∀ i, i < m → F.TRule H i
  IHA : ∀ i, i < m → F.ARule H i
  hnsJ : ¬ F.StrL ((m : ℝ) + 1) (lv : ℝ) (F.pt ((m : ℝ) + 1) (lv : ℝ))

/-- A far tile on `[D_{s'}, D_{s'+1}]` presenting `γ` at `D_{s'+1}`. -/
def FarB (m lv s' : ℕ) : Prop :=
  ∃ (i : Fin N) (Z : Plane), TileVerts (D.tile i) (F.Dp m lv (s' : ℝ)) (F.Dp m lv ((s' : ℝ) + 1)) Z ∧
    (∀ j, (crossL (F.v - F.e0) : Plane →ₗ[ℝ] ℝ) ((D.tile i).pts j) ≤ cross (F.v - F.e0) (F.pt ((m : ℝ) + 1) (lv : ℝ))) ∧
    (D.tile i).localAngle (F.Dp m lv ((s' : ℝ) + 1)) = γ

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

end LFrame

end Erdos634.LaczMJ
