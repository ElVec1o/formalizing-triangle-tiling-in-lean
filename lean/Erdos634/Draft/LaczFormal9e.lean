import Erdos634.Draft.LaczFormalThm33iii3
import Erdos634.Draft.LaczFormalThm21Final
import Erdos634.Draft.LaczFormalCaseIIINote
import Erdos634.Draft.LaczFormalThm33if5

/-!
# Laczkovich: DM 140 (1995) Theorem 5.4 (congruent form) and DCG 48 (2012) Theorem 2.4

NOTE, UNAUDITED.  Credit: Laczkovich (Discrete Math. 140 (1995) Thm 5.4; DCG 48 (2012) Thm 2.1, Thm 2.4, Thm 3.3), Beeson,
Beeson-Zhang.  Formalization debt, not progress on the /goal outcomes.

* `thm54_congruent`: every dissection of the equilateral triangle into CONGRUENT triangles has tile angle `pi/3` or `2pi/3`
  (the congruent case of printed DM 140 Thm 5.4, which concerns similar, not nec. congruent, pieces: WEAKER than printed).
* `thm24_2012`: printed DCG 48 (2012) Thm 2.4: a regular tiling (any of the three alternatives `p=q`, `p=r`, `q=r`) of a convex
  `M`-gon by congruent triangles of sides `a, b, c` gives `M <= 6`, or `A` is a regular `M`-gon, or `A` is rational and
  centrally symmetric (`CSym`: opposite sides equal and all angles equal, which for convex polygons is the printed central symmetry;
  the equivalence is NOT proved here), or `a, b, c` are pairwise commensurable.  From `RG.theorem21_unconditional` and the
  relabelling `RG.regular_relabel`.
-/

open scoped Classical
open Erdos634.Geometry Erdos634.TilePlacement Erdos634.RegionDissection Erdos634.Draft.TheoremPConditional
  Erdos634.Draft.LaczFormal Erdos634.Draft.LaczFormal.Thm21 Erdos634.Draft.LaczFormal.RG

namespace Erdos634.Laczkovich9

/-- **DM 140 (1995) Thm 5.4, congruent form.** -/
theorem thm54_congruent {N : ℕ} (D : CongruentDissection N) (hEq : Equilateral D) :
    ∃ k : Fin 3, D.model.angleAt k = Real.pi / 3 ∨ D.model.angleAt k = 2 * Real.pi / 3 := by
  obtain ⟨x, y, z, ⟨σ, h0, h1, h2⟩, h⟩ := thm33_only_if D hEq
  refine ⟨σ 2, ?_⟩
  rcases h with ⟨_, _, hz⟩ | ⟨_, _, hz⟩ | ⟨hz, -⟩
  · exact Or.inr (by rw [h2, hz])
  · exact Or.inl (by rw [h2, hz])
  · rcases hz with hz | hz
    · exact Or.inl (by rw [h2, hz])
    · exact Or.inr (by rw [h2, hz])

theorem comm_sides {sx sy a b : ℝ} (hsy : 0 < sy) (hr : sy * a = sx * b) (hc : Comm sx sy) : Comm a b := by
  obtain ⟨p, q, hp, hq, e⟩ := hc
  refine ⟨p, q, hp, hq, ?_⟩
  have : ((p : ℝ) * a - q * b) * sy = 0 := by
    have e1 : (p : ℝ) * a * sy = p * (sy * a) := by ring
    rw [sub_mul, e1, hr]
    linear_combination (b : ℝ) * e
  rcases mul_eq_zero.mp this with h | h
  · linarith
  · exact absurd h hsy.ne'

theorem comm_symm' {x y : ℝ} (h : Comm x y) : Comm y x := by
  obtain ⟨p, q, hp, hq, e⟩ := h; exact ⟨q, p, hq, hp, e.symm⟩

theorem comm_refl' (x : ℝ) : Comm x x := ⟨1, 1, one_pos, one_pos, by simp⟩

/-- Sine-commensurability of the (relabelled) model gives commensurable sides of the model. -/
theorem sides_of_sinComm {N : ℕ} (C : CongruentRegionDissection N) (σ : Equiv.Perm (Fin 3))
    (h : SinComm (relabel C σ)) :
    Comm (sideOpp C.model 0) (sideOpp C.model 1) ∧ Comm (sideOpp C.model 1) (sideOpp C.model 2) ∧
      Comm (sideOpp C.model 0) (sideOpp C.model 2) := by
  have h' : Comm (Real.sin (angleAt C.model (σ 0))) (Real.sin (angleAt C.model (σ 1))) ∧
      Comm (Real.sin (angleAt C.model (σ 1))) (Real.sin (angleAt C.model (σ 2))) ∧
      Comm (Real.sin (angleAt C.model (σ 0))) (Real.sin (angleAt C.model (σ 2))) := by
    simpa only [SinComm, relabel_angleAt] using h
  have all : ∀ i j : Fin 3, Comm (Real.sin (angleAt C.model i)) (Real.sin (angleAt C.model j)) := by
    intro i j
    obtain ⟨a, rfl⟩ := σ.surjective i
    obtain ⟨b, rfl⟩ := σ.surjective j
    have ha : a = 0 ∨ a = 1 ∨ a = 2 := by fin_cases a <;> simp
    have hb : b = 0 ∨ b = 1 ∨ b = 2 := by fin_cases b <;> simp
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
    · exact comm_refl' _
    · exact h'.1
    · exact h'.2.2
    · exact comm_symm' h'.1
    · exact comm_refl' _
    · exact h'.2.1
    · exact comm_symm' h'.2.2
    · exact comm_symm' h'.2.1
    · exact comm_refl' _
  have l0 := Erdos634.TriLawSin.sin_angleAt_mul_sideOpp C.model 0
  have l1 := Erdos634.TriLawSin.sin_angleAt_mul_sideOpp C.model 1
  have e01 : (0 : Fin 3) + 1 = 1 := rfl
  have e12 : (1 : Fin 3) + 1 = 2 := rfl
  rw [e01] at l0
  rw [e12] at l1
  refine ⟨?_, ?_, ?_⟩
  · exact comm_sides (sin_angleAt_pos C.model 1) l0 (all 0 1)
  · exact comm_sides (sin_angleAt_pos C.model 2) l1 (all 1 2)
  · have l2 := Erdos634.TriLawSin.sin_angleAt_mul_sideOpp C.model 2
    have e20 : (2 : Fin 3) + 1 = 0 := rfl
    rw [e20] at l2
    -- sin(angle 0) * c = sin(angle 2) * a, so a, c commensurable via the pair (2, 0)
    exact comm_symm' (comm_sides (sin_angleAt_pos C.model 0) l2 (all 2 0))

/-- The shadow of central symmetry used here: opposite sides equal, all angles equal. -/
def CSym {M : ℕ} [NeZero M] (P : ConvPoly M) : Prop :=
  ∃ k : ℕ, M = 2 * k ∧ (∀ i : Fin M, P.side i = P.side (i + Fin.ofNat M k)) ∧ ∀ i, P.angle i = P.angle 0

theorem thm24_of_sigma {N M : ℕ} [NeZero M] (T : PolyTiling N M) (σ : Equiv.Perm (Fin 3))
    (h : ∃ idx : Fin N → Equiv.Perm (Fin 3), (∀ i v, angleAt T.C.model (idx i v) = angleAt (T.C.tile i) v) ∧
      ∀ X, cntR T.C idx X (σ 0) = cntR T.C idx X (σ 1)) :
    M ≤ 6 ∨ ((∀ i, T.P.side i = T.P.side 0) ∧ ∀ i, T.P.angle i = T.P.angle 0) ∨ (RationalPoly T.P ∧ CSym T.P) ∨
      (Comm (sideOpp T.C.model 0) (sideOpp T.C.model 1) ∧ Comm (sideOpp T.C.model 1) (sideOpp T.C.model 2) ∧
        Comm (sideOpp T.C.model 0) (sideOpp T.C.model 2)) := by
  have hreg := regular_relabel T.C σ h
  let T' : PolyTiling N M := ⟨relabel T.C σ, T.P, T.region_eq⟩
  have hc : Thm21Concl T'.C T'.P := theorem21_unconditional N M T' hreg
  have hsc : SinComm (relabel T.C σ) → _ := sides_of_sinComm T.C σ
  rcases hc with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9
  · exact Or.inl (by rcases h1 with ⟨⟨h4, -⟩, -⟩; omega)
  · exact Or.inr (Or.inr (Or.inr (hsc h2.2.2)))
  · exact Or.inr (Or.inr (Or.inr (hsc h3.2.2)))
  · exact Or.inl (by have := h4.1; omega)
  · right; right; left
    obtain ⟨k, hM, -, hrat, hang, hside, -⟩ := h5
    exact ⟨hrat, k, hM, hside, fun i => by rw [hang i, hang 0]⟩
  · exact Or.inl (by have := h6.1; omega)
  · right; left
    exact ⟨h7.1, h7.2.1⟩
  · exact Or.inl h8.2.1
  · exact Or.inl (by have := h9.1; omega)

/-- **Laczkovich DCG 48 (2012), Theorem 2.4.** -/
theorem thm24_2012 {N M : ℕ} [NeZero M] (T : PolyTiling N M)
    (h : ∃ idx : Fin N → Equiv.Perm (Fin 3), (∀ i v, angleAt T.C.model (idx i v) = angleAt (T.C.tile i) v) ∧
      ((∀ X, cntR T.C idx X 0 = cntR T.C idx X 1) ∨ (∀ X, cntR T.C idx X 0 = cntR T.C idx X 2) ∨
        (∀ X, cntR T.C idx X 1 = cntR T.C idx X 2))) :
    M ≤ 6 ∨ ((∀ i, T.P.side i = T.P.side 0) ∧ ∀ i, T.P.angle i = T.P.angle 0) ∨ (RationalPoly T.P ∧ CSym T.P) ∨
      (Comm (sideOpp T.C.model 0) (sideOpp T.C.model 1) ∧ Comm (sideOpp T.C.model 1) (sideOpp T.C.model 2) ∧
        Comm (sideOpp T.C.model 0) (sideOpp T.C.model 2)) := by
  obtain ⟨idx, hA, h01 | h02 | h12⟩ := h
  · exact thm24_of_sigma T 1 ⟨idx, hA, fun X => h01 X⟩
  · exact thm24_of_sigma T (Equiv.swap 1 2) ⟨idx, hA, fun X => by simpa using h02 X⟩
  · exact thm24_of_sigma T (Equiv.swap 0 2) ⟨idx, hA, fun X => by simpa using (h12 X).symm⟩

end Erdos634.Laczkovich9

#print axioms Erdos634.Laczkovich9.thm54_congruent
#print axioms Erdos634.Laczkovich9.thm24_2012
