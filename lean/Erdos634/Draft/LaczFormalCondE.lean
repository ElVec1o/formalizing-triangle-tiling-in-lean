-- Draft/LaczFormalCondE.lean -- CONDITION (E) of Laczkovich, "Irregular tilings of regular polygons with similar triangles" (arXiv 2002.12013, Sect. 1.3, p. 6),
-- for a congruent dissection of a triangle: the tile corners fall into vertices (points of the plane); at the three corners of the target the corner
-- angles sum to the target's angle, at every other vertex the tile angles sum to pi or 2 pi, and (each tile having one corner of each kind) the totals
-- sum_P p_P = sum_P q_P = sum_P r_P = N.  Stated in the style of `KConj.fig`/`vertex_sum`: `cnt D idx P l` = number of tile corners at P of model type l.
-- (The paper's vertex sums pi/2pi at "non-corner" points are obtained here from `sum_localAngle_eq`: the corner sum at P is the total angle at P
-- minus pi times a natural number, and is positive.)  UNAUDITED.  Credit: Laczkovich (2020, Condition (E); 1995, vertex equations).
import Erdos634.Draft.KConjLemmaK

open scoped BigOperators Classical
open Erdos634.Geometry Erdos634.KConj Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal

variable {N : ℕ}

/-- Number of tile corners located at `P` of model type `l` (same as `KConj.fig` at a target corner). -/
noncomputable def cnt (D : CongruentDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) (P : Plane) (l : Fin 3) : ℕ :=
  (Finset.univ.filter (fun p : Fin N × Fin 3 => (D.tile p.1).pts p.2 = P ∧ idx p.1 p.2 = l)).card

theorem exists_idx_general (D : CongruentDissection N) :
    ∃ idx : Fin N → Equiv.Perm (Fin 3), ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v := by
  choose idx hidx using fun i => Tri.Congruent.cornerAngle_perm (D.tiles_congruent i)
  exact ⟨idx, fun i v => hidx i v⟩

theorem fiber_sum_P (D : CongruentDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) (P : Plane)
    (g : Fin 3 → ℝ) :
    ∑ i, ∑ v, (if (D.tile i).pts v = P then g (idx i v) else 0) = ∑ l, (cnt D idx P l : ℝ) * g l := by
  have h1 : ∀ l, (cnt D idx P l : ℝ) * g l = ∑ p : Fin N × Fin 3,
      (if (D.tile p.1).pts p.2 = P ∧ idx p.1 p.2 = l then g l else 0) := by
    intro l
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, cnt]
  calc ∑ i, ∑ v, (if (D.tile i).pts v = P then g (idx i v) else 0)
      = ∑ p : Fin N × Fin 3, (if (D.tile p.1).pts p.2 = P then g (idx p.1 p.2) else 0) :=
        by rw [Fintype.sum_prod_type]
    _ = ∑ p : Fin N × Fin 3, ∑ l, (if (D.tile p.1).pts p.2 = P ∧ idx p.1 p.2 = l then g l else 0) := by
        refine Finset.sum_congr rfl (fun p _ => ?_)
        by_cases hp : (D.tile p.1).pts p.2 = P
        · simp only [hp, true_and, if_true]
          rw [Finset.sum_ite_eq]; simp
        · simp [hp]
    _ = ∑ l, ∑ p : Fin N × Fin 3, (if (D.tile p.1).pts p.2 = P ∧ idx p.1 p.2 = l then g l else 0) :=
        Finset.sum_comm
    _ = ∑ l, (cnt D idx P l : ℝ) * g l := by simp_rw [h1]

end Erdos634.Draft.LaczFormal

namespace Erdos634.Draft.LaczFormal

open Erdos634.Geometry Erdos634.KConj Erdos634.TilePlacement

variable {N : ℕ}

/-- **Vertex sum at any vertex.**  At a point `P` that is a corner of some tile, the angles of the tile corners located at `P` sum to the target's
angle (if `P` is a target corner) or to `π` or `2π` (otherwise). -/
theorem vertex_group (D : CongruentDissection N) (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v) (P : Plane)
    (hP : ∃ p : Fin N × Fin 3, (D.tile p.1).pts p.2 = P) :
    (∃ j, P = D.target.pts j ∧
        ∑ l, (cnt D idx P l : ℝ) * D.model.angleAt l = D.target.angleAt j) ∨
    ((∀ j, P ≠ D.target.pts j) ∧
        (∑ l, (cnt D idx P l : ℝ) * D.model.angleAt l = Real.pi ∨
         ∑ l, (cnt D idx P l : ℝ) * D.model.angleAt l = 2 * Real.pi)) := by
  have hpi := Real.pi_pos
  set S : ℝ := ∑ l, (cnt D idx P l : ℝ) * D.model.angleAt l with hS
  -- S = ∑_i vc
  have hSvc : S = ∑ i, vc (D.tile i) P := by
    rw [hS, ← fiber_sum_P D idx P D.model.angleAt]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    unfold vc
    refine Finset.sum_congr rfl (fun v _ => ?_)
    split_ifs
    · exact hidx i v
    · rfl
  -- each tile: localAngle = vc + a_i * π
  have hloc : ∀ i, ∃ a : ℕ, a ≤ 2 ∧ (D.tile i).localAngle P = vc (D.tile i) P + a * Real.pi := by
    intro i
    by_cases hv : ∃ v, (D.tile i).pts v = P
    · obtain ⟨v, hv⟩ := hv
      refine ⟨0, by norm_num, ?_⟩
      rw [← hv, vc_of_vertex]; simp
    · push Not at hv
      have hv' : ∀ v, P ≠ (D.tile i).pts v := fun v h => hv v h.symm
      rw [vc_of_nonvertex _ _ hv']
      rcases Erdos634.PinPlumbing.localAngle_cases (D.tile i) P with ⟨j, hj, -⟩ | h2 | h1 | h0
      · exact absurd hj (hv' j)
      · exact ⟨2, by norm_num, by rw [h2]; push_cast; ring⟩
      · exact ⟨1, by norm_num, by rw [h1]; push_cast; ring⟩
      · exact ⟨0, by norm_num, by rw [h0]; simp⟩
  choose a ha2 hloc using hloc
  set A : ℕ := ∑ i, a i with hA
  have hsum : ∑ i, (D.tile i).localAngle P = S + A * Real.pi := by
    rw [hSvc, hA]
    push_cast
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => hloc i)
  have hnn : ∀ i, 0 ≤ vc (D.tile i) P := by
    intro i; unfold vc
    exact Finset.sum_nonneg (fun v _ => by
      split_ifs
      · exact (Erdos634.MarchFlank.cornerAngle_pos (D.tile i) v).le
      · exact le_refl _)
  obtain ⟨p0, hp0⟩ := hP
  have hSpos : 0 < S := by
    rw [hSvc]
    have h1 : 0 < vc (D.tile p0.1) P := by
      unfold vc
      have hpos : ∀ T : Tri, ∀ v, 0 < T.angleAt v := fun T v => Erdos634.MarchFlank.cornerAngle_pos T v
      have := Finset.single_le_sum (f := fun v => if (D.tile p0.1).pts v = P then (D.tile p0.1).angleAt v else 0)
        (fun v _ => by
          dsimp only
          split_ifs
          · exact (hpos _ v).le
          · exact le_refl _) (Finset.mem_univ p0.2)
      refine lt_of_lt_of_le ?_ this
      dsimp only
      rw [if_pos hp0]
      exact hpos _ _
    exact lt_of_lt_of_le h1 (Finset.single_le_sum (f := fun i => vc (D.tile i) P) (fun i _ => hnn i)
      (Finset.mem_univ p0.1))
  have htot := D.toDissection.sum_localAngle_eq P
  rw [hsum] at htot
  have hAnn : (0 : ℝ) ≤ A := by positivity
  by_cases hc : ∃ j, P = D.target.pts j
  · obtain ⟨j, hj⟩ := hc
    left
    refine ⟨j, hj, ?_⟩
    have hT : D.target.localAngle P = D.target.angleAt j := by
      rw [hj, Tri.localAngle_vertex]; rfl
    have hlt : D.target.angleAt j < Real.pi := Erdos634.RouteOneVertexKill.cornerAngle_lt_pi D.target j
    rw [hT] at htot
    have hA0 : A = 0 := by
      by_contra hne
      have : (1 : ℝ) ≤ A := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hne
      nlinarith
    rw [hA0] at htot; simp at htot; linarith
  · right
    push Not at hc
    refine ⟨hc, ?_⟩
    rcases Erdos634.PinPlumbing.localAngle_cases D.target P with ⟨j, hj, -⟩ | h2 | h1 | h0
    · exact absurd hj (hc j)
    · rw [h2] at htot
      have : A = 0 ∨ A = 1 ∨ 2 ≤ A := by omega
      rcases this with h | h | h
      · right; rw [h] at htot; simp at htot; linarith
      · left; rw [h] at htot; simp at htot; linarith
      · exfalso
        have : (2 : ℝ) ≤ A := by exact_mod_cast h
        nlinarith
    · rw [h1] at htot
      have : A = 0 ∨ 1 ≤ A := by omega
      rcases this with h | h
      · left; rw [h] at htot; simp at htot; linarith
      · exfalso
        have : (1 : ℝ) ≤ A := by exact_mod_cast h
        nlinarith
    · rw [h0] at htot
      exfalso
      nlinarith

end Erdos634.Draft.LaczFormal
