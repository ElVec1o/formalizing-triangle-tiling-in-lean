-- Draft/LaczFormalRG9Sides.lean -- open sides of a strictly convex polygon (pairwise disjoint, disjoint from the vertices), and, for Case I, the normality of tiling vertices on a side
-- without exceptional vertex; the number of sides carrying an exceptional vertex is at most the number of exceptional vertices.  UNAUDITED.
-- Credit: Laczkovich (DCG 48 (2012), Sect. 5), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalRG9Count
import Erdos634.Draft.LaczFormalRG9Side

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ} [NeZero M]

theorem c_vertex_nonneg (P : ConvPoly M) (j m : Fin M) : 0 ≤ P.c j (P.v m) := by
  by_cases h1 : m = j
  · rw [h1, ConvPoly.c_self]
  · by_cases h2 : m = j + 1
    · rw [h2, ConvPoly.c_next]
    · exact (P.c_vertex_pos h1 h2).le

/-- A point of the open side `i` has `c_j > 0` for every `j ≠ i`. -/
theorem openSide_c_pos (P : ConvPoly M) {i j : Fin M} (hij : j ≠ i) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    0 < P.c j ((1 - t) • P.v i + t • P.v (i + 1)) := by
  rw [ConvPoly.c_comb]
  have hM := P.three_le
  have hf := ConvPoly.fin_facts hM j
  have hex : 0 < P.c j (P.v i) ∨ 0 < P.c j (P.v (i + 1)) := by
    by_cases h1 : i = j + 1
    · right
      apply P.c_vertex_pos
      · rw [h1, hf.2.2.2.2.2]; exact hf.2.1
      · rw [h1, hf.2.2.2.2.2]; exact hf.2.2.1
    · left
      exact P.c_vertex_pos hij.symm h1
  have h0 := c_vertex_nonneg P j i
  have h0' := c_vertex_nonneg P j (i + 1)
  rcases hex with h | h
  · nlinarith [mul_pos (sub_pos.mpr ht1) h, mul_nonneg ht0.le h0']
  · nlinarith [mul_pos ht0 h, mul_nonneg (sub_pos.mpr ht1).le h0]

/-- Distinct sides have disjoint relative interiors. -/
theorem openSide_unique (P : ConvPoly M) {i j : Fin M} {t t' : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (ht0' : 0 < t') (ht1' : t' < 1)
    (h : (1 - t) • P.v i + t • P.v (i + 1) = (1 - t') • P.v j + t' • P.v (j + 1)) : i = j := by
  by_contra hne
  have h1 := openSide_c_pos P (i := j) (j := i) hne ht0' ht1'
  rw [← h, c_on_edge] at h1
  exact lt_irrefl _ h1

/-- The relative interior of a side contains no vertex of the polygon. -/
theorem openSide_ne_vertex (P : ConvPoly M) {i : Fin M} {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (m : Fin M) :
    (1 - t) • P.v i + t • P.v (i + 1) ≠ P.v m := by
  intro h
  have hc : P.c i (P.v m) = 0 := by rw [← h]; exact c_on_edge P i t
  have hM := P.three_le
  have hf := ConvPoly.fin_facts hM i
  by_cases h1 : m = i
  · subst h1
    have : t • (P.v (m + 1) - P.v m) = 0 := by
      have e : t • (P.v (m + 1) - P.v m) = ((1 - t) • P.v m + t • P.v (m + 1)) - P.v m := by module
      rw [e, h, sub_self]
    rcases smul_eq_zero.mp this with h0 | h0
    · exact ht0.ne' h0
    · have := polyV_injective P (sub_eq_zero.mp h0)
      exact hf.1 this
  · by_cases h2 : m = i + 1
    · subst h2
      have : (1 - t) • (P.v i - P.v (i + 1)) = 0 := by
        have e : (1 - t) • (P.v i - P.v (i + 1)) = ((1 - t) • P.v i + t • P.v (i + 1)) - P.v (i + 1) := by module
        rw [e, h, sub_self]
      rcases smul_eq_zero.mp this with h0 | h0
      · exact (sub_pos.mpr ht1).ne' h0
      · have := polyV_injective P (sub_eq_zero.mp h0)
        exact hf.1 this.symm
    · have := P.c_vertex_pos h1 h2
      linarith

/-- **Normal vertices on a side without exceptional vertex** (Case I). -/
theorem caseI_normal_side (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v) (hregc : ∀ X, cnt D idx X 0 = cnt D idx X 1)
    (h1 : Real.pi / 2 < D.model.angleAt 2) (h3 : D.model.angleAt 2 ≠ 2 * Real.pi / 3) {i : Fin M} {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) {X : Plane}
    (hX : X = (1 - t) • P.v i + t • P.v (i + 1)) (hvert : ∃ j k, (D.tile j).pts k = X) (hne : X ∉ excVerts D idx P) :
    cnt D idx X 0 = 1 ∧ cnt D idx X 1 = 1 ∧ cnt D idx X 2 = 1 := by
  have hnc : ∀ k : Fin M, X ≠ P.v (k + 1) := fun k => by rw [hX]; exact openSide_ne_vertex P ht0 ht1 (k + 1)
  have hni : X ∉ interior D.region := by
    rw [hreg, hX]; exact not_interior_of_c_zero P (c_on_edge P i t)
  obtain ⟨hle, -, hn⟩ := caseI_nonpoly D P hreg idx hidxA hregc h1 h3 hvert hnc
  have hnex : ¬ cnt D idx X 2 < cnt D idx X 0 := by
    intro hlt
    apply hne
    unfold excVerts
    simp only [Finset.mem_filter, Finset.mem_sdiff]
    exact ⟨⟨mem_vtxSet.mpr hvert, fun hp => by obtain ⟨k, hk⟩ := mem_polyVerts.mp hp; exact hnc k hk⟩, hlt⟩
  have heq : cnt D idx X 2 = cnt D idx X 0 := by omega
  have h0 := hn heq hni
  refine ⟨h0, ?_, by omega⟩
  rw [← hregc X]; exact h0

/-- The side `i` carries an exceptional vertex in its relative interior. -/
def SideBad (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) (P : ConvPoly M) (i : Fin M) : Prop :=
  ∃ X ∈ excVerts D idx P, ∃ t : ℝ, 0 < t ∧ t < 1 ∧ X = (1 - t) • P.v i + t • P.v (i + 1)

/-- At most as many sides carry an exceptional vertex as there are exceptional vertices. -/
theorem sideBad_card (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) (P : ConvPoly M) :
    (Finset.univ.filter (SideBad D idx P)).card ≤ (excVerts D idx P).card := by
  classical
  let g : Fin M → Plane := fun i => if h : SideBad D idx P i then Classical.choose h else 0
  apply Finset.card_le_card_of_injOn g
  · intro i hi
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hi
    simp only [g, dif_pos hi]
    exact (Classical.choose_spec hi).1
  · intro i hi j hj hij
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hi hj
    simp only [g, dif_pos hi, dif_pos hj] at hij
    obtain ⟨-, t, ht0, ht1, hX⟩ := Classical.choose_spec hi
    obtain ⟨-, t', ht0', ht1', hX'⟩ := Classical.choose_spec hj
    rw [hij] at hX
    exact openSide_unique P ht0 ht1 ht0' ht1' (hX.symm.trans hX')

/-- A set of sides larger than the number of exceptional vertices contains a side without exceptional vertex. -/
theorem exists_good_side (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) (P : ConvPoly M) (S : Finset (Fin M))
    (hS : (excVerts D idx P).card < S.card) : ∃ i ∈ S, ¬ SideBad D idx P i := by
  by_contra hall
  push Not at hall
  have hsub : S ⊆ Finset.univ.filter (SideBad D idx P) := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hall i hi
  have := Finset.card_le_card hsub
  have := sideBad_card D idx P
  omega

end Erdos634.Draft.LaczFormal.RG
