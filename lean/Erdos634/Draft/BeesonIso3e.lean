import Erdos634.Draft.BeesonIso3d
import Erdos634.Draft.LaczFormalBZL7e1

/-!
# Beeson, "Tilings of an isosceles triangle" (arXiv 1206.1974 v7), Lemma 11.8: the angle step ("its angles at E and F must each be alpha")

NOTE, UNAUDITED.  Credit: Michael Beeson (arXiv 1206.1974 v7, Lemma 11.8; arXiv 1206.2229), Laczkovich (DCG 48 (2012), Sect. 4), Beeson-Zhang, Herdt, Zhang.
Formalization debt, not progress on the /goal outcomes.

Printed: "Since [triangle BEF] has the same angle at B as ABC, namely alpha + beta, its angles at E and F must each be alpha."  The sum `x + y = 2 alpha` of the two remaining angles
is the angle sum of `BEF`; each of `x`, `y` is a sum of tile angles `alpha`, `beta = pi - 3 alpha`, `gamma = 2 alpha`.  `north_arith` is the arithmetic: two non-empty families of
labels whose angles add up to `2 alpha` (H1: `alpha` not a rational multiple of `pi`) are one label `alpha` each.  The printed text gives no justification.
Witness: the families `{0}`, `{0}` (angles `alpha + alpha = 2 alpha`): `wit_north`.
-/

open scoped Classical

namespace Erdos634.Draft.LaczFormal.RG

theorem sum_labels (g : Fin 3 → ℝ) (T : Finset ℕ) (l : ℕ → Fin 3) :
    ∑ j ∈ T, g (l j) = ∑ k : Fin 3, ((T.filter (fun j => l j = k)).card : ℝ) * g k := by
  rw [← Finset.sum_fiberwise T l (fun j => g (l j))]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_congr rfl (fun j hj => by rw [(Finset.mem_filter.mp hj).2])]
  simp [Finset.sum_const]

theorem card_labels (T : Finset ℕ) (l : ℕ → Fin 3) :
    T.card = (T.filter (fun j => l j = 0)).card + (T.filter (fun j => l j = 1)).card + (T.filter (fun j => l j = 2)).card := by
  have := Finset.card_eq_sum_card_fiberwise (s := T) (t := (Finset.univ : Finset (Fin 3))) (f := l) (fun x _ => Finset.mem_univ _)
  rw [this, Fin.sum_univ_three]

theorem north_arith {α : ℝ} (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (g : Fin 3 → ℝ) (hg0 : g 0 = α)
    (hg1 : g 1 = Real.pi - 3 * α) (hg2 : g 2 = 2 * α)
    (S S' : Finset ℕ) (l l' : ℕ → Fin 3) (hS : S.Nonempty) (hS' : S'.Nonempty)
    (hsum : ∑ j ∈ S, g (l j) + ∑ j ∈ S', g (l' j) = 2 * α) :
    S.card = 1 ∧ S'.card = 1 ∧ (∀ j ∈ S, l j = 0) ∧ (∀ j ∈ S', l' j = 0) := by
  rw [sum_labels g S l, sum_labels g S' l', Fin.sum_univ_three, Fin.sum_univ_three, hg0, hg1, hg2] at hsum
  set n0 := (S.filter (fun j => l j = 0)).card with hn0
  set n1 := (S.filter (fun j => l j = 1)).card with hn1
  set n2 := (S.filter (fun j => l j = 2)).card with hn2
  set m0 := (S'.filter (fun j => l' j = 0)).card with hm0
  set m1 := (S'.filter (fun j => l' j = 1)).card with hm1
  set m2 := (S'.filter (fun j => l' j = 2)).card with hm2
  have key := vtype_arith (α := α) (β := Real.pi - 3 * α) rfl hα (n0 + m0) (n1 + m1) (n2 + m2) 2 0
    (by push_cast; linarith)
  obtain ⟨k1, k2⟩ := key
  have hcS := card_labels S l
  have hcS' := card_labels S' l'
  have hSpos : 0 < S.card := Finset.card_pos.mpr hS
  have hS'pos : 0 < S'.card := Finset.card_pos.mpr hS'
  have k1' : n1 + m1 = 0 := by exact_mod_cast k1
  have k2' : n0 + m0 + 2 * (n2 + m2) = 2 := by omega
  have e1 : n1 = 0 := by omega
  have e1' : m1 = 0 := by omega
  have e2 : n2 = 0 := by omega
  have e2' : m2 = 0 := by omega
  have e0 : n0 = 1 := by omega
  have e0' : m0 = 1 := by omega
  refine ⟨by omega, by omega, ?_, ?_⟩
  · intro j hj
    have h1 : j ∉ S.filter (fun j => l j = 1) := by
      intro h; have : 0 < n1 := Finset.card_pos.mpr ⟨j, h⟩; omega
    have h2 : j ∉ S.filter (fun j => l j = 2) := by
      intro h; have : 0 < n2 := Finset.card_pos.mpr ⟨j, h⟩; omega
    simp only [Finset.mem_filter, not_and] at h1 h2
    have a1 := h1 hj
    have a2 := h2 hj
    generalize l j = x at a1 a2 ⊢
    fin_cases x <;> simp_all
  · intro j hj
    have h1 : j ∉ S'.filter (fun j => l' j = 1) := by
      intro h; have : 0 < m1 := Finset.card_pos.mpr ⟨j, h⟩; omega
    have h2 : j ∉ S'.filter (fun j => l' j = 2) := by
      intro h; have : 0 < m2 := Finset.card_pos.mpr ⟨j, h⟩; omega
    simp only [Finset.mem_filter, not_and] at h1 h2
    have a1 := h1 hj
    have a2 := h2 hj
    generalize l' j = x at a1 a2 ⊢
    fin_cases x <;> simp_all

/-- Witness: two families `{0}`, `{0}` of label `alpha` give `2 alpha`. -/
theorem wit_north (α : ℝ) (g : Fin 3 → ℝ) (hg0 : g 0 = α) :
    ∑ j ∈ ({0} : Finset ℕ), g ((fun _ => (0 : Fin 3)) j) + ∑ j ∈ ({0} : Finset ℕ), g ((fun _ => (0 : Fin 3)) j) = 2 * α := by
  simp [hg0]; ring

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.north_arith
