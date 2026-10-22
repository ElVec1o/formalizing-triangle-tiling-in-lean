import Erdos634.Draft.BeesonIso5c

/-!
# Beeson, "Tilings of an isosceles triangle" (arXiv 1206.1974 v7), Lemma 11.10, "at least four": the structure of a leg of length `a + c`

NOTE, UNAUDITED.  Credit: Michael Beeson (arXiv 1206.1974 v7, Lemma 11.10), Laczkovich (DCG 48 (2012)), Beeson-Zhang, Herdt, Zhang.
Formalization debt, not progress on the /goal outcomes.

`leg_structure`: a left walk along a side `i` of the polygon of total length `a + c` (tile `t (k^2, m^2-k^2, km)`) consists of exactly two steps `e1`, `e2`, of lengths `(a, c)` or `(c, a)`
(arithmetic `leg_arith`, existence of a c-step `side_has_c_step`), with the junction in the relative interior of the side.
-/

open scoped Classical
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ} [NeZero M]

theorem leg_structure (C : CongruentRegionDissection N) [HasFansC C.toRegionDissection] (P : ConvPoly M) (hreg : C.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((C.tile i).pts k) ((C.tile i).pts k') = dist (C.model.pts (idx i k)) (C.model.pts (idx i k')))
    (hidxA : ∀ i v, C.model.angleAt (idx i v) = (C.tile i).angleAt v)
    (hβ : C.model.angleAt 1 = Real.pi - 3 * C.model.angleAt 0) (hγ : C.model.angleAt 2 = 2 * C.model.angleAt 0)
    (hα : ¬ ∃ r : ℚ, C.model.angleAt 0 = (r : ℝ) * Real.pi)
    (hPang : ∀ k : Fin M, P.angle (k + 1) = C.model.angleAt 0 ∨ P.angle (k + 1) = Real.pi - 2 * C.model.angleAt 0)
    (hab : slen C 0 ≠ slen C 1) (hac : slen C 0 ≠ slen C 2) (hbc : slen C 1 ≠ slen C 2)
    {t : ℝ} (ht : 0 < t) {kt mt : ℕ} (hcop : Nat.Coprime kt mt) (hlt : kt < mt) (hm2 : mt < 2 * kt)
    (ea : slen C 0 = t * (kt : ℝ) ^ 2) (eb : slen C 1 = t * ((mt : ℝ) ^ 2 - (kt : ℝ) ^ 2)) (ec : slen C 2 = t * ((kt : ℝ) * mt))
    (i : Fin M) {L : List (Fin N × Plane × Plane)} (W : WalkT C.toRegionDissection (toV2 (P.e i)) (P.v i) (P.v (i + 1)) L)
    (hX : dist (P.v i) (P.v (i + 1)) = slen C 0 + slen C 2) :
    ∃ e1 e2 : Fin N × Plane × Plane, L = [e1, e2] ∧
      ((dist e1.2.1 e1.2.2 = slen C 0 ∧ dist e2.2.1 e2.2.2 = slen C 2) ∨ (dist e1.2.1 e1.2.2 = slen C 2 ∧ dist e2.2.1 e2.2.2 = slen C 0)) ∧
      e1.2.1 = P.v i ∧ e1.2.2 = e2.2.1 ∧ e2.2.2 = P.v (i + 1) ∧
      TriStep (C.tile e1.1) (toV2 (P.e i)) e1.2.1 e1.2.2 ∧ TriStep (C.tile e2.1) (toV2 (P.e i)) e2.2.1 e2.2.2 ∧
      ∃ s : ℝ, 0 < s ∧ s < 1 ∧ e2.2.1 = (1 - s) • P.v i + s • P.v (i + 1) := by
  have hmem : ∀ x ∈ L.map (fun e => dist e.2.1 e.2.2), x = slen C 0 ∨ x = slen C 1 ∨ x = slen C 2 := by
    intro x hx
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
    exact side_len_mem C idx hidx (walkT_mem_step W e he)
  have hsum : (L.map (fun e => dist e.2.1 e.2.2)).sum = slen C 0 + slen C 2 := by rw [walkT_dist_sum W]; exact hX
  have hcx : ∃ x ∈ L.map (fun e => dist e.2.1 e.2.2), x = slen C 2 := by
    obtain ⟨e, he, hno⟩ := side_has_c_step C P hreg idx hidxA hβ hγ hα hPang i W
    exact ⟨dist e.2.1 e.2.2, List.mem_map.mpr ⟨e, he, rfl⟩, cstep_dist C idx hidx (walkT_mem_step W e he) hno⟩
  obtain ⟨x, y, hds, hcase⟩ := leg_pair ht hcop hlt hm2 ea eb ec hab hac hbc _ hmem hsum hcx
  have hlen : L.length = 2 := by
    have := congrArg List.length hds
    simpa using this
  obtain ⟨e1, e2, rfl⟩ := List.length_eq_two.mp hlen
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hds
  obtain ⟨hx, hy⟩ := hds
  obtain ⟨e1j, e10, e11⟩ := e1
  obtain ⟨e2j, e20, e21⟩ := e2
  obtain ⟨h0, hS1, W'⟩ := walkT_cons_inv' W
  obtain ⟨h0', hS2, W''⟩ := walkT_cons_inv' W'
  have hY := walkT_nil_inv' W''
  obtain ⟨s, hs0, hs1, hs⟩ := walkT_open_side C.toRegionDissection P i W (L1 := []) (x := (e1j, e10, e11)) (y := (e2j, e20, e21)) (L2 := []) rfl
  have hS1' : TriStep (C.tile e1j) (toV2 (P.e i)) e10 e11 := by rw [h0]; exact hS1
  have hS2' : TriStep (C.tile e2j) (toV2 (P.e i)) e20 e21 := by rw [h0']; exact hS2
  refine ⟨(e1j, e10, e11), (e2j, e20, e21), rfl, ?_, h0, h0'.symm, hY, hS1', hS2', s, hs0, hs1, hs⟩
  rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left; exact ⟨hx.trans h1, hy.trans h2⟩
  · right; exact ⟨hx.trans h1, hy.trans h2⟩

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.leg_structure
