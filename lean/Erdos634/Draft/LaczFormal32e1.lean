-- Draft/LaczFormal32e1.lean -- Laczkovich, DCG 48 (2012) Lemma 3.2, TILING form (printed statement, p. 337-338):
--   "Suppose the convex polygon A has an irregular tiling with congruent triangles of angles alpha, beta, gamma.  Then alpha, beta, gamma are
--    linear combinations of the angles of A with rational coefficients."
-- `lemma32_tiling`: T a PolyTiling (any N, any strictly convex M-gon, reflections allowed, not edge-to-edge), idx an angle-preserving vertex
-- correspondence for which the tiling is irregular (p_i != q_i somewhere, p_i != r_i somewhere, q_i != r_i somewhere, p,q,r = cntR),
-- conclusion: each model angle lies in the Q-span of the polygon angles.  Route: rows = the vertices of the tiles (subtype of vtxSet);
-- corners = polygon vertices (c = A_X/pi = delta/pi from `corner_A`), other rows c in {1,2} (`vertex_A`); counting (4) = `sum_cnt_vtx`;
-- then `lemma32_arith` (Laczkovich DCG 19 (1998) Lemma 10 minimisation).  pi is in the span by `poly_angle_sum`.
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012) Lemma 3.2; DCG 19 (1998) Lemma 10), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormal32c
import Erdos634.Draft.LaczFormalBZ2
import Erdos634.Draft.LaczFormalRG9Geo
import Erdos634.Draft.LaczFormalRG4AngleSum
import Erdos634.Draft.LaczFormalRGCondE

open scoped Classical BigOperators
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ} [NeZero M]

/-- Irregular (Laczkovich, Sect. 2), for the vertex correspondence `idx`: none of the three equalities p = q, p = r, q = r holds at every point. -/
def IrregularIdx (C : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) : Prop :=
  (∃ X, cntR C idx X 0 ≠ cntR C idx X 1) ∧ (∃ X, cntR C idx X 0 ≠ cntR C idx X 2) ∧ (∃ X, cntR C idx X 1 ≠ cntR C idx X 2)

theorem cnt_eq_cntR' (C : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) (X : Plane) (l : Fin 3) :
    cnt C idx X l = cntR C idx X l := by
  unfold cnt cntR; congr

theorem cnt_zero_of_notin (C : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) {X : Plane}
    (hX : X ∉ vtxSet C.toRegionDissection) (l : Fin 3) : cnt C idx X l = 0 := by
  unfold cnt
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro p _ hp
  exact hX (mem_vtxSet.mpr ⟨p.1, p.2, hp.1⟩)

theorem mem_vtx_of_cnt_ne (C : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) {X : Plane} {l l' : Fin 3}
    (h : cnt C idx X l ≠ cnt C idx X l') : X ∈ vtxSet C.toRegionDissection := by
  by_contra hX
  exact h (by rw [cnt_zero_of_notin C idx hX, cnt_zero_of_notin C idx hX])

theorem pi_mem_span (P : ConvPoly M) : Real.pi ∈ Submodule.span ℚ (Set.range P.angle) := by
  have hsum := poly_angle_sum P
  have hmem : ∑ i : Fin M, P.angle i ∈ Submodule.span ℚ (Set.range P.angle) :=
    Submodule.sum_mem _ (fun i _ => Submodule.subset_span ⟨i, rfl⟩)
  have h3 := P.three_le
  have hne : ((M - 2 : ℕ) : ℚ) ≠ 0 := by
    have : 0 < M - 2 := by omega
    exact_mod_cast this.ne'
  have : Real.pi = ((((M - 2 : ℕ) : ℚ))⁻¹) • ∑ i : Fin M, P.angle i := by
    rw [hsum, Rat.smul_def]
    push_cast
    have hne' : ((M - 2 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hne
    field_simp
  rw [this]
  exact Submodule.smul_mem _ _ hmem

/-- **Laczkovich, DCG 48 (2012), Lemma 3.2, for tilings.** -/
theorem lemma32_tiling (T : PolyTiling N M) (idx : Fin N → Equiv.Perm (Fin 3))
    (hidxA : ∀ i v, angleAt T.C.model (idx i v) = angleAt (T.C.tile i) v) (hirr : IrregularIdx T.C idx) :
    ∀ l : Fin 3, angleAt T.C.model l ∈ Submodule.span ℚ (Set.range T.P.angle) := by
  classical
  have hpi := Real.pi_pos
  set D := T.C with hD
  haveI : HasFansC D.toRegionDissection := hasFansC_poly _ T.P T.region_eq
  set V := vtxSet D.toRegionDissection with hV
  have hreg : D.region = T.P.carrier := T.region_eq
  set m0 := D.model.angleAt 0 with hm0
  set m1 := D.model.angleAt 1 with hm1
  set m2 := D.model.angleAt 2 with hm2
  let Pn : V → ℕ := fun X => cnt D idx X.1 0
  let Qn : V → ℕ := fun X => cnt D idx X.1 1
  let Rn : V → ℕ := fun X => cnt D idx X.1 2
  let c : V → ℝ := fun X => Asum D idx X.1 / Real.pi
  let C : Finset V := Finset.univ.filter (fun X => ∃ k : Fin M, X.1 = T.P.v (k + 1))
  let a : V → ℝ := fun X => if h : ∃ k : Fin M, X.1 = T.P.v (k + 1) then T.P.angle (Classical.choose h + 1) / Real.pi else 0
  have hvert : ∀ X : V, ∃ j k, (D.tile j).pts k = X.1 := fun X => mem_vtxSet.mp X.2
  have haX : ∀ X : V, X ∈ C → ∃ k : Fin M, X.1 = T.P.v (k + 1) ∧ a X = T.P.angle (k + 1) / Real.pi ∧ c X = a X := by
    intro X hX
    have h : ∃ k : Fin M, X.1 = T.P.v (k + 1) := by simpa [C] using hX
    refine ⟨Classical.choose h, Classical.choose_spec h, ?_, ?_⟩
    · simp only [a, dif_pos h]
    · simp only [a, dif_pos h, c]
      have hk := Classical.choose_spec h
      have := corner_A D T.P hreg idx hidxA (Classical.choose h) (by rw [← hk]; exact hvert X)
      rw [← hk] at this
      rw [this]
  have hsum1 : m0 / Real.pi + m1 / Real.pi + m2 / Real.pi = 1 := by
    have : m0 + m1 + m2 = Real.pi := Erdos634.Draft.LaczFormal.angleAt_sum D.model
    field_simp; linarith
  have hx : 0 < m0 / Real.pi := div_pos (model_angle_pos' D 0) hpi
  have hy : 0 < m1 / Real.pi := div_pos (model_angle_pos' D 1) hpi
  have hz : 0 < m2 / Real.pi := div_pos (model_angle_pos' D 2) hpi
  have hG : Erdos634.Draft.LaczFormal32.Good C a (m0 / Real.pi) (m1 / Real.pi) (m2 / Real.pi) Pn Qn Rn c := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro X
      have hA : Asum D idx X.1 = (cnt D idx X.1 0 : ℝ) * m0 + cnt D idx X.1 1 * m1 + cnt D idx X.1 2 * m2 := by
        unfold Asum; rw [Fin.sum_univ_three]
      show (cnt D idx X.1 0 : ℝ) * (m0 / Real.pi) + (cnt D idx X.1 1 : ℝ) * (m1 / Real.pi) + (cnt D idx X.1 2 : ℝ) * (m2 / Real.pi)
        = Asum D idx X.1 / Real.pi
      rw [hA]; ring
    · intro X hX
      obtain ⟨k, -, -, hc⟩ := haX X hX
      exact Or.inl hc
    · intro X hX
      have hX2 : ¬ ∃ k : Fin M, X.1 = T.P.v (k + 1) := by simpa [C] using hX
      show Asum D idx X.1 / Real.pi = 0 ∨ Asum D idx X.1 / Real.pi = 1 ∨ Asum D idx X.1 / Real.pi = 2
      rcases vertex_A D T.P hreg idx hidxA (hvert X) with ⟨-, h | h⟩ | ⟨-, h | ⟨k, hk, -⟩⟩
      · right; right; rw [h]; field_simp
      · right; left; rw [h]; field_simp
      · right; left; rw [h]; field_simp
      · exact absurd ⟨k, hk⟩ hX2
    · show ∑ X : V, cnt D idx X.1 0 = ∑ X : V, cnt D idx X.1 1
      rw [Finset.sum_coe_sort V (fun v => cnt D idx v 0), Finset.sum_coe_sort V (fun v => cnt D idx v 1),
        sum_cnt_vtx D idx 0, sum_cnt_vtx D idx 1]
    · show ∑ X : V, cnt D idx X.1 1 = ∑ X : V, cnt D idx X.1 2
      rw [Finset.sum_coe_sort V (fun v => cnt D idx v 1), Finset.sum_coe_sort V (fun v => cnt D idx v 2),
        sum_cnt_vtx D idx 1, sum_cnt_vtx D idx 2]
    · obtain ⟨X, hX⟩ := hirr.1
      rw [← cnt_eq_cntR', ← cnt_eq_cntR'] at hX
      exact ⟨⟨X, mem_vtx_of_cnt_ne D idx hX⟩, hX⟩
    · obtain ⟨X, hX⟩ := hirr.2.1
      rw [← cnt_eq_cntR', ← cnt_eq_cntR'] at hX
      exact ⟨⟨X, mem_vtx_of_cnt_ne D idx hX⟩, hX⟩
    · obtain ⟨X, hX⟩ := hirr.2.2
      rw [← cnt_eq_cntR', ← cnt_eq_cntR'] at hX
      exact ⟨⟨X, mem_vtx_of_cnt_ne D idx hX⟩, hX⟩
  have haC : ∀ X ∈ C, 0 < a X ∧ a X < 2 ∧ a X ≠ 1 := by
    intro X hX
    obtain ⟨k, -, ha, -⟩ := haX X hX
    have hb := polyAngle_bounds T.P (k + 1)
    rw [ha]
    have h1 : T.P.angle (k + 1) / Real.pi < 1 := (div_lt_one hpi).mpr hb.2
    exact ⟨div_pos hb.1 hpi, by linarith, h1.ne⟩
  have hCne : C.Nonempty := by
    obtain ⟨i, k, hik⟩ := poly_vertex_is_tile_vertex D.toRegionDissection T.P hreg (0 + 1)
    exact ⟨⟨T.P.v (0 + 1), mem_vtxSet.mpr ⟨i, k, hik⟩⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, 0, rfl⟩⟩
  have hsumA : ∑ X ∈ C, a X < C.card := by
    have : ∑ X ∈ C, a X < ∑ X ∈ C, (1 : ℝ) := by
      refine Finset.sum_lt_sum_of_nonempty hCne (fun X hX => ?_)
      obtain ⟨k, -, ha, -⟩ := haX X hX
      have hb := polyAngle_bounds T.P (k + 1)
      rw [ha]; exact (div_lt_one hpi).mpr hb.2
    simpa using this
  obtain ⟨hxm, hym, hzm⟩ := Erdos634.Draft.LaczFormal32.lemma32_arith hx hy hz hsum1 haC hsumA hG
  -- multiply by pi
  have hmul : ∀ y ∈ Submodule.span ℚ (insert (1:ℝ) (a '' (C : Set V))), Real.pi * y ∈ Submodule.span ℚ (Set.range T.P.angle) := by
    intro y hy
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hy
    · intro w hw
      rcases hw with rfl | ⟨X, hX, rfl⟩
      · simpa using pi_mem_span T.P
      · obtain ⟨k, -, ha, -⟩ := haX X hX
        rw [ha]
        have : Real.pi * (T.P.angle (k + 1) / Real.pi) = T.P.angle (k + 1) := by field_simp
        rw [this]; exact Submodule.subset_span ⟨k + 1, rfl⟩
    · simp
    · intro u w _ _ hu hw; rw [mul_add]; exact Submodule.add_mem _ hu hw
    · intro r u _ hu
      have : Real.pi * (r • u) = r • (Real.pi * u) := by rw [Rat.smul_def, Rat.smul_def]; ring
      rw [this]; exact Submodule.smul_mem _ _ hu
  intro l
  fin_cases l
  · have := hmul _ hxm
    rw [mul_div_cancel₀ _ hpi.ne'] at this
    exact this
  · have := hmul _ hym
    rwa [mul_div_cancel₀ _ hpi.ne'] at this
  · have := hmul _ hzm
    rwa [mul_div_cancel₀ _ hpi.ne'] at this

#print axioms lemma32_tiling

end Erdos634.Draft.LaczFormal.RG
