-- Draft/LaczFormalIVcRatBr7a.lean -- Laczkovich DCG 48 (2012), Sect. 8.3 (Subcase IVc, rational branch): BRIDGE item (3).
--   `polygon_not_parallelogram`: a strictly convex polygon (`ConvPoly M`) with M >= 5 vertices is not a parallelogram `{0 <= fa <= k, 0 <= fb <= m}` (k, m >= 1) of a `Frame`.
--   Route: each vertex is an extreme point (`vertex_extreme`: the lines of the two edges at v_j meet only at v_j); an extreme point of the box has fa in {0, k}, fb in {0, m};
--   `P.v` is injective and `(fa, fb)` determines the point, so M <= 4.  This is the contradiction of `vw_star` with M >= 5.
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 8.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIVcRatB7d
import Erdos634.Draft.LaczFormalThm21Loc

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.Draft.LaczFormal.Thm21 Erdos634.CertCoord

namespace Erdos634.Draft.LaczFormal.RG

variable {M : ℕ} [NeZero M]

theorem vertex_mem_carrier (P : ConvPoly M) (j : Fin M) : P.v j ∈ P.carrier := by
  intro i
  show 0 ≤ P.c i (P.v j)
  by_cases h1 : j = i
  · subst h1; exact (P.c_self j).ge
  · by_cases h2 : j = i + 1
    · subst h2; exact (P.c_next i).ge
    · exact (P.c_vertex_pos h1 h2).le

theorem two_lines_unique {a0 a1 b0 b1 u0 u1 : ℝ} (hD : 0 < a0 * b1 - a1 * b0) (ha : a0 * u1 - a1 * u0 = 0) (hb : b0 * u1 - b1 * u0 = 0) :
    u0 = 0 ∧ u1 = 0 := by
  have h1 : (a0 * b1 - a1 * b0) * u1 = 0 := by linear_combination b1 * ha - a1 * hb
  have h2 : (a0 * b1 - a1 * b0) * u0 = 0 := by linear_combination b0 * ha - a0 * hb
  exact ⟨(mul_eq_zero.1 h2).resolve_left hD.ne', (mul_eq_zero.1 h1).resolve_left hD.ne'⟩

/-- A vertex of the polygon is an extreme point of it. -/
theorem vertex_extreme (P : ConvPoly M) (j : Fin M) {x y : Plane} (hx : x ∈ P.carrier) (hy : y ∈ P.carrier)
    (h : (1 - 1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y = P.v j) : x = P.v j := by
  have hM := P.three_le
  have hcx := (P.mem_carrier_iff x).1 hx
  have hcy := (P.mem_carrier_iff y).1 hy
  have hj1 : j - 1 + 1 = j := (ConvPoly.fin_facts hM j).2.2.2.2.1
  have hj2 : j - 1 + 2 = j + 1 := by rw [← fin_one_add_one (M := M), ← add_assoc, hj1]
  have e1 : P.c j (P.v j) = (1 - 1 / 2) * P.c j x + (1 / 2) * P.c j y := by
    have := P.c_comb j x y (1 / 2); rw [h] at this; exact this
  have z1 : P.c j x = 0 := by have := hcx j; have := hcy j; have h0 := P.c_self j; linarith
  have e2 : P.c (j - 1) (P.v j) = (1 - 1 / 2) * P.c (j - 1) x + (1 / 2) * P.c (j - 1) y := by
    have := P.c_comb (j - 1) x y (1 / 2); rw [h] at this; exact this
  have z2 : P.c (j - 1) x = 0 := by have := hcx (j - 1); have := hcy (j - 1); have h0 := P.c_prev_next hM j; linarith
  have z3 : P.c (j - 1) (P.v j) = 0 := P.c_prev_next hM j
  have hori := P.ori_pos hM (j - 1)
  rw [hj1, hj2] at hori
  have hEp : P.e (j - 1) = P.v j - P.v (j - 1) := by unfold ConvPoly.e; rw [hj1]
  have hEj : P.e j = P.v (j + 1) - P.v j := rfl
  unfold ConvPoly.c cross2 at z1 z2 z3
  rw [hEp] at z2 z3
  rw [hEj] at z1
  unfold cross2 at hori
  simp only [PiLp.sub_apply] at z1 z2 z3 hori
  have hD : 0 < (P.v j 0 - P.v (j - 1) 0) * (P.v (j + 1) 1 - P.v j 1) - (P.v j 1 - P.v (j - 1) 1) * (P.v (j + 1) 0 - P.v j 0) := by
    nlinarith [hori]
  obtain ⟨u0, u1⟩ := two_lines_unique (a0 := P.v j 0 - P.v (j - 1) 0) (a1 := P.v j 1 - P.v (j - 1) 1) (b0 := P.v (j + 1) 0 - P.v j 0)
    (b1 := P.v (j + 1) 1 - P.v j 1) (u0 := x 0 - P.v j 0) (u1 := x 1 - P.v j 1) hD (by linarith) (by linarith)
  exact plane_ext' (by linarith) (by linarith)

theorem vertex_inj (P : ConvPoly M) : Function.Injective P.v := by
  intro i j hij
  by_contra hne
  by_cases h : j = i + 1
  · subst h
    apply P.e_ne_zero P.three_le i
    unfold ConvPoly.e
    rw [hij]; simp
  · have h1 := P.c_vertex_pos (j := i) (m := j) (fun e => hne e.symm) h
    rw [← hij, P.c_self] at h1
    exact lt_irrefl _ h1

/-- **A polygon with at least five vertices is not a parallelogram.** -/
theorem polygon_not_parallelogram (P : ConvPoly M) (hM5 : 5 ≤ M) {b : ℝ} (hb : 0 < b) (F : Frame b) {k m : ℕ} (hk : 1 ≤ k) (hm : 1 ≤ m)
    (hA : P.carrier = {y | 0 ≤ F.fa y ∧ F.fa y ≤ (k : ℝ) ∧ 0 ≤ F.fb y ∧ F.fb y ≤ (m : ℝ)}) : False := by
  have key : ∀ j, (F.fa (P.v j) = 0 ∨ F.fa (P.v j) = k) ∧ (F.fb (P.v j) = 0 ∨ F.fb (P.v j) = m) := by
    intro j
    have hv : P.v j ∈ {y : Plane | 0 ≤ F.fa y ∧ F.fa y ≤ (k : ℝ) ∧ 0 ≤ F.fb y ∧ F.fb y ≤ (m : ℝ)} := hA ▸ vertex_mem_carrier P j
    obtain ⟨h1, h2, h3, h4⟩ := hv
    have hrec : P.v j = F.pt (F.fa (P.v j)) (F.fb (P.v j)) := F.recon hb _
    set a := F.fa (P.v j) with ha
    set β := F.fb (P.v j) with hβ
    constructor
    · by_contra hcon
      push_neg at hcon
      obtain ⟨hn0, hnk⟩ := hcon
      have ha0 : 0 < a := lt_of_le_of_ne h1 (Ne.symm hn0)
      have hak : a < k := lt_of_le_of_ne h2 hnk
      set δ : ℝ := min a (k - a) with hδ
      have hδ0 : 0 < δ := lt_min ha0 (by linarith)
      have hδa : δ ≤ a := min_le_left _ _
      have hδk : δ ≤ k - a := min_le_right _ _
      have hx : F.pt (a + δ) β ∈ P.carrier := by
        rw [hA]; simp only [Set.mem_setOf_eq, F.fa_pt hb, F.fb_pt hb]; refine ⟨by linarith, by linarith, h3, h4⟩
      have hy : F.pt (a - δ) β ∈ P.carrier := by
        rw [hA]; simp only [Set.mem_setOf_eq, F.fa_pt hb, F.fb_pt hb]; refine ⟨by linarith, by linarith, h3, h4⟩
      have hmid : (1 - 1 / 2 : ℝ) • F.pt (a + δ) β + (1 / 2 : ℝ) • F.pt (a - δ) β = P.v j := by
        rw [hrec]
        apply plane_ext'
        · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, F.pt_zero]; ring
        · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, F.pt_one]; ring
      have := vertex_extreme P j hx hy hmid
      have h5 := congrArg F.fa this
      rw [F.fa_pt hb] at h5
      linarith
    · by_contra hcon
      push_neg at hcon
      obtain ⟨hn0, hnk⟩ := hcon
      have ha0 : 0 < β := lt_of_le_of_ne h3 (Ne.symm hn0)
      have hak : β < m := lt_of_le_of_ne h4 hnk
      set δ : ℝ := min β (m - β) with hδ
      have hδ0 : 0 < δ := lt_min ha0 (by linarith)
      have hδa : δ ≤ β := min_le_left _ _
      have hδk : δ ≤ m - β := min_le_right _ _
      have hx : F.pt a (β + δ) ∈ P.carrier := by
        rw [hA]; simp only [Set.mem_setOf_eq, F.fa_pt hb, F.fb_pt hb]; refine ⟨h1, h2, by linarith, by linarith⟩
      have hy : F.pt a (β - δ) ∈ P.carrier := by
        rw [hA]; simp only [Set.mem_setOf_eq, F.fa_pt hb, F.fb_pt hb]; refine ⟨h1, h2, by linarith, by linarith⟩
      have hmid : (1 - 1 / 2 : ℝ) • F.pt a (β + δ) + (1 / 2 : ℝ) • F.pt a (β - δ) = P.v j := by
        rw [hrec]
        apply plane_ext'
        · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, F.pt_zero]; ring
        · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, F.pt_one]; ring
      have := vertex_extreme P j hx hy hmid
      have h5 := congrArg F.fb this
      rw [F.fb_pt hb] at h5
      linarith
  have hk' : (k : ℝ) ≠ 0 := by positivity
  have hm' : (m : ℝ) ≠ 0 := by positivity
  have hinj : Function.Injective (fun j : Fin M => (decide (F.fa (P.v j) = k), decide (F.fb (P.v j) = m))) := by
    intro i j hij
    simp only [Prod.mk.injEq, decide_eq_decide] at hij
    obtain ⟨h1, h2⟩ := hij
    have ea : F.fa (P.v i) = F.fa (P.v j) := by
      rcases (key i).1 with a | a <;> rcases (key j).1 with b | b
      · rw [a, b]
      · exfalso; have := h1.2 b; rw [a] at this; exact hk' this.symm
      · exfalso; have := h1.1 a; rw [b] at this; exact hk' this.symm
      · rw [a, b]
    have eb : F.fb (P.v i) = F.fb (P.v j) := by
      rcases (key i).2 with a | a <;> rcases (key j).2 with b | b
      · rw [a, b]
      · exfalso; have := h2.2 b; rw [a] at this; exact hm' this.symm
      · exfalso; have := h2.1 a; rw [b] at this; exact hm' this.symm
      · rw [a, b]
    apply vertex_inj P
    rw [F.recon hb (P.v i), F.recon hb (P.v j), ea, eb]
  have := Fintype.card_le_of_injective _ hinj
  simp at this
  omega

#print axioms Erdos634.Draft.LaczFormal.RG.polygon_not_parallelogram

end Erdos634.Draft.LaczFormal.RG
