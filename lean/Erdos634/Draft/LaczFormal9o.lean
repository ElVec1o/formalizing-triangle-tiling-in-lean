import Erdos634.Draft.LaczFormal9n

/-!
# Laczkovich DM 140 (1995), Theorem 2.3: the chart geometry of Fig. 3 (cover and disjointness)

NOTE, UNAUDITED.  Credit: Laczkovich (Discrete Math. 140 (1995) 79-94, Theorem 2.3, Fig. 3), Beeson, Beeson-Zhang, Zhang.  Formalization debt,
not /goal progress.

Fig. 3 read from the printed page (the figure was rendered and inspected).  The tile `ABC` has angles `α, β = 2α, γ = π - 3α` at `A, B, C`;
`BCD, BDE, DEF` have angles `(C, B, D) = (α, β, γ)`, `(D, B, E) = (α, γ, β)`, `(D, E, F) = (β, γ, α)`;
`GFC` is isosceles with base angles `α` at `G, F` and apex `C`; `A` lies on `GC` with `AB ∥ GF`; `D` on `CF`, `E` on `GF`;
`GEBA` is the isosceles trapezoid (angles `α` at `G, E`, `β + γ` at `A, B`).  With `c = 4 cos² α - 1 > 0` (tile sides `a : b : c = 1 : 2 cos α : c`)
and the chart `(G; w = GE, d = GA)` (so `E = (1,0)`, `A = (0,1)`), with `n = c² + 1`, `h = c² + c + 1`:
`B = (c²/n, 1)`, `C = (0, h)`, `F = (h/n, 0)`, `D = ((c+1)/n, c²)`; the target is `GFC = {x, y ≥ 0, n x + y ≤ h}`.
The cover is proved by the hull calculus of `LaczFormal9n` (fan from `B`, then cevian cuts at `A`, `D`, `E`, and at `Q = BF ∩ DE`).
All statements hold for every real `c > 0`.
-/

open scoped Classical
open Erdos634.Geometry Erdos634.CertCoord Erdos634.LaczL22 Erdos634.LaczL24 Erdos634.Laczkovich9n

namespace Erdos634.Laczkovich9o

noncomputable def wn (c : ℝ) : ℝ := c ^ 2 + 1
noncomputable def wh (c : ℝ) : ℝ := c ^ 2 + c + 1
noncomputable def wt (c : ℝ) : ℝ := c ^ 2 / (c ^ 2 + 1)
noncomputable def wf (c : ℝ) : ℝ := (c ^ 2 + c + 1) / (c ^ 2 + 1)
noncomputable def wp (c : ℝ) : ℝ := (c + 1) / (c ^ 2 + 1)
noncomputable def wq (c : ℝ) : ℝ := c ^ 2
noncomputable def wQx (c : ℝ) : ℝ := (c ^ 2 * (c ^ 2 + 1) + c + 1) / (c ^ 2 + 1) ^ 2
noncomputable def wQy (c : ℝ) : ℝ := c ^ 2 / (c ^ 2 + 1)

noncomputable def pG : Plane := mkPt 0 0
noncomputable def pE : Plane := mkPt 1 0
noncomputable def pA : Plane := mkPt 0 1
noncomputable def pB (c : ℝ) : Plane := mkPt (wt c) 1
noncomputable def pC (c : ℝ) : Plane := mkPt 0 (wh c)
noncomputable def pF (c : ℝ) : Plane := mkPt (wf c) 0
noncomputable def pD (c : ℝ) : Plane := mkPt (wp c) (wq c)
noncomputable def pQ (c : ℝ) : Plane := mkPt (wQx c) (wQy c)

theorem mk_smul (a x y : ℝ) : a • mkPt x y = mkPt (a * x) (a * y) := by
  ext i; fin_cases i <;> simp

theorem mk_add (a b x y : ℝ) : mkPt a b + mkPt x y = mkPt (a + x) (b + y) := by
  ext i; fin_cases i <;> simp

theorem mk_eq {x y x' y' : ℝ} (hx : x = x') (hy : y = y') : mkPt x y = mkPt x' y' := by rw [hx, hy]

theorem comb3 (s t u a b c' d e f : ℝ) :
    s • mkPt a b + t • mkPt c' d + u • mkPt e f = mkPt (s * a + t * c' + u * e) (s * b + t * d + u * f) := by
  rw [mk_smul, mk_smul, mk_smul, mk_add, mk_add]

theorem comb2 (s t a b c' d : ℝ) :
    s • mkPt a b + t • mkPt c' d = mkPt (s * a + t * c') (s * b + t * d) := by
  rw [mk_smul, mk_smul, mk_add]

section pos
variable {c : ℝ} (hc : 0 < c)
include hc

theorem n_pos : 0 < c ^ 2 + 1 := by positivity
theorem h_pos : 0 < c ^ 2 + c + 1 := by positivity
theorem wt_pos : 0 < wt c := by unfold wt; positivity
theorem wt_lt : wt c < 1 := by
  unfold wt; rw [div_lt_one (n_pos hc)]; linarith
theorem wf_gt : 1 < wf c := by
  unfold wf; rw [one_lt_div (n_pos hc)]; linarith
theorem wh_gt : 1 < wh c := by unfold wh; nlinarith [sq_nonneg c]
theorem wp_pos : 0 < wp c := by unfold wp; positivity
theorem wq_pos : 0 < wq c := by unfold wq; positivity

theorem det_T : det3 0 0 (wf c) 0 0 (wh c) = (c ^ 2 + c + 1) ^ 2 / (c ^ 2 + 1) := by
  have := (n_pos hc).ne'
  simp only [det3, wf, wh]; field_simp; ring

theorem det_ABC : det3 0 1 (wt c) 1 0 (wh c) = c ^ 3 * (c + 1) / (c ^ 2 + 1) := by
  have := (n_pos hc).ne'
  simp only [det3, wt, wh]; field_simp; ring

theorem det_BCD : det3 (wt c) 1 0 (wh c) (wp c) (wq c) = -(c * (c + 1) / (c ^ 2 + 1)) := by
  have := (n_pos hc).ne'
  simp only [det3, wt, wh, wp, wq]; field_simp; ring

theorem det_BDE : det3 (wt c) 1 (wp c) (wq c) 1 0 = -(c / (c ^ 2 + 1)) := by
  have := (n_pos hc).ne'
  simp only [det3, wt, wp, wq]; field_simp; ring

theorem det_DEF : det3 (wp c) (wq c) 1 0 (wf c) 0 = c ^ 3 / (c ^ 2 + 1) := by
  have := (n_pos hc).ne'
  simp only [det3, wp, wq, wf]; field_simp; ring

theorem det_T_ne : det3 0 0 (wf c) 0 0 (wh c) ≠ 0 := by rw [det_T hc]; have := n_pos hc; positivity
theorem det_ABC_ne : det3 0 1 (wt c) 1 0 (wh c) ≠ 0 := by rw [det_ABC hc]; positivity
theorem det_BCD_ne : det3 (wt c) 1 0 (wh c) (wp c) (wq c) ≠ 0 := by
  rw [det_BCD hc]; have : 0 < c * (c + 1) / (c ^ 2 + 1) := by positivity
  linarith
theorem det_BDE_ne : det3 (wt c) 1 (wp c) (wq c) 1 0 ≠ 0 := by
  rw [det_BDE hc]; have : 0 < c / (c ^ 2 + 1) := by positivity
  linarith
theorem det_DEF_ne : det3 (wp c) (wq c) 1 0 (wf c) 0 ≠ 0 := by rw [det_DEF hc]; positivity

end pos

noncomputable def triT (c : ℝ) (hc : 0 < c) : Tri := mkTri 0 0 (wf c) 0 0 (wh c) (det_T_ne hc)
noncomputable def triABC (c : ℝ) (hc : 0 < c) : Tri := mkTri 0 1 (wt c) 1 0 (wh c) (det_ABC_ne hc)
noncomputable def triBCD (c : ℝ) (hc : 0 < c) : Tri := mkTri (wt c) 1 0 (wh c) (wp c) (wq c) (det_BCD_ne hc)
noncomputable def triBDE (c : ℝ) (hc : 0 < c) : Tri := mkTri (wt c) 1 (wp c) (wq c) 1 0 (det_BDE_ne hc)
noncomputable def triDEF (c : ℝ) (hc : 0 < c) : Tri := mkTri (wp c) (wq c) 1 0 (wf c) 0 (det_DEF_ne hc)

/-! ## The target as a half-plane set -/

def inTgt (c : ℝ) (z : Plane) : Prop := 0 ≤ z 0 ∧ 0 ≤ z 1 ∧ (c ^ 2 + 1) * z 0 + z 1 ≤ c ^ 2 + c + 1

theorem convex_inTgt (c : ℝ) : Convex ℝ {z : Plane | inTgt c z} := by
  intro x hx y hy p q hp hq hpq
  obtain ⟨hx1, hx2, hx3⟩ := hx
  obtain ⟨hy1, hy2, hy3⟩ := hy
  simp only [inTgt, Set.mem_setOf_eq, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  obtain rfl : q = 1 - p := by linarith
  refine ⟨?_, ?_, ?_⟩
  · nlinarith [mul_nonneg hp hx1, mul_nonneg hq hy1]
  · nlinarith [mul_nonneg hp hx2, mul_nonneg hq hy2]
  · nlinarith [mul_nonneg hp (sub_nonneg.2 hx3), mul_nonneg hq (sub_nonneg.2 hy3)]

private theorem htri3 : ∀ k : Fin 3, k = 0 ∨ k = 1 ∨ k = 2 := by decide

section tgt
variable {c : ℝ} (hc : 0 < c)
include hc

theorem triT_carrier : (triT c hc).carrier = {z : Plane | inTgt c z} := by
  have hn := n_pos hc
  have hf := wf_gt hc
  have hh := h_pos hc
  apply Set.Subset.antisymm
  · refine convexHull_min (Set.range_subset_iff.mpr ?_) (convex_inTgt c)
    intro k
    rcases htri3 k with rfl | rfl | rfl
    · show inTgt c (mkPt 0 0); simp [inTgt]; linarith
    · show inTgt c (mkPt (wf c) 0); simp [inTgt]
      refine ⟨by linarith, ?_⟩
      unfold wf; field_simp; linarith
    · show inTgt c (mkPt 0 (wh c))
      simp only [inTgt, mkPt_zero, mkPt_one]
      refine ⟨le_refl _, ?_, ?_⟩ <;> unfold wh <;> nlinarith [sq_nonneg c]
  · intro z hz
    obtain ⟨hs, ht, hh'⟩ := hz
    have hfpos : 0 < wf c := by linarith
    have hwf : wf c * (c ^ 2 + 1) = c ^ 2 + c + 1 := by unfold wf; field_simp
    have h1 : z 0 / wf c + z 1 / (c ^ 2 + c + 1) ≤ 1 := by
      have : z 0 / wf c = (c ^ 2 + 1) * z 0 / (c ^ 2 + c + 1) := by
        rw [div_eq_div_iff hfpos.ne' hh.ne']; nlinarith
      rw [this, ← add_div, div_le_one hh]; linarith
    have hmem : mkPt (z 0) (z 1) ∈ H (pG) (pF c) (pC c) := by
      have := H_mk (P := pG) (Q := pF c) (R := pC c) (1 - z 0 / wf c - z 1 / (c ^ 2 + c + 1)) (z 0 / wf c)
        (z 1 / (c ^ 2 + c + 1)) (by linarith) (by positivity) (by positivity) (by ring)
      convert this using 1
      unfold pG pF pC
      rw [comb3]
      refine mk_eq ?_ ?_
      · unfold wf; field_simp; ring
      · unfold wh; field_simp; ring
    rw [← mkPt_self z]
    exact H_sub_tri (triT c hc) hmem

end tgt

/-! ## Cover -/

section cover
variable {c : ℝ} (hc : 0 < c)
include hc

theorem pB_eq : pB c = (c / (c ^ 2 + c + 1)) • pG + (c ^ 2 / (c ^ 2 + c + 1)) • pF c + (1 / (c ^ 2 + c + 1)) • pC c := by
  have := h_pos hc; have := n_pos hc
  unfold pB pG pF pC wt wf wh
  rw [comb3]
  refine mk_eq ?_ ?_ <;> field_simp <;> ring

theorem pA_eq : pA = (1 / (c ^ 2 + c + 1)) • pC c + (c * (c + 1) / (c ^ 2 + c + 1)) • pG := by
  have := h_pos hc
  unfold pA pG pC wh
  rw [comb2]
  refine mk_eq ?_ ?_ <;> field_simp <;> ring

theorem pD_eq : pD c = ((c + 1) / (c ^ 2 + c + 1)) • pF c + (c ^ 2 / (c ^ 2 + c + 1)) • pC c := by
  have := h_pos hc; have := n_pos hc
  unfold pD pF pC wp wq wf wh
  rw [comb2]
  refine mk_eq ?_ ?_ <;> field_simp <;> ring

theorem pE_eq : pE = (c / (c ^ 2 + c + 1)) • pG + ((c ^ 2 + 1) / (c ^ 2 + c + 1)) • pF c := by
  have := h_pos hc; have := n_pos hc
  unfold pE pG pF wf
  rw [comb2]
  refine mk_eq ?_ ?_ <;> field_simp <;> ring

theorem pQ_BF : pQ c = (c ^ 2 / (c ^ 2 + 1)) • pB c + (1 / (c ^ 2 + 1)) • pF c := by
  have := n_pos hc
  unfold pQ pB pF wQx wQy wt wf
  rw [comb2]
  refine mk_eq ?_ ?_ <;> field_simp <;> ring

theorem pQ_DE : pQ c = (1 / (c ^ 2 + 1)) • pD c + (c ^ 2 / (c ^ 2 + 1)) • pE := by
  have := n_pos hc
  unfold pQ pD pE wQx wQy wp wq
  rw [comb2]
  refine mk_eq ?_ ?_ <;> field_simp <;> ring

/-- The trapezoid `GEBA` of Fig. 3 (as `trapSet τ`, in the chart `(G; GE, GA)`). -/
theorem trap_vertices : pG ∈ trapSet (wt c) ∧ pE ∈ trapSet (wt c) ∧ pA ∈ trapSet (wt c) ∧ pB c ∈ trapSet (wt c) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [trapSet, pG, pE, pA, pB] <;> nlinarith [wt_pos hc, wt_lt hc]

theorem Q_P3 : pQ c ∈ (triBDE c hc).carrier := by
  rw [pQ_DE hc]
  exact (triBDE c hc).convex (vm (triBDE c hc) 1 : pD c ∈ _) (vm (triBDE c hc) 2 : pE ∈ _)
    (by have := n_pos hc; positivity) (by have := n_pos hc; positivity)
    (by have := n_pos hc; field_simp; ring)

theorem Q_P4 : pQ c ∈ (triDEF c hc).carrier := by
  rw [pQ_DE hc]
  exact (triDEF c hc).convex (vm (triDEF c hc) 0 : pD c ∈ _) (vm (triDEF c hc) 1 : pE ∈ _)
    (by have := n_pos hc; positivity) (by have := n_pos hc; positivity)
    (by have := n_pos hc; field_simp; ring)

theorem cover : (triT c hc).carrier ⊆
    (((trapSet (wt c) ∪ (triABC c hc).carrier) ∪ (triBCD c hc).carrier) ∪ (triBDE c hc).carrier) ∪
      (triDEF c hc).carrier := by
  have hh := h_pos hc
  have hn := n_pos hc
  obtain ⟨tG, tE, tA, tB⟩ := trap_vertices hc
  have P1B : pB c ∈ (triABC c hc).carrier := vm (triABC c hc) 1
  have P1C : pC c ∈ (triABC c hc).carrier := vm (triABC c hc) 2
  have P1A : pA ∈ (triABC c hc).carrier := vm (triABC c hc) 0
  have P2B : pB c ∈ (triBCD c hc).carrier := vm (triBCD c hc) 0
  have P2C : pC c ∈ (triBCD c hc).carrier := vm (triBCD c hc) 1
  have P2D : pD c ∈ (triBCD c hc).carrier := vm (triBCD c hc) 2
  have P3B : pB c ∈ (triBDE c hc).carrier := vm (triBDE c hc) 0
  have P3D : pD c ∈ (triBDE c hc).carrier := vm (triBDE c hc) 1
  have P3E : pE ∈ (triBDE c hc).carrier := vm (triBDE c hc) 2
  have P4D : pD c ∈ (triDEF c hc).carrier := vm (triDEF c hc) 0
  have P4E : pE ∈ (triDEF c hc).carrier := vm (triDEF c hc) 1
  have P4F : pF c ∈ (triDEF c hc).carrier := vm (triDEF c hc) 2
  have P3Q := Q_P3 hc
  have P4Q := Q_P4 hc
  intro z hz
  have h0 : z ∈ H pG (pF c) (pC c) := tri_sub_H (triT c hc) hz
  have hfan := H_fan (X := pG) (Y := pF c) (Z := pC c) (B := pB c) (l := c / (c ^ 2 + c + 1))
    (m := c ^ 2 / (c ^ 2 + c + 1)) (n := 1 / (c ^ 2 + c + 1)) (by positivity) (by positivity) (by positivity)
    (by field_simp; ring) (pB_eq hc) h0
  have inP1 : H (pB c) (pC c) pA ⊆ (triABC c hc).carrier := H_sub_convex (triABC c hc).convex P1B P1C P1A
  have inTr1 : H (pB c) pA pG ⊆ trapSet (wt c) := H_sub_convex (convex_trapSet _) tB tA tG
  have inTr2 : H (pB c) pG pE ⊆ trapSet (wt c) := H_sub_convex (convex_trapSet _) tB tG tE
  have inP2 : H (pB c) (pD c) (pC c) ⊆ (triBCD c hc).carrier := H_sub_convex (triBCD c hc).convex P2B P2D P2C
  have inP3a : H (pD c) (pB c) (pQ c) ⊆ (triBDE c hc).carrier := H_sub_convex (triBDE c hc).convex P3D P3B P3Q
  have inP4a : H (pD c) (pQ c) (pF c) ⊆ (triDEF c hc).carrier := H_sub_convex (triDEF c hc).convex P4D P4Q P4F
  have inP3b : H pE (pB c) (pQ c) ⊆ (triBDE c hc).carrier := H_sub_convex (triBDE c hc).convex P3E P3B P3Q
  have inP4b : H pE (pQ c) (pF c) ⊆ (triDEF c hc).carrier := H_sub_convex (triDEF c hc).convex P4E P4Q P4F
  have wQ1 : (0 : ℝ) < c ^ 2 / (c ^ 2 + 1) := by positivity
  have wQ2 : (0 : ℝ) < 1 / (c ^ 2 + 1) := by positivity
  have wQsum : c ^ 2 / (c ^ 2 + 1) + 1 / (c ^ 2 + 1) = 1 := by field_simp
  rcases hfan with (h | h) | h
  · -- cone `B G F`
    have e := H_cev (X := pB c) (Y := pG) (Z := pF c) (D := pE) (p := c / (c ^ 2 + c + 1))
      (q := (c ^ 2 + 1) / (c ^ 2 + c + 1)) (by positivity) (by positivity) (by field_simp; ring) (pE_eq hc) h
    rcases e with e | e
    · exact Or.inl (Or.inl (Or.inl (Or.inl (inTr2 e))))
    · have e' : z ∈ H pE (pB c) (pF c) := H_swap _ _ _ (H_rot _ _ _ e)
      rcases H_cev (X := pE) (Y := pB c) (Z := pF c) (D := pQ c) (p := c ^ 2 / (c ^ 2 + 1))
        (q := 1 / (c ^ 2 + 1)) wQ1 wQ2 wQsum (pQ_BF hc) e' with e2 | e2
      · exact Or.inl (Or.inr (inP3b e2))
      · exact Or.inr (inP4b e2)
  · -- cone `B F C`
    have e := H_cev (X := pB c) (Y := pF c) (Z := pC c) (D := pD c) (p := (c + 1) / (c ^ 2 + c + 1))
      (q := c ^ 2 / (c ^ 2 + c + 1)) (by positivity) (by positivity) (by field_simp; ring) (pD_eq hc) h
    rcases e with e | e
    · have e' : z ∈ H (pD c) (pB c) (pF c) := H_rot _ _ _ (H_rot _ _ _ e)
      rcases H_cev (X := pD c) (Y := pB c) (Z := pF c) (D := pQ c) (p := c ^ 2 / (c ^ 2 + 1))
        (q := 1 / (c ^ 2 + 1)) wQ1 wQ2 wQsum (pQ_BF hc) e' with e2 | e2
      · exact Or.inl (Or.inr (inP3a e2))
      · exact Or.inr (inP4a e2)
    · exact Or.inl (Or.inl (Or.inr (inP2 e)))
  · -- cone `B C G`
    have e := H_cev (X := pB c) (Y := pC c) (Z := pG) (D := pA) (p := 1 / (c ^ 2 + c + 1))
      (q := c * (c + 1) / (c ^ 2 + c + 1)) (by positivity) (by positivity) (by field_simp; ring) (pA_eq hc) h
    rcases e with e | e
    · exact Or.inl (Or.inl (Or.inl (Or.inr (inP1 e))))
    · exact Or.inl (Or.inl (Or.inl (Or.inl (inTr1 e))))

end cover

end Erdos634.Laczkovich9o

#print axioms Erdos634.Laczkovich9o.cover
#print axioms Erdos634.Laczkovich9o.triT_carrier
