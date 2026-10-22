-- Draft/LaczFormalThm21Loc.lean -- S1 of PLAN_THM21: LOCAL structure of a strictly convex polygon (half-plane form).
-- Every point of the polygon is interior (all edge constraints strict), or has a LOCAL TRIANGLE: a `Tri` equal to the polygon near it, with the point
-- a vertex of the triangle (polygon vertex) or an interior point of one of its sides (polygon edge).  Used to build the fan with virtual sectors at
-- boundary vertices of a dissection of the polygon (S2).
-- UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 4: the angular domains at a vertex of the tiling and of A), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalThm21Def
import Erdos634.CertGeom

open MeasureTheory Erdos634.Geometry

namespace Erdos634.Draft.LaczFormal.Thm21

theorem fin_val_two {M : ℕ} [NeZero M] : ((2 : Fin M) : ℕ) = 2 % M := rfl
theorem fin_val_one {M : ℕ} [NeZero M] : ((1 : Fin M) : ℕ) = 1 % M := rfl
theorem fin_val_zero {M : ℕ} [NeZero M] : ((0 : Fin M) : ℕ) = 0 := rfl

theorem fin_one_ne_zero' {M : ℕ} [NeZero M] (h : 2 ≤ M) : (1 : Fin M) ≠ 0 := by
  intro h1
  have := congrArg Fin.val h1
  rw [fin_val_one, fin_val_zero, Nat.mod_eq_of_lt (by omega : 1 < M)] at this
  omega

theorem fin_two_ne_zero' {M : ℕ} [NeZero M] (h : 3 ≤ M) : (2 : Fin M) ≠ 0 := by
  intro h1
  have := congrArg Fin.val h1
  rw [fin_val_two, fin_val_zero, Nat.mod_eq_of_lt (by omega : 2 < M)] at this
  omega

theorem fin_two_ne_one' {M : ℕ} [NeZero M] (h : 3 ≤ M) : (2 : Fin M) ≠ 1 := by
  intro h1
  have := congrArg Fin.val h1
  rw [fin_val_two, fin_val_one, Nat.mod_eq_of_lt (by omega : 1 < M), Nat.mod_eq_of_lt (by omega : 2 < M)] at this
  omega

theorem fin_one_add_one {M : ℕ} [NeZero M] : (1 + 1 : Fin M) = 2 := by
  rw [Fin.ext_iff, Fin.val_add, fin_val_one, fin_val_two]
  exact (Nat.add_mod 1 1 M).symm

namespace ConvPoly
variable {M : ℕ} [NeZero M] (P : ConvPoly M)

/-- Edge vector `v_{i+1} - v_i`. -/
def e (i : Fin M) : Plane := P.v (i + 1) - P.v i
/-- The `i`-th edge constraint function (nonnegative on the polygon). -/
def c (i : Fin M) (x : Plane) : ℝ := cross2 (P.e i) (x - P.v i)

theorem mem_carrier_iff (x : Plane) : x ∈ P.carrier ↔ ∀ j, 0 ≤ P.c j x := Iff.rfl

theorem c_vertex_pos {j m : Fin M} (h1 : m ≠ j) (h2 : m ≠ j + 1) : 0 < P.c j (P.v m) := P.left j m h1 h2

theorem c_self (j : Fin M) : P.c j (P.v j) = 0 := by simp [c, cross2]
theorem c_next (j : Fin M) : P.c j (P.v (j + 1)) = 0 := by
  simp [c, e, cross2]; ring

theorem c_comb (j : Fin M) (A B : Plane) (t : ℝ) : P.c j ((1 - t) • A + t • B) = (1 - t) * P.c j A + t * P.c j B := by
  unfold c cross2; simp; ring

theorem fin_facts (hM : 3 ≤ M) (i : Fin M) : i + 1 ≠ i ∧ i + 2 ≠ i ∧ i + 2 ≠ i + 1 ∧ i + 1 ≠ i - 1 ∧ i - 1 + 1 = i ∧ i + 1 + 1 = i + 2 := by
  have h1 : (1 : Fin M) ≠ 0 := fin_one_ne_zero' (by omega)
  have h2 : (2 : Fin M) ≠ 0 := fin_two_ne_zero' hM
  have h21 : (2 : Fin M) ≠ 1 := fin_two_ne_one' hM
  refine ⟨fun h => h1 (by simpa using h), fun h => h2 (by simpa using h), fun h => ?_, fun h => ?_, sub_add_cancel i 1, (add_assoc i 1 1).trans (by rw [fin_one_add_one])⟩
  · apply h21
    have : i + 2 = i + 1 := h
    exact add_left_cancel this
  · apply h2
    have : i + 1 = i - 1 := h
    have h3 : (i + 1) - (i - 1) = 1 + 1 := by abel
    rw [fin_one_add_one] at h3
    rw [← h3, this]; simp

end ConvPoly

/-! ## Triangles from three points of positive orientation, and their half-plane description -/

theorem affineIndependent_of_cross (a b c : Plane) (h : cross2 (b - a) (c - a) ≠ 0) : AffineIndependent ℝ ![a, b, c] := by
  rw [affineIndependent_iff_not_collinear_of_ne (show (0 : Fin 3) ≠ 1 by decide) (show (0 : Fin 3) ≠ 2 by decide)
    (show (1 : Fin 3) ≠ 2 by decide)]
  intro hc
  rw [collinear_iff_exists_forall_eq_smul_vadd] at hc
  obtain ⟨q, v, hv⟩ := hc
  obtain ⟨ra, ha⟩ := hv a (by simp)
  obtain ⟨rb, hb⟩ := hv b (by simp)
  obtain ⟨rc, hc⟩ := hv c (by simp)
  apply h
  have e1 : b - a = (rb - ra) • v := by rw [hb, ha]; simp [sub_smul]
  have e2 : c - a = (rc - ra) • v := by rw [hc, ha]; simp [sub_smul]
  rw [e1, e2, cross2_smul_left, cross2_smul_right, cross2_self]; ring

/-- The triangle with vertices `a, b, c` (positively oriented). -/
noncomputable def triOf (a b c : Plane) (h : 0 < cross2 (b - a) (c - a)) : Tri where
  pts := ![a, b, c]
  indep := affineIndependent_of_cross a b c h.ne'

theorem halfplane_convex (u w : Plane) : Convex ℝ {z : Plane | 0 ≤ cross2 u (z - w)} := by
  intro z1 hz1 z2 hz2 a b ha hb hab
  simp only [Set.mem_setOf_eq] at *
  have : cross2 u (a • z1 + b • z2 - w) = a * cross2 u (z1 - w) + b * cross2 u (z2 - w) := by
    have hb' : b = 1 - a := by linarith
    subst hb'
    unfold cross2; simp; ring
  rw [this]; positivity

theorem triOf_carrier (a b c : Plane) (h : 0 < cross2 (b - a) (c - a)) (y : Plane) :
    y ∈ (triOf a b c h).carrier ↔
      0 ≤ cross2 (b - a) (y - a) ∧ 0 ≤ cross2 (c - b) (y - b) ∧ 0 ≤ cross2 (a - c) (y - c) := by
  constructor
  · intro hy
    have hhull : (triOf a b c h).carrier ⊆ {z | 0 ≤ cross2 (b - a) (z - a)} ∩ {z | 0 ≤ cross2 (c - b) (z - b)} ∩ {z | 0 ≤ cross2 (a - c) (z - c)} := by
      apply convexHull_min
      · rintro _ ⟨k, rfl⟩
        fin_cases k
        · refine ⟨⟨?_, ?_⟩, ?_⟩ <;> simp [triOf, cross2] <;> unfold cross2 at h <;> simp at h <;> nlinarith
        · refine ⟨⟨?_, ?_⟩, ?_⟩ <;> simp [triOf, cross2] <;> unfold cross2 at h <;> simp at h <;> nlinarith
        · refine ⟨⟨?_, ?_⟩, ?_⟩ <;> simp [triOf, cross2] <;> unfold cross2 at h <;> simp at h <;> nlinarith
      · exact ((halfplane_convex _ _).inter (halfplane_convex _ _)).inter (halfplane_convex _ _)
    exact ⟨(hhull hy).1.1, (hhull hy).1.2, (hhull hy).2⟩
  · rintro ⟨k1, k2, k3⟩
    set Ori := cross2 (b - a) (c - a) with hOri
    refine Erdos634.CertGeom.mem_carrier_of_combo (triOf a b c h) y
      ![cross2 (c - b) (y - b) / Ori, cross2 (a - c) (y - c) / Ori, cross2 (b - a) (y - a) / Ori] ?_ ?_ ?_
    · show _ / Ori + _ / Ori + _ / Ori = 1
      rw [← add_div, ← add_div, div_eq_one_iff_eq h.ne']
      rw [hOri]; unfold cross2; simp; ring
    · intro k; fin_cases k
      · exact div_nonneg k2 h.le
      · exact div_nonneg k3 h.le
      · exact div_nonneg k1 h.le
    · show y = _ • a + _ • b + _ • c
      have hOne : Ori ≠ 0 := h.ne'
      ext j; fin_cases j
      · show y 0 = _ / Ori * a 0 + _ / Ori * b 0 + _ / Ori * c 0
        rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, ← add_div, eq_div_iff hOne, hOri]
        unfold cross2; simp; ring
      · show y 1 = _ / Ori * a 1 + _ / Ori * b 1 + _ / Ori * c 1
        rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, ← add_div, eq_div_iff hOne, hOri]
        unfold cross2; simp; ring


namespace ConvPoly
variable {M : ℕ} [NeZero M] (P : ConvPoly M)

theorem e_ne_zero (hM : 3 ≤ M) (i : Fin M) : P.e i ≠ 0 := by
  obtain ⟨-, h2, h3, -⟩ := fin_facts hM i
  intro h
  have := P.c_vertex_pos (j := i) (m := i + 2) h2 h3
  unfold c at this
  rw [h] at this
  simp [cross2] at this

theorem c_prev_next (hM : 3 ≤ M) (i : Fin M) : P.c (i - 1) (P.v i) = 0 := by
  have := P.c_next (i - 1)
  rwa [(fin_facts hM i).2.2.2.2.1] at this

/-- A point of the polygon on the line of edge `i` lies on the edge. -/
theorem edge_param (hM : 3 ≤ M) {i : Fin M} {V : Plane} (hV : V ∈ P.carrier) (h0 : P.c i V = 0) :
    ∃ t ∈ Set.Icc (0:ℝ) 1, V = (1 - t) • P.v i + t • P.v (i + 1) := by
  obtain ⟨hf1, hf2, hf3, hf4, hf5, hf6⟩ := fin_facts hM i
  have hE := P.e_ne_zero hM i
  have hn : P.e i 0 ^ 2 + P.e i 1 ^ 2 ≠ 0 := by
    intro h
    apply hE
    have h0' : P.e i 0 = 0 := by nlinarith [sq_nonneg (P.e i 0), sq_nonneg (P.e i 1)]
    have h1' : P.e i 1 = 0 := by nlinarith [sq_nonneg (P.e i 0), sq_nonneg (P.e i 1)]
    ext j; fin_cases j <;> simp [h0', h1']
  have hcr : P.e i 0 * (V - P.v i) 1 - P.e i 1 * (V - P.v i) 0 = 0 := h0
  set t := ((V - P.v i) 0 * P.e i 0 + (V - P.v i) 1 * P.e i 1) / (P.e i 0 ^ 2 + P.e i 1 ^ 2) with ht
  have hW : V = (1 - t) • P.v i + t • P.v (i + 1) := by
    have hv1 : P.v (i + 1) = P.v i + P.e i := by unfold e; abel
    rw [hv1]
    ext j; fin_cases j
    · show V 0 = (1 - t) * P.v i 0 + t * (P.v i 0 + P.e i 0)
      have : t * P.e i 0 = (V - P.v i) 0 := by
        rw [ht, div_mul_eq_mul_div, div_eq_iff hn]
        simp only [PiLp.sub_apply] at hcr ⊢
        linear_combination (P.e i 1) * hcr
      simp only [PiLp.sub_apply] at this
      linarith
    · show V 1 = (1 - t) * P.v i 1 + t * (P.v i 1 + P.e i 1)
      have : t * P.e i 1 = (V - P.v i) 1 := by
        rw [ht, div_mul_eq_mul_div, div_eq_iff hn]
        simp only [PiLp.sub_apply] at hcr ⊢
        linear_combination (-(P.e i 0)) * hcr
      simp only [PiLp.sub_apply] at this
      linarith
  refine ⟨t, ⟨?_, ?_⟩, hW⟩
  · by_contra hneg
    replace hneg := not_le.mp hneg
    have h1 : 0 ≤ P.c (i - 1) V := hV (i - 1)
    rw [hW, c_comb, P.c_prev_next hM i] at h1
    have h2 := P.c_vertex_pos (j := i - 1) (m := i + 1) hf4 (by rw [hf5]; exact hf1)
    nlinarith
  · by_contra hneg
    replace hneg := not_le.mp hneg
    have h1 : 0 ≤ P.c (i + 1) V := hV (i + 1)
    rw [hW, c_comb, P.c_self] at h1
    have h2 := P.c_vertex_pos (j := i + 1) (m := i) (Ne.symm hf1) (by rw [hf6]; exact Ne.symm hf2)
    nlinarith

theorem c_edge_pos (hM : 3 ≤ M) (i : Fin M) {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) {j : Fin M} (hj : j ≠ i)
    (h1 : j = i + 1 → t < 1) (h2 : j = i - 1 → 0 < t) : 0 < P.c j ((1 - t) • P.v i + t • P.v (i + 1)) := by
  obtain ⟨hf1, hf2, hf3, hf4, hf5, hf6⟩ := fin_facts hM i
  rw [c_comb]
  by_cases hA : j = i + 1
  · subst hA
    have hlt := h1 rfl
    have h := P.c_vertex_pos (j := i + 1) (m := i) (Ne.symm hf1) (by rw [hf6]; exact Ne.symm hf2)
    rw [P.c_self]
    nlinarith
  by_cases hB : j = i - 1
  · subst hB
    have hlt := h2 rfl
    have h := P.c_vertex_pos (j := i - 1) (m := i + 1) hf4 (by rw [hf5]; exact hf1)
    rw [P.c_prev_next hM i]
    nlinarith [ht.1]
  have hA1 : P.c j (P.v i) > 0 := P.c_vertex_pos (Ne.symm hj) (fun h => hB (eq_sub_of_add_eq h.symm))
  have hA2 : P.c j (P.v (i + 1)) > 0 := P.c_vertex_pos (Ne.symm hA) (fun h => hj (add_right_cancel h).symm)
  by_cases hh : t ≤ 1 / 2
  · nlinarith [mul_nonneg (sub_nonneg.2 hh) hA1.le, mul_nonneg ht.1 hA2.le]
  · have hh' := not_le.mp hh
    nlinarith [mul_nonneg (sub_nonneg.2 ht.2) hA1.le, mul_pos (by linarith : (0:ℝ) < t) hA2]


theorem continuous_c (j : Fin M) : Continuous (P.c j) := by
  unfold c cross2; fun_prop

/-- Orientation of three consecutive vertices is positive (strict convexity). -/
theorem ori_pos (hM : 3 ≤ M) (k : Fin M) : 0 < cross2 (P.v (k + 1) - P.v k) (P.v (k + 2) - P.v k) := by
  obtain ⟨-, h2, h3, -⟩ := fin_facts hM k
  exact P.c_vertex_pos (j := k) (m := k + 2) h2 h3

/-- The local triangle `(v_k, v_{k+1}, v_{k+2})`. -/
noncomputable def locTri (hM : 3 ≤ M) (k : Fin M) : Tri := triOf (P.v k) (P.v (k + 1)) (P.v (k + 2)) (P.ori_pos hM k)

/-- The chord constraint of `locTri k` (the side from `v_{k+2}` to `v_k`). -/
def chord (k : Fin M) (y : Plane) : ℝ := cross2 (P.v k - P.v (k + 2)) (y - P.v (k + 2))

theorem continuous_chord (k : Fin M) : Continuous (P.chord k) := by
  unfold chord cross2; fun_prop

theorem locTri_carrier (hM : 3 ≤ M) (k : Fin M) (y : Plane) :
    y ∈ (P.locTri hM k).carrier ↔ 0 ≤ P.c k y ∧ 0 ≤ P.c (k + 1) y ∧ 0 ≤ P.chord k y := by
  have h6 := (fin_facts hM k).2.2.2.2.2
  unfold locTri
  rw [triOf_carrier]
  unfold c chord e
  rw [h6]

theorem chord_vertex (hM : 3 ≤ M) (k : Fin M) : P.chord k (P.v (k + 1)) = cross2 (P.v (k + 1) - P.v k) (P.v (k + 2) - P.v k) := by
  unfold chord cross2; simp; ring

theorem chord_self (k : Fin M) : P.chord k (P.v k) = 0 := by
  unfold chord cross2; simp; ring

theorem chord_comb (k : Fin M) (A B : Plane) (t : ℝ) : P.chord k ((1 - t) • A + t • B) = (1 - t) * P.chord k A + t * P.chord k B := by
  unfold chord cross2; simp; ring

/-- Near a point where all constraints except those of edges `k, k+1` and the chord of `locTri k` are strict, the polygon equals `locTri k`. -/
theorem local_equiv (hM : 3 ≤ M) (k : Fin M) {V : Plane} (hstrict : ∀ j, j ≠ k → j ≠ k + 1 → 0 < P.c j V)
    (hch : 0 < P.chord k V) :
    ∃ ρ > 0, ∀ y, dist y V < ρ → (y ∈ P.carrier ↔ y ∈ (P.locTri hM k).carrier) := by
  have hev : ∀ᶠ y in nhds V, (∀ j, j ≠ k → j ≠ k + 1 → 0 < P.c j y) ∧ 0 < P.chord k y := by
    refine Filter.Eventually.and ?_ ?_
    · refine Filter.eventually_all.2 fun j => ?_
      by_cases h1 : j = k
      · exact Filter.Eventually.of_forall (fun y hy => absurd h1 hy)
      by_cases h2 : j = k + 1
      · exact Filter.Eventually.of_forall (fun y _ hy => absurd h2 hy)
      exact ((P.continuous_c j).continuousAt.eventually (lt_mem_nhds (hstrict j h1 h2))).mono (fun y hy _ _ => hy)
    · exact (P.continuous_chord k).continuousAt.eventually (lt_mem_nhds hch)
  obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨ρ, hρ, fun y hy => ?_⟩
  obtain ⟨hs, hc⟩ := hball hy
  rw [locTri_carrier]
  constructor
  · intro hyP
    exact ⟨hyP k, hyP (k + 1), hc.le⟩
  · rintro ⟨h1, h2, -⟩ j
    by_cases hjk : j = k
    · subst hjk; exact h1
    by_cases hjk1 : j = k + 1
    · subst hjk1; exact h2
    exact (hs j hjk hjk1).le


/-- A point at which every edge constraint is strict is an interior point. -/
theorem interior_of_pos {V : Plane} (h : ∀ j, 0 < P.c j V) : V ∈ interior P.carrier := by
  have hopen : IsOpen {y : Plane | ∀ j, 0 < P.c j y} := by
    have : {y : Plane | ∀ j, 0 < P.c j y} = ⋂ j, {y : Plane | 0 < P.c j y} := by ext y; simp
    rw [this]
    exact isOpen_iInter_of_finite fun j => isOpen_lt continuous_const (P.continuous_c j)
  have hsub : {y : Plane | ∀ j, 0 < P.c j y} ⊆ P.carrier := fun y hy j => (hy j).le
  exact interior_maximal hsub hopen h

/-- Local triangle at the vertex `v_{k+1}` (the middle vertex of `locTri k`). -/
theorem vertex_local' (hM : 3 ≤ M) (k : Fin M) :
    ∃ T : Tri, P.v (k + 1) ∈ T.carrier ∧ ∃ ρ > 0, ∀ y, dist y (P.v (k + 1)) < ρ → (y ∈ P.carrier ↔ y ∈ T.carrier) := by
  obtain ⟨hf1, -⟩ := fin_facts hM k
  have hstrict : ∀ j, j ≠ k → j ≠ k + 1 → 0 < P.c j (P.v (k + 1)) := by
    intro j h1 h2
    exact P.c_vertex_pos (Ne.symm h2) (fun h => h1 (add_right_cancel h).symm)
  have hch : 0 < P.chord k (P.v (k + 1)) := by
    rw [P.chord_vertex hM k]; exact P.ori_pos hM k
  obtain ⟨ρ, hρ, hiff⟩ := P.local_equiv hM k hstrict hch
  refine ⟨P.locTri hM k, ?_, ρ, hρ, hiff⟩
  rw [locTri_carrier]
  exact ⟨(P.c_next k).ge, (P.c_self (k + 1)).ge, hch.le⟩

theorem vertex_local (hM : 3 ≤ M) (m : Fin M) :
    ∃ T : Tri, P.v m ∈ T.carrier ∧ ∃ ρ > 0, ∀ y, dist y (P.v m) < ρ → (y ∈ P.carrier ↔ y ∈ T.carrier) := by
  have hm : m - 1 + 1 = m := (fin_facts hM m).2.2.2.2.1
  have := P.vertex_local' hM (m - 1)
  rwa [hm] at this

/-- Local triangle at an interior point of an edge. -/
theorem open_edge_local (hM : 3 ≤ M) (i : Fin M) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    ∃ T : Tri, (1 - t) • P.v i + t • P.v (i + 1) ∈ T.carrier ∧ ∃ ρ > 0, ∀ y, dist y ((1 - t) • P.v i + t • P.v (i + 1)) < ρ →
      (y ∈ P.carrier ↔ y ∈ T.carrier) := by
  have htI : t ∈ Set.Icc (0:ℝ) 1 := ⟨ht0.le, ht1.le⟩
  have hstrict : ∀ j, j ≠ i → j ≠ i + 1 → 0 < P.c j ((1 - t) • P.v i + t • P.v (i + 1)) := by
    intro j h1 h2
    exact P.c_edge_pos hM i htI h1 (fun h => absurd h h2) (fun _ => ht0)
  have hch : 0 < P.chord i ((1 - t) • P.v i + t • P.v (i + 1)) := by
    rw [P.chord_comb, P.chord_self, P.chord_vertex hM i]
    have := P.ori_pos hM i
    nlinarith
  obtain ⟨ρ, hρ, hiff⟩ := P.local_equiv hM i hstrict hch
  refine ⟨P.locTri hM i, ?_, ρ, hρ, hiff⟩
  rw [locTri_carrier]
  refine ⟨?_, ?_, hch.le⟩
  · rw [P.c_comb, P.c_self, P.c_next]; simp
  · exact (P.c_edge_pos hM i htI (fin_facts hM i).1 (fun _ => ht1) (fun _ => ht0)).le

/-- The local triangle at the middle vertex `v_{k+1}`, explicitly: the polygon agrees with `locTri k` near `v_{k+1}`. -/
theorem vertex_local_T (hM : 3 ≤ M) (k : Fin M) :
    ∃ ρ > 0, ∀ y, dist y (P.v (k + 1)) < ρ → (y ∈ P.carrier ↔ y ∈ (P.locTri hM k).carrier) := by
  have hstrict : ∀ j, j ≠ k → j ≠ k + 1 → 0 < P.c j (P.v (k + 1)) := by
    intro j h1 h2
    exact P.c_vertex_pos (Ne.symm h2) (fun h => h1 (add_right_cancel h).symm)
  have hch : 0 < P.chord k (P.v (k + 1)) := by
    rw [P.chord_vertex hM k]; exact P.ori_pos hM k
  exact P.local_equiv hM k hstrict hch

/-- The same at an interior point of the edge `i`: the polygon agrees with `locTri i` near it. -/
theorem open_edge_local_T (hM : 3 ≤ M) (i : Fin M) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    ∃ ρ > 0, ∀ y, dist y ((1 - t) • P.v i + t • P.v (i + 1)) < ρ → (y ∈ P.carrier ↔ y ∈ (P.locTri hM i).carrier) := by
  have htI : t ∈ Set.Icc (0:ℝ) 1 := ⟨ht0.le, ht1.le⟩
  have hstrict : ∀ j, j ≠ i → j ≠ i + 1 → 0 < P.c j ((1 - t) • P.v i + t • P.v (i + 1)) := by
    intro j h1 h2
    exact P.c_edge_pos hM i htI h1 (fun h => absurd h h2) (fun _ => ht0)
  have hch : 0 < P.chord i ((1 - t) • P.v i + t • P.v (i + 1)) := by
    rw [P.chord_comb, P.chord_self, P.chord_vertex hM i]
    have := P.ori_pos hM i
    nlinarith
  exact P.local_equiv hM i hstrict hch

/-- **Local structure of a strictly convex polygon (S1).**  A point of the polygon is an interior point, or there is a triangle `T` containing
it and equal to the polygon near it (the point is then a vertex of `T`, or in the relative interior of a side of `T`, or -- for a vertex of the
polygon -- the middle vertex of three consecutive polygon vertices). -/
theorem polygon_local (hM : 3 ≤ M) {V : Plane} (hV : V ∈ P.carrier) :
    V ∈ interior P.carrier ∨
      ∃ T : Tri, V ∈ T.carrier ∧ ∃ ρ > 0, ∀ y, dist y V < ρ → (y ∈ P.carrier ↔ y ∈ T.carrier) := by
  by_cases hpos : ∀ j, 0 < P.c j V
  · exact Or.inl (P.interior_of_pos hpos)
  right
  push Not at hpos
  obtain ⟨i, hi⟩ := hpos
  have h0 : P.c i V = 0 := le_antisymm hi (hV i)
  obtain ⟨t, ⟨ht0, ht1⟩, hVt⟩ := P.edge_param hM hV h0
  rcases ht0.eq_or_lt with h | h
  · subst hVt
    rw [← h] at *
    have := P.vertex_local hM i
    simpa using this
  rcases ht1.eq_or_lt with h' | h'
  · rw [hVt, h']
    have := P.vertex_local hM (i + 1)
    simpa using this
  · rw [hVt]; exact P.open_edge_local hM i h h'

end ConvPoly

end Erdos634.Draft.LaczFormal.Thm21
