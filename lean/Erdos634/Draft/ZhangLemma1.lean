import Erdos634.Draft.ZhangL1Aux

/-!
# Zhang's Lemma 1 (arXiv 2512.22696v4, Figure 2): the ideal trapezoid is tiled by `a²+b²+c²` tiles

Setting (reading of Fig. 2 fixed by the coordinator; Zhang's printed x/y labels are inconsistent).
Let `a, b, c` be positive integers with `c² = a² + b² + a b` (the tile `(a,b,c)` has an angle
`2π/3` between its sides `a` and `b`).  The isosceles trapezoid with `60°` base angles,
`A = (0,0)`, `B = (c²,0)`, `C = (c² − ab/2, ab√3/2)`, `D = (ab/2, ab√3/2)` (base `c²`, top `a²+b²`,
legs `ab`) splits through `E = (ab/2 + a², ab√3/2) ∈ DC` into the triangles `AED`, `BCE`, `ABE`,
which are `a·R`, `b·R`, `c·R` for the tile `R` (up to congruence).  By `Ladder` they are cut into
`a²`, `b²`, `c²` copies of `R`; the three are glued with `GlueCut.glueByLine`.

Theorem `zhang_lemma1`: the convex hull of `A,B,C,D` carries a `CongruentRegionDissection` with
`a² + b² + c²` tiles, all congruent to `R`.  UNAUDITED.  Hypotheses are witnessed:
`(a,b,c) = (3,5,7)` and `(8,7,13)` below.  Not covered: `(1,1,√3)` (`c` not an integer, so the
ladder scale for `c·R` does not apply).  Credit Zhang, Beeson, Beeson-Rosu, Laczkovich.
-/

namespace Erdos634.ZhangL1

open Erdos634.Geometry Erdos634.CertCoord Erdos634.CertGeom Erdos634.RegionDissection
  Erdos634.GlueCut Erdos634.SssCongruent

noncomputable def zs : ℝ := Real.sqrt 3
theorem zs_sq : zs * zs = 3 := Real.mul_self_sqrt (by norm_num)
theorem zs_pos : 0 < zs := Real.sqrt_pos.mpr (by norm_num)

section geom

variable (a b c : ℝ)

/-- height `ab√3/2` -/
noncomputable def hh : ℝ := a * b * zs / 2

noncomputable def pA : Plane := mkPt 0 0
noncomputable def pB : Plane := mkPt (c ^ 2) 0
noncomputable def pC : Plane := mkPt (c ^ 2 - a * b / 2) (hh a b)
noncomputable def pD : Plane := mkPt (a * b / 2) (hh a b)
noncomputable def pE : Plane := mkPt (a * b / 2 + a ^ 2) (hh a b)

/-- The ideal trapezoid, as the convex hull of its four vertices. -/
noncomputable def Trap : Set Plane := convexHull ℝ {pA, pB c, pC a b c, pD a b}

end geom

variable {a b c : ℝ}

theorem hh_pos (ha : 0 < a) (hb : 0 < b) : 0 < hh a b := by
  unfold hh; have := zs_pos; positivity

theorem dR (ha : 0 < a) (hb : 0 < b) :
    0 < det3 0 0 (b / 2 + a) (b * zs / 2) (b / 2) (b * zs / 2) := by
  have : det3 0 0 (b / 2 + a) (b * zs / 2) (b / 2) (b * zs / 2) = a * b * zs / 2 := by
    simp only [det3]; ring
  rw [this]; have := zs_pos; positivity

/-- The model tile: sides `|01| = c`, `|12| = a`, `|02| = b`, angle `2π/3` at vertex `0`... -/
noncomputable def Rmodel (ha : 0 < a) (hb : 0 < b) : Tri :=
  mkTri 0 0 (b / 2 + a) (b * zs / 2) (b / 2) (b * zs / 2) (dR ha hb).ne'

theorem dU2 (ha : 0 < a) (hb : 0 < b) :
    0 < det3 (c ^ 2) 0 (c ^ 2 - a / 2) (a * zs / 2) (c ^ 2 - b - a / 2) (a * zs / 2) := by
  have : det3 (c ^ 2) 0 (c ^ 2 - a / 2) (a * zs / 2) (c ^ 2 - b - a / 2) (a * zs / 2)
      = a * b * zs / 2 := by simp only [det3]; ring
  rw [this]; have := zs_pos; positivity

noncomputable def U2 (ha : 0 < a) (hb : 0 < b) : Tri :=
  mkTri (c ^ 2) 0 (c ^ 2 - a / 2) (a * zs / 2) (c ^ 2 - b - a / 2) (a * zs / 2) (dU2 (c := c) ha hb).ne'

theorem dU3 (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    0 < det3 0 0 c 0 ((a * b / 2 + a ^ 2) / c) (a * b * zs / (2 * c)) := by
  have : det3 0 0 c 0 ((a * b / 2 + a ^ 2) / c) (a * b * zs / (2 * c)) = a * b * zs / 2 := by
    simp only [det3]; field_simp; ring
  rw [this]; have := zs_pos; positivity

noncomputable def U3 (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : Tri :=
  mkTri 0 0 c 0 ((a * b / 2 + a ^ 2) / c) (a * b * zs / (2 * c)) (dU3 ha hb hc).ne'

theorem dT1 (ha : 0 < a) (hb : 0 < b) :
    0 < det3 0 0 (a * b / 2 + a ^ 2) (hh a b) (a * b / 2) (hh a b) := by
  have : det3 0 0 (a * b / 2 + a ^ 2) (hh a b) (a * b / 2) (hh a b) = a ^ 2 * hh a b := by
    simp only [det3]; ring
  rw [this]; have := hh_pos ha hb; positivity

theorem dT2 (ha : 0 < a) (hb : 0 < b) (hc2 : c ^ 2 = a ^ 2 + b ^ 2 + a * b) :
    0 < det3 (c ^ 2) 0 (c ^ 2 - a * b / 2) (hh a b) (a * b / 2 + a ^ 2) (hh a b) := by
  have : det3 (c ^ 2) 0 (c ^ 2 - a * b / 2) (hh a b) (a * b / 2 + a ^ 2) (hh a b)
      = b ^ 2 * hh a b := by simp only [det3]; rw [hc2]; ring
  rw [this]; have := hh_pos ha hb; positivity

theorem dT3 (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    0 < det3 0 0 (c ^ 2) 0 (a * b / 2 + a ^ 2) (hh a b) := by
  have : det3 0 0 (c ^ 2) 0 (a * b / 2 + a ^ 2) (hh a b) = c ^ 2 * hh a b := by
    simp only [det3]; ring
  rw [this]; have := hh_pos ha hb; positivity

noncomputable def T1 (ha : 0 < a) (hb : 0 < b) : Tri :=
  mkTri 0 0 (a * b / 2 + a ^ 2) (hh a b) (a * b / 2) (hh a b) (dT1 ha hb).ne'
noncomputable def T2 (ha : 0 < a) (hb : 0 < b) (hc2 : c ^ 2 = a ^ 2 + b ^ 2 + a * b) : Tri :=
  mkTri (c ^ 2) 0 (c ^ 2 - a * b / 2) (hh a b) (a * b / 2 + a ^ 2) (hh a b) (dT2 ha hb hc2).ne'
noncomputable def T3 (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : Tri :=
  mkTri 0 0 (c ^ 2) 0 (a * b / 2 + a ^ 2) (hh a b) (dT3 ha hb hc).ne'

/-! ### Congruences -/

theorem U2_cong (ha : 0 < a) (hb : 0 < b) (hc2 : c ^ 2 = a ^ 2 + b ^ 2 + a * b) :
    (U2 (c := c) ha hb).Congruent (Rmodel ha hb) := by
  have hs := zs_sq
  refine congruent_of_sq_dist_perm ⟨![1, 2, 0], ![2, 0, 1], by decide, by decide⟩ ?_
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [U2, Rmodel, mkTri, dist_sq_mkPt] <;> nlinarith [hs, hc2]

theorem U3_cong (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hc2 : c ^ 2 = a ^ 2 + b ^ 2 + a * b) :
    (U3 ha hb hc).Congruent (Rmodel ha hb) := by
  have hs := zs_sq
  have hz : zs ^ 2 = 3 := by nlinarith
  refine congruent_of_sq_dist_perm ⟨![1, 0, 2], ![1, 0, 2], by decide, by decide⟩ ?_
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [U3, Rmodel, mkTri, dist_sq_mkPt] <;> field_simp <;>
    first | nlinarith [hs, hc2] | (rw [hz, hc2]; ring)


theorem mkPt_congr {x y x' y' : ℝ} (hx : x = x') (hy : y = y') : mkPt x y = mkPt x' y' := by
  rw [hx, hy]

/-! ### The three scaled pieces -/

theorem piece1 (ha : 0 < a) (hb : 0 < b) (k : ℕ) (hk : 0 < k) (hka : (k : ℝ) = a) :
    ∃ C : CongruentRegionDissection (k * k * 1),
      C.region = (T1 ha hb).carrier ∧ C.model = Rmodel ha hb := by
  refine scaledPiece (Rmodel ha hb) (Rmodel ha hb) (T1 ha hb) ⟨IsometryEquiv.refl _, Equiv.refl _,
    fun _ => rfl⟩ k hk ?_ ?_ ?_
  · simp [T1, Rmodel, mkTri]
  · simp [T1, Rmodel, mkTri, mkPt_sub, mkPt_smul, mkPt_add, hka]; refine mkPt_congr ?_ ?_ <;> (try simp only [hh]) <;> ring
  · simp [T1, Rmodel, mkTri, mkPt_sub, mkPt_smul, mkPt_add, hka]; refine mkPt_congr ?_ ?_ <;> (try simp only [hh]) <;> ring

theorem piece2 (ha : 0 < a) (hb : 0 < b) (hc2 : c ^ 2 = a ^ 2 + b ^ 2 + a * b)
    (k : ℕ) (hk : 0 < k) (hkb : (k : ℝ) = b) :
    ∃ C : CongruentRegionDissection (k * k * 1),
      C.region = (T2 ha hb hc2).carrier ∧ C.model = Rmodel ha hb := by
  refine scaledPiece (U2 (c := c) ha hb) (Rmodel ha hb) (T2 ha hb hc2) (U2_cong ha hb hc2) k hk ?_ ?_ ?_
  · simp [T2, U2, mkTri]
  · simp [T2, U2, mkTri, mkPt_sub, mkPt_smul, mkPt_add, hkb]; refine mkPt_congr ?_ ?_ <;> (try simp only [hh]) <;> ring
  · simp [T2, U2, mkTri, mkPt_sub, mkPt_smul, mkPt_add, hkb]; refine mkPt_congr ?_ ?_ <;> (try simp only [hh]) <;>
      first | ring1 | linear_combination hc2 | linear_combination (-1:ℝ) * hc2

theorem piece3 (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hc2 : c ^ 2 = a ^ 2 + b ^ 2 + a * b)
    (k : ℕ) (hk : 0 < k) (hkc : (k : ℝ) = c) :
    ∃ C : CongruentRegionDissection (k * k * 1),
      C.region = (T3 ha hb hc).carrier ∧ C.model = Rmodel ha hb := by
  have hc' : c ≠ 0 := hc.ne'
  refine scaledPiece (U3 ha hb hc) (Rmodel ha hb) (T3 ha hb hc) (U3_cong ha hb hc hc2) k hk ?_ ?_ ?_
  · simp [T3, U3, mkTri]
  · simp [T3, U3, mkTri, mkPt_sub, mkPt_smul, mkPt_add, hkc]; refine mkPt_congr ?_ ?_ <;> (try simp only [hh]) <;> first | ring1 | (field_simp; done) | (field_simp; ring1)
  · simp [T3, U3, mkTri, mkPt_sub, mkPt_smul, mkPt_add, hkc]; refine mkPt_congr ?_ ?_ <;> (try simp only [hh]) <;> first | ring1 | (field_simp; done) | (field_simp; ring1)


/-! ### The trapezoid is the union of the three triangles -/

theorem hull_le {t : Tri} {S : Set Plane} (hS : Convex ℝ S) (h : ∀ k, t.pts k ∈ S) :
    t.carrier ⊆ S :=
  convexHull_min (Set.range_subset_iff.mpr h) hS

theorem pE_mem (ha : 0 < a) (hb : 0 < b) (hc2 : c ^ 2 = a ^ 2 + b ^ 2 + a * b) :
    pE a b ∈ Trap a b c := by
  have hconv : Convex ℝ (Trap a b c) := convex_convexHull ℝ _
  have hD : pD a b ∈ Trap a b c := subset_convexHull ℝ _ (by simp)
  have hC : pC a b c ∈ Trap a b c := subset_convexHull ℝ _ (by simp)
  refine hconv.segment_subset hD hC ?_
  have hab : 0 < a ^ 2 + b ^ 2 := by positivity
  refine ⟨1 - a ^ 2 / (a ^ 2 + b ^ 2), a ^ 2 / (a ^ 2 + b ^ 2), ?_, by positivity, by ring, ?_⟩
  · rw [sub_nonneg, div_le_one hab]; nlinarith [sq_nonneg b]
  · simp only [pD, pC, pE, mkPt_smul, mkPt_add]
    refine mkPt_congr ?_ ?_
    · field_simp; rw [hc2]; ring
    · field_simp; ring

theorem hull_ineq (ha : 0 < a) (hb : 0 < b) (hc2 : c ^ 2 = a ^ 2 + b ^ 2 + a * b)
    (p : Plane) (hp : p ∈ Trap a b c) :
    0 ≤ det3 0 0 (c ^ 2) 0 (p 0) (p 1) ∧
    0 ≤ det3 (c ^ 2) 0 (c ^ 2 - a * b / 2) (hh a b) (p 0) (p 1) ∧
    0 ≤ det3 (c ^ 2 - a * b / 2) (hh a b) (a * b / 2) (hh a b) (p 0) (p 1) ∧
    0 ≤ det3 (a * b / 2) (hh a b) 0 0 (p 0) (p 1) := by
  have hh0 := hh_pos ha hb
  have hab : 0 < a * b := mul_pos ha hb
  have hcab : 0 < c ^ 2 - a * b := by nlinarith [sq_nonneg a, sq_nonneg b]
  have hc0 : 0 ≤ c ^ 2 := sq_nonneg c
  have key : ∀ (px py qx qy : ℝ),
      0 ≤ det3 px py qx qy 0 0 → 0 ≤ det3 px py qx qy (c ^ 2) 0 →
      0 ≤ det3 px py qx qy (c ^ 2 - a * b / 2) (hh a b) → 0 ≤ det3 px py qx qy (a * b / 2) (hh a b) →
      0 ≤ det3 px py qx qy (p 0) (p 1) := by
    intro px py qx qy h1 h2 h3 h4
    have := hull_subset_halfplane {pA, pB c, pC a b c, pD a b} (lineFun px py qx qy) ?_ p hp
    · rw [← mkPt_eta p, lineFun_mkPt] at this; simpa [mkPt_eta] using this
    · intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · rw [pA, lineFun_mkPt]; exact h1
      · rw [pB, lineFun_mkPt]; exact h2
      · rw [pC, lineFun_mkPt]; exact h3
      · rw [pD, lineFun_mkPt]; exact h4
  refine ⟨key _ _ _ _ ?_ ?_ ?_ ?_, key _ _ _ _ ?_ ?_ ?_ ?_, key _ _ _ _ ?_ ?_ ?_ ?_,
    key _ _ _ _ ?_ ?_ ?_ ?_⟩ <;> simp only [det3] <;>
    nlinarith [mul_pos hh0 hcab, mul_nonneg hh0.le hc0, mul_pos hh0 hab]


theorem tri_sub_trap (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hc2 : c ^ 2 = a ^ 2 + b ^ 2 + a * b) :
    (T1 ha hb).carrier ⊆ Trap a b c ∧ (T2 ha hb hc2).carrier ⊆ Trap a b c ∧
      (T3 ha hb hc).carrier ⊆ Trap a b c := by
  have hA : pA ∈ Trap a b c := subset_convexHull ℝ _ (by simp)
  have hB : pB c ∈ Trap a b c := subset_convexHull ℝ _ (by simp)
  have hC : pC a b c ∈ Trap a b c := subset_convexHull ℝ _ (by simp)
  have hD : pD a b ∈ Trap a b c := subset_convexHull ℝ _ (by simp)
  have hE := pE_mem ha hb hc2
  refine ⟨?_, ?_, ?_⟩ <;>
  · refine hull_le (convex_convexHull ℝ _) ?_
    intro k; fin_cases k <;> simp [T1, T2, T3, mkTri] <;> assumption


theorem trap_sub_union_of_ineq (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hc2 : c ^ 2 = a ^ 2 + b ^ 2 + a * b) (p : Plane)
    (hAB : 0 ≤ det3 0 0 (c ^ 2) 0 (p 0) (p 1))
    (hBC : 0 ≤ det3 (c ^ 2) 0 (c ^ 2 - a * b / 2) (hh a b) (p 0) (p 1))
    (hCD : 0 ≤ det3 (c ^ 2 - a * b / 2) (hh a b) (a * b / 2) (hh a b) (p 0) (p 1))
    (hDA : 0 ≤ det3 (a * b / 2) (hh a b) 0 0 (p 0) (p 1)) :
    p ∈ (T2 ha hb hc2).carrier ∪ (T3 ha hb hc).carrier ∪ (T1 ha hb).carrier := by
  have hh0 := hh_pos ha hb
  have hab : 0 < a * b := mul_pos ha hb
  have hcab : 0 < c ^ 2 - a * b := by nlinarith [sq_nonneg a, sq_nonneg b]
  -- the top edge: p 1 ≤ h
  have hy : p 1 ≤ hh a b := by
    by_contra hcon
    have hcon' := not_le.mp hcon
    simp only [det3] at hCD
    nlinarith [mul_pos hcab (sub_pos.mpr hcon')]
  have hy' : 0 ≤ hh a b - p 1 := by linarith
  rcases le_total 0 (det3 0 0 (a * b / 2 + a ^ 2) (hh a b) (p 0) (p 1)) with g1 | g1
  · -- left of AE : triangle ADE = T1
    right
    rw [T1, mem_carrier_mkTri_iff (dT1 ha hb)]
    refine ⟨?_, ?_, g1⟩
    · have : det3 (p 0) (p 1) (a * b / 2 + a ^ 2) (hh a b) (a * b / 2) (hh a b)
          = a ^ 2 * (hh a b - p 1) := by simp only [det3]; ring
      rw [this]; positivity
    · have : det3 0 0 (p 0) (p 1) (a * b / 2) (hh a b)
          = det3 (a * b / 2) (hh a b) 0 0 (p 0) (p 1) := by simp only [det3]; ring
      rw [this]; exact hDA
  · rcases le_total 0 (det3 (c ^ 2) 0 (a * b / 2 + a ^ 2) (hh a b) (p 0) (p 1)) with g2 | g2
    · left; right
      rw [T3, mem_carrier_mkTri_iff (dT3 ha hb hc)]
      refine ⟨?_, ?_, hAB⟩
      · have : det3 (p 0) (p 1) (c ^ 2) 0 (a * b / 2 + a ^ 2) (hh a b)
            = det3 (c ^ 2) 0 (a * b / 2 + a ^ 2) (hh a b) (p 0) (p 1) := by
          simp only [det3]; ring
        rw [this]; exact g2
      · have : det3 0 0 (p 0) (p 1) (a * b / 2 + a ^ 2) (hh a b)
            = - det3 0 0 (a * b / 2 + a ^ 2) (hh a b) (p 0) (p 1) := by simp only [det3]; ring
        rw [this]; linarith
    · left; left
      rw [T2, mem_carrier_mkTri_iff (dT2 ha hb hc2)]
      refine ⟨?_, ?_, hBC⟩
      · have : det3 (p 0) (p 1) (c ^ 2 - a * b / 2) (hh a b) (a * b / 2 + a ^ 2) (hh a b)
            = b ^ 2 * (hh a b - p 1) := by simp only [det3]; rw [hc2]; ring
        rw [this]; positivity
      · have : det3 (c ^ 2) 0 (p 0) (p 1) (a * b / 2 + a ^ 2) (hh a b)
            = - det3 (c ^ 2) 0 (a * b / 2 + a ^ 2) (hh a b) (p 0) (p 1) := by
          simp only [det3]; ring
        rw [this]; linarith


theorem trap_sub_union (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hc2 : c ^ 2 = a ^ 2 + b ^ 2 + a * b)
    (p : Plane) (hp : p ∈ Trap a b c) :
    p ∈ (T2 ha hb hc2).carrier ∪ (T3 ha hb hc).carrier ∪ (T1 ha hb).carrier := by
  obtain ⟨hAB, hBC, hCD, hDA⟩ := hull_ineq ha hb hc2 p hp
  exact trap_sub_union_of_ineq ha hb hc hc2 p hAB hBC hCD hDA

theorem tri_halfplane (T : Tri) (px py qx qy : ℝ) (h : ∀ k, 0 ≤ lineFun px py qx qy (T.pts k)) :
    ∀ x ∈ T.carrier, 0 ≤ lineFun px py qx qy x :=
  hull_subset_halfplane (Set.range T.pts) _ (by rintro _ ⟨k, rfl⟩; exact h k)

theorem tri_nonpos (T : Tri) (px py qx qy : ℝ) (h : ∀ k, 0 ≤ lineFun qx qy px py (T.pts k)) :
    ∀ x ∈ T.carrier, lineFun px py qx qy x ≤ 0 := by
  intro x hx
  have := tri_halfplane T qx qy px py h x hx
  rw [lineFun_swap] at this; linarith

/-- **Zhang's Lemma 1 (Fig. 2 reading), UNAUDITED.**  For positive integers with
`c² = a² + b² + a b`, the ideal trapezoid `Trap` is dissected into `a² + b² + c²` tiles, each
congruent to the model tile `Rmodel` (sides `c, a, b`, angle `2π/3` between `a` and `b`). -/
theorem zhang_lemma1 (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hcab : c * c = a * a + b * b + a * b) :
    ∃ N : ℕ, N = a * a + b * b + c * c ∧ ∃ C : CongruentRegionDissection N,
      C.region = Trap (a : ℝ) b c ∧
      C.model = Rmodel (Nat.cast_pos.mpr ha : (0:ℝ) < a) (Nat.cast_pos.mpr hb : (0:ℝ) < b) := by
  have ha' : (0:ℝ) < a := Nat.cast_pos.mpr ha
  have hb' : (0:ℝ) < b := Nat.cast_pos.mpr hb
  have hc' : (0:ℝ) < c := Nat.cast_pos.mpr hc
  have hc2 : (c:ℝ) ^ 2 = (a:ℝ) ^ 2 + (b:ℝ) ^ 2 + a * b := by exact_mod_cast (by nlinarith [hcab] : c ^ 2 = a ^ 2 + b ^ 2 + a * b)
  have hh0 := hh_pos ha' hb'
  obtain ⟨C1, hC1r, hC1m⟩ := piece1 ha' hb' a ha rfl
  obtain ⟨C2, hC2r, hC2m⟩ := piece2 ha' hb' hc2 b hb rfl
  obtain ⟨C3, hC3r, hC3m⟩ := piece3 ha' hb' hc' hc2 c hc rfl
  -- generic vertex facts
  have hbc : (b:ℝ) ^ 2 * hh a b ≥ 0 := by positivity
  -- cut 1: line B E, T2 on the ≤ 0 side, T3 on the ≥ 0 side
  have f1 : (lineFun ((c:ℝ) ^ 2) 0 ((a:ℝ) * b / 2 + (a:ℝ) ^ 2) (hh a b)).linear ≠ 0 :=
    lineFun_linear_ne_zero (Or.inr hh0.ne)
  have f2 : (lineFun 0 0 ((a:ℝ) * b / 2 + (a:ℝ) ^ 2) (hh a b)).linear ≠ 0 :=
    lineFun_linear_ne_zero (Or.inr hh0.ne)
  set A' : ℝ := (a:ℝ)
  set B' : ℝ := (b:ℝ)
  set Cc : ℝ := (c:ℝ)
  have hab : 0 < A' * B' := mul_pos ha' hb'
  have hbh : 0 ≤ hh A' B' * B' ^ 2 := by positivity
  have hah : 0 ≤ hh A' B' * A' ^ 2 := by positivity
  have hch : 0 ≤ hh A' B' * Cc ^ 2 := by positivity
  have hmain : 0 ≤ hh A' B' * (Cc ^ 2 - A' * B') := by nlinarith
  -- cut BE
  have c2le : ∀ x ∈ C2.region, lineFun ((Cc) ^ 2) 0 (A' * B' / 2 + A' ^ 2) (hh A' B') x ≤ 0 := by
    rw [hC2r]
    refine tri_nonpos _ _ _ _ _ ?_
    intro k; fin_cases k <;> simp [T2, mkTri, lineFun_mkPt, det3] <;> nlinarith
  have c3ge : ∀ x ∈ C3.region, 0 ≤ lineFun ((Cc) ^ 2) 0 (A' * B' / 2 + A' ^ 2) (hh A' B') x := by
    rw [hC3r]
    refine tri_halfplane _ _ _ _ _ ?_
    intro k; fin_cases k <;> simp [T3, mkTri, lineFun_mkPt, det3] <;> nlinarith
  let C23 := glueByLine C2 C3 (hC2m.trans hC3m.symm) _ f1 c2le c3ge
  -- cut AE
  have c23le : ∀ x ∈ C23.region, lineFun 0 0 (A' * B' / 2 + A' ^ 2) (hh A' B') x ≤ 0 := by
    intro x hx
    simp only [C23, glueByLine_region, hC2r, hC3r] at hx
    rcases hx with hx | hx
    · refine tri_nonpos (T2 ha' hb' hc2) _ _ _ _ ?_ x hx
      intro k; fin_cases k <;> simp [T2, mkTri, lineFun_mkPt, det3] <;> nlinarith
    · refine tri_nonpos (T3 ha' hb' hc') _ _ _ _ ?_ x hx
      intro k; fin_cases k <;> simp [T3, mkTri, lineFun_mkPt, det3] <;> nlinarith
  have c1ge : ∀ x ∈ C1.region, 0 ≤ lineFun 0 0 (A' * B' / 2 + A' ^ 2) (hh A' B') x := by
    rw [hC1r]
    refine tri_halfplane _ _ _ _ _ ?_
    intro k; fin_cases k <;> simp [T1, mkTri, lineFun_mkPt, det3] <;> nlinarith
  let C123 := glueByLine C23 C1 (by simp [C23, glueByLine_model, hC2m, hC1m]) _ f2 c23le c1ge
  refine ⟨b * b * 1 + c * c * 1 + a * a * 1, by ring, C123, ?_, ?_⟩
  · simp only [C123, C23, glueByLine_region, hC1r, hC2r, hC3r]
    ext p
    constructor
    · intro hp
      rcases hp with (hp | hp) | hp
      · exact (tri_sub_trap ha' hb' hc' hc2).2.1 hp
      · exact (tri_sub_trap ha' hb' hc' hc2).2.2 hp
      · exact (tri_sub_trap ha' hb' hc' hc2).1 hp
    · intro hp; exact trap_sub_union ha' hb' hc' hc2 p hp
  · simp [C123, C23, glueByLine_model, hC2m]


/-- Witness for the hypotheses: `(3,5,7)`, the tile of the 143-tiling; `83 = 9 + 25 + 49`. -/
theorem zhang_lemma1_357 : ∃ N : ℕ, N = 83 ∧ ∃ C : CongruentRegionDissection N,
    C.region = Trap ((3:ℕ) : ℝ) ((5:ℕ) : ℝ) ((7:ℕ) : ℝ) := by
  obtain ⟨N, hN, C, hC, -⟩ := zhang_lemma1 3 5 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨N, by omega, C, hC⟩

/-- Second witness: `(8,7,13)`, `64 + 49 + 169 = 282`. -/
theorem zhang_lemma1_8_7_13 : ∃ N : ℕ, N = 282 ∧ ∃ C : CongruentRegionDissection N,
    C.region = Trap ((8:ℕ) : ℝ) ((7:ℕ) : ℝ) ((13:ℕ) : ℝ) := by
  obtain ⟨N, hN, C, hC, -⟩ := zhang_lemma1 8 7 13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨N, by omega, C, hC⟩

end Erdos634.ZhangL1
