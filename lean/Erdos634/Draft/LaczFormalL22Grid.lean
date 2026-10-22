import Erdos634.Draft.LaczFormalL22Base

/-!
# Laczkovich Lemma 2.2 (i), chart-plane combinatorics: the `n × m` grid of a coordinate rectangle

NOTE, UNAUDITED.  Credit: Laczkovich (Discrete Math. 140 (1995) 79-94), Beeson, Beeson-Zhang, Zhang.

In the standard plane, the rectangle `[s0, s0+p] × [t0, t0+q]` is cut into `n × m` cells, each cell into a
lower and an upper right triangle (corner vertex first).  This file proves covering and pairwise
interior-disjointness; the similarity statements (after moving by a chart) are in `LaczFormalL22Par`.
-/

namespace Erdos634.LaczL22

open Erdos634.Geometry Erdos634.CertCoord

/-! ## Separation tools (sets and triangles) -/

/-- The affine functional `a x₀ + b x₁ + c` of the standard plane. -/
noncomputable def coordFun (a b c : ℝ) : Plane →ᵃ[ℝ] ℝ where
  toFun v := a * v 0 + b * v 1 + c
  linear :=
    { toFun := fun w => a * w 0 + b * w 1
      map_add' := by intro w z; simp only [PiLp.add_apply]; ring
      map_smul' := by intro k w; simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }
  map_vadd' := by
    intro v w
    simp only [vadd_eq_add, PiLp.add_apply, LinearMap.coe_mk, AddHom.coe_mk]
    ring

@[simp] theorem coordFun_apply (a b c : ℝ) (v : Plane) :
    coordFun a b c v = a * v 0 + b * v 1 + c := rfl

theorem coordFun_linear_ne_zero {a b : ℝ} (c : ℝ) (h : a ≠ 0 ∨ b ≠ 0) :
    (coordFun a b c).linear ≠ 0 := by
  intro hcon
  set e0 : Plane := EuclideanSpace.single 0 (1 : ℝ) with he0
  set e1 : Plane := EuclideanSpace.single 1 (1 : ℝ) with he1
  have hb00 : e0 0 = 1 := by simp [he0]
  have hb01 : e0 1 = 0 := by simp [he0]
  have hb10 : e1 0 = 0 := by simp [he1]
  have hb11 : e1 1 = 1 := by simp [he1]
  have h0 : (coordFun a b c).linear e0 = 0 := by rw [hcon]; rfl
  have h1 : (coordFun a b c).linear e1 = 0 := by rw [hcon]; rfl
  have eq0 : a * e0 0 + b * e0 1 = 0 := h0
  have eq1 : a * e1 0 + b * e1 1 = 0 := h1
  rw [hb00, hb01] at eq0
  rw [hb10, hb11] at eq1
  rcases h with h | h
  · exact h (by linarith)
  · exact h (by linarith)

/-- Interiors of two sets separated by a closed half-plane pair are disjoint. -/
theorem disjoint_interior_of_sep {S U : Set Plane} (f : Plane →ᵃ[ℝ] ℝ) (hf : f.linear ≠ 0) (c : ℝ)
    (h1 : ∀ x ∈ S, f x ≤ c) (h2 : ∀ x ∈ U, c ≤ f x) :
    Disjoint (interior S) (interior U) := by
  rw [Set.disjoint_left]
  intro x hx1 hx2
  have hxt : x ∈ S := interior_subset hx1
  have hxu : x ∈ U := interior_subset hx2
  have hxc : f x = c := le_antisymm (h1 x hxt) (h2 x hxu)
  set g : Plane →ᵃ[ℝ] ℝ := AffineMap.const ℝ Plane c - f with hg
  have hglin : g.linear ≠ 0 := by
    intro hcon
    apply hf
    have : (AffineMap.const ℝ Plane c).linear - f.linear = 0 := hcon
    have hzero : (AffineMap.const ℝ Plane c).linear = 0 := rfl
    rw [hzero, zero_sub, neg_eq_zero] at this
    exact this
  have hgx : g x = 0 := by simp [hg, hxc]
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hx1)
  obtain ⟨y, hy, hyneg⟩ := Erdos634.Geometry.exists_neg_near_of_affine_zero g hglin hgx hr
  have hyt : y ∈ S := hball hy
  have : c < f y := by
    have hgy : g y = c - f y := rfl
    rw [hgy] at hyneg
    linarith
  exact absurd (h1 y hyt) (not_le.mpr this)

theorem ge_of_forall_pts_ge {t : Tri} (f : Plane →ᵃ[ℝ] ℝ) {c : ℝ} (h : ∀ k, c ≤ f (t.pts k)) :
    ∀ x ∈ t.carrier, c ≤ f x := by
  have hconv : Convex ℝ (f ⁻¹' Set.Ici c) := (convex_Ici c).affine_preimage f
  have hsub : t.carrier ⊆ f ⁻¹' Set.Ici c :=
    convexHull_min (Set.range_subset_iff.mpr h) hconv
  exact fun x hx => hsub hx

/-- Two triangles separated at their vertices by an affine functional have disjoint interiors. -/
theorem sep_tri {T U : Tri} (f : Plane →ᵃ[ℝ] ℝ) (hf : f.linear ≠ 0) (c : ℝ)
    (h1 : ∀ k, f (T.pts k) ≤ c) (h2 : ∀ k, c ≤ f (U.pts k)) :
    Disjoint (interior T.carrier) (interior U.carrier) :=
  disjoint_interior_of_sep f hf c (Erdos634.CertGeom.le_of_forall_pts_le f h1)
    (ge_of_forall_pts_ge f h2)

/-! ## Rectangles -/

/-- The closed coordinate rectangle. -/
def rectSet (s0 s1 t0 t1 : ℝ) : Set Plane :=
  {z | s0 ≤ z 0 ∧ z 0 ≤ s1 ∧ t0 ≤ z 1 ∧ z 1 ≤ t1}

theorem convex_rectSet (s0 s1 t0 t1 : ℝ) : Convex ℝ (rectSet s0 s1 t0 t1) := by
  intro x hx y hy a b ha hb hab
  obtain ⟨hx1, hx2, hx3, hx4⟩ := hx
  obtain ⟨hy1, hy2, hy3, hy4⟩ := hy
  simp only [rectSet, Set.mem_setOf_eq, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  obtain rfl : b = 1 - a := by linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · nlinarith [mul_nonneg ha (sub_nonneg.2 hx1), mul_nonneg hb (sub_nonneg.2 hy1)]
  · nlinarith [mul_nonneg ha (sub_nonneg.2 hx2), mul_nonneg hb (sub_nonneg.2 hy2)]
  · nlinarith [mul_nonneg ha (sub_nonneg.2 hx3), mul_nonneg hb (sub_nonneg.2 hy3)]
  · nlinarith [mul_nonneg ha (sub_nonneg.2 hx4), mul_nonneg hb (sub_nonneg.2 hy4)]

theorem carrier_subset_rect {T : Tri} {s0 s1 t0 t1 : ℝ}
    (h : ∀ k, T.pts k ∈ rectSet s0 s1 t0 t1) : T.carrier ⊆ rectSet s0 s1 t0 t1 :=
  convexHull_min (Set.range_subset_iff.mpr h) (convex_rectSet _ _ _ _)

/-! ## Cells -/

/-- Lower triangle of the cell with lower-left corner `(x, y)` and size `du × dv`, corner first. -/
noncomputable def cellLow (x y du dv : ℝ) (hu : 0 < du) (hv : 0 < dv) : Tri :=
  mkTri x y (x + du) y x (y + dv) (by
    simp only [det3]; nlinarith [mul_pos hu hv])

/-- Upper triangle of the cell, corner first (the upper-right corner). -/
noncomputable def cellUpp (x y du dv : ℝ) (hu : 0 < du) (hv : 0 < dv) : Tri :=
  mkTri (x + du) (y + dv) (x + du) y x (y + dv) (by
    simp only [det3]; nlinarith [mul_pos hu hv])

noncomputable def cellTri (x y du dv : ℝ) (hu : 0 < du) (hv : 0 < dv) (b : Bool) : Tri :=
  if b then cellUpp x y du dv hu hv else cellLow x y du dv hu hv

theorem cellLow_pts (x y du dv : ℝ) (hu : 0 < du) (hv : 0 < dv) :
    (cellLow x y du dv hu hv).pts 0 = mkPt x y ∧ (cellLow x y du dv hu hv).pts 1 = mkPt (x + du) y ∧
      (cellLow x y du dv hu hv).pts 2 = mkPt x (y + dv) := by
  refine ⟨rfl, rfl, rfl⟩

theorem cellUpp_pts (x y du dv : ℝ) (hu : 0 < du) (hv : 0 < dv) :
    (cellUpp x y du dv hu hv).pts 0 = mkPt (x + du) (y + dv) ∧
      (cellUpp x y du dv hu hv).pts 1 = mkPt (x + du) y ∧
      (cellUpp x y du dv hu hv).pts 2 = mkPt x (y + dv) := by
  refine ⟨rfl, rfl, rfl⟩

theorem cellTri_sub_rect (x y du dv : ℝ) (hu : 0 < du) (hv : 0 < dv) (b : Bool) :
    (cellTri x y du dv hu hv b).carrier ⊆ rectSet x (x + du) y (y + dv) := by
  have htri : ∀ k : Fin 3, k = 0 ∨ k = 1 ∨ k = 2 := by decide
  cases b
  · apply carrier_subset_rect
    intro k
    obtain ⟨h0, h1, h2⟩ := cellLow_pts x y du dv hu hv
    show (cellLow x y du dv hu hv).pts k ∈ _
    rcases htri k with rfl | rfl | rfl
    · rw [h0]; simp [rectSet]; constructor <;> linarith
    · rw [h1]; simp [rectSet]; constructor <;> linarith
    · rw [h2]; simp [rectSet]; constructor <;> linarith
  · apply carrier_subset_rect
    intro k
    obtain ⟨h0, h1, h2⟩ := cellUpp_pts x y du dv hu hv
    show (cellUpp x y du dv hu hv).pts k ∈ _
    rcases htri k with rfl | rfl | rfl
    · rw [h0]; simp [rectSet]; constructor <;> linarith
    · rw [h1]; simp [rectSet]; constructor <;> linarith
    · rw [h2]; simp [rectSet]; constructor <;> linarith

/-- A point of the lower triangle, by local coordinates. -/
theorem low_mem (x y du dv : ℝ) (hu : 0 < du) (hv : 0 < dv) (l m : ℝ) (hl : 0 ≤ l) (hm : 0 ≤ m)
    (hlm : l + m ≤ 1) :
    mkPt (x + l * du) (y + m * dv) ∈ (cellLow x y du dv hu hv).carrier := by
  have hD : 0 < det3 x y (x + du) y x (y + dv) := by simp only [det3]; nlinarith [mul_pos hu hv]
  have := mem_carrier_of_dets (a := x + l * du) (b := y + m * dv) hD
    (by simp only [det3]; nlinarith [mul_pos hu hv, mul_nonneg (mul_pos hu hv).le (sub_nonneg.2 hlm)])
    (by simp only [det3]; nlinarith [mul_pos hu hv, mul_nonneg (mul_pos hu hv).le hl])
    (by simp only [det3]; nlinarith [mul_pos hu hv, mul_nonneg (mul_pos hu hv).le hm])
  exact this

/-- A point of the upper triangle, by local coordinates. -/
theorem upp_mem (x y du dv : ℝ) (hu : 0 < du) (hv : 0 < dv) (l m : ℝ) (hl : l ≤ 1) (hm : m ≤ 1)
    (hlm : 1 ≤ l + m) :
    mkPt (x + l * du) (y + m * dv) ∈ (cellUpp x y du dv hu hv).carrier := by
  -- reflect: the upper triangle is the lower one of the reversed orientation; use weights directly
  have hD : det3 (x + du) (y + dv) (x + du) y x (y + dv) < 0 := by
    simp only [det3]; nlinarith [mul_pos hu hv]
  set T := cellUpp x y du dv hu hv with hT
  refine Erdos634.CertGeom.mem_carrier_of_combo T _ ![l + m - 1, 1 - m, 1 - l] ?_ ?_ ?_
  · show (l + m - 1) + (1 - m) + (1 - l) = 1
    ring
  · intro k
    have htri : ∀ y : Fin 3, y = 0 ∨ y = 1 ∨ y = 2 := by decide
    rcases htri k with rfl | rfl | rfl <;> simp <;> linarith
  · obtain ⟨h0, h1, h2⟩ := cellUpp_pts x y du dv hu hv
    show mkPt (x + l * du) (y + m * dv) = (l + m - 1) • T.pts 0 + (1 - m) • T.pts 1 + (1 - l) • T.pts 2
    rw [h0, h1, h2]
    ext i
    fin_cases i <;> simp [mkPt] <;> ring


theorem sepX {S U : Set Plane} (c : ℝ) (hS : ∀ z ∈ S, z 0 ≤ c) (hU : ∀ z ∈ U, c ≤ z 0) :
    Disjoint (interior S) (interior U) :=
  disjoint_interior_of_sep (coordFun 1 0 0) (coordFun_linear_ne_zero 0 (Or.inl one_ne_zero)) c
    (fun z hz => by simpa using hS z hz) (fun z hz => by simpa using hU z hz)

theorem sepY {S U : Set Plane} (c : ℝ) (hS : ∀ z ∈ S, z 1 ≤ c) (hU : ∀ z ∈ U, c ≤ z 1) :
    Disjoint (interior S) (interior U) :=
  disjoint_interior_of_sep (coordFun 0 1 0) (coordFun_linear_ne_zero 0 (Or.inr one_ne_zero)) c
    (fun z hz => by simpa using hS z hz) (fun z hz => by simpa using hU z hz)

/-- The grid tile of cell `(i, j)`, lower (`false`) or upper (`true`). -/
noncomputable def gridTile (s0 t0 du dv : ℝ) (hu : 0 < du) (hv : 0 < dv) (i j : ℕ) (b : Bool) : Tri :=
  cellTri (s0 + i * du) (t0 + j * dv) du dv hu hv b

theorem exists_index (n : ℕ) (hn : 0 < n) (u : ℝ) (h0 : 0 ≤ u) (h1 : u ≤ n) :
    ∃ i : ℕ, i < n ∧ (i : ℝ) ≤ u ∧ u ≤ i + 1 := by
  refine ⟨min ⌊u⌋₊ (n - 1), by omega, ?_, ?_⟩
  · exact le_trans (by exact_mod_cast min_le_left _ _) (Nat.floor_le h0)
  · by_cases h : ⌊u⌋₊ ≤ n - 1
    · rw [min_eq_left h]; exact (Nat.lt_floor_add_one u).le
    · rw [min_eq_right (by omega)]
      have : ((n - 1 : ℕ) : ℝ) + 1 = n := by
        rw [Nat.cast_sub (by omega)]; push_cast; ring
      linarith

theorem grid_cover (s0 t0 du dv : ℝ) (hu : 0 < du) (hv : 0 < dv) (n m : ℕ) (hn : 0 < n) (hm : 0 < m)
    (z : Plane) (hz : z ∈ rectSet s0 (s0 + n * du) t0 (t0 + m * dv)) :
    ∃ (i : Fin n) (j : Fin m) (b : Bool), z ∈ (gridTile s0 t0 du dv hu hv i j b).carrier := by
  obtain ⟨hz1, hz2, hz3, hz4⟩ := hz
  obtain ⟨i, hi, hi1, hi2⟩ := exists_index n hn ((z 0 - s0) / du) (by positivity) (by
    rw [div_le_iff₀ hu]; linarith)
  obtain ⟨j, hj, hj1, hj2⟩ := exists_index m hm ((z 1 - t0) / dv) (by positivity) (by
    rw [div_le_iff₀ hv]; linarith)
  set l := (z 0 - s0) / du - i with hl
  set mm := (z 1 - t0) / dv - j with hmm
  have hzc : z = mkPt (s0 + i * du + l * du) (t0 + j * dv + mm * dv) := by
    have e0 : s0 + i * du + l * du = z 0 := by
      rw [hl]; field_simp; ring
    have e1 : t0 + j * dv + mm * dv = z 1 := by
      rw [hmm]; field_simp; ring
    rw [e0, e1, mkPt_self]
  have hl0 : 0 ≤ l := by rw [hl]; linarith
  have hl1 : l ≤ 1 := by rw [hl]; linarith
  have hm0 : 0 ≤ mm := by rw [hmm]; linarith
  have hm1 : mm ≤ 1 := by rw [hmm]; linarith
  refine ⟨⟨i, hi⟩, ⟨j, hj⟩, ?_⟩
  by_cases hlm : l + mm ≤ 1
  · refine ⟨false, ?_⟩
    rw [hzc]
    exact low_mem (s0 + i * du) (t0 + j * dv) du dv hu hv l mm hl0 hm0 hlm
  · refine ⟨true, ?_⟩
    rw [hzc]
    exact upp_mem (s0 + i * du) (t0 + j * dv) du dv hu hv l mm hl1 hm1 (by linarith)

theorem grid_disjoint (s0 t0 du dv : ℝ) (hu : 0 < du) (hv : 0 < dv) (i j i' j' : ℕ) (b b' : Bool)
    (hne : ¬ (i = i' ∧ j = j' ∧ b = b')) :
    Disjoint (interior (gridTile s0 t0 du dv hu hv i j b).carrier)
      (interior (gridTile s0 t0 du dv hu hv i' j' b').carrier) := by
  have hb1 := cellTri_sub_rect (s0 + i * du) (t0 + j * dv) du dv hu hv b
  have hb2 := cellTri_sub_rect (s0 + i' * du) (t0 + j' * dv) du dv hu hv b'
  unfold gridTile
  by_cases hi : i = i'
  · subst hi
    by_cases hj : j = j'
    · subst hj
      have hbb : b ≠ b' := fun h => hne ⟨rfl, rfl, h⟩
      -- lower vs upper in one cell
      have key : ∀ x y : ℝ, Disjoint (interior (cellLow x y du dv hu hv).carrier)
          (interior (cellUpp x y du dv hu hv).carrier) := by
        intro x y
        refine sep_tri (coordFun (1 / du) (1 / dv) (-x / du - y / dv))
          (coordFun_linear_ne_zero _ (Or.inl (by positivity))) 1 ?_ ?_
        · intro k
          obtain ⟨h0, h1, h2⟩ := cellLow_pts x y du dv hu hv
          have htri : ∀ y : Fin 3, y = 0 ∨ y = 1 ∨ y = 2 := by decide
          rcases htri k with rfl | rfl | rfl
          · rw [h0]; simp; field_simp; nlinarith [mul_pos hu hv]
          · rw [h1]; simp; field_simp; nlinarith [mul_pos hu hv]
          · rw [h2]; simp; field_simp; nlinarith [mul_pos hu hv]
        · intro k
          obtain ⟨h0, h1, h2⟩ := cellUpp_pts x y du dv hu hv
          have htri : ∀ y : Fin 3, y = 0 ∨ y = 1 ∨ y = 2 := by decide
          rcases htri k with rfl | rfl | rfl
          · rw [h0]; simp; field_simp; nlinarith [mul_pos hu hv]
          · rw [h1]; simp; field_simp; nlinarith [mul_pos hu hv]
          · rw [h2]; simp; field_simp; nlinarith [mul_pos hu hv]
      cases b <;> cases b'
      · exact absurd rfl hbb
      · simpa [cellTri] using key _ _
      · simpa [cellTri] using (key _ _).symm
      · exact absurd rfl hbb
    · rcases lt_or_gt_of_ne hj with hjj | hjj
      · refine sepY (t0 + (j + 1) * dv) ?_ ?_
        · intro z hz; have := (hb1 hz).2.2.2; linarith
        · intro z hz; have := (hb2 hz).2.2.1
          have : (j : ℝ) + 1 ≤ j' := by exact_mod_cast hjj
          nlinarith
      · refine Disjoint.symm (sepY (t0 + (j' + 1) * dv) ?_ ?_)
        · intro z hz; have := (hb2 hz).2.2.2; linarith
        · intro z hz; have := (hb1 hz).2.2.1
          have : (j' : ℝ) + 1 ≤ j := by exact_mod_cast hjj
          nlinarith
  · rcases lt_or_gt_of_ne hi with hii | hii
    · refine sepX (s0 + (i + 1) * du) ?_ ?_
      · intro z hz; have := (hb1 hz).2.1; linarith
      · intro z hz; have := (hb2 hz).1
        have : (i : ℝ) + 1 ≤ i' := by exact_mod_cast hii
        nlinarith
    · refine Disjoint.symm (sepX (s0 + (i' + 1) * du) ?_ ?_)
      · intro z hz; have := (hb2 hz).2.1; linarith
      · intro z hz; have := (hb1 hz).1
        have : (i' : ℝ) + 1 ≤ i := by exact_mod_cast hii
        nlinarith

end Erdos634.LaczL22
