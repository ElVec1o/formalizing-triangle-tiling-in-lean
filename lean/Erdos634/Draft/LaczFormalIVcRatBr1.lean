-- Draft/LaczFormalIVcRatBr1.lean -- Laczkovich DCG 48 (2012), Sect. 8.3 (Subcase IVc, rational branch): BRIDGE `VWTiling.ofPolyTiling`, stage Br1 (tile-free plane lemmas).
--   `tri_mem_abc`: barycentric description of `Tri.carrier` in ANY vertex order (distinct a b c : Fin 3).
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 8.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIVcRatB4

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement Erdos634.CertCoord

namespace Erdos634.Draft.LaczFormal.RG

/-- Barycentric description of a triangle, vertex order 0,1,2. -/
theorem tri_mem_012 (T : Tri) (x : Plane) :
    x ∈ T.carrier ↔ ∃ l m n : ℝ, 0 ≤ l ∧ 0 ≤ m ∧ 0 ≤ n ∧ l + m + n = 1 ∧
      x 0 = l * (T.pts 0) 0 + m * (T.pts 1) 0 + n * (T.pts 2) 0 ∧ x 1 = l * (T.pts 0) 1 + m * (T.pts 1) 1 + n * (T.pts 2) 1 := by
  constructor
  · intro hx
    have hsub : T.carrier ⊆ {y : Plane | ∃ l m n : ℝ, 0 ≤ l ∧ 0 ≤ m ∧ 0 ≤ n ∧ l + m + n = 1 ∧
        y 0 = l * (T.pts 0) 0 + m * (T.pts 1) 0 + n * (T.pts 2) 0 ∧ y 1 = l * (T.pts 0) 1 + m * (T.pts 1) 1 + n * (T.pts 2) 1} := by
      apply convexHull_min
      · rintro _ ⟨k, rfl⟩
        fin_cases k
        · exact ⟨1, 0, 0, by norm_num, le_rfl, le_rfl, by norm_num, by simp, by simp⟩
        · exact ⟨0, 1, 0, le_rfl, by norm_num, le_rfl, by norm_num, by simp, by simp⟩
        · exact ⟨0, 0, 1, le_rfl, le_rfl, by norm_num, by norm_num, by simp, by simp⟩
      · intro y hy z hz a b ha hb hab
        obtain ⟨l, m, n, hl, hm, hn, hs, hy0, hy1⟩ := hy
        obtain ⟨l', m', n', hl', hm', hn', hs', hz0, hz1⟩ := hz
        refine ⟨a * l + b * l', a * m + b * m', a * n + b * n', by positivity, by positivity, by positivity, by nlinarith, ?_, ?_⟩
        · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
          rw [hy0, hz0]; ring
        · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
          rw [hy1, hz1]; ring
    exact hsub hx
  · rintro ⟨l, m, n, hl, hm, hn, hs, h0, h1⟩
    refine Erdos634.CertGeom.mem_carrier_of_combo _ x ![l, m, n] (by simpa using hs) ?_ ?_
    · intro k; fin_cases k <;> simpa
    · ext j
      fin_cases j
      · simpa using h0
      · simpa using h1

/-- Barycentric description of a triangle in any vertex order. -/
theorem tri_mem_abc (T : Tri) {a b c : Fin 3} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (x : Plane) :
    x ∈ T.carrier ↔ ∃ l m n : ℝ, 0 ≤ l ∧ 0 ≤ m ∧ 0 ≤ n ∧ l + m + n = 1 ∧
      x 0 = l * (T.pts a) 0 + m * (T.pts b) 0 + n * (T.pts c) 0 ∧ x 1 = l * (T.pts a) 1 + m * (T.pts b) 1 + n * (T.pts c) 1 := by
  rw [tri_mem_012]
  fin_cases a <;> fin_cases b <;> fin_cases c <;> simp at hab hac hbc <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;>
  constructor <;> rintro ⟨l, m, n, hl, hm, hn, hs, h0, h1⟩ <;>
  first
  | exact ⟨l, m, n, hl, hm, hn, by linarith, by linarith, by linarith⟩
  | exact ⟨l, n, m, hl, hn, hm, by linarith, by linarith, by linarith⟩
  | exact ⟨m, l, n, hm, hl, hn, by linarith, by linarith, by linarith⟩
  | exact ⟨m, n, l, hm, hn, hl, by linarith, by linarith, by linarith⟩
  | exact ⟨n, l, m, hn, hl, hm, by linarith, by linarith, by linarith⟩
  | exact ⟨n, m, l, hn, hm, hl, by linarith, by linarith, by linarith⟩


/-- `x` lies in the triangle with vertices `A B C` (barycentric form). -/
def H3 (A B C x : Plane) : Prop :=
  ∃ l m n : ℝ, 0 ≤ l ∧ 0 ≤ m ∧ 0 ≤ n ∧ l + m + n = 1 ∧ x 0 = l * A 0 + m * B 0 + n * C 0 ∧ x 1 = l * A 1 + m * B 1 + n * C 1

theorem mkPt_self (P : Plane) : mkPt (P 0) (P 1) = P := by
  ext i; fin_cases i <;> simp [mkPt]

/-- Lagrange: the determinant of two vectors of length `b` with scalar product `b^2/2` is nonzero. -/
theorem det_ne_of_equi {b : ℝ} (hb : 0 < b) {s0 s1 w0 w1 : ℝ} (hs : s0 ^ 2 + s1 ^ 2 = b ^ 2) (hw : w0 ^ 2 + w1 ^ 2 = b ^ 2)
    (hsw : s0 * w0 + s1 * w1 = b ^ 2 / 2) : s0 * w1 - s1 * w0 ≠ 0 := by
  intro h
  have l : (s0 * w1 - s1 * w0) ^ 2 + (s0 * w0 + s1 * w1) ^ 2 = (s0 ^ 2 + s1 ^ 2) * (w0 ^ 2 + w1 ^ 2) := by ring
  rw [h, hsw, hs, hw] at l
  have : 0 < b ^ 4 := by positivity
  nlinarith

/-- **Kite from a mirror pair.**  `R` is the midpoint of `Q Q'`, the three sides `PQ, PQ', QQ'` have length `2b`:
the union of the triangles `R P Q` and `R P Q'` is a `KiteData b` with apex `P` and base midpoint `R`. -/
theorem kite_of_H3 {b : ℝ} (hb : 0 < b) (P Q Q' R : Plane) (hR0 : 2 * R 0 = Q 0 + Q' 0) (hR1 : 2 * R 1 = Q 1 + Q' 1)
    (hQP : (Q 0 - P 0) ^ 2 + (Q 1 - P 1) ^ 2 = (2 * b) ^ 2) (hQ'P : (Q' 0 - P 0) ^ 2 + (Q' 1 - P 1) ^ 2 = (2 * b) ^ 2)
    (hQQ' : (Q 0 - Q' 0) ^ 2 + (Q 1 - Q' 1) ^ 2 = (2 * b) ^ 2) :
    ∃ K : KiteData b, K.V = P ∧ K.W = R ∧ ∀ x, x ∈ K.set ↔ (H3 R P Q x ∨ H3 R P Q' x) := by
  have hs : ((Q 0 - P 0) / 2) ^ 2 + ((Q 1 - P 1) / 2) ^ 2 = b ^ 2 := by nlinarith
  have hw : ((Q' 0 - P 0) / 2) ^ 2 + ((Q' 1 - P 1) / 2) ^ 2 = b ^ 2 := by nlinarith
  have hsw : ((Q 0 - P 0) / 2) * ((Q' 0 - P 0) / 2) + ((Q 1 - P 1) / 2) * ((Q' 1 - P 1) / 2) = b ^ 2 / 2 := by nlinarith
  have hD := det_ne_of_equi hb hs hw hsw
  refine ⟨⟨P 0, P 1, (Q 0 - P 0) / 2, (Q 1 - P 1) / 2, (Q' 0 - P 0) / 2, (Q' 1 - P 1) / 2, hD, hs, hw, hsw⟩, mkPt_self P, ?_, ?_⟩
  · rw [← mkPt_self R]
    show mkPt _ _ = mkPt _ _
    congr 1 <;> linarith
  · intro x
    have hmem : x ∈ (KiteData.mk (b := b) (P 0) (P 1) ((Q 0 - P 0) / 2) ((Q 1 - P 1) / 2) ((Q' 0 - P 0) / 2) ((Q' 1 - P 1) / 2) hD hs hw hsw).set ↔
        ∃ l m : ℝ, 0 ≤ l ∧ 0 ≤ m ∧ l + m ≤ 1 ∧ x 0 = P 0 + l * (2 * ((Q 0 - P 0) / 2)) + m * (2 * ((Q' 0 - P 0) / 2)) ∧
          x 1 = P 1 + l * (2 * ((Q 1 - P 1) / 2)) + m * (2 * ((Q' 1 - P 1) / 2)) :=
      ct_carrier (hD4 hD) x
    rw [hmem]
    have e0 : R 0 = (Q 0 + Q' 0) / 2 := by linarith
    have e1 : R 1 = (Q 1 + Q' 1) / 2 := by linarith
    unfold H3
    rw [e0, e1]
    constructor
    · rintro ⟨l, m, hl, hm, hlm, h0, h1⟩
      rcases le_total m l with hml | hlm'
      · left
        refine ⟨2 * m, 1 - l - m, l - m, by linarith, by linarith, by linarith, by ring, ?_, ?_⟩
        · linear_combination h0
        · linear_combination h1
      · right
        refine ⟨2 * l, 1 - l - m, m - l, by linarith, by linarith, by linarith, by ring, ?_, ?_⟩
        · linear_combination h0
        · linear_combination h1
    · rintro (⟨l, m, n, hl, hm, hn, hs', h0, h1⟩ | ⟨l, m, n, hl, hm, hn, hs', h0, h1⟩)
      · refine ⟨n + l / 2, l / 2, by linarith, by linarith, by linarith, ?_, ?_⟩
        · linear_combination h0 + P 0 * hs'
        · linear_combination h1 + P 1 * hs'
      · refine ⟨l / 2, n + l / 2, by linarith, by linarith, by linarith, ?_, ?_⟩
        · linear_combination h0 + P 0 * hs'
        · linear_combination h1 + P 1 * hs'


/-- Set version of `CertGeom.interiors_disjoint_of_separating`. -/
theorem disj_of_sep_sets {S U : Set Plane} (f : Plane →ᵃ[ℝ] ℝ) (hf : f.linear ≠ 0)
    (c : ℝ) (h1 : ∀ x ∈ S, f x ≤ c) (h2 : ∀ x ∈ U, c ≤ f x) :
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

/-- Separation by a coordinate functional, for sets. -/
theorem sep_coords_sets {S U : Set Plane} {v0 v1 s0 s1 w0 w1 : ℝ} (hD : s0 * w1 - s1 * w0 ≠ 0) (p q c : ℝ) (hpq : p ≠ 0 ∨ q ≠ 0)
    (h1 : ∀ x ∈ S, ∃ a b : ℝ, x 0 = v0 + a * s0 + b * w0 ∧ x 1 = v1 + a * s1 + b * w1 ∧ p * a + q * b ≤ c)
    (h2 : ∀ x ∈ U, ∃ a b : ℝ, x 0 = v0 + a * s0 + b * w0 ∧ x 1 = v1 + a * s1 + b * w1 ∧ c ≤ p * a + q * b) :
    Disjoint (interior S) (interior U) := by
  set D := s0 * w1 - s1 * w0 with hDdef
  set A := (p * w1 - q * s1) / D with hA
  set B := (q * s0 - p * w0) / D with hB
  have eS : A * s0 + B * s1 = p := by rw [hA, hB]; field_simp; ring
  have eW : A * w0 + B * w1 = q := by rw [hA, hB]; field_simp; ring
  have key : ∀ a b : ℝ, A * (v0 + a * s0 + b * w0) + B * (v1 + a * s1 + b * w1) = A * v0 + B * v1 + a * p + b * q := by
    intro a b
    have : A * (v0 + a * s0 + b * w0) + B * (v1 + a * s1 + b * w1) = A * v0 + B * v1 + a * (A * s0 + B * s1) + b * (A * w0 + B * w1) := by ring
    rw [this, eS, eW]
  have hf : (linF A B).linear ≠ 0 := by
    rcases hpq with h | h
    · exact linF_ne (c := s0) (d := s1) (by rw [eS]; exact h)
    · exact linF_ne (c := w0) (d := w1) (by rw [eW]; exact h)
  refine disj_of_sep_sets (linF A B) hf (A * v0 + B * v1 + c) ?_ ?_
  · intro x hx
    obtain ⟨a, b, h0, h1', hle⟩ := h1 x hx
    rw [linF_apply, h0, h1', key]; nlinarith
  · intro x hx
    obtain ⟨a, b, h0, h1', hle⟩ := h2 x hx
    rw [linF_apply, h0, h1', key]; nlinarith

/-- The interior of a union of two sets that are closures of their interiors misses the interior of `C` when each part does. -/
theorem interior_union_disj {A B C : Set Plane} (hA : A ⊆ closure (interior A)) (hB : B ⊆ closure (interior B))
    (hAC : Disjoint (interior A) (interior C)) (hBC : Disjoint (interior B) (interior C)) :
    Disjoint (interior (A ∪ B)) (interior C) := by
  rw [Set.disjoint_left]
  intro x hx hxC
  have hU : IsOpen (interior (A ∪ B) ∩ interior C) := isOpen_interior.inter isOpen_interior
  have hxU : x ∈ interior (A ∪ B) ∩ interior C := ⟨hx, hxC⟩
  have hxAB : x ∈ A ∪ B := interior_subset hx
  rcases hxAB with h | h
  · obtain ⟨y, hyU, hyA⟩ := mem_closure_iff.1 (hA h) _ hU hxU
    exact Set.disjoint_left.1 hAC hyA hyU.2
  · obtain ⟨y, hyU, hyB⟩ := mem_closure_iff.1 (hB h) _ hU hxU
    exact Set.disjoint_left.1 hBC hyB hyU.2

/-- A triangle is the closure of its interior. -/
theorem tri_closure_interior (T : Tri) : T.carrier ⊆ closure (interior T.carrier) := by
  have h := T.convex.closure_interior_eq_closure_of_nonempty_interior T.interior_nonempty
  rw [h, T.isCompact.isClosed.closure_eq]


/-- **Parallelogram from a point-symmetric pair.**  `W' = A + B - W`, `|AW| = b`, `|BW| = 2b`, `(A-W).(B-W) = b^2`:
the union of the triangles `A B W` and `A B W'` is the union of two rhombi of side `b` (`x = W` and `x = W + (B-W)/2`, sides `A-W`, `(B-W)/2`),
with disjoint interiors. -/
theorem rhombs_of_H3 {b : ℝ} (hb : 0 < b) (W A B W' : Plane) (hW0 : W' 0 = A 0 + B 0 - W 0) (hW1 : W' 1 = A 1 + B 1 - W 1)
    (hA : (A 0 - W 0) ^ 2 + (A 1 - W 1) ^ 2 = b ^ 2) (hB : (B 0 - W 0) ^ 2 + (B 1 - W 1) ^ 2 = (2 * b) ^ 2)
    (hAB : (A 0 - W 0) * (B 0 - W 0) + (A 1 - W 1) * (B 1 - W 1) = b ^ 2) :
    ∃ R1 R2 : RhombData b, Disjoint (interior R1.set) (interior R2.set) ∧
      ∀ x, (x ∈ R1.set ∨ x ∈ R2.set) ↔ (H3 A B W x ∨ H3 A B W' x) := by
  have hs : (A 0 - W 0) ^ 2 + (A 1 - W 1) ^ 2 = b ^ 2 := hA
  have hw : ((B 0 - W 0) / 2) ^ 2 + ((B 1 - W 1) / 2) ^ 2 = b ^ 2 := by nlinarith
  have hsw : (A 0 - W 0) * ((B 0 - W 0) / 2) + (A 1 - W 1) * ((B 1 - W 1) / 2) = b ^ 2 / 2 := by nlinarith
  have hD := det_ne_of_equi hb hs hw hsw
  refine ⟨⟨W 0, W 1, A 0 - W 0, A 1 - W 1, (B 0 - W 0) / 2, (B 1 - W 1) / 2, hD, hs, hw, hsw⟩,
    ⟨W 0 + (B 0 - W 0) / 2, W 1 + (B 1 - W 1) / 2, A 0 - W 0, A 1 - W 1, (B 0 - W 0) / 2, (B 1 - W 1) / 2, hD, hs, hw, hsw⟩, ?_, ?_⟩
  · refine sep_coords_sets (v0 := W 0) (v1 := W 1) (s0 := A 0 - W 0) (s1 := A 1 - W 1) (w0 := (B 0 - W 0) / 2) (w1 := (B 1 - W 1) / 2)
      hD 0 1 1 (Or.inr one_ne_zero) ?_ ?_
    · intro x hx
      obtain ⟨l, m, hl, hl1, hm, hm1, h0, h1⟩ := hx
      exact ⟨l, m, h0, h1, by linarith⟩
    · intro x hx
      obtain ⟨l, m, hl, hl1, hm, hm1, h0, h1⟩ := hx
      exact ⟨l, m + 1, by rw [h0]; ring, by rw [h1]; ring, by linarith⟩
  · intro x
    have m1 : ∀ x : Plane, x ∈ (RhombData.mk (b := b) (W 0) (W 1) (A 0 - W 0) (A 1 - W 1) ((B 0 - W 0) / 2) ((B 1 - W 1) / 2) hD hs hw hsw).set ↔
        ∃ l m : ℝ, 0 ≤ l ∧ l ≤ 1 ∧ 0 ≤ m ∧ m ≤ 1 ∧ x 0 = W 0 + l * (A 0 - W 0) + m * ((B 0 - W 0) / 2) ∧
          x 1 = W 1 + l * (A 1 - W 1) + m * ((B 1 - W 1) / 2) := fun x => Iff.rfl
    have m2 : ∀ x : Plane, x ∈ (RhombData.mk (b := b) (W 0 + (B 0 - W 0) / 2) (W 1 + (B 1 - W 1) / 2) (A 0 - W 0) (A 1 - W 1) ((B 0 - W 0) / 2) ((B 1 - W 1) / 2) hD hs hw hsw).set ↔
        ∃ l m : ℝ, 0 ≤ l ∧ l ≤ 1 ∧ 0 ≤ m ∧ m ≤ 1 ∧ x 0 = W 0 + (B 0 - W 0) / 2 + l * (A 0 - W 0) + m * ((B 0 - W 0) / 2) ∧
          x 1 = W 1 + (B 1 - W 1) / 2 + l * (A 1 - W 1) + m * ((B 1 - W 1) / 2) := fun x => Iff.rfl
    rw [m1, m2]
    unfold H3
    rw [hW0, hW1]
    constructor
    · rintro (⟨l, m, hl, hl1, hm, hm1, h0, h1⟩ | ⟨l, m, hl, hl1, hm, hm1, h0, h1⟩)
      · -- u = l, v = m/2
        rcases le_total (l + m / 2) 1 with h | h
        · left
          refine ⟨l, m / 2, 1 - l - m / 2, hl, by linarith, by linarith, by ring, ?_, ?_⟩
          · linear_combination h0
          · linear_combination h1
        · right
          refine ⟨1 - m / 2, 1 - l, l + m / 2 - 1, by linarith, by linarith, by linarith, by ring, ?_, ?_⟩
          · linear_combination h0
          · linear_combination h1
      · -- u = l, v = (m+1)/2
        rcases le_total (l + (m + 1) / 2) 1 with h | h
        · left
          refine ⟨l, (m + 1) / 2, 1 - l - (m + 1) / 2, hl, by linarith, by linarith, by ring, ?_, ?_⟩
          · linear_combination h0
          · linear_combination h1
        · right
          refine ⟨1 - (m + 1) / 2, 1 - l, l + (m + 1) / 2 - 1, by linarith, by linarith, by linarith, by ring, ?_, ?_⟩
          · linear_combination h0
          · linear_combination h1
    · rintro (⟨l, m, n, hl, hm, hn, hs', h0, h1⟩ | ⟨l, m, n, hl, hm, hn, hs', h0, h1⟩)
      · -- x = W + l (A-W) + m (B-W), l + m <= 1
        rcases le_total m (1 / 2) with h | h
        · left
          refine ⟨l, 2 * m, hl, by linarith, by linarith, by linarith, ?_, ?_⟩
          · linear_combination h0 + W 0 * hs'
          · linear_combination h1 + W 1 * hs'
        · right
          refine ⟨l, 2 * m - 1, hl, by linarith, by linarith, by linarith, ?_, ?_⟩
          · linear_combination h0 + W 0 * hs'
          · linear_combination h1 + W 1 * hs'
      · -- x = l A + m B + n (A + B - W): u = l + n, v = m + n
        rcases le_total (m + n) (1 / 2) with h | h
        · left
          refine ⟨l + n, 2 * (m + n), by linarith, by linarith, by linarith, by linarith, ?_, ?_⟩
          · linear_combination h0 + W 0 * hs'
          · linear_combination h1 + W 1 * hs'
        · right
          refine ⟨l + n, 2 * (m + n) - 1, by linarith, by linarith, by linarith, by linarith, ?_, ?_⟩
          · linear_combination h0 + W 0 * hs'
          · linear_combination h1 + W 1 * hs'


/-- Witness (b = 1): kite P = (0,0), Q = (2,0), Q' = (1, sqrt 3), R = (3/2, sqrt 3 / 2). -/
theorem kite_of_H3_witness : ∃ K : KiteData 1, K.V = mkPt 0 0 := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  obtain ⟨K, hK, -, -⟩ := kite_of_H3 (b := 1) one_pos (mkPt 0 0) (mkPt 2 0) (mkPt 1 (Real.sqrt 3)) (mkPt (3 / 2) (Real.sqrt 3 / 2))
    (by simp only [mkPt_zero]; norm_num) (by simp only [mkPt_one]; ring) (by simp [mkPt_zero, mkPt_one])
    (by simp [mkPt_zero, mkPt_one]; nlinarith) (by simp [mkPt_zero, mkPt_one]; nlinarith)
  exact ⟨K, hK⟩

/-- Control: with `Q'` = Q the base has length 0, so the hypothesis `|QQ'| = 2b` fails. -/
theorem kite_of_H3_control : ¬ (((mkPt 2 0 : Plane) 0 - (mkPt 2 0 : Plane) 0) ^ 2 + ((mkPt 2 0 : Plane) 1 - (mkPt 2 0 : Plane) 1) ^ 2 = (2 * (1 : ℝ)) ^ 2) := by
  simp; norm_num

/-- Witness (b = 1): W = (0,0), A = (1,0), B = (1, sqrt 3). -/
theorem rhombs_of_H3_witness : ∃ R1 R2 : RhombData 1, Disjoint (interior R1.set) (interior R2.set) := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  obtain ⟨R1, R2, hd, -⟩ := rhombs_of_H3 (b := 1) one_pos (mkPt 0 0) (mkPt 1 0) (mkPt 1 (Real.sqrt 3)) (mkPt 2 (Real.sqrt 3))
    (by simp [mkPt_zero]; norm_num) (by simp [mkPt_one]) (by simp [mkPt_zero, mkPt_one])
    (by simp [mkPt_zero, mkPt_one]; nlinarith) (by simp [mkPt_zero, mkPt_one])
  exact ⟨R1, R2, hd⟩

#print axioms Erdos634.Draft.LaczFormal.RG.tri_mem_abc
#print axioms Erdos634.Draft.LaczFormal.RG.kite_of_H3
#print axioms Erdos634.Draft.LaczFormal.RG.kite_of_H3_witness
#print axioms Erdos634.Draft.LaczFormal.RG.kite_of_H3_control
#print axioms Erdos634.Draft.LaczFormal.RG.rhombs_of_H3
#print axioms Erdos634.Draft.LaczFormal.RG.rhombs_of_H3_witness
#print axioms Erdos634.Draft.LaczFormal.RG.interior_union_disj
#print axioms Erdos634.Draft.LaczFormal.RG.tri_closure_interior

end Erdos634.Draft.LaczFormal.RG
