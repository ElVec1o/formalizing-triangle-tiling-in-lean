import Erdos634.Draft.ZhangProp3

/-!
# Zhang Theorem 4 (arXiv 2512.22696v4): equilateral triangles of side `m a b` are tiled by `(a,b,c)`

Definitions.  `Tri3 0 0 X` (see `ZhangPara`) is the equilateral triangle with vertices
`(0,0), (X,0), (X/2, X√3/2)`; `tri3_eq_carrier` identifies it with the convex hull.
"`X` is equiconstructible by `(a,b,c)`" (Zhang §3.1): the triangle `(X,X,X)` tiles into triangles
congruent to `(a,b,c)`.  Here the tile `(a,b,c)` is `Rmodel` (sides `c,a,b`, angle `2π/3` between
`a` and `b`, which is forced by `c² = a²+b²+ab`), and `EquiConstr a b X n` says the triangle carries
a `CongruentRegionDissection n` with model `Rmodel`.  By area `n = X²/(ab)`.

`zhang_thm4_rst`: for `r,s,t` with each `c² < ·ab + a + b` the triangle of side `(r+s+t)ab` is
`EquiConstr` with `(r+s+t)²ab` tiles (three isosceles trapezoids `Tz(rab,sab)`, `Tz(sab,tab)`,
`Tz(tab,rab)` in a pinwheel, the second and third rotated by `2π/3`, `4π/3`; Zhang's Fig. 5).
`zhang_thm4`: `m ≥ 3 M₀` with `M₀ = ⌊(c²−a−b)/(ab)⌋ + 1`.  Remark on Zhang's constant:
his `M = 3⌈(c²−a−b)/(ab)⌉` equals `3 M₀` unless `ab ∣ c² − a − b`; the proof needs strict
`x > c²−a−b`, hence `M₀` (and his proof's "`r,s,t ≥ M`" should read `≥ M/3`).  UNAUDITED.
Credit Zhang (arXiv 2512.22696), Beeson, Beeson-Rosu, Laczkovich.
-/

namespace Erdos634.ZhangThm4

open Erdos634.Geometry Erdos634.CertCoord Erdos634.CertGeom Erdos634.RegionDissection
  Erdos634.GlueCut Erdos634.SssCongruent Erdos634.ZhangL1 Erdos634.ZhangPara
  Erdos634.ZhangProp3 Erdos634.TranslateDissection

theorem pext {u w : Plane} (h0 : u 0 = w 0) (h1 : u 1 = w 1) : u = w := by
  ext i; fin_cases i <;> simpa

/-! ### Rotation by `2π/3` about a point -/

noncomputable def rotLin : Plane →ₗ[ℝ] Plane where
  toFun p := mkPt (-(p 0) / 2 - zs * (p 1) / 2) (zs * (p 0) / 2 - (p 1) / 2)
  map_add' := by intro p q; apply pext <;> simp <;> ring
  map_smul' := by intro r p; apply pext <;> simp <;> ring

noncomputable def rotLin' : Plane →ₗ[ℝ] Plane where
  toFun p := mkPt (-(p 0) / 2 + zs * (p 1) / 2) (-(zs * (p 0)) / 2 - (p 1) / 2)
  map_add' := by intro p q; apply pext <;> simp <;> ring
  map_smul' := by intro r p; apply pext <;> simp <;> ring

noncomputable def rotEquiv : Plane ≃ₗ[ℝ] Plane :=
  LinearEquiv.ofLinear rotLin rotLin'
    (by
      apply LinearMap.ext; intro p
      apply pext
      · simp [rotLin, rotLin']; linear_combination (p 0 / 4) * zs_sq
      · simp [rotLin, rotLin']; linear_combination (p 1 / 4) * zs_sq)
    (by
      apply LinearMap.ext; intro p
      apply pext
      · simp [rotLin, rotLin']; linear_combination (p 0 / 4) * zs_sq
      · simp [rotLin, rotLin']; linear_combination (p 1 / 4) * zs_sq)

theorem rotEquiv_apply (p : Plane) :
    rotEquiv p = mkPt (-(p 0) / 2 - zs * (p 1) / 2) (zs * (p 0) / 2 - (p 1) / 2) := rfl

noncomputable def rotIso : Plane ≃ₗᵢ[ℝ] Plane :=
  rotEquiv.isometryOfInner (by
    intro x y
    simp only [rotEquiv_apply, PiLp.inner_apply, Fin.sum_univ_two, mkPt_zero, mkPt_one,
      RCLike.inner_apply, conj_trivial]
    have hs := zs_sq
    linear_combination ((y 0 * x 0 + y 1 * x 1) / 4) * hs)

theorem rotIso_apply (p : Plane) :
    rotIso p = mkPt (-(p 0) / 2 - zs * (p 1) / 2) (zs * (p 0) / 2 - (p 1) / 2) := by
  simp only [rotIso, LinearEquiv.coe_isometryOfInner, rotEquiv_apply]

/-- Rotation by `2π/3` about `(cx, cy)`. -/
noncomputable def rotE (cx cy : ℝ) : Plane ≃ᵃⁱ[ℝ] Plane :=
  AffineIsometryEquiv.mk' (fun q => mkPt cx cy + rotIso (q - mkPt cx cy)) rotIso (mkPt cx cy) (by
    intro p
    simp; abel)

theorem rotE_apply (cx cy : ℝ) (q : Plane) : rotE cx cy q = mkPt cx cy + rotIso (q - mkPt cx cy) := by
  simp [rotE]

/-- In the frame at `c`, the rotation is `(u,v) ↦ (-u-v, u)`. -/
theorem rotE_ptP (cx cy u v : ℝ) :
    rotE cx cy (ptP cx cy u v) = ptP cx cy (-u - v) u := by
  have hs := zs_sq
  rw [rotE_apply, rotIso_apply]
  apply pext
  · simp [ptP, shx, shy]
    linear_combination (-v / 4) * hs
  · simp [ptP, shx, shy]; ring

theorem image_rot (cx cy : ℝ) (P : ℝ → ℝ → Prop) :
    (rotE cx cy) '' {q | P (uu cx cy q) (vv cx cy q)}
      = {q | P (vv cx cy q) (-uu cx cy q - vv cx cy q)} := by
  ext q
  constructor
  · rintro ⟨r, hr, rfl⟩
    have e := rotE_ptP cx cy (uu cx cy r) (vv cx cy r)
    rw [← eq_ptP] at e
    simp only [Set.mem_setOf_eq] at hr ⊢
    rw [e, uu_ptP, vv_ptP]
    convert hr using 2; ring
  · intro hq
    refine ⟨ptP cx cy (vv cx cy q) (-uu cx cy q - vv cx cy q), ?_, ?_⟩
    · simp only [Set.mem_setOf_eq, uu_ptP, vv_ptP]; exact hq
    · rw [rotE_ptP]
      conv_rhs => rw [eq_ptP cx cy q]
      congr 1 <;> ring

theorem Dis.rot {R : Tri} {n : ℕ} (cx cy : ℝ) (P : ℝ → ℝ → Prop)
    (h : Dis R {q | P (uu cx cy q) (vv cx cy q)} n) :
    Dis R {q | P (vv cx cy q) (-uu cx cy q - vv cx cy q)} n := by
  obtain ⟨C, hr, hm⟩ := h
  refine ⟨mapCongruentRegionDissection (rotE cx cy) C, ?_, hm⟩
  show (rotE cx cy).toAffineEquiv '' C.region = _
  rw [hr]
  exact image_rot cx cy P

/-! ### Gluing along `u + v = w`, and disjointness for a pinwheel -/

theorem lineFun_s (w : ℝ) (q : Plane) :
    lineFun (w / 2) (w * zs / 2) w 0 q = (w * zs / 2) * (uu 0 0 q + vv 0 0 q - w) := by
  have := zs_pos.ne'
  simp only [lineFun_apply]; unfold uu vv; field_simp; ring

theorem Dis.glue_s {R : Tri} {S1 S2 : Set Plane} {n1 n2 : ℕ} (h1 : Dis R S1 n1) (h2 : Dis R S2 n2)
    (w : ℝ) (hw : 0 < w) (hS1 : ∀ q ∈ S1, uu 0 0 q + vv 0 0 q ≤ w)
    (hS2 : ∀ q ∈ S2, w ≤ uu 0 0 q + vv 0 0 q) : Dis R (S1 ∪ S2) (n1 + n2) := by
  obtain ⟨C1, r1, m1⟩ := h1
  obtain ⟨C2, r2, m2⟩ := h2
  have hz := zs_pos
  have hf := lineFun_linear_ne_zero (px := w / 2) (py := w * zs / 2) (qx := w) (qy := 0)
    (Or.inl (by intro h; linarith))
  have hwz : 0 < w * zs / 2 := by positivity
  refine ⟨glueByLine C1 C2 (m1.trans m2.symm) _ hf ?_ ?_, ?_, ?_⟩
  · intro x hx
    rw [lineFun_s]
    have := hS1 x (by rwa [← r1])
    nlinarith
  · intro x hx
    rw [lineFun_s]
    have := hS2 x (by rwa [← r2])
    nlinarith
  · simp [r1, r2]
  · simp [m1]

theorem lt_of_mem_interior {T : Set Plane} (f : Plane →ᵃ[ℝ] ℝ) (hf : f.linear ≠ 0)
    (hT : ∀ x ∈ T, f x ≤ 0) {x : Plane} (hx : x ∈ interior T) : f x < 0 := by
  by_contra hcon
  have h0 : f x = 0 := le_antisymm (hT x (interior_subset hx)) (not_lt.mp hcon)
  set g : Plane →ᵃ[ℝ] ℝ := AffineMap.const ℝ Plane 0 - f with hg
  have hglin : g.linear ≠ 0 := by
    intro hcon
    apply hf
    have : (AffineMap.const ℝ Plane (0:ℝ)).linear - f.linear = 0 := hcon
    have hzero : (AffineMap.const ℝ Plane (0:ℝ)).linear = 0 := rfl
    rw [hzero, zero_sub, neg_eq_zero] at this
    exact this
  have hgx : g x = 0 := by simp [hg, h0]
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hx)
  obtain ⟨y, hy, hyneg⟩ := Erdos634.Geometry.exists_neg_near_of_affine_zero g hglin hgx hr
  have hyS : y ∈ T := hball hy
  have : 0 < f y := by
    have hgy : g y = 0 - f y := rfl
    rw [hgy] at hyneg
    linarith
  exact absurd (hT y hyS) (not_le.mpr this)

/-- The pinwheel disjointness: `T` in the closed quadrant `f ≤ 0, g ≤ 0`, `S` in `f ≥ 0 ∪ g ≥ 0`. -/
theorem disjoint_quadrant {S T : Set Plane} (f g : Plane →ᵃ[ℝ] ℝ) (hf : f.linear ≠ 0)
    (hg : g.linear ≠ 0) (hTf : ∀ x ∈ T, f x ≤ 0) (hTg : ∀ x ∈ T, g x ≤ 0)
    (hS : ∀ x ∈ S, 0 ≤ f x ∨ 0 ≤ g x) : Disjoint (interior S) (interior T) := by
  rw [Set.disjoint_left]
  intro x hxS hxT
  have h1 := lt_of_mem_interior f hf hTf hxT
  have h2 := lt_of_mem_interior g hg hTg hxT
  rcases hS x (interior_subset hxS) with h | h <;> linarith

theorem Dis.glue_disj {R : Tri} {S1 S2 : Set Plane} {n1 n2 : ℕ} (h1 : Dis R S1 n1)
    (h2 : Dis R S2 n2) (hd : Disjoint (interior S1) (interior S2)) : Dis R (S1 ∪ S2) (n1 + n2) := by
  obtain ⟨C1, r1, m1⟩ := h1
  obtain ⟨C2, r2, m2⟩ := h2
  refine ⟨unionCongruentRegion C1 C2 (m1.trans m2.symm) (by rw [r1, r2]; exact hd), ?_, ?_⟩
  · show C1.region ∪ C2.region = _
    rw [r1, r2]
  · show C1.model = R
    exact m1

/-! ### The equilateral triangle as a hull -/

theorem tri3_eq_carrier (X : ℝ) (hX : 0 < X) (h : 0 < det3 0 0 X 0 0 X) :
    Tri3 0 0 X = (triUV 0 0 0 0 X 0 0 X h).carrier := by
  ext q
  rw [mem_triUV]
  simp only [Tri3, Set.mem_setOf_eq, det3]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨by nlinarith, by nlinarith, by nlinarith⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨by nlinarith, by nlinarith, by nlinarith⟩

/-! ### The pinwheel -/

/-- The three pieces, in frame coordinates `U = uu 0 0`, `V = vv 0 0`, with `r',s',t'` the side
lengths (`r' = r a b` etc.).  `A1 = Tz(r',s')`, `A2` the rotated `Tz(s',t')`, `A3` the doubly rotated
`Tz(t',r')`. -/
def A2 (r' s' t' : ℝ) : Set Plane :=
  {q | 0 ≤ vv 0 0 q ∧ r' ≤ uu 0 0 q ∧ r' + s' ≤ uu 0 0 q + vv 0 0 q ∧
    uu 0 0 q + vv 0 0 q ≤ r' + s' + t'}

def A3 (r' s' t' : ℝ) : Set Plane :=
  {q | 0 ≤ uu 0 0 q ∧ uu 0 0 q ≤ r' ∧ s' ≤ vv 0 0 q ∧ uu 0 0 q + vv 0 0 q ≤ r' + s' + t'}

theorem tri3_eq_union (r' s' t' : ℝ) (hr : 0 < r') (hs : 0 < s') (ht : 0 < t') :
    Tri3 0 0 (r' + s' + t') = (Tz 0 0 r' s' ∪ A2 r' s' t') ∪ A3 r' s' t' := by
  ext q
  simp only [Tri3, Tz, A2, A3, Set.mem_union, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h1, h2, h3⟩
    by_cases hA : vv 0 0 q ≤ s' ∧ uu 0 0 q + vv 0 0 q ≤ r' + s'
    · exact Or.inl (Or.inl ⟨h1, h2, hA.1, hA.2⟩)
    by_cases hB : r' ≤ uu 0 0 q ∧ r' + s' ≤ uu 0 0 q + vv 0 0 q
    · exact Or.inl (Or.inr ⟨h2, hB.1, hB.2, h3⟩)
    right
    refine ⟨h1, ?_, ?_, h3⟩
    · by_contra hu
      replace hu := not_le.mp hu
      rcases le_or_gt (r' + s') (uu 0 0 q + vv 0 0 q) with h4 | h4
      · exact hB ⟨hu.le, h4⟩
      · exact hA ⟨by linarith, h4.le⟩
    · by_contra hv
      replace hv := not_le.mp hv
      rcases le_or_gt (uu 0 0 q + vv 0 0 q) (r' + s') with h4 | h4
      · exact hA ⟨hv.le, h4⟩
      · exact hB ⟨by linarith, h4.le⟩
  · rintro ((⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩) | ⟨h1, h2, h3, h4⟩)
    · exact ⟨h1, h2, by linarith⟩
    · exact ⟨by linarith, h1, h4⟩
    · exact ⟨h1, by linarith, h4⟩

theorem Dis_A2 {R : Tri} {n : ℕ} (r' s' t' : ℝ) (h : ∀ px py, Dis R (Tz px py s' t') n) :
    Dis R (A2 r' s' t') n := by
  have h2 := Dis.rot (shx 0 (r' + s' + t') 0) (shy 0 0)
    (fun u v => 0 ≤ u ∧ 0 ≤ v ∧ v ≤ t' ∧ u + v ≤ s' + t') (h _ _)
  refine h2.congr ?_ rfl
  ext q
  simp only [Set.mem_setOf_eq, A2, uu_sh, vv_sh]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨by linarith, by linarith, by linarith, by linarith⟩
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem Dis_A3 {R : Tri} {n : ℕ} (r' s' t' : ℝ) (h : ∀ px py, Dis R (Tz px py t' r') n) :
    Dis R (A3 r' s' t') n := by
  have h1 := h (shx 0 0 (r' + s' + t')) (shy 0 (r' + s' + t'))
  have h2 := Dis.rot (shx 0 0 (r' + s' + t')) (shy 0 (r' + s' + t'))
    (fun u v => 0 ≤ u ∧ 0 ≤ v ∧ v ≤ r' ∧ u + v ≤ t' + r') h1
  have h3 := Dis.rot (shx 0 0 (r' + s' + t')) (shy 0 (r' + s' + t'))
    (fun u v => 0 ≤ v ∧ 0 ≤ -u - v ∧ -u - v ≤ r' ∧ v + (-u - v) ≤ t' + r') h2
  refine h3.congr ?_ rfl
  ext q
  simp only [Set.mem_setOf_eq, A3, uu_sh, vv_sh]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨by linarith, by linarith, by linarith, by linarith⟩
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem lineFun_vneg (s' : ℝ) (q : Plane) :
    lineFun (s' / 2 + 1) (s' * zs / 2) (s' / 2) (s' * zs / 2) q = -(zs / 2 * (vv 0 0 q - s')) := by
  have := zs_pos.ne'
  simp only [lineFun_apply]; unfold vv; field_simp; ring

/-- **Pinwheel (Zhang Fig. 5), abstract form.**  If the three trapezoid pieces carry dissections
(at every frame origin), the triangle of side `r'+s'+t'` does. -/
theorem Dis_pinwheel {R : Tri} {n1 n2 n3 : ℕ} (r' s' t' : ℝ) (hr : 0 < r') (hs : 0 < s')
    (ht : 0 < t') (h1 : Dis R (Tz 0 0 r' s') n1) (h2 : ∀ px py, Dis R (Tz px py s' t') n2)
    (h3 : ∀ px py, Dis R (Tz px py t' r') n3) :
    Dis R (Tri3 0 0 (r' + s' + t')) (n1 + n2 + n3) := by
  have hz := zs_pos
  have c12 := Dis.glue_s h1 (Dis_A2 r' s' t' h2) (r' + s') (by linarith)
    (fun q hq => hq.2.2.2) (fun q hq => hq.2.2.1)
  have hf1 : (lineFun (s' / 2 + 1) (s' * zs / 2) (s' / 2) (s' * zs / 2)).linear ≠ 0 :=
    lineFun_linear_ne_zero (Or.inl (by intro h; linarith))
  have hf2 : (lineFun (0 + r' + 1 / 2) (0 + zs / 2) (0 + r') 0).linear ≠ 0 :=
    lineFun_linear_ne_zero (Or.inl (by intro h; linarith))
  have hd : Disjoint (interior (Tz 0 0 r' s' ∪ A2 r' s' t')) (interior (A3 r' s' t')) := by
    refine disjoint_quadrant (lineFun (s' / 2 + 1) (s' * zs / 2) (s' / 2) (s' * zs / 2))
      (lineFun (0 + r' + 1 / 2) (0 + zs / 2) (0 + r') 0) hf1 hf2 ?_ ?_ ?_
    · intro x hx
      rw [lineFun_vneg]
      have := hx.2.2.1
      nlinarith
    · intro x hx
      rw [lineFun_u]
      have := hx.2.1
      nlinarith
    · intro x hx
      rcases hx with hx | hx
      · left
        rw [lineFun_vneg]
        have := hx.2.2.1
        nlinarith
      · right
        rw [lineFun_u]
        have := hx.2.1
        nlinarith
  have c123 := Dis.glue_disj c12 (Dis_A3 r' s' t' h3) hd
  exact c123.congr (tri3_eq_union r' s' t' hr hs ht).symm rfl

/-- Frame-origin-free form of Proposition 3 with real side lengths `x' = x a b`-style casts. -/
theorem prop3_cast (a b c x k : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hcab : c * c = a * a + b * b + a * b) (hcop : Nat.Coprime a b)
    (hx : c * c < x * (a * b) + a + b) (hk : 0 < k) (px py : ℝ) :
    Dis (Rmodel (Nat.cast_pos.mpr ha : (0:ℝ) < a) (Nat.cast_pos.mpr hb : (0:ℝ) < b))
      (Tz px py ((x : ℝ) * ((a : ℝ) * b)) ((k : ℝ) * ((a : ℝ) * b)))
      (k * (2 * (x * (a * b)) + k * (a * b))) := by
  refine (zhang_prop3 a b c (x * (a * b)) k ha hb hc hcab hcop hx hk px py).congr ?_ rfl
  push_cast; rfl

/-- **Zhang's Theorem 4, `r,s,t` form (UNAUDITED).**  For naturals `a,b,c` with `c² = a²+b²+ab`,
`gcd(a,b)=1`, and `r,s,t` with `c² < ·(ab) + a + b` each, the equilateral triangle of side
`(r+s+t) a b` carries `(r+s+t)² a b` tiles congruent to `Rmodel`. -/
theorem zhang_thm4_rst (a b c r s t : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hcab : c * c = a * a + b * b + a * b) (hcop : Nat.Coprime a b)
    (hr : c * c < r * (a * b) + a + b) (hs : c * c < s * (a * b) + a + b)
    (ht : c * c < t * (a * b) + a + b) :
    Dis (Rmodel (Nat.cast_pos.mpr ha : (0:ℝ) < a) (Nat.cast_pos.mpr hb : (0:ℝ) < b))
      (Tri3 0 0 (((r + s + t : ℕ) : ℝ) * ((a : ℝ) * b))) ((r + s + t) * (r + s + t) * (a * b)) := by
  have ha' : (0:ℝ) < a := Nat.cast_pos.mpr ha
  have hb' : (0:ℝ) < b := Nat.cast_pos.mpr hb
  have hge := add_le_mul_of_cab a b c ha hb hcab
  have hpos : ∀ x : ℕ, c * c < x * (a * b) + a + b → 0 < x := by
    intro x hx
    rcases Nat.eq_zero_or_pos x with rfl | h
    · exfalso; simp at hx; nlinarith [Nat.mul_pos ha hb]
    · exact h
  have hr0 := hpos r hr
  have hs0 := hpos s hs
  have ht0 := hpos t ht
  have hab : (0:ℝ) < (a:ℝ) * b := mul_pos ha' hb'
  have h1 := prop3_cast a b c r s ha hb hc hcab hcop hr hs0 0 0
  have h2 := fun px py => prop3_cast a b c s t ha hb hc hcab hcop hs ht0 px py
  have h3 := fun px py => prop3_cast a b c t r ha hb hc hcab hcop ht hr0 px py
  have key := Dis_pinwheel (((r:ℝ)) * ((a:ℝ) * b)) ((s:ℝ) * ((a:ℝ) * b)) ((t:ℝ) * ((a:ℝ) * b))
    (by positivity) (by positivity) (by positivity) h1 h2 h3
  refine key.congr ?_ ?_
  · congr 1; push_cast; ring
  · ring

/-- Zhang's definition (§3.1): `X` is equiconstructible by `(a,b,c)` when the equilateral
triangle of side `X` tiles into `n` triangles congruent to `(a,b,c)`. -/
def EquiConstr (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (X : ℝ) (n : ℕ) : Prop :=
  Dis (Rmodel (Nat.cast_pos.mpr ha : (0:ℝ) < a) (Nat.cast_pos.mpr hb : (0:ℝ) < b)) (Tri3 0 0 X) n

/-- **Zhang's Theorem 4 (UNAUDITED).**  With `M₀ = ⌊(c²−a−b)/(ab)⌋ + 1`, for all `m ≥ 3 M₀`,
`m a b` is equiconstructible by `(a,b,c)`, with `m² a b` tiles. -/
theorem zhang_thm4 (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hcab : c * c = a * a + b * b + a * b) (hcop : Nat.Coprime a b)
    (m : ℕ) (hm : 3 * ((c * c - a - b) / (a * b) + 1) ≤ m) :
    EquiConstr a b ha hb ((m : ℝ) * ((a : ℝ) * b)) (m * m * (a * b)) := by
  set M0 := (c * c - a - b) / (a * b) + 1 with hM0
  have hab : 0 < a * b := Nat.mul_pos ha hb
  have hlt : c * c - a - b < M0 * (a * b) := by
    have := Nat.lt_mul_div_succ (c * c - a - b) hab
    rw [hM0]; linarith [Nat.mul_comm (a * b) ((c * c - a - b) / (a * b) + 1)]
  have hM : c * c < M0 * (a * b) + a + b := by omega
  have hge : ∀ x, M0 ≤ x → c * c < x * (a * b) + a + b := by
    intro x hx
    have := Nat.mul_le_mul_right (a * b) hx
    omega
  have key := zhang_thm4_rst a b c M0 M0 (m - 2 * M0) ha hb hc hcab hcop hM hM
    (hge _ (by omega))
  unfold EquiConstr
  have e : M0 + M0 + (m - 2 * M0) = m := by omega
  rw [e] at key
  exact key

/-- Witness `(3,5,7)`: `M₀ = ⌊41/15⌋ + 1 = 3`, so `m = 9` works: `15·9 = 135` is equiconstructible
with `9·9·15 = 1215` tiles (area `135²√3/4 = 1215 · 15√3/4`). -/
theorem zhang_thm4_357 : ∃ n : ℕ, n = 1215 ∧ ∃ C : CongruentRegionDissection n,
    C.region = Tri3 0 0 (((9:ℕ):ℝ) * (((3:ℕ):ℝ) * ((5:ℕ):ℝ))) := by
  obtain ⟨C, hr, -⟩ := zhang_thm4 3 5 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) 9 (by norm_num)
  exact ⟨_, by norm_num, C, hr⟩

/-- Witness `(8,7,13)`: `M₀ = ⌊154/56⌋ + 1 = 3`, `m = 9`: side `504`, `9·9·56 = 4536` tiles. -/
theorem zhang_thm4_8_7_13 : ∃ n : ℕ, n = 4536 ∧ ∃ C : CongruentRegionDissection n,
    C.region = Tri3 0 0 (((9:ℕ):ℝ) * (((8:ℕ):ℝ) * ((7:ℕ):ℝ))) := by
  obtain ⟨C, hr, -⟩ := zhang_thm4 8 7 13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) 9 (by norm_num)
  exact ⟨_, by norm_num, C, hr⟩

end Erdos634.ZhangThm4
