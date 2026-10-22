import Erdos634.Draft.LaczFormalL22Grid

/-!
# Laczkovich Lemma 2.2 (i): a rational parallelogram with an angle of `Δ` is dissected into rational
# triangles similar to `Δ`

NOTE, UNAUDITED.  Credit: Laczkovich (Discrete Math. 140 (1995) 79-94, Lemma 2.2 (i)), Beeson, Beeson-Zhang, Zhang.

Statement (chart form).  `Δ` is a rational triangle with sides `a = |Δ₁Δ₂|`, `b = |Δ₂Δ₀|`, `c = |Δ₀Δ₁|`
(rational, positive); `α` is its angle at the vertex `Δ₀`, `cos α = (b²+c²-a²)/(2bc)`.  A chart
`(A, w, d)` with `|w| = W`, `|d| = D` rational and `⟨w,d⟩ = W D cos α` (the parallelogram `A, A+w, A+w+d, A+d`
has the angle `α`).  Then every coordinate rectangle `[s0, s0+p] × [t0, t0+q]` of the chart (`p, q`
rational positive), i.e. the parallelogram with sides `p w`, `q d`, is the union of finitely many rational
triangles similar to `Δ` with pairwise disjoint interiors (`rect_ratSim`).
Proof as in the paper: divide the sides into `n` and `m` equal parts so that the small parallelograms have
the side ratio of `Δ` at `α` (`n/m = p W b / (q D c)`), cut each by a diagonal.
-/

namespace Erdos634.LaczL22

open Erdos634.Geometry Erdos634.CertCoord Erdos634.LaczL21 Erdos634.Realizable

/-- A rational triangle together with its rational side lengths. -/
structure RTri where
  Δ : Tri
  a : ℚ
  b : ℚ
  c : ℚ
  ha : dist (Δ.pts 1) (Δ.pts 2) = a
  hb : dist (Δ.pts 2) (Δ.pts 0) = b
  hc : dist (Δ.pts 0) (Δ.pts 1) = c
  pa : 0 < a
  pb : 0 < b
  pc : 0 < c

theorem RTri.rational (R : RTri) : IsRationalTri R.Δ := by
  have htri : ∀ y : Fin 3, y = 0 ∨ y = 1 ∨ y = 2 := by decide
  intro j k
  rcases htri j with rfl | rfl | rfl <;> rcases htri k with rfl | rfl | rfl
  · exact ⟨0, by simp⟩
  · exact ⟨R.c, R.hc⟩
  · exact ⟨R.b, by rw [dist_comm]; exact R.hb⟩
  · exact ⟨R.c, by rw [dist_comm]; exact R.hc⟩
  · exact ⟨0, by simp⟩
  · exact ⟨R.a, R.ha⟩
  · exact ⟨R.b, R.hb⟩
  · exact ⟨R.a, by rw [dist_comm]; exact R.ha⟩
  · exact ⟨0, by simp⟩

/-- `cos` of the angle of `Δ` at the vertex `0`, from the sides. -/
def RTri.cos0 (R : RTri) : ℚ := (R.b ^ 2 + R.c ^ 2 - R.a ^ 2) / (2 * R.b * R.c)

/-- A lower or upper cell of rational size, moved into the chart, is a rational similar tile. -/
theorem cell_ratSim (R : RTri) (A w d : Plane) (h : w 0 * d 1 - w 1 * d 0 ≠ 0) (W Dd : ℚ)
    (hw : inner ℝ w w = (W : ℝ) ^ 2) (hd : inner ℝ d d = (Dd : ℝ) ^ 2)
    (hwd : inner ℝ w d = (W : ℝ) * Dd * (R.cos0 : ℝ))
    (x y : ℝ) (du dv k : ℚ) (hu : 0 < (du : ℝ)) (hv : 0 < (dv : ℝ)) (hk : 0 < k)
    (hdu : du * W = k * R.c) (hdv : dv * Dd = k * R.b) (bb : Bool) :
    RatSimTile R.Δ (Erdos634.DissectionMap.mapTri (chartEquiv A w d h)
      (cellTri x y du dv hu hv bb)) := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hdu' : (du : ℝ) * W = k * R.c := by exact_mod_cast hdu
  have hdv' : (dv : ℝ) * Dd = k * R.b := by exact_mod_cast hdv
  have hb0 : (R.b : ℝ) ≠ 0 := by exact_mod_cast R.pb.ne'
  have hc0 : (R.c : ℝ) ≠ 0 := by exact_mod_cast R.pc.ne'
  have hcos : (R.cos0 : ℝ) = ((R.b : ℝ) ^ 2 + R.c ^ 2 - R.a ^ 2) / (2 * R.b * R.c) := by
    simp [RTri.cos0]
  have e1 : (du : ℝ) ^ 2 * (W : ℝ) ^ 2 = (k : ℝ) ^ 2 * (R.c : ℝ) ^ 2 := by
    rw [show (du : ℝ) ^ 2 * (W : ℝ) ^ 2 = ((du : ℝ) * W) ^ 2 by ring, hdu']; ring
  have e2 : (dv : ℝ) ^ 2 * (Dd : ℝ) ^ 2 = (k : ℝ) ^ 2 * (R.b : ℝ) ^ 2 := by
    rw [show (dv : ℝ) ^ 2 * (Dd : ℝ) ^ 2 = ((dv : ℝ) * Dd) ^ 2 by ring, hdv']; ring
  have e3 : (du : ℝ) ^ 2 * (W : ℝ) ^ 2 - 2 * ((du : ℝ) * dv) * ((W : ℝ) * Dd * (R.cos0 : ℝ))
      + (dv : ℝ) ^ 2 * (Dd : ℝ) ^ 2 = (k : ℝ) ^ 2 * (R.a : ℝ) ^ 2 := by
    have : 2 * ((du : ℝ) * dv) * ((W : ℝ) * Dd * (R.cos0 : ℝ))
        = 2 * (((du : ℝ) * W) * ((dv : ℝ) * Dd)) * (R.cos0 : ℝ) := by ring
    rw [this, hdu', hdv', e1, e2, hcos]
    field_simp
    ring
  -- vertex coordinates
  have hsq : ∀ (p q : Plane), dist (chartEquiv A w d h p) (chartEquiv A w d h q) ^ 2
      = (p 0 - q 0) ^ 2 * (W : ℝ) ^ 2 + 2 * ((p 0 - q 0) * (p 1 - q 1)) * ((W : ℝ) * Dd * (R.cos0 : ℝ))
        + (p 1 - q 1) ^ 2 * (Dd : ℝ) ^ 2 := by
    intro p q
    rw [dist_chart_sq, hw, hd, hwd]
  refine ratSimTile_of_cong R.rational k hk ?_
  cases bb
  · -- lower triangle, vertex correspondence = identity
    refine congr_of_sq3 _ R.Δ (Equiv.refl _) k hk' ?_ ?_ ?_
    · show dist (chartEquiv A w d h (mkPt x y)) (chartEquiv A w d h (mkPt (x + du) y)) ^ 2 = _
      rw [hsq]; simp only [mkPt_zero, mkPt_one, Equiv.refl_apply, R.hc]; linear_combination e1
    · show dist (chartEquiv A w d h (mkPt (x + du) y)) (chartEquiv A w d h (mkPt x (y + dv))) ^ 2 = _
      rw [hsq]; simp only [mkPt_zero, mkPt_one, Equiv.refl_apply, R.ha]; linear_combination e3
    · show dist (chartEquiv A w d h (mkPt x (y + dv))) (chartEquiv A w d h (mkPt x y)) ^ 2 = _
      rw [hsq]; simp only [mkPt_zero, mkPt_one, Equiv.refl_apply, R.hb]; linear_combination e2
  · -- upper triangle, mirror: vertex 1 <-> Δ₂, vertex 2 <-> Δ₁
    have s0 : (Equiv.swap (1 : Fin 3) 2) 0 = 0 := by decide
    have s1 : (Equiv.swap (1 : Fin 3) 2) 1 = 2 := by decide
    have s2 : (Equiv.swap (1 : Fin 3) 2) 2 = 1 := by decide
    refine congr_of_sq3 _ R.Δ (Equiv.swap 1 2) k hk' ?_ ?_ ?_
    · show dist (chartEquiv A w d h (mkPt (x + du) (y + dv)))
        (chartEquiv A w d h (mkPt (x + du) y)) ^ 2 = _
      rw [hsq, s0, s1, dist_comm (R.Δ.pts 0) (R.Δ.pts 2), R.hb]
      simp only [mkPt_zero, mkPt_one]; linear_combination e2
    · show dist (chartEquiv A w d h (mkPt (x + du) y))
        (chartEquiv A w d h (mkPt x (y + dv))) ^ 2 = _
      rw [hsq, s1, s2, dist_comm (R.Δ.pts 2) (R.Δ.pts 1), R.ha]
      simp only [mkPt_zero, mkPt_one]; linear_combination e3
    · show dist (chartEquiv A w d h (mkPt x (y + dv)))
        (chartEquiv A w d h (mkPt (x + du) (y + dv))) ^ 2 = _
      rw [hsq, s2, s0, dist_comm (R.Δ.pts 1) (R.Δ.pts 0), R.hc]
      simp only [mkPt_zero, mkPt_one]; linear_combination e1


/-- **Laczkovich Lemma 2.2 (i), chart form.**  The chart rectangle with rational sides `p, q` and corner
`(s0, t0)` is dissected into rational triangles similar to `Δ`. -/
theorem rect_ratSim (R : RTri) (A w d : Plane) (h : w 0 * d 1 - w 1 * d 0 ≠ 0) (W Dd : ℚ)
    (hW : 0 < W) (hD : 0 < Dd)
    (hw : inner ℝ w w = (W : ℝ) ^ 2) (hd : inner ℝ d d = (Dd : ℝ) ^ 2)
    (hwd : inner ℝ w d = (W : ℝ) * Dd * (R.cos0 : ℝ))
    (s0 t0 p q : ℚ) (hp : 0 < p) (hq : 0 < q) :
    RatSimDiss R.Δ (chartEquiv A w d h '' rectSet (s0 : ℝ) ((s0 : ℝ) + p) (t0 : ℝ) ((t0 : ℝ) + q)) := by
  have hb := R.pb
  have hc := R.pc
  set r : ℚ := (p * W * R.b) / (q * Dd * R.c) with hrdef
  have hr : 0 < r := by positivity
  set n : ℕ := r.num.toNat with hndef
  set m : ℕ := r.den with hmdef
  have hnum : 0 < r.num := Rat.num_pos.mpr hr
  have hn : 0 < n := by rw [hndef]; omega
  have hm : 0 < m := r.den_pos
  have hnr : (n : ℚ) = r.num := by
    rw [hndef]; exact_mod_cast Int.toNat_of_nonneg hnum.le
  have hrat : (n : ℚ) / (m : ℚ) = r := by rw [hnr]; exact Rat.num_div_den r
  have hn' : (0 : ℚ) < n := by exact_mod_cast hn
  have hm' : (0 : ℚ) < m := by exact_mod_cast hm
  have hrel : (n : ℚ) * (q * Dd * R.c) = (p * W * R.b) * m := by
    have := hrat
    rw [hrdef, div_eq_div_iff hm'.ne' (by positivity)] at this
    linarith
  set du : ℚ := p / n with hdudef
  set dv : ℚ := q / m with hdvdef
  set k : ℚ := p * W / (n * R.c) with hkdef
  have hdu0 : 0 < du := by positivity
  have hdv0 : 0 < dv := by positivity
  have hk0 : 0 < k := by positivity
  have hdu : du * W = k * R.c := by
    rw [hdudef, hkdef]; field_simp
  have hdv : dv * Dd = k * R.b := by
    rw [hdvdef, hkdef]; field_simp; linear_combination hrel
  have hu' : (0 : ℝ) < (du : ℝ) := by exact_mod_cast hdu0
  have hv' : (0 : ℝ) < (dv : ℝ) := by exact_mod_cast hdv0
  have hnd : (n : ℝ) * du = p := by
    have : (n : ℚ) * du = p := by rw [hdudef]; field_simp
    exact_mod_cast this
  have hmd : (m : ℝ) * dv = q := by
    have : (m : ℚ) * dv = q := by rw [hdvdef]; field_simp
    exact_mod_cast this
  refine ofChartTiles A w d h (ι := Fin n × Fin m × Bool)
    (fun e => gridTile (s0 : ℝ) (t0 : ℝ) (du : ℝ) (dv : ℝ) hu' hv' e.1 e.2.1 e.2.2) _ ?_ ?_ ?_
  · ext z
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨⟨i, j, b⟩, hz⟩
      have hsub := cellTri_sub_rect ((s0 : ℝ) + i * du) ((t0 : ℝ) + j * dv) du dv hu' hv' b hz
      obtain ⟨h1, h2, h3, h4⟩ := hsub
      have hi : (i : ℝ) + 1 ≤ n := by exact_mod_cast i.isLt
      have hj : (j : ℝ) + 1 ≤ m := by exact_mod_cast j.isLt
      have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg _
      have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg _
      refine ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩
    · intro hz
      have hz' : z ∈ rectSet (s0 : ℝ) ((s0 : ℝ) + n * du) (t0 : ℝ) ((t0 : ℝ) + m * dv) := by
        rw [hnd, hmd]; exact hz
      obtain ⟨i, j, b, hz⟩ := grid_cover (s0 : ℝ) (t0 : ℝ) (du : ℝ) (dv : ℝ) hu' hv' n m hn hm z hz'
      exact ⟨⟨i, j, b⟩, hz⟩
  · rintro ⟨i, j, b⟩ ⟨i', j', b'⟩ hne
    apply grid_disjoint
    rintro ⟨h1, h2, h3⟩
    obtain rfl : i = i' := Fin.ext (by simpa using h1)
    obtain rfl : j = j' := Fin.ext (by simpa using h2)
    obtain rfl : b = b' := by simpa using h3
    exact hne rfl
  · rintro ⟨i, j, b⟩
    exact cell_ratSim R A w d h W Dd hw hd hwd _ _ du dv k hu' hv' hk0 hdu hdv b


/-! ## From angles to the Gram data -/

/-- The parallelogram `{A + s w + t d : 0 ≤ s ≤ p, 0 ≤ t ≤ q}`. -/
def parSet (A w d : Plane) (p q : ℝ) : Set Plane :=
  {x | ∃ s t : ℝ, 0 ≤ s ∧ s ≤ p ∧ 0 ≤ t ∧ t ≤ q ∧ x = A + s • w + t • d}

theorem chart_image_rect (A w d : Plane) (h : w 0 * d 1 - w 1 * d 0 ≠ 0) (s0 t0 p q : ℝ) :
    chartEquiv A w d h '' rectSet s0 (s0 + p) t0 (t0 + q)
      = {x | ∃ s t : ℝ, s0 ≤ s ∧ s ≤ s0 + p ∧ t0 ≤ t ∧ t ≤ t0 + q ∧ x = A + s • w + t • d} := by
  ext x
  constructor
  · rintro ⟨z, ⟨h1, h2, h3, h4⟩, rfl⟩
    exact ⟨z 0, z 1, h1, h2, h3, h4, chartEquiv_apply A w d h z⟩
  · rintro ⟨s, t, h1, h2, h3, h4, rfl⟩
    refine ⟨mkPt s t, ⟨by simpa using h1, by simpa using h2, by simpa using h3, by simpa using h4⟩, ?_⟩
    rw [chartEquiv_apply]; simp

theorem RTri.inner_uv (R : RTri) :
    inner ℝ (R.Δ.pts 1 - R.Δ.pts 0) (R.Δ.pts 2 - R.Δ.pts 0)
      = ((R.c : ℝ) ^ 2 + (R.b : ℝ) ^ 2 - (R.a : ℝ) ^ 2) / 2 := by
  have h1 : ‖R.Δ.pts 1 - R.Δ.pts 0‖ = R.c := by rw [← dist_eq_norm, dist_comm]; exact R.hc
  have h2 : ‖R.Δ.pts 2 - R.Δ.pts 0‖ = R.b := by rw [← dist_eq_norm]; exact R.hb
  have h3 : ‖(R.Δ.pts 1 - R.Δ.pts 0) - (R.Δ.pts 2 - R.Δ.pts 0)‖ = R.a := by
    rw [show (R.Δ.pts 1 - R.Δ.pts 0) - (R.Δ.pts 2 - R.Δ.pts 0) = R.Δ.pts 1 - R.Δ.pts 2 by abel,
      ← dist_eq_norm]; exact R.ha
  have := norm_sub_sq_real (R.Δ.pts 1 - R.Δ.pts 0) (R.Δ.pts 2 - R.Δ.pts 0)
  rw [h1, h2, h3] at this
  linarith

theorem RTri.cos0_sq_lt (R : RTri) : (R.cos0 : ℝ) ^ 2 < 1 := by
  have hdet := R.Δ.det_ne_zero
  have hin := R.inner_uv
  have hlag : (R.Δ.det) ^ 2 + (inner ℝ (R.Δ.pts 1 - R.Δ.pts 0) (R.Δ.pts 2 - R.Δ.pts 0)) ^ 2
      = (R.c : ℝ) ^ 2 * (R.b : ℝ) ^ 2 := by
    have h1 : ‖R.Δ.pts 1 - R.Δ.pts 0‖ = R.c := by rw [← dist_eq_norm, dist_comm]; exact R.hc
    have h2 : ‖R.Δ.pts 2 - R.Δ.pts 0‖ = R.b := by rw [← dist_eq_norm]; exact R.hb
    have e1 : ‖R.Δ.pts 1 - R.Δ.pts 0‖ ^ 2 = (R.Δ.pts 1 - R.Δ.pts 0) 0 ^ 2 + (R.Δ.pts 1 - R.Δ.pts 0) 1 ^ 2 := by
      rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
      simp [Fin.sum_univ_two, sq_abs]
    have e2 : ‖R.Δ.pts 2 - R.Δ.pts 0‖ ^ 2 = (R.Δ.pts 2 - R.Δ.pts 0) 0 ^ 2 + (R.Δ.pts 2 - R.Δ.pts 0) 1 ^ 2 := by
      rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
      simp [Fin.sum_univ_two, sq_abs]
    have e3 : inner ℝ (R.Δ.pts 1 - R.Δ.pts 0) (R.Δ.pts 2 - R.Δ.pts 0)
        = (R.Δ.pts 1 - R.Δ.pts 0) 0 * (R.Δ.pts 2 - R.Δ.pts 0) 0
          + (R.Δ.pts 1 - R.Δ.pts 0) 1 * (R.Δ.pts 2 - R.Δ.pts 0) 1 := by
      simp [PiLp.inner_apply, Fin.sum_univ_two]; ring
    rw [e3, Erdos634.Geometry.Tri.det]
    have : (R.c : ℝ) ^ 2 * (R.b : ℝ) ^ 2 = ‖R.Δ.pts 1 - R.Δ.pts 0‖ ^ 2 * ‖R.Δ.pts 2 - R.Δ.pts 0‖ ^ 2 := by
      rw [h1, h2]
    rw [this, e1, e2]; ring
  have hb : (R.b : ℝ) ≠ 0 := by exact_mod_cast R.pb.ne'
  have hc : (R.c : ℝ) ≠ 0 := by exact_mod_cast R.pc.ne'
  have hcos : (R.cos0 : ℝ) = ((R.c : ℝ) ^ 2 + (R.b : ℝ) ^ 2 - (R.a : ℝ) ^ 2) / (2 * R.b * R.c) := by
    simp [RTri.cos0]; field_simp; ring
  have hcos2 : (R.cos0 : ℝ) = inner ℝ (R.Δ.pts 1 - R.Δ.pts 0) (R.Δ.pts 2 - R.Δ.pts 0) / (R.b * R.c) := by
    rw [hin, hcos]; field_simp
  have hpos : 0 < (R.Δ.det) ^ 2 := by positivity
  rw [hcos2, div_pow, div_lt_one (by positivity)]
  nlinarith [hlag, hpos]

/-- Gram data from the angle: `⟨w, d⟩ = W D cos α` when the angle between `w` and `d` is `Δ`'s angle at
vertex `0`. -/
theorem gram_of_angle (R : RTri) (w d : Plane) (W Dd : ℚ) (hW : 0 < W) (hD : 0 < Dd)
    (hwn : ‖w‖ = W) (hdn : ‖d‖ = Dd)
    (hang : InnerProductGeometry.angle w d
      = cornerAngle (R.Δ.pts 1) (R.Δ.pts 0) (R.Δ.pts 2)) :
    inner ℝ w d = (W : ℝ) * Dd * (R.cos0 : ℝ) := by
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  have hD' : (0 : ℝ) < Dd := by exact_mod_cast hD
  have hb : (R.b : ℝ) ≠ 0 := by exact_mod_cast R.pb.ne'
  have hc : (R.c : ℝ) ≠ 0 := by exact_mod_cast R.pc.ne'
  have h1 : ‖R.Δ.pts 1 - R.Δ.pts 0‖ = R.c := by rw [← dist_eq_norm, dist_comm]; exact R.hc
  have h2 : ‖R.Δ.pts 2 - R.Δ.pts 0‖ = R.b := by rw [← dist_eq_norm]; exact R.hb
  have hcA : Real.cos (cornerAngle (R.Δ.pts 1) (R.Δ.pts 0) (R.Δ.pts 2))
      = ((R.c : ℝ) ^ 2 + (R.b : ℝ) ^ 2 - (R.a : ℝ) ^ 2) / 2 / (R.c * R.b) := by
    unfold cornerAngle EuclideanGeometry.angle
    rw [InnerProductGeometry.cos_angle]
    simp only [vsub_eq_sub]
    rw [R.inner_uv, h1, h2]
  have hw : Real.cos (InnerProductGeometry.angle w d) = inner ℝ w d / (W * Dd) := by
    rw [InnerProductGeometry.cos_angle, hwn, hdn]
  rw [hang, hcA] at hw
  have hcos : (R.cos0 : ℝ) = ((R.c : ℝ) ^ 2 + (R.b : ℝ) ^ 2 - (R.a : ℝ) ^ 2) / (2 * R.b * R.c) := by
    simp [RTri.cos0]; field_simp; ring
  rw [hcos]
  have hWD : (W : ℝ) * Dd ≠ 0 := by positivity
  field_simp at hw ⊢
  linarith [hw]

/-- **Laczkovich Lemma 2.2 (i), actual-plane form.**  `Δ` a rational triangle; `w, d` vectors with
rational lengths whose angle is the angle of `Δ` at its vertex `0`.  Then the parallelogram
`{A + s w + t d : 0 ≤ s ≤ p, 0 ≤ t ≤ q}` (`p, q` positive rationals) is the union of finitely many rational
triangles similar to `Δ` with pairwise disjoint interiors.  (Any other vertex of `Δ`: apply to
`Δ.relabel`; the angle `π - α` is the same parallelogram.) -/
theorem lemma22_i (R : RTri) (A w d : Plane) (W Dd : ℚ) (hW : 0 < W) (hD : 0 < Dd)
    (hwn : ‖w‖ = W) (hdn : ‖d‖ = Dd)
    (hang : InnerProductGeometry.angle w d
      = cornerAngle (R.Δ.pts 1) (R.Δ.pts 0) (R.Δ.pts 2))
    (p q : ℚ) (hp : 0 < p) (hq : 0 < q) :
    RatSimDiss R.Δ (parSet A w d p q) := by
  have hwd := gram_of_angle R w d W Dd hW hD hwn hdn hang
  have hw : inner ℝ w w = (W : ℝ) ^ 2 := by rw [real_inner_self_eq_norm_sq, hwn]
  have hd : inner ℝ d d = (Dd : ℝ) ^ 2 := by rw [real_inner_self_eq_norm_sq, hdn]
  have hdet : w 0 * d 1 - w 1 * d 0 ≠ 0 := by
    intro h0
    have ewd : inner ℝ w d = w 0 * d 0 + w 1 * d 1 := by
      simp [PiLp.inner_apply, Fin.sum_univ_two]; ring
    have eww : inner ℝ w w = w 0 * w 0 + w 1 * w 1 := by
      rw [PiLp.inner_apply, Fin.sum_univ_two]; simp; ring
    have edd : inner ℝ d d = d 0 * d 0 + d 1 * d 1 := by
      rw [PiLp.inner_apply, Fin.sum_univ_two]; simp; ring
    have hlag : (w 0 * d 1 - w 1 * d 0) ^ 2 + (inner ℝ w d) ^ 2 = inner ℝ w w * inner ℝ d d := by
      rw [ewd, eww, edd]; ring
    rw [h0, hwd, hw, hd] at hlag
    have hW' : (0 : ℝ) < W := by exact_mod_cast hW
    have hD' : (0 : ℝ) < Dd := by exact_mod_cast hD
    have := R.cos0_sq_lt
    nlinarith [mul_pos hW' hD', sq_pos_of_pos (mul_pos hW' hD')]
  have key := rect_ratSim R A w d hdet W Dd hW hD hw hd hwd 0 0 p q hp hq
  have himg := chart_image_rect A w d hdet (((0 : ℚ) : ℝ)) (((0 : ℚ) : ℝ)) (p : ℝ) (q : ℝ)
  simp only [Rat.cast_zero, zero_add] at himg key
  rw [himg] at key
  convert key using 2

end Erdos634.LaczL22
