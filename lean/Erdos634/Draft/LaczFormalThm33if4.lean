import Erdos634.Draft.LaczFormalThm33if3
import Erdos634.Draft.GlueCut

/-!
# Laczkovich DCG 48 (2012) Thm 3.3, "if" direction, module 4 of 5: clauses (i) and (ii)

NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012) 330-372, Thm 3.3; Discrete Math. 140 (1995)), Beeson, Beeson-Zhang, Zhang.

The tiles of (i) `(π/6, π/6, 2π/3)` and (ii) `(π/6, π/2, π/3)` have irrational side ratios, so the rational machinery
(`RatSimDiss`) does not apply.  Explicit dissections in the chart `(u, v)` (`|u| = |v| = 1`, `<u, v> = 1/2`, so the chart image of
`{0,0 ; s,0 ; 0,s}` is equilateral of side `s`) with rational coordinates:
* (ii): the triangle `(0,0),(2,0),(0,2)` is cut along the median to the midpoint `(1,1)` of its opposite side: 2 tiles `30-60-90`;
* (i): the triangle `(0,0),(2,0),(0,2)` is cut from the centre `(2/3,2/3)`: 3 tiles `30-30-120`.
Carriers by `GlueCut.mem_carrier_mkTri_iff`, separation by `interiors_disjoint_of_cut`, congruence by squared chart distances.
-/

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.TilePlacement Erdos634.Draft.TheoremPConditional
  Erdos634.Draft.LaczFormal Erdos634.LaczL35 Erdos634.LaczL22 Erdos634.CertCoord Erdos634.DissectionMap Erdos634.CertGeom
open Erdos634.GlueCut (mem_carrier_mkTri_iff interiors_disjoint_of_cut)
open Erdos634.LaczL33 (equi_angle)

namespace Erdos634.LaczThm33If

theorem exists_chart : ∃ (u v : Plane) (hdet : u 0 * v 1 - u 1 * v 0 ≠ 0),
    inner ℝ u u = 1 ∧ inner ℝ v v = 1 ∧ inner ℝ u v = 1 / 2 := by
  obtain ⟨u, v, hu', hv', huv', hdet⟩ := Erdos634.LaczL24.exists_gram_chart 1 1 (1 / 2) one_pos one_pos (by norm_num)
  exact ⟨u, v, hdet, by simpa using hu', by simpa using hv', by simpa using huv'⟩

/-- squared chart distance -/
theorem qdist (u v : Plane) (hdet : u 0 * v 1 - u 1 * v 0 ≠ 0) (hu : inner ℝ u u = 1) (hv : inner ℝ v v = 1)
    (huv : inner ℝ u v = 1 / 2) (p q : Plane) :
    dist (chartEquiv 0 u v hdet p) (chartEquiv 0 u v hdet q) ^ 2
      = (p 0 - q 0) ^ 2 + (p 0 - q 0) * (p 1 - q 1) + (p 1 - q 1) ^ 2 := by
  rw [dist_chart_sq, hu, hv, huv]; ring

/-- SSS from squared distances, with a vertex permutation. -/
theorem cong_sq (T U : Tri) (σ : Equiv.Perm (Fin 3))
    (h01 : dist (T.pts 0) (T.pts 1) ^ 2 = dist (U.pts (σ 0)) (U.pts (σ 1)) ^ 2)
    (h12 : dist (T.pts 1) (T.pts 2) ^ 2 = dist (U.pts (σ 1)) (U.pts (σ 2)) ^ 2)
    (h20 : dist (T.pts 2) (T.pts 0) ^ 2 = dist (U.pts (σ 2)) (U.pts (σ 0)) ^ 2) : T.Congruent U := by
  have e01 := Erdos634.SssCongruent.dist_of_sq h01
  have e12 := Erdos634.SssCongruent.dist_of_sq h12
  have e20 := Erdos634.SssCongruent.dist_of_sq h20
  refine Erdos634.SssCongruent.congruent_of_dist_perm σ ?_
  clear h01 h12 h20
  have htri : ∀ y : Fin 3, y = 0 ∨ y = 1 ∨ y = 2 := by decide
  intro i j
  rcases htri i with rfl | rfl | rfl <;> rcases htri j with rfl | rfl | rfl <;> simp_all [dist_comm]

theorem ang_cos (p q r : Plane) (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (h1 : dist p q = a) (h2 : dist r q = b)
    (h3 : dist p r = c) : Real.cos (cornerAngle p q r) = (a ^ 2 + b ^ 2 - c ^ 2) / (2 * a * b) := by
  have := Erdos634.AngleThreshold.cos_of_sides p q r (by rw [h1]; exact ha.ne') (by rw [h2]; exact hb.ne')
  rw [h1, h2, h3] at this; exact this

theorem ang_eq (p q r : Plane) (a b c θ : ℝ) (ha : 0 < a) (hb : 0 < b) (h1 : dist p q = a) (h2 : dist r q = b)
    (h3 : dist p r = c) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ Real.pi) (hc : (a ^ 2 + b ^ 2 - c ^ 2) / (2 * a * b) = Real.cos θ) :
    cornerAngle p q r = θ :=
  angle_eq_of_cos (EuclideanGeometry.angle_nonneg _ _ _) (EuclideanGeometry.angle_le_pi _ _ _) hθ0 hθ1
    ((ang_cos p q r a b c ha hb h1 h2 h3).trans hc)

theorem dist_of_sq' {p q : Plane} {a : ℝ} (ha : 0 ≤ a) (h : dist p q ^ 2 = a ^ 2) : dist p q = a :=
  eq_of_sq_eq' dist_nonneg ha h

/-- the equilateral triangle of side `s` in the chart has angles `π/3`. -/
theorem equi_chart (u v : Plane) (hdet : u 0 * v 1 - u 1 * v 0 ≠ 0) (hu : inner ℝ u u = 1) (hv : inner ℝ v v = 1)
    (huv : inner ℝ u v = 1 / 2) (s : ℝ) (hs : 0 < s) (h : det3 0 0 s 0 0 s ≠ 0) :
    ∀ k, (mapTri (chartEquiv 0 u v hdet) (mkTri 0 0 s 0 0 s h)).angleAt k = Real.pi / 3 := by
  set e := chartEquiv 0 u v hdet with he
  have d3 : ∀ p q : Plane, (p 0 - q 0) ^ 2 + (p 0 - q 0) * (p 1 - q 1) + (p 1 - q 1) ^ 2 = s ^ 2 →
      dist (e p) (e q) = s := by
    intro p q h
    exact eq_of_sq_eq' dist_nonneg hs.le (by rw [he, qdist u v hdet hu hv huv, h])
  have D01 : dist (e (mkPt 0 0)) (e (mkPt s 0)) = s := d3 _ _ (by first | (simp; done) | (simp; ring))
  have D02 : dist (e (mkPt 0 0)) (e (mkPt 0 s)) = s := d3 _ _ (by first | (simp; done) | (simp; ring))
  have D12 : dist (e (mkPt s 0)) (e (mkPt 0 s)) = s := d3 _ _ (by first | (simp; done) | (simp; ring))
  intro k
  have htri : ∀ y : Fin 3, y = 0 ∨ y = 1 ∨ y = 2 := by decide
  rcases htri k with rfl | rfl | rfl
  · show cornerAngle (e (mkPt s 0)) (e (mkPt 0 0)) (e (mkPt 0 s)) = _
    exact equi_angle _ _ _ s hs (by rw [dist_comm]; exact D01) (by rw [dist_comm]; exact D02) D12
  · show cornerAngle (e (mkPt 0 s)) (e (mkPt s 0)) (e (mkPt 0 0)) = _
    exact equi_angle _ _ _ s hs (by rw [dist_comm]; exact D12) D01 (by rw [dist_comm]; exact D02)
  · show cornerAngle (e (mkPt 0 0)) (e (mkPt 0 s)) (e (mkPt s 0)) = _
    exact equi_angle _ _ _ s hs D02 D12 D01

/-- Transport a coordinate dissection of the chart triangle to a `CongruentDissection`. -/
noncomputable def mkCD {n : ℕ} (e : Plane ≃ᵃ[ℝ] Plane) (T0 : Tri) (t : Fin n → Tri)
    (hcov : (⋃ i, (t i).carrier) = T0.carrier)
    (hdis : Pairwise fun i j => Disjoint (interior (t i).carrier) (interior (t j).carrier))
    (M : Tri) (hcong : ∀ i, (mapTri e (t i)).Congruent M) : CongruentDissection n where
  toDissection := mapDissection e ⟨T0, t, hcov, hdis⟩
  model := M
  tiles_congruent := hcong

theorem mkCD_target {n : ℕ} (e : Plane ≃ᵃ[ℝ] Plane) (T0 : Tri) (t : Fin n → Tri) hcov hdis (M : Tri) hcong :
    (mkCD e T0 t hcov hdis M hcong).target = mapTri e T0 := rfl

/-! ### clause (ii): the median split -/

section clause_ii

private theorem hT0 : 0 < det3 0 0 2 0 0 2 := by simp [det3]
private theorem hA1 : 0 < det3 0 0 2 0 1 1 := by simp [det3]
private theorem hA2 : 0 < det3 0 0 1 1 0 2 := by simp [det3]

noncomputable def tII : Fin 2 → Tri := ![mkTri 0 0 2 0 1 1 hA1.ne', mkTri 0 0 1 1 0 2 hA2.ne']

theorem cov_ii : (⋃ i, (tII i).carrier) = (mkTri 0 0 2 0 0 2 hT0.ne').carrier := by
  ext p
  simp only [Set.mem_iUnion, Fin.exists_fin_two, tII]
  show (p ∈ (mkTri 0 0 2 0 1 1 hA1.ne').carrier ∨ p ∈ (mkTri 0 0 1 1 0 2 hA2.ne').carrier) ↔ _
  rw [mem_carrier_mkTri_iff hA1, mem_carrier_mkTri_iff hA2, mem_carrier_mkTri_iff hT0]
  simp only [det3]
  constructor
  · rintro (⟨a, b, c⟩ | ⟨a, b, c⟩) <;> refine ⟨?_, ?_, ?_⟩ <;> nlinarith
  · rintro ⟨a, b, c⟩
    by_cases h : p 1 ≤ p 0
    · exact Or.inl ⟨by nlinarith, by nlinarith, by nlinarith⟩
    · exact Or.inr ⟨by nlinarith, by nlinarith, by nlinarith⟩

theorem dis_ii : Pairwise fun i j => Disjoint (interior (tII i).carrier) (interior (tII j).carrier) := by
  have key : Disjoint (interior (mkTri 0 0 2 0 1 1 hA1.ne').carrier) (interior (mkTri 0 0 1 1 0 2 hA2.ne').carrier) := by
    refine interiors_disjoint_of_cut (lineFun 0 0 1 1) (lineFun_linear_ne_zero (Or.inl (by norm_num))) ?_ ?_
    · intro x hx
      rw [mem_carrier_mkTri_iff hA1] at hx
      simp only [lineFun_apply, det3] at hx ⊢; nlinarith [hx.1, hx.2.1, hx.2.2]
    · intro x hx
      rw [mem_carrier_mkTri_iff hA2] at hx
      simp only [lineFun_apply, det3] at hx ⊢; nlinarith [hx.1, hx.2.1, hx.2.2]
  intro i j hij
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij
  · exact key
  · exact key.symm
  · exact absurd rfl hij

/-- distances between chart points of given coordinates -/
theorem cdist (u v : Plane) (hdet : u 0 * v 1 - u 1 * v 0 ≠ 0) (hu : inner ℝ u u = 1) (hv : inner ℝ v v = 1)
    (huv : inner ℝ u v = 1 / 2) (x y x' y' a : ℝ) (ha : 0 ≤ a)
    (h : (x - x') ^ 2 + (x - x') * (y - y') + (y - y') ^ 2 = a ^ 2) :
    dist (chartEquiv 0 u v hdet (mkPt x y)) (chartEquiv 0 u v hdet (mkPt x' y')) = a := by
  apply dist_of_sq' ha
  rw [qdist u v hdet hu hv huv]; simpa using h

theorem sq3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)

theorem clause_ii : ∃ (N : ℕ) (D : CongruentDissection N), Equilateral D ∧
    TileAngles D (Real.pi / 6) (Real.pi / 2) (Real.pi / 3) := by
  obtain ⟨u, v, hdet, hu, hv, huv⟩ := exists_chart
  set e := chartEquiv 0 u v hdet with he
  have q := qdist u v hdet hu hv huv
  have pt : ∀ (x y : ℝ) (x' y' : ℝ), dist (e (mkPt x y)) (e (mkPt x' y')) ^ 2
      = (x - x') ^ 2 + (x - x') * (y - y') + (y - y') ^ 2 := by
    intro x y x' y'; rw [he, q]; simp
  have cd := cdist u v hdet hu hv huv
  have hs0 : Equiv.swap (1 : Fin 3) 2 0 = 0 := by decide
  have hs1 : Equiv.swap (1 : Fin 3) 2 1 = 2 := by decide
  have hs2 : Equiv.swap (1 : Fin 3) 2 2 = 1 := by decide
  have hcong : ∀ i, (mapTri e (tII i)).Congruent (mapTri e (tII 0)) := by
    intro i
    fin_cases i
    · exact Tri.Congruent.refl _
    · refine cong_sq _ _ (Equiv.swap 1 2) ?_ ?_ ?_
      · rw [hs0, hs1]
        show dist (e (mkPt 0 0)) (e (mkPt 1 1)) ^ 2 = dist (e (mkPt 0 0)) (e (mkPt 1 1)) ^ 2
        rfl
      · rw [hs1, hs2]
        show dist (e (mkPt 1 1)) (e (mkPt 0 2)) ^ 2 = dist (e (mkPt 1 1)) (e (mkPt 2 0)) ^ 2
        rw [pt, pt]; norm_num
      · rw [hs2, hs0]
        show dist (e (mkPt 0 2)) (e (mkPt 0 0)) ^ 2 = dist (e (mkPt 2 0)) (e (mkPt 0 0)) ^ 2
        rw [pt, pt]; norm_num
  have s3pos : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have s3 := sq3
  -- model distances
  have d10 : dist (e (mkPt 2 0)) (e (mkPt 0 0)) = 2 := cd _ _ _ _ _ (by norm_num) (by norm_num)
  have d20 : dist (e (mkPt 1 1)) (e (mkPt 0 0)) = Real.sqrt 3 := cd _ _ _ _ _ s3pos.le (by norm_num [s3])
  have d12 : dist (e (mkPt 2 0)) (e (mkPt 1 1)) = 1 := cd _ _ _ _ _ (by norm_num) (by norm_num)
  refine ⟨2, mkCD e _ tII cov_ii dis_ii (mapTri e (tII 0)) hcong, ?_, ?_⟩
  · exact equi_chart u v hdet hu hv huv 2 two_pos hT0.ne'
  · refine ⟨Equiv.swap 1 2, ?_, ?_, ?_⟩
    · rw [hs0]
      show cornerAngle (e (mkPt 2 0)) (e (mkPt 0 0)) (e (mkPt 1 1)) = _
      refine ang_eq _ _ _ 2 (Real.sqrt 3) 1 _ (by norm_num) s3pos d10 d20 d12 (by positivity)
        (by linarith [Real.pi_pos]) ?_
      rw [Real.cos_pi_div_six]; field_simp; nlinarith [s3]
    · rw [hs1]
      show cornerAngle (e (mkPt 0 0)) (e (mkPt 1 1)) (e (mkPt 2 0)) = _
      refine ang_eq _ _ _ (Real.sqrt 3) 1 2 _ s3pos (by norm_num) (by rw [dist_comm]; exact d20)
        d12 (by rw [dist_comm]; exact d10) (by positivity)
        (by linarith [Real.pi_pos]) ?_
      rw [Real.cos_pi_div_two]; rw [s3]; norm_num
    · rw [hs2]
      show cornerAngle (e (mkPt 1 1)) (e (mkPt 2 0)) (e (mkPt 0 0)) = _
      refine ang_eq _ _ _ 1 2 (Real.sqrt 3) _ (by norm_num) (by norm_num) (by rw [dist_comm]; exact d12)
        (by rw [dist_comm]; exact d10) d20 (by positivity) (by linarith [Real.pi_pos]) ?_
      rw [Real.cos_pi_div_three, s3]; norm_num

end clause_ii

/-! ### clause (i): the centre split -/

section clause_i

private theorem hT0' : 0 < det3 0 0 2 0 0 2 := by simp [det3]
private theorem hB1 : 0 < det3 0 0 2 0 (2 / 3) (2 / 3) := by norm_num [det3]
private theorem hB2 : 0 < det3 2 0 0 2 (2 / 3) (2 / 3) := by norm_num [det3]
private theorem hB3 : 0 < det3 0 2 0 0 (2 / 3) (2 / 3) := by norm_num [det3]

noncomputable def tI : Fin 3 → Tri :=
  ![mkTri 0 0 2 0 (2 / 3) (2 / 3) hB1.ne', mkTri 2 0 0 2 (2 / 3) (2 / 3) hB2.ne',
    mkTri 0 2 0 0 (2 / 3) (2 / 3) hB3.ne']

theorem cov_i : (⋃ i, (tI i).carrier) = (mkTri 0 0 2 0 0 2 hT0'.ne').carrier := by
  ext p
  simp only [Set.mem_iUnion, tI]
  have e3 : (∃ i : Fin 3, p ∈ (![mkTri 0 0 2 0 (2 / 3) (2 / 3) hB1.ne', mkTri 2 0 0 2 (2 / 3) (2 / 3) hB2.ne',
      mkTri 0 2 0 0 (2 / 3) (2 / 3) hB3.ne'] i).carrier) ↔
      (p ∈ (mkTri 0 0 2 0 (2 / 3) (2 / 3) hB1.ne').carrier ∨ p ∈ (mkTri 2 0 0 2 (2 / 3) (2 / 3) hB2.ne').carrier ∨
        p ∈ (mkTri 0 2 0 0 (2 / 3) (2 / 3) hB3.ne').carrier) := by
    constructor
    · rintro ⟨i, hi⟩
      fin_cases i
      · exact Or.inl hi
      · exact Or.inr (Or.inl hi)
      · exact Or.inr (Or.inr hi)
    · rintro (h | h | h)
      · exact ⟨0, h⟩
      · exact ⟨1, h⟩
      · exact ⟨2, h⟩
  rw [e3, mem_carrier_mkTri_iff hB1, mem_carrier_mkTri_iff hB2, mem_carrier_mkTri_iff hB3,
    mem_carrier_mkTri_iff hT0']
  simp only [det3]
  constructor
  · rintro (⟨a, b, c⟩ | ⟨a, b, c⟩ | ⟨a, b, c⟩) <;> refine ⟨?_, ?_, ?_⟩ <;> nlinarith
  · rintro ⟨a, b, c⟩
    by_cases h1 : p 1 ≤ p 0 ∧ p 0 + 2 * p 1 ≤ 2
    · exact Or.inl ⟨by nlinarith [h1.1, h1.2], by nlinarith [h1.1, h1.2], by nlinarith [h1.1, h1.2]⟩
    · by_cases h2 : 2 ≤ p 0 + 2 * p 1 ∧ 2 ≤ 2 * p 0 + p 1
      · exact Or.inr (Or.inl ⟨by nlinarith [h2.1, h2.2], by nlinarith [h2.1, h2.2], by nlinarith [h2.1, h2.2]⟩)
      · have h3 : p 0 ≤ p 1 ∧ 2 * p 0 + p 1 ≤ 2 := by
          by_contra hh
          rw [not_and_or] at hh h1 h2
          push_neg at hh h1 h2
          rcases hh with hh | hh <;> rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> linarith
        exact Or.inr (Or.inr ⟨by nlinarith [h3.1, h3.2], by nlinarith [h3.1, h3.2], by nlinarith [h3.1, h3.2]⟩)

theorem dis_i : Pairwise fun i j => Disjoint (interior (tI i).carrier) (interior (tI j).carrier) := by
  have k12 : Disjoint (interior (mkTri 2 0 0 2 (2 / 3) (2 / 3) hB2.ne').carrier)
      (interior (mkTri 0 0 2 0 (2 / 3) (2 / 3) hB1.ne').carrier) := by
    refine interiors_disjoint_of_cut (lineFun 2 0 (2 / 3) (2 / 3)) (lineFun_linear_ne_zero (Or.inl (by norm_num))) ?_ ?_
    · intro x hx
      rw [mem_carrier_mkTri_iff hB2] at hx
      simp only [lineFun_apply, det3] at hx ⊢; nlinarith [hx.1, hx.2.1, hx.2.2]
    · intro x hx
      rw [mem_carrier_mkTri_iff hB1] at hx
      simp only [lineFun_apply, det3] at hx ⊢; nlinarith [hx.1, hx.2.1, hx.2.2]
  have k23 : Disjoint (interior (mkTri 0 2 0 0 (2 / 3) (2 / 3) hB3.ne').carrier)
      (interior (mkTri 2 0 0 2 (2 / 3) (2 / 3) hB2.ne').carrier) := by
    refine interiors_disjoint_of_cut (lineFun 0 2 (2 / 3) (2 / 3)) (lineFun_linear_ne_zero (Or.inl (by norm_num))) ?_ ?_
    · intro x hx
      rw [mem_carrier_mkTri_iff hB3] at hx
      simp only [lineFun_apply, det3] at hx ⊢; nlinarith [hx.1, hx.2.1, hx.2.2]
    · intro x hx
      rw [mem_carrier_mkTri_iff hB2] at hx
      simp only [lineFun_apply, det3] at hx ⊢; nlinarith [hx.1, hx.2.1, hx.2.2]
  have k31 : Disjoint (interior (mkTri 0 0 2 0 (2 / 3) (2 / 3) hB1.ne').carrier)
      (interior (mkTri 0 2 0 0 (2 / 3) (2 / 3) hB3.ne').carrier) := by
    refine interiors_disjoint_of_cut (lineFun 0 0 (2 / 3) (2 / 3)) (lineFun_linear_ne_zero (Or.inl (by norm_num))) ?_ ?_
    · intro x hx
      rw [mem_carrier_mkTri_iff hB1] at hx
      simp only [lineFun_apply, det3] at hx ⊢; nlinarith [hx.1, hx.2.1, hx.2.2]
    · intro x hx
      rw [mem_carrier_mkTri_iff hB3] at hx
      simp only [lineFun_apply, det3] at hx ⊢; nlinarith [hx.1, hx.2.1, hx.2.2]
  intro i j hij
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij
  · exact k12.symm
  · exact k31
  · exact k12
  · exact absurd rfl hij
  · exact k23.symm
  · exact k31.symm
  · exact k23
  · exact absurd rfl hij

theorem clause_i : ∃ (N : ℕ) (D : CongruentDissection N), Equilateral D ∧
    TileAngles D (Real.pi / 6) (Real.pi / 6) (2 * Real.pi / 3) := by
  obtain ⟨u, v, hdet, hu, hv, huv⟩ := exists_chart
  set e := chartEquiv 0 u v hdet with he
  have q := qdist u v hdet hu hv huv
  have pt : ∀ (x y : ℝ) (x' y' : ℝ), dist (e (mkPt x y)) (e (mkPt x' y')) ^ 2
      = (x - x') ^ 2 + (x - x') * (y - y') + (y - y') ^ 2 := by
    intro x y x' y'; rw [he, q]; simp
  have cd := cdist u v hdet hu hv huv
  have hcong : ∀ i, (mapTri e (tI i)).Congruent (mapTri e (tI 0)) := by
    intro i
    fin_cases i
    · exact Tri.Congruent.refl _
    · refine cong_sq _ _ (Equiv.refl _) ?_ ?_ ?_
      · show dist (e (mkPt 2 0)) (e (mkPt 0 2)) ^ 2 = dist (e (mkPt 0 0)) (e (mkPt 2 0)) ^ 2
        rw [pt, pt]; norm_num
      · show dist (e (mkPt 0 2)) (e (mkPt (2 / 3) (2 / 3))) ^ 2 = dist (e (mkPt 2 0)) (e (mkPt (2 / 3) (2 / 3))) ^ 2
        rw [pt, pt]; norm_num
      · show dist (e (mkPt (2 / 3) (2 / 3))) (e (mkPt 2 0)) ^ 2 = dist (e (mkPt (2 / 3) (2 / 3))) (e (mkPt 0 0)) ^ 2
        rw [pt, pt]; norm_num
    · refine cong_sq _ _ (Equiv.refl _) ?_ ?_ ?_
      · show dist (e (mkPt 0 2)) (e (mkPt 0 0)) ^ 2 = dist (e (mkPt 0 0)) (e (mkPt 2 0)) ^ 2
        rw [pt, pt]; norm_num
      · show dist (e (mkPt 0 0)) (e (mkPt (2 / 3) (2 / 3))) ^ 2 = dist (e (mkPt 2 0)) (e (mkPt (2 / 3) (2 / 3))) ^ 2
        rw [pt, pt]; norm_num
      · show dist (e (mkPt (2 / 3) (2 / 3))) (e (mkPt 0 2)) ^ 2 = dist (e (mkPt (2 / 3) (2 / 3))) (e (mkPt 0 0)) ^ 2
        rw [pt, pt]; norm_num
  have s3pos : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have s3 := sq3
  set s : ℝ := Real.sqrt (4 / 3) with hsdef
  have spos : 0 < s := Real.sqrt_pos.mpr (by norm_num)
  have s2 : s ^ 2 = 4 / 3 := Real.sq_sqrt (by norm_num)
  have hk : Real.sqrt 3 * s = 2 := by
    have h2 : (Real.sqrt 3 * s) ^ 2 = 2 ^ 2 := by rw [mul_pow, s3, s2]; norm_num
    exact (sq_eq_sq₀ (by positivity) (by norm_num)).mp h2
  have d10 : dist (e (mkPt 2 0)) (e (mkPt 0 0)) = 2 := cd _ _ _ _ _ (by norm_num) (by norm_num)
  have d20 : dist (e (mkPt (2 / 3) (2 / 3))) (e (mkPt 0 0)) = s := cd _ _ _ _ _ spos.le (by rw [s2]; norm_num)
  have d12 : dist (e (mkPt 2 0)) (e (mkPt (2 / 3) (2 / 3))) = s := cd _ _ _ _ _ spos.le (by rw [s2]; norm_num)
  refine ⟨3, mkCD e _ tI cov_i dis_i (mapTri e (tI 0)) hcong, ?_, ?_⟩
  · exact equi_chart u v hdet hu hv huv 2 two_pos hT0'.ne'
  · refine ⟨Equiv.refl _, ?_, ?_, ?_⟩
    · show cornerAngle (e (mkPt 2 0)) (e (mkPt 0 0)) (e (mkPt (2 / 3) (2 / 3))) = _
      refine ang_eq _ _ _ 2 s s _ (by norm_num) spos d10 d20 d12 (by positivity)
        (by linarith [Real.pi_pos]) ?_
      rw [Real.cos_pi_div_six]; field_simp; nlinarith [hk]
    · show cornerAngle (e (mkPt (2 / 3) (2 / 3))) (e (mkPt 2 0)) (e (mkPt 0 0)) = _
      refine ang_eq _ _ _ s 2 s _ spos (by norm_num) (by rw [dist_comm]; exact d12) (by rw [dist_comm]; exact d10)
        d20 (by positivity) (by linarith [Real.pi_pos]) ?_
      rw [Real.cos_pi_div_six]; field_simp; nlinarith [hk]
    · show cornerAngle (e (mkPt 0 0)) (e (mkPt (2 / 3) (2 / 3))) (e (mkPt 2 0)) = _
      refine ang_eq _ _ _ s s 2 _ spos spos (by rw [dist_comm]; exact d20) d12
        (by rw [dist_comm]; exact d10) (by positivity) (by linarith [Real.pi_pos]) ?_
      rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring, Real.cos_pi_sub, Real.cos_pi_div_three]
      field_simp; nlinarith [s2]

end clause_i

#print axioms Erdos634.LaczThm33If.clause_i
#print axioms Erdos634.LaczThm33If.clause_ii

end Erdos634.LaczThm33If
