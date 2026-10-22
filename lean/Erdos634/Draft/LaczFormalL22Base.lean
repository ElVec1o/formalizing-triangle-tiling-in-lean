import Erdos634.Draft.LaczFormalL21
import Erdos634.CertCoord
import Erdos634.CertGeom
import Erdos634.SssCongruent

/-!
# Laczkovich (Discrete Math 140 (1995)), Sect. 2: base layer for Lemma 2.2 and Theorem 2.4

NOTE, UNAUDITED.  Credit: Laczkovich (Discrete Math. 140 (1995) 79-94), Beeson, Beeson-Zhang, Zhang.

Vocabulary used by the later files.

* `RatSimTile Δ T`  : `T` has rational sides and is a homothetic copy (any real ratio) of `Δ`, up to congruence.
* `RatSimDiss Δ S`  : the set `S` is the union of finitely many `RatSimTile` triangles with pairwise disjoint
  interiors.  `RatSimDiss.union` glues two such sets with disjoint interiors; `RatSimDiss.toCongruent`
  feeds Lemma 2.1 (`LaczL21.lemma21`).
* chart `chartEquiv A w d` : the affine equivalence `x ↦ A + x₀ w + x₁ d` of the plane (needs `w`, `d`
  independent).  All dissections are built in the standard chart plane by coordinates and moved by
  `ofChartTiles`; similarity is then tested through the Gram data of `(w, d)` (`dist_chart_sq`) and the
  squared-side criterion `congr_of_sq3` (rational arithmetic only).
-/

namespace Erdos634.LaczL22

open Erdos634.Geometry Erdos634.LaczL21 Erdos634.Realizable Erdos634.CertCoord

/-! ## Rational similar tiles and dissections -/

/-- `T` has rational sides and is congruent to a homothetic copy of `Δ`. -/
def RatSimTile (Δ T : Tri) : Prop :=
  IsRationalTri T ∧ ∃ (ρ : ℝ) (hρ : 0 < ρ), T.Congruent (scaleTri ρ hρ.ne' Δ)

/-- `S` is dissected into finitely many rational triangles similar to `Δ`. -/
def RatSimDiss (Δ : Tri) (S : Set Plane) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (t : ι → Tri), (⋃ i, (t i).carrier) = S ∧
    (∀ i j, i ≠ j → Disjoint (interior (t i).carrier) (interior (t j).carrier)) ∧
    ∀ i, RatSimTile Δ (t i)

theorem RatSimDiss.union {Δ : Tri} {S₁ S₂ : Set Plane} (h₁ : RatSimDiss Δ S₁) (h₂ : RatSimDiss Δ S₂)
    (hd : Disjoint (interior S₁) (interior S₂)) : RatSimDiss Δ (S₁ ∪ S₂) := by
  obtain ⟨ι₁, f₁, t₁, c₁, d₁, r₁⟩ := h₁
  obtain ⟨ι₂, f₂, t₂, c₂, d₂, r₂⟩ := h₂
  refine ⟨ι₁ ⊕ ι₂, inferInstance, Sum.elim t₁ t₂, ?_, ?_, ?_⟩
  · rw [Set.iUnion_sum]
    simp only [Sum.elim_inl, Sum.elim_inr]
    rw [c₁, c₂]
  · have s₁ : ∀ i, interior (t₁ i).carrier ⊆ interior S₁ := fun i =>
      interior_mono (c₁ ▸ Set.subset_iUnion (fun i => (t₁ i).carrier) i)
    have s₂ : ∀ i, interior (t₂ i).carrier ⊆ interior S₂ := fun i =>
      interior_mono (c₂ ▸ Set.subset_iUnion (fun i => (t₂ i).carrier) i)
    intro i j hij
    rcases i with i | i <;> rcases j with j | j
    · exact d₁ i j (fun h => hij (by rw [h]))
    · exact hd.mono (s₁ i) (s₂ j)
    · exact (hd.mono (s₁ j) (s₂ i)).symm
    · exact d₂ i j (fun h => hij (by rw [h]))
  · intro i
    rcases i with i | i
    · exact r₁ i
    · exact r₂ i

theorem RatSimDiss.empty (Δ : Tri) : RatSimDiss Δ (∅ : Set Plane) := by
  refine ⟨Empty, inferInstance, fun e => e.elim, ?_, ?_, ?_⟩
  · simp
  · intro i; exact i.elim
  · intro i; exact i.elim

/-- **Bridge to Lemma 2.1.**  A rational similar dissection of `S` yields a dissection of `S` into
congruent triangles similar to `Δ` (Laczkovich Lemma 2.1). -/
theorem RatSimDiss.toCongruent {Δ : Tri} (hΔ : IsRationalTri Δ) {S : Set Plane}
    (h : RatSimDiss Δ S) :
    ∃ (q : ℕ) (hq : 0 < q) (M : ℕ) (C : Erdos634.RegionDissection.CongruentRegionDissection M),
      C.region = S ∧
      C.model = scaleTri (1 / (q : ℝ)) (one_div_pos.mpr (Nat.cast_pos.mpr hq)).ne' Δ := by
  obtain ⟨ι, fι, t, hc, hd, hr⟩ := h
  letI := fι
  let e := Fintype.equivFin ι
  let R : Erdos634.RegionDissection.RegionDissection (Fintype.card ι) :=
    { region := S
      tile := fun n => t (e.symm n)
      covers := by
        rw [← hc]
        exact e.symm.surjective.iUnion_comp (fun i => (t i).carrier)
      interiors_disjoint := fun n m hnm => hd _ _ (fun h => hnm (e.symm.injective h)) }
  have hρ : ∀ n, ∃ ρ : ℝ, ∃ hρ : 0 < ρ, (R.tile n).Congruent (scaleTri ρ hρ.ne' Δ) :=
    fun n => (hr (e.symm n)).2
  choose ρ hρpos hsim using hρ
  obtain ⟨q, hq, M, C, h1, h2⟩ := lemma21 Δ hΔ R ρ hρpos (fun n => (hr (e.symm n)).1) hsim
  exact ⟨q, hq, M, C, h1, h2⟩

/-- A tile congruent to a RATIONAL homothetic copy of a rational triangle is a rational tile. -/
theorem ratSimTile_of_cong {Δ T : Tri} (hΔ : IsRationalTri Δ) (k : ℚ) (hk : 0 < k)
    (hc : T.Congruent (scaleTri (k : ℝ) (by exact_mod_cast hk.ne') Δ)) : RatSimTile Δ T := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  refine ⟨?_, (k : ℝ), hk', hc⟩
  obtain ⟨σ, hσ⟩ := hc.dist_eq
  intro i j
  obtain ⟨s, hs⟩ := hΔ (σ i) (σ j)
  refine ⟨k * s, ?_⟩
  rw [hσ i j]
  simp only [scaleTri_pts]
  rw [Erdos634.Realizable.dist_homothety, hs, abs_of_pos hk']
  push_cast; ring

/-! ## Squared-side similarity criterion -/

theorem eq_of_sq_eq' {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (h : x ^ 2 = y ^ 2) : x = y := by
  nlinarith [sq_nonneg (x - y), sq_nonneg (x + y)]

/-- **SSS from squares.**  If the squared sides of `T` are `k²` times those of `Δ` (for a vertex
matching `σ`), then `T` is congruent to the scale-`k` copy of `Δ`. -/
theorem congr_of_sq3 (T Δ : Tri) (σ : Equiv.Perm (Fin 3)) (k : ℝ) (hk : 0 < k)
    (h01 : dist (T.pts 0) (T.pts 1) ^ 2 = k ^ 2 * dist (Δ.pts (σ 0)) (Δ.pts (σ 1)) ^ 2)
    (h12 : dist (T.pts 1) (T.pts 2) ^ 2 = k ^ 2 * dist (Δ.pts (σ 1)) (Δ.pts (σ 2)) ^ 2)
    (h20 : dist (T.pts 2) (T.pts 0) ^ 2 = k ^ 2 * dist (Δ.pts (σ 2)) (Δ.pts (σ 0)) ^ 2) :
    T.Congruent (scaleTri k hk.ne' Δ) := by
  set S := scaleTri k hk.ne' Δ with hS
  have hU : ∀ i j, dist ((S.relabel σ).pts i) ((S.relabel σ).pts j)
      = k * dist (Δ.pts (σ i)) (Δ.pts (σ j)) := by
    intro i j
    simp only [Tri.relabel_pts, hS, scaleTri_pts]
    rw [Erdos634.Realizable.dist_homothety, abs_of_pos hk]
  have e01 : dist (T.pts 0) (T.pts 1) = k * dist (Δ.pts (σ 0)) (Δ.pts (σ 1)) :=
    eq_of_sq_eq' dist_nonneg (by positivity) (by rw [h01]; ring)
  have e12 : dist (T.pts 1) (T.pts 2) = k * dist (Δ.pts (σ 1)) (Δ.pts (σ 2)) :=
    eq_of_sq_eq' dist_nonneg (by positivity) (by rw [h12]; ring)
  have e20 : dist (T.pts 2) (T.pts 0) = k * dist (Δ.pts (σ 2)) (Δ.pts (σ 0)) :=
    eq_of_sq_eq' dist_nonneg (by positivity) (by rw [h20]; ring)
  have hrel : T.Congruent (S.relabel σ) := by
    refine Erdos634.SssCongruent.congruent_of_dist ?_
    intro i j
    rw [hU]
    clear h01 h12 h20 hU
    have htri : ∀ y : Fin 3, y = 0 ∨ y = 1 ∨ y = 2 := by decide
    rcases htri i with rfl | rfl | rfl <;> rcases htri j with rfl | rfl | rfl <;>
      simp_all [dist_comm]
  exact hrel.trans (S.congruent_relabel σ).symm

/-! ## Charts -/

/-- The coordinate chart `x ↦ A + x₀ w + x₁ d`, as an affine equivalence (needs `det(w,d) ≠ 0`). -/
noncomputable def chartTri (A w d : Plane) (h : w 0 * d 1 - w 1 * d 0 ≠ 0) : Tri :=
  mkTri (A 0) (A 1) (A 0 + w 0) (A 1 + w 1) (A 0 + d 0) (A 1 + d 1) (by
    simp only [det3]; intro h'; apply h; linarith)


theorem mkPt_self (A : Plane) : mkPt (A 0) (A 1) = A := by
  ext i; fin_cases i <;> simp

theorem mkPt_add_coords (A w : Plane) : mkPt (A 0 + w 0) (A 1 + w 1) = A + w := by
  ext i; fin_cases i <;> simp

theorem chartTri_pts (A w d : Plane) (h : w 0 * d 1 - w 1 * d 0 ≠ 0) :
    (chartTri A w d h).pts 0 = A ∧ (chartTri A w d h).pts 1 = A + w ∧
      (chartTri A w d h).pts 2 = A + d := by
  refine ⟨?_, ?_, ?_⟩
  · simp [chartTri, mkTri_pts, mkPt_self]
  · simp [chartTri, mkTri_pts, mkPt_add_coords]
  · simp [chartTri, mkTri_pts, mkPt_add_coords]

theorem edgeMap_apply (T : Tri) (x : Plane) :
    Erdos634.AreaDet.edgeMap T x = x 0 • (T.pts 1 - T.pts 0) + x 1 • (T.pts 2 - T.pts 0) := by
  have hx : x = x 0 • Erdos634.AreaDet.pb 0 + x 1 • Erdos634.AreaDet.pb 1 := by
    conv_lhs => rw [← (Erdos634.AreaDet.pb).sum_repr x]
    simp [Fin.sum_univ_two, Erdos634.AreaDet.pb_repr]
  conv_lhs => rw [hx]
  rw [map_add, map_smul, map_smul, Erdos634.AreaDet.edgeMap_basis, Erdos634.AreaDet.edgeMap_basis]
  rfl

theorem chartTri_det_ne (A w d : Plane) (h : w 0 * d 1 - w 1 * d 0 ≠ 0) :
    LinearMap.det (Erdos634.AreaDet.edgeMap (chartTri A w d h)) ≠ 0 := by
  have := Erdos634.CertCoord.detTri_mkTri (A 0) (A 1) (A 0 + w 0) (A 1 + w 1) (A 0 + d 0) (A 1 + d 1)
    (by simp only [det3]; intro h'; apply h; linarith)
  show Erdos634.AreaDet.detTri (chartTri A w d h) ≠ 0
  unfold chartTri
  rw [this]
  simp only [det3]
  intro h'; apply h; linarith

/-- The chart `x ↦ A + x₀ w + x₁ d` as an affine equivalence of the plane. -/
noncomputable def chartEquiv (A w d : Plane) (h : w 0 * d 1 - w 1 * d 0 ≠ 0) :
    Plane ≃ᵃ[ℝ] Plane := by
  refine AffineEquiv.ofBijective (φ := Erdos634.AreaDet.placeMap (chartTri A w d h)) ?_
  have hne := chartTri_det_ne A w d h
  set e := LinearMap.equivOfDetNeZero _ hne with he
  have hcoe : ∀ x, e x = Erdos634.AreaDet.edgeMap (chartTri A w d h) x := fun x => by
    simp [he]
  constructor
  · intro x y hxy
    rw [Erdos634.AreaDet.placeMap_apply, Erdos634.AreaDet.placeMap_apply] at hxy
    have : Erdos634.AreaDet.edgeMap (chartTri A w d h) x
        = Erdos634.AreaDet.edgeMap (chartTri A w d h) y := add_left_cancel hxy
    rw [← hcoe, ← hcoe] at this
    exact e.injective this
  · intro y
    refine ⟨e.symm (y - (chartTri A w d h).pts 0), ?_⟩
    rw [Erdos634.AreaDet.placeMap_apply, ← hcoe, e.apply_symm_apply]
    abel

theorem chartEquiv_apply (A w d : Plane) (h : w 0 * d 1 - w 1 * d 0 ≠ 0) (x : Plane) :
    chartEquiv A w d h x = A + x 0 • w + x 1 • d := by
  show Erdos634.AreaDet.placeMap (chartTri A w d h) x = _
  rw [Erdos634.AreaDet.placeMap_apply, edgeMap_apply]
  obtain ⟨h0, h1, h2⟩ := chartTri_pts A w d h
  rw [h0, h1, h2]
  simp only [add_sub_cancel_left]
  abel

/-- **Gram formula.**  Squared distances between chart images. -/
theorem dist_chart_sq (A w d : Plane) (h : w 0 * d 1 - w 1 * d 0 ≠ 0) (p q : Plane) :
    dist (chartEquiv A w d h p) (chartEquiv A w d h q) ^ 2
      = (p 0 - q 0) ^ 2 * inner ℝ w w + 2 * ((p 0 - q 0) * (p 1 - q 1)) * inner ℝ w d
        + (p 1 - q 1) ^ 2 * inner ℝ d d := by
  rw [chartEquiv_apply, chartEquiv_apply, dist_eq_norm]
  have : A + p 0 • w + p 1 • d - (A + q 0 • w + q 1 • d) = (p 0 - q 0) • w + (p 1 - q 1) • d := by
    module
  rw [this, ← real_inner_self_eq_norm_sq]
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right]
  rw [real_inner_comm d w]
  ring

/-- Move a chart-plane dissection by the chart; the moved tiles must be rational similar tiles. -/
theorem ofChartTiles {Δ : Tri} (A w d : Plane) (h : w 0 * d 1 - w 1 * d 0 ≠ 0)
    {ι : Type} [Fintype ι] (t : ι → Tri) (S : Set Plane)
    (hc : (⋃ i, (t i).carrier) = S)
    (hd : ∀ i j, i ≠ j → Disjoint (interior (t i).carrier) (interior (t j).carrier))
    (hs : ∀ i, RatSimTile Δ (Erdos634.DissectionMap.mapTri (chartEquiv A w d h) (t i))) :
    RatSimDiss Δ (chartEquiv A w d h '' S) := by
  refine ⟨ι, inferInstance, fun i => Erdos634.DissectionMap.mapTri (chartEquiv A w d h) (t i),
    ?_, ?_, hs⟩
  · simp only [Erdos634.DissectionMap.mapTri_carrier]
    rw [← Set.image_iUnion, hc]
  · intro i j hij
    exact Erdos634.DissectionMap.mapTri_interiors_disjoint _ (hd i j hij)

end Erdos634.LaczL22
