-- Draft/CVCCevianCut.lean -- CVC: the geometric cevian cut of `prop:cevianatom` (companion tex:4649).
--
-- Paper: Delta_m = fm.T u fm.T u A_m, apex fan.  At (e,f)=(1,2), m = 4k: Delta_{4k} has sides
-- (32k,32k,44k); the atom A_{4k} (legs 24k, base 12k, apex W) sits between two scaled tiles
-- (16k,24k,32k) = (8k)*(2,3,4); the base is cut at 16k, 28k, 44k from the west corner.
-- Here: from ANY atom tiling DA of A_{4k} (apex W, base U V) we build the genuine union
-- CongruentDissection of Delta_{4k}, with all three carriers shown to cover Delta_{4k} and to have
-- pairwise disjoint interiors, vertex-free (no Z[sqrt 15] coordinates): pure vector/inner-product algebra.
-- UNAUDITED; promotes no label.  Imported via AllNew6.lean → All.lean:851 (stale "NOT imported" header corrected 2026-10-04).  No sorry, no native_decide.
import Erdos634.Draft.FDCCevianAtom
import Erdos634.UnionDissection
import Erdos634.SssCongruent
import Erdos634.Ladder
import Erdos634.DissectionMap
import Erdos634.CongruentArea
import Erdos634.CertCoord
import Erdos634.AreaDet
import Erdos634.Subdivision

namespace Erdos634.Draft.CVCCevianCut

open Erdos634.Geometry MeasureTheory
open Erdos634.Draft.FDBBaseBetaE1 (HasSides congruent_of_hasSides)
open Erdos634.Draft.FDCCevianAtom (atomTiles_four_mul hasSides_scaleN hasSides_congr)

/-! ## Coordinate toolkit -/

theorem dist_of_sqd (p q : Plane) (d : ℝ) (hd : 0 ≤ d)
    (h : (p 0 - q 0) ^ 2 + (p 1 - q 1) ^ 2 = d ^ 2) : dist p q = d := by
  rw [EuclideanSpace.dist_eq]
  simp only [Fin.sum_univ_two, Real.dist_eq, sq_abs]
  rw [h]; exact Real.sqrt_sq hd

theorem sqd_of_dist (p q : Plane) (d : ℝ) (h : dist p q = d) :
    (p 0 - q 0) ^ 2 + (p 1 - q 1) ^ 2 = d ^ 2 := by
  rw [← h, EuclideanSpace.dist_eq, Real.sq_sqrt (by positivity)]
  simp [Fin.sum_univ_two, Real.dist_eq, sq_abs]

/-- twice the signed area, `det3` on the coordinates -/
def cr (p q r : Plane) : ℝ := (q 0 - p 0) * (r 1 - p 1) - (r 0 - p 0) * (q 1 - p 1)

theorem mkPt_self (p : Plane) : CertCoord.mkPt (p 0) (p 1) = p := by
  ext i; fin_cases i <;> simp

/-- the triangle on three points with nonzero determinant -/
noncomputable def triOf (p q r : Plane) (h : cr p q r ≠ 0) : Tri where
  pts := ![p, q, r]
  indep := by
    have h1 := CertCoord.not_collinear_of_det (x₀ := p 0) (y₀ := p 1) (x₁ := q 0) (y₁ := q 1)
      (x₂ := r 0) (y₂ := r 1) h
    rw [mkPt_self, mkPt_self, mkPt_self] at h1
    exact (affineIndependent_iff_not_collinear_of_ne (show (0 : Fin 3) ≠ 1 by decide)
      (show (0 : Fin 3) ≠ 2 by decide) (show (1 : Fin 3) ≠ 2 by decide)).mpr h1

theorem range_three (p q r : Plane) : Set.range (![p, q, r] : Fin 3 → Plane) = {p, q, r} := by
  ext x
  simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp
  · rintro (rfl | rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩

theorem carrier_triOf (p q r : Plane) (h : cr p q r ≠ 0) :
    (triOf p q r h).carrier = convexHull ℝ {p, q, r} := by
  unfold Tri.carrier
  show convexHull ℝ (Set.range (![p, q, r] : Fin 3 → Plane)) = _
  rw [range_three]

/-- a genuine `Tri` has nonzero coordinate determinant -/
theorem cr_pts_ne_zero (T : Tri) : cr (T.pts 0) (T.pts 1) (T.pts 2) ≠ 0 := by
  intro hc
  have h := T.volume_pos
  rw [Erdos634.AreaDet.volume_eq_det_mul, Erdos634.AreaDet.detTri_eq] at h
  have h0 : (T.pts 1 - T.pts 0) 0 * (T.pts 2 - T.pts 0) 1
      - (T.pts 2 - T.pts 0) 0 * (T.pts 1 - T.pts 0) 1 = 0 := by
    simp only [PiLp.sub_apply]; unfold cr at hc; linarith
  rw [h0] at h; simp at h

theorem mem_hull3 {x p q r : Plane} (hx : x ∈ convexHull ℝ ({p, q, r} : Set Plane)) :
    ∃ a b c : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ a + b + c = 1 ∧ x = a • p + b • q + c • r := by
  rw [convexHull_insert (by simp), convexHull_pair] at hx
  obtain ⟨a, ha, y, hy, hxy⟩ := mem_convexJoin.mp hx
  rw [Set.mem_singleton_iff] at ha
  subst ha
  obtain ⟨s1, s2, hs1, hs2, hs, hx'⟩ := hxy
  obtain ⟨u1, u2, hu1, hu2, hu, hy'⟩ := hy
  refine ⟨s1, s2 * u1, s2 * u2, hs1, mul_nonneg hs2 hu1, mul_nonneg hs2 hu2, ?_, ?_⟩
  · have : s1 + s2 * u1 + s2 * u2 = s1 + s2 * (u1 + u2) := by ring
    rw [this, hu]; linarith
  · rw [← hx', ← hy']; module

/-! ## The fan lemma: a cevian splits a triangle -/

theorem fan_cover (W B C P : Plane) (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
    (hP : P = B + t • (C - B)) :
    convexHull ℝ ({W, B, C} : Set Plane) =
      convexHull ℝ {W, B, P} ∪ convexHull ℝ {W, P, C} := by
  have ht0' : t ≠ 0 := ht0.ne'
  have h1t : 0 < 1 - t := by linarith
  have h1t' : 1 - t ≠ 0 := h1t.ne'
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨a, b, c, ha, hb, hc, hs, rfl⟩ := mem_hull3 hx
    by_cases hcase : c * (1 - t) ≤ t * b
    · left
      have e : a • W + b • B + c • C
          = a • W + (b - c * (1 - t) / t) • B + (c / t) • P := by
        rw [hP]
        ext i
        simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
        field_simp
        ring
      rw [e]
      refine Erdos634.Subdivision.combo_mem W B P a _ _ ha ?_ (by positivity) ?_
      · rw [sub_nonneg, div_le_iff₀ ht0]; linarith
      · have e2 : (b - c * (1 - t) / t) + c / t = b + c := by field_simp; ring
        linarith
    · right
      push_neg at hcase
      have e : a • W + b • B + c • C
          = a • W + (b / (1 - t)) • P + (c - t * b / (1 - t)) • C := by
        rw [hP]
        ext i
        simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
        field_simp
        ring
      rw [e]
      refine Erdos634.Subdivision.combo_mem W P C a _ _ ha (by positivity) ?_ ?_
      · rw [sub_nonneg, div_le_iff₀ h1t]; linarith
      · have e2 : b / (1 - t) + (c - t * b / (1 - t)) = b + c := by field_simp; ring
        linarith
  · have hP' : P ∈ convexHull ℝ ({W, B, C} : Set Plane) := by
      have := Erdos634.Subdivision.combo_mem W B C 0 (1 - t) t le_rfl (by linarith) ht0.le (by ring)
      convert this using 1
      rw [hP]; module
    have hW : W ∈ convexHull ℝ ({W, B, C} : Set Plane) := subset_convexHull ℝ _ (by simp)
    have hB : B ∈ convexHull ℝ ({W, B, C} : Set Plane) := subset_convexHull ℝ _ (by simp)
    have hC : C ∈ convexHull ℝ ({W, B, C} : Set Plane) := subset_convexHull ℝ _ (by simp)
    refine Set.union_subset (convexHull_min ?_ (convex_convexHull ℝ _))
      (convexHull_min ?_ (convex_convexHull ℝ _))
    · exact Set.insert_subset_iff.mpr ⟨hW, Set.insert_subset_iff.mpr ⟨hB, Set.singleton_subset_iff.mpr hP'⟩⟩
    · exact Set.insert_subset_iff.mpr ⟨hW, Set.insert_subset_iff.mpr ⟨hP', Set.singleton_subset_iff.mpr hC⟩⟩

theorem fan_disjoint (W B C P : Plane) (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
    (hP : P = B + t • (C - B)) (hD : cr W B C ≠ 0) :
    Disjoint (interior (convexHull ℝ ({W, B, P} : Set Plane)))
      (interior (convexHull ℝ ({W, P, C} : Set Plane))) := by
  have hP0 : P 0 = B 0 + t * (C 0 - B 0) := by rw [hP]; simp
  have hP1 : P 1 = B 1 + t * (C 1 - B 1) := by rw [hP]; simp
  obtain ⟨D, hDd⟩ : ∃ D, D = cr W B C := ⟨_, rfl⟩
  have hD' : D ≠ 0 := by rw [hDd]; exact hD
  have hD2 : 0 < D ^ 2 := lt_of_le_of_ne (sq_nonneg D) (Ne.symm (pow_ne_zero 2 hD'))
  obtain ⟨ψ, hψ⟩ : ∃ ψ : Plane →L[ℝ] ℝ, ∀ x, ψ x = -(D * (P 1 - W 1)) * x 0 + (D * (P 0 - W 0)) * x 1 :=
    ⟨(-(D * (P 1 - W 1))) • EuclideanSpace.proj (0 : Fin 2) + (D * (P 0 - W 0)) • EuclideanSpace.proj (1 : Fin 2),
      fun x => by simp⟩
  have hvB : ψ B - ψ W = -(t * D ^ 2) := by
    rw [hψ, hψ, hP0, hP1, hDd]; unfold cr; ring_nf
  have hvP : ψ P - ψ W = 0 := by
    rw [hψ, hψ, hP0, hP1]; ring
  have hvC : ψ C - ψ W = (1 - t) * D ^ 2 := by
    rw [hψ, hψ, hP0, hP1, hDd]; unfold cr; ring_nf
  have htD : 0 < t * D ^ 2 := mul_pos ht0 hD2
  have htD' : 0 < (1 - t) * D ^ 2 := mul_pos (by linarith) hD2
  have hψne : ψ ≠ 0 := by
    intro h
    have h0 : ψ B - ψ W = 0 := by rw [h]; simp
    linarith
  have hopen : IsOpenMap ψ := ContinuousLinearMap.isOpenMap_of_ne_zero ψ hψne
  have hlin : IsLinearMap ℝ ψ := ψ.toLinearMap.isLinear
  have hS1 : convexHull ℝ ({W, B, P} : Set Plane) ⊆ {x | ψ x ≤ ψ W} := by
    apply convexHull_min
    · intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl | rfl
      · show ψ y ≤ ψ y; exact le_refl _
      · show ψ y ≤ ψ W; linarith
      · show ψ y ≤ ψ W; linarith
    · exact convex_halfSpace_le hlin _
  have hS2 : convexHull ℝ ({W, P, C} : Set Plane) ⊆ {x | ψ W ≤ ψ x} := by
    apply convexHull_min
    · intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl | rfl
      · show ψ y ≤ ψ y; exact le_refl _
      · show ψ W ≤ ψ y; linarith
      · show ψ W ≤ ψ y; linarith
    · exact convex_halfSpace_ge hlin _
  have hI1 : ∀ x ∈ interior (convexHull ℝ ({W, B, P} : Set Plane)), ψ x < ψ W := by
    intro x hx
    have h1 : ψ '' interior (convexHull ℝ ({W, B, P} : Set Plane)) ⊆ Set.Iic (ψ W) :=
      (Set.image_mono interior_subset).trans (Set.image_subset_iff.mpr hS1)
    have h2 := interior_maximal h1 (hopen _ isOpen_interior)
    rw [interior_Iic] at h2
    exact h2 ⟨x, hx, rfl⟩
  have hI2 : ∀ x ∈ interior (convexHull ℝ ({W, P, C} : Set Plane)), ψ W < ψ x := by
    intro x hx
    have h1 : ψ '' interior (convexHull ℝ ({W, P, C} : Set Plane)) ⊆ Set.Ici (ψ W) :=
      (Set.image_mono interior_subset).trans (Set.image_subset_iff.mpr hS2)
    have h2 := interior_maximal h1 (hopen _ isOpen_interior)
    rw [interior_Ici] at h2
    exact h2 ⟨x, hx, rfl⟩
  exact Set.disjoint_left.mpr fun x h1 h2 => lt_asymm (hI1 x h1) (hI2 x h2)

/-! ## Dissections: the one-tile dissection, transport, the scale-`K` tile -/

noncomputable def selfDissection (t : Tri) : CongruentDissection 1 where
  target := t
  tile := fun _ => t
  covers := by rw [Set.iUnion_const]
  interiors_disjoint := fun i j h => absurd (Subsingleton.elim i j) h
  model := t
  tiles_congruent := fun _ => Tri.Congruent.refl t

theorem transport {N : ℕ} (D : CongruentDissection N) (U : Tri) (h : D.target.Congruent U) :
    ∃ E : CongruentDissection N, E.target.carrier = U.carrier ∧ E.model = D.model := by
  obtain ⟨f, σ, hf⟩ := h
  refine ⟨{ Erdos634.DissectionMap.mapDissection (Erdos634.Ladder.isoAff f) D.toDissection with
            model := D.model
            tiles_congruent := ?_ }, ?_, rfl⟩
  · intro i
    show Tri.Congruent (Erdos634.DissectionMap.mapTri (Erdos634.Ladder.isoAff f) (D.tile i)) D.model
    exact (Erdos634.Ladder.congruent_mapTri f (D.tile i)).symm.trans (D.tiles_congruent i)
  · show (Erdos634.DissectionMap.mapTri (Erdos634.Ladder.isoAff f) D.target).carrier = U.carrier
    rw [Erdos634.DissectionMap.mapTri_carrier, Erdos634.Ladder.isoAff_coe]
    exact Erdos634.CongruentArea.image_carrier_of_congruent hf

theorem exists_reindex {N M : ℕ} (h : N = M) (D : CongruentDissection N) :
    ∃ E : CongruentDissection M, E.target = D.target ∧ E.model = D.model := by
  subst h; exact ⟨D, rfl, rfl⟩

/-- **A triangle with sides `K(2,3,4)` is cut into `K^2` copies of the tile `t` (sides `2,3,4`),
placed anywhere**: the ladder `Cut (K t) t (K*K*1)` transported by SSS congruence. -/
theorem tileK (t T : Tri) (K : ℕ) (hK : 0 < K) (ht : HasSides t 2 3 4)
    (hT : HasSides T ((K : ℝ) * 2) ((K : ℝ) * 3) ((K : ℝ) * 4)) :
    ∃ E : CongruentDissection (K * K * 1), E.target.carrier = T.carrier ∧ E.model = t := by
  obtain ⟨D, hDt, hDm⟩ := Erdos634.Realizable.cut_scale (T := t) (t := t) (N := 1)
    ⟨selfDissection t, rfl, rfl⟩ K hK
  have hS := hasSides_scaleN ht K hK
  obtain ⟨τ, h1, h2, h3⟩ := hT
  have hc : (Erdos634.Realizable.scaleN K hK t).Congruent T :=
    Tri.Congruent.trans (congruent_of_hasSides hS (U := T.relabel τ) h1 h2 h3)
      (Tri.congruent_relabel T τ).symm
  obtain ⟨E, hEc, hEm⟩ := transport D T (by rw [hDt]; exact hc)
  exact ⟨E, hEc, hEm.trans hDm⟩

/-! ## The assembly: Delta = T1 u A u T2 along the apex fan -/

theorem assemble (k : ℕ) (hk : 0 < k) (DA : CongruentDissection (3 * (4 * k) ^ 2))
    (ht : HasSides DA.model 2 3 4) (W U V : Plane)
    (hcar : DA.target.carrier = convexHull ℝ {W, U, V})
    (hUV : dist U V = 12 * k) (hVW : dist V W = 24 * k) (hWU : dist W U = 24 * k)
    (hD : cr W U V ≠ 0) :
    ∃ (Δ : Tri) (D : CongruentDissection ((8 * k) * (8 * k) * 1 + (3 * (4 * k) ^ 2 + (8 * k) * (8 * k) * 1)))
      (D1 : CongruentDissection ((8 * k) * (8 * k) * 1)) (D2 : CongruentDissection ((8 * k) * (8 * k) * 1)),
      HasSides Δ (32 * k) (32 * k) (44 * k) ∧ D.target = Δ ∧ HasSides D.model 2 3 4 ∧
      D1.model = D.model ∧ DA.model = D.model ∧ D2.model = D.model ∧
      (∃ T1 : Tri, HasSides T1 (16 * k) (24 * k) (32 * k) ∧ D1.target.carrier = T1.carrier) ∧
      (∃ T2 : Tri, HasSides T2 (16 * k) (24 * k) (32 * k) ∧ D2.target.carrier = T2.carrier) ∧
      D1.target.carrier ∪ (DA.target.carrier ∪ D2.target.carrier) = Δ.carrier ∧
      Disjoint (interior D1.target.carrier) (interior (DA.target.carrier ∪ D2.target.carrier)) ∧
      Disjoint (interior DA.target.carrier) (interior D2.target.carrier) ∧
      (∀ i, D.tile (Fin.castAdd _ i) = D1.tile i) ∧
      (∀ i, D.tile (Fin.natAdd _ (Fin.castAdd _ i)) = DA.tile i) ∧
      (∀ i, D.tile (Fin.natAdd _ (Fin.natAdd _ i)) = D2.tile i) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hUV' := sqd_of_dist _ _ _ hUV
  have hVW' := sqd_of_dist _ _ _ hVW
  have hWU' := sqd_of_dist _ _ _ hWU
  obtain ⟨X, hX⟩ : ∃ X : Plane, X = U - (4 / 3 : ℝ) • (V - U) := ⟨_, rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y : Plane, Y = V + (4 / 3 : ℝ) • (V - U) := ⟨_, rfl⟩
  have hX0 : X 0 = U 0 - 4 / 3 * (V 0 - U 0) := by rw [hX]; simp
  have hX1 : X 1 = U 1 - 4 / 3 * (V 1 - U 1) := by rw [hX]; simp
  have hY0 : Y 0 = V 0 + 4 / 3 * (V 0 - U 0) := by rw [hY]; simp
  have hY1 : Y 1 = V 1 + 4 / 3 * (V 1 - U 1) := by rw [hY]; simp
  -- determinants
  have c1 : cr W X Y ≠ 0 := by
    have : cr W X Y = 11 / 3 * cr W U V := by unfold cr; rw [hX0, hX1, hY0, hY1]; ring
    rw [this]; exact mul_ne_zero (by norm_num) hD
  have c2 : cr W X U ≠ 0 := by
    have : cr W X U = 4 / 3 * cr W U V := by unfold cr; rw [hX0, hX1]; ring
    rw [this]; exact mul_ne_zero (by norm_num) hD
  have c3 : cr W Y V ≠ 0 := by
    have : cr W Y V = -(4 / 3) * cr W U V := by unfold cr; rw [hY0, hY1]; ring
    rw [this]; exact mul_ne_zero (by norm_num) hD
  have c4 : cr W U Y ≠ 0 := by
    have : cr W U Y = 7 / 3 * cr W U V := by unfold cr; rw [hY0, hY1]; ring
    rw [this]; exact mul_ne_zero (by norm_num) hD
  -- distances
  have dWX : dist W X = 32 * k := dist_of_sqd _ _ _ (by positivity) (by
    rw [hX0, hX1]; linear_combination (7 / 3) * hWU' + (-4 / 3) * hVW' + (28 / 9) * hUV')
  have dXU : dist X U = 16 * k := dist_of_sqd _ _ _ (by positivity) (by
    rw [hX0, hX1]; linear_combination (16 / 9) * hUV')
  have dWY : dist W Y = 32 * k := dist_of_sqd _ _ _ (by positivity) (by
    rw [hY0, hY1]; linear_combination (-4 / 3) * hWU' + (7 / 3) * hVW' + (28 / 9) * hUV')
  have dYV : dist Y V = 16 * k := dist_of_sqd _ _ _ (by positivity) (by
    rw [hY0, hY1]; linear_combination (16 / 9) * hUV')
  have dXY : dist X Y = 44 * k := dist_of_sqd _ _ _ (by positivity) (by
    rw [hX0, hX1, hY0, hY1]; linear_combination (121 / 9) * hUV')
  have dUW : dist U W = 24 * k := by rw [dist_comm]; exact hWU
  have dWV : dist W V = 24 * k := by rw [dist_comm]; exact hVW
  -- the four triangles
  let Δ : Tri := triOf W X Y c1
  let T1 : Tri := triOf W X U c2
  let M : Tri := triOf W U Y c4
  let T2 : Tri := triOf W Y V c3
  have hs1 : HasSides T1 (16 * k) (24 * k) (32 * k) :=
    ⟨Equiv.refl _, dXU, dUW, dWX⟩
  have hs2 : HasSides T2 (16 * k) (24 * k) (32 * k) :=
    ⟨Equiv.refl _, dYV, hVW, dWY⟩
  have hsK1 : HasSides T1 (((8 * k : ℕ) : ℝ) * 2) (((8 * k : ℕ) : ℝ) * 3) (((8 * k : ℕ) : ℝ) * 4) :=
    hasSides_congr hs1 (by push_cast; ring) (by push_cast; ring) (by push_cast; ring)
  have hsK2 : HasSides T2 (((8 * k : ℕ) : ℝ) * 2) (((8 * k : ℕ) : ℝ) * 3) (((8 * k : ℕ) : ℝ) * 4) :=
    hasSides_congr hs2 (by push_cast; ring) (by push_cast; ring) (by push_cast; ring)
  have hk8 : 0 < 8 * k := by omega
  obtain ⟨E1, hE1c, hE1m⟩ := tileK DA.model T1 (8 * k) hk8 ht hsK1
  obtain ⟨E2, hE2c, hE2m⟩ := tileK DA.model T2 (8 * k) hk8 ht hsK2
  have hsw : ({W, V, Y} : Set Plane) = {W, Y, V} := by rw [Set.pair_comm V Y]
  have hP1 : U = X + (4 / 11 : ℝ) • (Y - X) := by rw [hX, hY]; module
  have hP2 : V = U + (3 / 7 : ℝ) • (Y - U) := by rw [hY]; module
  have cov1 := fan_cover W X Y U (4 / 11) (by norm_num) (by norm_num) hP1
  have dis1 := fan_disjoint W X Y U (4 / 11) (by norm_num) (by norm_num) hP1 c1
  have cov2 := fan_cover W U Y V (3 / 7) (by norm_num) (by norm_num) hP2
  have dis2 := fan_disjoint W U Y V (3 / 7) (by norm_num) (by norm_num) hP2 c4
  have hT1c : T1.carrier = convexHull ℝ {W, X, U} := carrier_triOf _ _ _ c2
  have hT2c : T2.carrier = convexHull ℝ {W, Y, V} := carrier_triOf _ _ _ c3
  have hMc : M.carrier = convexHull ℝ {W, U, Y} := carrier_triOf _ _ _ c4
  have hΔc : Δ.carrier = convexHull ℝ {W, X, Y} := carrier_triOf _ _ _ c1
  have hcov2 : DA.target.carrier ∪ E2.target.carrier = M.carrier := by
    rw [hcar, hE2c, hT2c, hMc, ← hsw]; exact cov2.symm
  have hdisj2 : Disjoint (interior DA.target.carrier) (interior E2.target.carrier) := by
    rw [hcar, hE2c, hT2c, ← hsw]; exact dis2
  have hcov1 : E1.target.carrier ∪ M.carrier = Δ.carrier := by
    rw [hE1c, hT1c, hMc, hΔc]; exact cov1.symm
  have hdisj1 : Disjoint (interior E1.target.carrier) (interior M.carrier) := by
    rw [hE1c, hT1c, hMc]; exact dis1
  let inner : CongruentDissection (3 * (4 * k) ^ 2 + (8 * k) * (8 * k) * 1) :=
    unionCongruentDissection M DA E2 hE2m.symm hcov2 hdisj2
  have hinT : inner.target = M := rfl
  have hinM : inner.model = DA.model := rfl
  let outer := unionCongruentDissection Δ E1 inner (by rw [hinM]; exact hE1m)
    (by rw [hinT]; exact hcov1) (by rw [hinT]; exact hdisj1)
  let τ : Equiv.Perm (Fin 3) := ⟨![1, 2, 0], ![2, 0, 1], fun x => by fin_cases x <;> rfl,
    fun x => by fin_cases x <;> rfl⟩
  have hΔs : HasSides Δ (32 * k) (32 * k) (44 * k) := by
    refine ⟨τ, ?_, ?_, ?_⟩
    · show dist Y W = 32 * k
      rw [dist_comm]; exact dWY
    · show dist W X = 32 * k
      exact dWX
    · show dist X Y = 44 * k
      exact dXY
  have houtM : outer.model = E1.model := rfl
  refine ⟨Δ, outer, E1, E2, hΔs, rfl, ?_, rfl, ?_, ?_, ⟨T1, hs1, hE1c⟩, ⟨T2, hs2, hE2c⟩, ?_, ?_,
    hdisj2, ?_, ?_, ?_⟩
  · rw [houtM, hE1m]; exact ht
  · rw [houtM, hE1m]
  · rw [houtM, hE2m, hE1m]
  · rw [hcov2]; exact hcov1
  · rw [hcov2]; exact hdisj1
  · intro i
    show Fin.append E1.tile inner.tile (Fin.castAdd _ i) = _
    rw [Fin.append_left]
  · intro i
    show Fin.append E1.tile inner.tile (Fin.natAdd _ (Fin.castAdd _ i)) = _
    rw [Fin.append_right]
    show Fin.append DA.tile E2.tile (Fin.castAdd _ i) = _
    rw [Fin.append_left]
  · intro i
    show Fin.append E1.tile inner.tile (Fin.natAdd _ (Fin.natAdd _ i)) = _
    rw [Fin.append_right]
    show Fin.append DA.tile E2.tile (Fin.natAdd _ i) = _
    rw [Fin.append_right]

/-! ## The theorem: the geometric cut of `prop:cevianatom` at `(1,2)`, `m = 4k` -/

theorem range_perm (A : Tri) (τ : Equiv.Perm (Fin 3)) :
    Set.range A.pts = {A.pts (τ 0), A.pts (τ 1), A.pts (τ 2)} := by
  rw [← range_three, ← τ.surjective.range_comp A.pts]
  congr 1
  funext i; fin_cases i <;> rfl

/-- **`prop:cevianatom`, geometric cut (companion tex:4649), at `(e,f)=(1,2)`, `m = 4k`.**
For every `k >= 1`: the triangle `Delta` with sides `(32k,32k,44k)` (= `Delta_{4k}`, `4k(8,8,11)`) is the
union, along the apex fan from its apex, of three pieces with pairwise disjoint interiors:
two triangles with sides `(16k,24k,32k)` = `(8k)(2,3,4)` (each cut into `(8k)^2` tiles) and the atom
`A_{4k}` (the given tiling `DA` of the isosceles triangle with legs `24k`, base `12k`, `3(4k)^2` tiles);
count `2 (8k)^2 + 3 (4k)^2 = 176 k^2`.  The result is a `CongruentDissection` of `Delta` whose tile list
is the concatenation of the three. -/
theorem cevian_cut (k : ℕ) (hk : 0 < k) (DA : CongruentDissection (3 * (4 * k) ^ 2))
    (ht : HasSides DA.model 2 3 4)
    (hA : HasSides DA.target (12 * k) (24 * k) (24 * k)) :
    ∃ (Δ : Tri) (D : CongruentDissection ((8 * k) * (8 * k) * 1 + (3 * (4 * k) ^ 2 + (8 * k) * (8 * k) * 1)))
      (D1 : CongruentDissection ((8 * k) * (8 * k) * 1)) (D2 : CongruentDissection ((8 * k) * (8 * k) * 1)),
      HasSides Δ (32 * k) (32 * k) (44 * k) ∧ D.target = Δ ∧ HasSides D.model 2 3 4 ∧
      D1.model = D.model ∧ DA.model = D.model ∧ D2.model = D.model ∧
      (∃ T1 : Tri, HasSides T1 (16 * k) (24 * k) (32 * k) ∧ D1.target.carrier = T1.carrier) ∧
      (∃ T2 : Tri, HasSides T2 (16 * k) (24 * k) (32 * k) ∧ D2.target.carrier = T2.carrier) ∧
      D1.target.carrier ∪ (DA.target.carrier ∪ D2.target.carrier) = Δ.carrier ∧
      Disjoint (interior D1.target.carrier) (interior (DA.target.carrier ∪ D2.target.carrier)) ∧
      Disjoint (interior DA.target.carrier) (interior D2.target.carrier) ∧
      (∀ i, D.tile (Fin.castAdd _ i) = D1.tile i) ∧
      (∀ i, D.tile (Fin.natAdd _ (Fin.castAdd _ i)) = DA.tile i) ∧
      (∀ i, D.tile (Fin.natAdd _ (Fin.natAdd _ i)) = D2.tile i) := by
  obtain ⟨τ, h12, h20, h01⟩ := hA
  refine assemble k hk DA ht (DA.target.pts (τ 0)) (DA.target.pts (τ 1)) (DA.target.pts (τ 2)) ?_
    h12 h20 h01 (cr_pts_ne_zero (DA.target.relabel τ))
  unfold Tri.carrier
  rw [range_perm DA.target τ]

/-- The atom `A_{4k}` as produced by `FDCCevianAtom`, plugged in. -/
theorem cevian_cut_A4k (k : ℕ) (hk : 0 < k) :
    ∃ (Δ : Tri) (D : CongruentDissection (176 * k ^ 2)),
      HasSides Δ (32 * k) (32 * k) (44 * k) ∧ D.target = Δ ∧ HasSides D.model 2 3 4 := by
  obtain ⟨DA, hAs, hAm⟩ := atomTiles_four_mul k hk
  have hA : HasSides DA.target (12 * k) (24 * k) (24 * k) :=
    hasSides_congr hAs (by push_cast; ring) (by push_cast; ring) (by push_cast; ring)
  obtain ⟨Δ, D, D1, D2, hΔ, hDt, hDm, -⟩ := cevian_cut k hk DA hAm hA
  obtain ⟨E, hEt, hEm⟩ := exists_reindex (M := 176 * k ^ 2) (by ring) D
  exact ⟨Δ, E, hΔ, by rw [hEt, hDt], by rw [hEm]; exact hDm⟩

/-- `m = 4` (`k = 1`): the triangle `Delta_4` (sides `32,32,44`) has a `176`-tile `CongruentDissection`
**built from the cevian cut** `2 . T_8 u A_4` (`64 + 48 + 64 = 176`). -/
theorem delta4_cevian_176 :
    ∃ (Δ : Tri) (D : CongruentDissection 176),
      HasSides Δ 32 32 44 ∧ D.target = Δ ∧ HasSides D.model 2 3 4 := by
  obtain ⟨Δ, D, h1, h2, h3⟩ := cevian_cut_A4k 1 one_pos
  obtain ⟨E, hEt, hEm⟩ := exists_reindex (M := 176) (by norm_num) D
  exact ⟨Δ, E, hasSides_congr h1 (by norm_num) (by norm_num) (by norm_num), by rw [hEt, h2],
    by rw [hEm]; exact h3⟩

end Erdos634.Draft.CVCCevianCut

#print axioms Erdos634.Draft.CVCCevianCut.fan_cover
#print axioms Erdos634.Draft.CVCCevianCut.fan_disjoint
#print axioms Erdos634.Draft.CVCCevianCut.tileK
#print axioms Erdos634.Draft.CVCCevianCut.assemble
#print axioms Erdos634.Draft.CVCCevianCut.cevian_cut
#print axioms Erdos634.Draft.CVCCevianCut.cevian_cut_A4k
#print axioms Erdos634.Draft.CVCCevianCut.delta4_cevian_176
