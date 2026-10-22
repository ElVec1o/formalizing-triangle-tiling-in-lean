-- Draft/LaczFormalHexCell.lean -- generic parallelogram CELLS for the hexagon witness of `ivc_final_ge5` (M = 6 branch of Laczkovich's Case IV irrational):
-- `ct g u w` = triangle with vertices (g+u, g+w, g) (model order: alpha, beta, gamma), `Par g u w` = the parallelogram g + [0,1]u + [0,1]w,
-- `cellD` = the two-triangle `CongruentRegionDissection 2` of `Par` (second tile = point reflection), all congruent to the model `iTiling.C.model`
-- (the tile (1,3,sqrt7), gamma = pi/3) whenever |u|^2 = 9, |w|^2 = 1, u.w = 3/2 (either orientation).  `regular_union`: RegularPQ is preserved by `unionCongruentRegion`.
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 2 (vi), 8.3), Beeson-Zhang.
import Erdos634.Draft.LaczFormalIVcIrrWit
import Erdos634.SssCongruent

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement Erdos634.CertCoord

namespace Erdos634.Draft.LaczFormal.RG

theorem mkPt_congr {x y x' y' : ℝ} (hx : x = x') (hy : y = y') : mkPt x y = mkPt x' y' := by subst hx; subst hy; rfl

theorem det_ct {g0 g1 u0 u1 w0 w1 : ℝ} (hD : u0 * w1 - u1 * w0 ≠ 0) :
    det3 (g0 + u0) (g1 + u1) (g0 + w0) (g1 + w1) g0 g1 ≠ 0 := by
  have e : det3 (g0 + u0) (g1 + u1) (g0 + w0) (g1 + w1) g0 g1 = u0 * w1 - u1 * w0 := by unfold det3; ring
  rw [e]; exact hD

/-- The triangle `(g+u, g+w, g)` (vertex order alpha, beta, gamma). -/
noncomputable def ct (g0 g1 u0 u1 w0 w1 : ℝ) (hD : u0 * w1 - u1 * w0 ≠ 0) : Tri :=
  mkTri (g0 + u0) (g1 + u1) (g0 + w0) (g1 + w1) g0 g1 (det_ct hD)

theorem ct_carrier {g0 g1 u0 u1 w0 w1 : ℝ} (hD : u0 * w1 - u1 * w0 ≠ 0) (x : Plane) :
    x ∈ (ct g0 g1 u0 u1 w0 w1 hD).carrier ↔
      ∃ l m : ℝ, 0 ≤ l ∧ 0 ≤ m ∧ l + m ≤ 1 ∧ x 0 = g0 + l * u0 + m * w0 ∧ x 1 = g1 + l * u1 + m * w1 := by
  constructor
  · intro hx
    have hsub : (ct g0 g1 u0 u1 w0 w1 hD).carrier ⊆ {y : Plane | ∃ l m : ℝ, 0 ≤ l ∧ 0 ≤ m ∧ l + m ≤ 1 ∧ y 0 = g0 + l * u0 + m * w0 ∧ y 1 = g1 + l * u1 + m * w1} := by
      apply convexHull_min
      · rintro _ ⟨k, rfl⟩
        fin_cases k
        · exact ⟨1, 0, by norm_num, le_rfl, by norm_num, by simp [ct, mkTri, mkPt], by simp [ct, mkTri, mkPt]⟩
        · exact ⟨0, 1, le_rfl, by norm_num, by norm_num, by simp [ct, mkTri, mkPt], by simp [ct, mkTri, mkPt]⟩
        · exact ⟨0, 0, le_rfl, le_rfl, by norm_num, by simp [ct, mkTri, mkPt], by simp [ct, mkTri, mkPt]⟩
      · intro y hy z hz a b ha hb hab
        obtain ⟨l, m, hl, hm, hlm, hy0, hy1⟩ := hy
        obtain ⟨l', m', hl', hm', hlm', hz0, hz1⟩ := hz
        have hb' : b = 1 - a := by linarith
        refine ⟨a * l + b * l', a * m + b * m', by positivity, by positivity, by nlinarith, ?_, ?_⟩
        · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
          rw [hy0, hz0]; subst hb'; ring
        · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
          rw [hy1, hz1]; subst hb'; ring
    exact hsub hx
  · rintro ⟨l, m, hl, hm, hlm, h0, h1⟩
    refine Erdos634.CertGeom.mem_carrier_of_combo _ x ![l, m, 1 - l - m] (by simp) ?_ ?_
    · intro k; fin_cases k <;> simp <;> linarith
    · ext j
      fin_cases j
      · simp [ct, mkTri, mkPt, h0]; ring
      · simp [ct, mkTri, mkPt, h1]; ring

/-- The parallelogram `g + [0,1] u + [0,1] w`. -/
def Par (g0 g1 u0 u1 w0 w1 : ℝ) : Set Plane :=
  {x | ∃ l m : ℝ, 0 ≤ l ∧ l ≤ 1 ∧ 0 ≤ m ∧ m ≤ 1 ∧ x 0 = g0 + l * u0 + m * w0 ∧ x 1 = g1 + l * u1 + m * w1}

theorem hD2 {u0 u1 w0 w1 : ℝ} (hD : u0 * w1 - u1 * w0 ≠ 0) : (-u0) * (-w1) - (-u1) * (-w0) ≠ 0 := by
  have e : (-u0) * (-w1) - (-u1) * (-w0) = u0 * w1 - u1 * w0 := by ring
  rw [e]; exact hD

/-- linear functional `a x_0 + b x_1` as an affine map. -/
noncomputable def linF (a b : ℝ) : Plane →ᵃ[ℝ] ℝ :=
  ((a • (EuclideanSpace.proj (0 : Fin 2) : Plane →L[ℝ] ℝ) + b • (EuclideanSpace.proj (1 : Fin 2) : Plane →L[ℝ] ℝ) : Plane →L[ℝ] ℝ)).toLinearMap.toAffineMap

theorem linF_apply (a b : ℝ) (x : Plane) : linF a b x = a * x 0 + b * x 1 := by simp [linF]

theorem linF_ne {a b c d : ℝ} (h : a * c + b * d ≠ 0) : (linF a b).linear ≠ 0 := by
  intro hz
  have := congrArg (fun l => l (mkPt c d)) hz
  simp [linF, mkPt] at this
  exact h (by linarith)

theorem cell_cover {g0 g1 u0 u1 w0 w1 : ℝ} (hD : u0 * w1 - u1 * w0 ≠ 0) :
    ((ct g0 g1 u0 u1 w0 w1 hD).carrier ∪ (ct (g0 + u0 + w0) (g1 + u1 + w1) (-u0) (-u1) (-w0) (-w1) (hD2 hD)).carrier)
      = Par g0 g1 u0 u1 w0 w1 := by
  ext x
  simp only [Set.mem_union, ct_carrier, Par, Set.mem_setOf_eq]
  constructor
  · rintro (⟨l, m, hl, hm, hlm, h0, h1⟩ | ⟨l, m, hl, hm, hlm, h0, h1⟩)
    · exact ⟨l, m, hl, by linarith, hm, by linarith, h0, h1⟩
    · exact ⟨1 - l, 1 - m, by linarith, by linarith, by linarith, by linarith, by rw [h0]; ring, by rw [h1]; ring⟩
  · rintro ⟨l, m, hl, hl1, hm, hm1, h0, h1⟩
    by_cases hc : l + m ≤ 1
    · exact Or.inl ⟨l, m, hl, hm, hc, h0, h1⟩
    · exact Or.inr ⟨1 - l, 1 - m, by linarith, by linarith, by linarith, by rw [h0]; ring, by rw [h1]; ring⟩

theorem sqd_mk (x y x' y' : ℝ) : dist (mkPt x y) (mkPt x' y') ^ 2 = (x - x') ^ 2 + (y - y') ^ 2 := dist_sq_mkPt x y x' y'

theorem iso_of_dist3 {T U : Tri}
    (h01 : dist (T.pts 0) (T.pts 1) = dist (U.pts 0) (U.pts 1))
    (h12 : dist (T.pts 1) (T.pts 2) = dist (U.pts 1) (U.pts 2))
    (h20 : dist (T.pts 2) (T.pts 0) = dist (U.pts 2) (U.pts 0)) :
    ∃ g : Plane ≃ᵢ Plane, ∀ k, g (T.pts k) = U.pts k := by
  have htri : ∀ y : Fin 3, y = 0 ∨ y = 1 ∨ y = 2 := by decide
  have hd : ∀ i j, dist (T.pts i) (T.pts j) = dist (U.pts i) (U.pts j) := by
    intro i j
    rcases htri i with rfl | rfl | rfl <;> rcases htri j with rfl | rfl | rfl <;>
      simp_all [dist_comm]
  refine ⟨Erdos634.SssCongruent.sssIso hd, ?_⟩
  intro k
  rcases htri k with rfl | rfl | rfl
  · rw [Erdos634.SssCongruent.sssIso_apply]
    have h0 : T.pts 0 + -T.pts 0 = (0 : Plane) := by abel
    rw [h0, map_zero, zero_add]
  · rw [Erdos634.SssCongruent.sssIso_apply]
    have h1 : T.pts 1 + -T.pts 0 = Erdos634.SssCongruent.ev T 0 := by simp [Erdos634.SssCongruent.ev]; abel
    rw [h1, Erdos634.SssCongruent.evMap_basis]
    show U.pts 1 - U.pts 0 + U.pts 0 = U.pts 1
    abel
  · rw [Erdos634.SssCongruent.sssIso_apply]
    have h2 : T.pts 2 + -T.pts 0 = Erdos634.SssCongruent.ev T 1 := by simp [Erdos634.SssCongruent.ev]; abel
    rw [h2, Erdos634.SssCongruent.evMap_basis]
    show U.pts 2 - U.pts 0 + U.pts 0 = U.pts 2
    abel

theorem iT_sq : iT ^ 2 = 3 / 4 := by unfold iT; rw [div_pow, sqrt3_sq']; norm_num

/-- Any triangle `ct g u w` with `|u|^2 = 9`, `|w|^2 = 1`, `u.w = 3/2` is isometric to the model vertex for vertex. -/
theorem ct_iso {g0 g1 u0 u1 w0 w1 : ℝ} (hD : u0 * w1 - u1 * w0 ≠ 0)
    (hu : u0 ^ 2 + u1 ^ 2 = 9) (hw : w0 ^ 2 + w1 ^ 2 = 1) (huw : u0 * w0 + u1 * w1 = 3 / 2) :
    ∃ f : Plane ≃ᵢ Plane, ∀ k, f ((ct g0 g1 u0 u1 w0 w1 hD).pts k) = iTiling.C.model.pts k := by
  have hh := iT_sq
  refine iso_of_dist3 ?_ ?_ ?_
  · show dist (mkPt (g0 + u0) (g1 + u1)) (mkPt (g0 + w0) (g1 + w1)) = dist (mkPt 3 0) (mkPt (1 / 2) iT)
    refine Erdos634.SssCongruent.dist_of_sq ?_
    rw [sqd_mk, sqd_mk]; nlinarith
  · show dist (mkPt (g0 + w0) (g1 + w1)) (mkPt g0 g1) = dist (mkPt (1 / 2) iT) (mkPt 0 0)
    refine Erdos634.SssCongruent.dist_of_sq ?_
    rw [sqd_mk, sqd_mk]; nlinarith
  · show dist (mkPt g0 g1) (mkPt (g0 + u0) (g1 + u1)) = dist (mkPt 0 0) (mkPt 3 0)
    refine Erdos634.SssCongruent.dist_of_sq ?_
    rw [sqd_mk, sqd_mk]; nlinarith


/-- Separation of the two tiles of a cell by the functional `l + m`. -/
theorem cell_sep {g0 g1 u0 u1 w0 w1 : ℝ} (hD : u0 * w1 - u1 * w0 ≠ 0) :
    ∃ (f : Plane →ᵃ[ℝ] ℝ) (c : ℝ), f.linear ≠ 0 ∧ (∀ x ∈ (ct g0 g1 u0 u1 w0 w1 hD).carrier, f x ≤ c) ∧
      (∀ x ∈ (ct (g0 + u0 + w0) (g1 + u1 + w1) (-u0) (-u1) (-w0) (-w1) (hD2 hD)).carrier, c ≤ f x) := by
  set D := u0 * w1 - u1 * w0 with hDdef
  have hu : (w1 - u1) / D * u0 + (u0 - w0) / D * u1 = 1 := by field_simp; ring
  have hw : (w1 - u1) / D * w0 + (u0 - w0) / D * w1 = 1 := by field_simp; ring
  refine ⟨linF ((w1 - u1) / D) ((u0 - w0) / D), (w1 - u1) / D * g0 + (u0 - w0) / D * g1 + 1,
    linF_ne (c := u0) (d := u1) (by rw [hu]; norm_num), ?_, ?_⟩
  · intro x hx
    obtain ⟨l, m, hl, hm, hlm, h0, h1⟩ := (ct_carrier hD x).mp hx
    rw [linF_apply, h0, h1]
    have : (w1 - u1) / D * (g0 + l * u0 + m * w0) + (u0 - w0) / D * (g1 + l * u1 + m * w1)
        = ((w1 - u1) / D * g0 + (u0 - w0) / D * g1) + l * ((w1 - u1) / D * u0 + (u0 - w0) / D * u1) + m * ((w1 - u1) / D * w0 + (u0 - w0) / D * w1) := by ring
    rw [this, hu, hw]; linarith
  · intro x hx
    obtain ⟨l, m, hl, hm, hlm, h0, h1⟩ := (ct_carrier (hD2 hD) x).mp hx
    rw [linF_apply, h0, h1]
    have : (w1 - u1) / D * (g0 + u0 + w0 + l * -u0 + m * -w0) + (u0 - w0) / D * (g1 + u1 + w1 + l * -u1 + m * -w1)
        = ((w1 - u1) / D * g0 + (u0 - w0) / D * g1) + (1 - l) * ((w1 - u1) / D * u0 + (u0 - w0) / D * u1) + (1 - m) * ((w1 - u1) / D * w0 + (u0 - w0) / D * w1) := by ring
    rw [this, hu, hw]; linarith

/-- **A cell**: the parallelogram `Par g u w` cut into two congruent triangles (point reflections of each other), both congruent to the model `iTiling.C.model`. -/
noncomputable def cellD (g0 g1 u0 u1 w0 w1 : ℝ) (hD : u0 * w1 - u1 * w0 ≠ 0)
    (hu : u0 ^ 2 + u1 ^ 2 = 9) (hw : w0 ^ 2 + w1 ^ 2 = 1) (huw : u0 * w0 + u1 * w1 = 3 / 2) : CongruentRegionDissection 2 where
  region := Par g0 g1 u0 u1 w0 w1
  tile := ![ct g0 g1 u0 u1 w0 w1 hD, ct (g0 + u0 + w0) (g1 + u1 + w1) (-u0) (-u1) (-w0) (-w1) (hD2 hD)]
  covers := by
    rw [← cell_cover hD]
    ext x
    simp only [Set.mem_iUnion, Fin.exists_fin_two, Set.mem_union]
    rfl
  interiors_disjoint := by
    intro i j hij
    obtain ⟨f, c, hf, h1, h2⟩ := cell_sep (g0 := g0) (g1 := g1) hD
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact Erdos634.CertGeom.interiors_disjoint_of_separating f hf c h1 h2
    · exact (Erdos634.CertGeom.interiors_disjoint_of_separating f hf c h1 h2).symm
    · exact absurd rfl hij
  model := iTiling.C.model
  tiles_congruent := by
    intro i
    fin_cases i
    · obtain ⟨f, hf⟩ := ct_iso (g0 := g0) (g1 := g1) hD hu hw huw
      exact ⟨f, Equiv.refl _, hf⟩
    · have hu' : (-u0) ^ 2 + (-u1) ^ 2 = 9 := by nlinarith
      have hw' : (-w0) ^ 2 + (-w1) ^ 2 = 1 := by nlinarith
      have huw' : (-u0) * (-w0) + (-u1) * (-w1) = 3 / 2 := by nlinarith
      obtain ⟨f, hf⟩ := ct_iso (g0 := g0 + u0 + w0) (g1 := g1 + u1 + w1) (hD2 hD) hu' hw' huw'
      exact ⟨f, Equiv.refl _, hf⟩

theorem cell_swap0 {g0 g1 u0 u1 w0 w1 : ℝ} (hD : u0 * w1 - u1 * w0 ≠ 0)
    (hu : u0 ^ 2 + u1 ^ 2 = 9) (hw : w0 ^ 2 + w1 ^ 2 = 1) (huw : u0 * w0 + u1 * w1 = 3 / 2) (i : Fin 2) :
    ((cellD g0 g1 u0 u1 w0 w1 hD hu hw huw).tile (i + 1)).pts 1 = ((cellD g0 g1 u0 u1 w0 w1 hD hu hw huw).tile i).pts 0 := by
  fin_cases i
  · exact mkPt_congr (by ring) (by ring)
  · exact mkPt_congr (by ring) (by ring)

theorem cell_swap1 {g0 g1 u0 u1 w0 w1 : ℝ} (hD : u0 * w1 - u1 * w0 ≠ 0)
    (hu : u0 ^ 2 + u1 ^ 2 = 9) (hw : w0 ^ 2 + w1 ^ 2 = 1) (huw : u0 * w0 + u1 * w1 = 3 / 2) (i : Fin 2) :
    ((cellD g0 g1 u0 u1 w0 w1 hD hu hw huw).tile (i + 1)).pts 0 = ((cellD g0 g1 u0 u1 w0 w1 hD hu hw huw).tile i).pts 1 := by
  fin_cases i
  · exact mkPt_congr (by ring) (by ring)
  · exact mkPt_congr (by ring) (by ring)

theorem cellD_regular {g0 g1 u0 u1 w0 w1 : ℝ} (hD : u0 * w1 - u1 * w0 ≠ 0)
    (hu : u0 ^ 2 + u1 ^ 2 = 9) (hw : w0 ^ 2 + w1 ^ 2 = 1) (huw : u0 * w0 + u1 * w1 = 3 / 2) :
    RegularPQ (cellD g0 g1 u0 u1 w0 w1 hD hu hw huw) := by
  refine ⟨fun _ => 1, fun i v => ?_, fun X => ?_⟩
  · fin_cases i
    · obtain ⟨f, hf⟩ := ct_iso (g0 := g0) (g1 := g1) hD hu hw huw
      exact angleAt_of_iso' f hf v
    · have hu' : (-u0) ^ 2 + (-u1) ^ 2 = 9 := by nlinarith
      have hw' : (-w0) ^ 2 + (-w1) ^ 2 = 1 := by nlinarith
      have huw' : (-u0) * (-w0) + (-u1) * (-w1) = 3 / 2 := by nlinarith
      obtain ⟨f, hf⟩ := ct_iso (g0 := g0 + u0 + w0) (g1 := g1 + u1 + w1) (hD2 hD) hu' hw' huw'
      exact angleAt_of_iso' f hf v
  · unfold cntR
    refine Finset.card_nbij' (fun x => (x.1 + 1, (1 : Fin 3))) (fun x => (x.1 + 1, (0 : Fin 3))) ?_ ?_ ?_ ?_
    · intro x hx
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq, Equiv.Perm.coe_one, id_eq] at hx ⊢
      obtain ⟨h1, h2⟩ := hx
      rw [h2] at h1
      exact ⟨by rw [cell_swap0 hD hu hw huw]; exact h1, trivial⟩
    · intro x hx
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq, Equiv.Perm.coe_one, id_eq] at hx ⊢
      obtain ⟨h1, h2⟩ := hx
      rw [h2] at h1
      exact ⟨by rw [cell_swap1 hD hu hw huw]; exact h1, trivial⟩
    · intro x hx
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq, Equiv.Perm.coe_one, id_eq] at hx
      obtain ⟨i, k⟩ := x
      simp only at hx ⊢
      obtain ⟨h1, h2⟩ := hx
      subst h2
      ext
      · simp only; fin_cases i <;> rfl
      · rfl
    · intro x hx
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq, Equiv.Perm.coe_one, id_eq] at hx
      obtain ⟨i, k⟩ := x
      simp only at hx ⊢
      obtain ⟨h1, h2⟩ := hx
      subst h2
      ext
      · simp only; fin_cases i <;> rfl
      · rfl


theorem union_tile_left {M N : ℕ} (C1 : CongruentRegionDissection M) (C2 : CongruentRegionDissection N) (hm : C1.model = C2.model)
    (hd : Disjoint (interior C1.region) (interior C2.region)) (i : Fin M) :
    (unionCongruentRegion C1 C2 hm hd).tile (Fin.castAdd N i) = C1.tile i := Fin.append_left _ _ i

theorem union_tile_right {M N : ℕ} (C1 : CongruentRegionDissection M) (C2 : CongruentRegionDissection N) (hm : C1.model = C2.model)
    (hd : Disjoint (interior C1.region) (interior C2.region)) (i : Fin N) :
    (unionCongruentRegion C1 C2 hm hd).tile (Fin.natAdd M i) = C2.tile i := Fin.append_right _ _ i

theorem cntR_union {M N : ℕ} (C1 : CongruentRegionDissection M) (C2 : CongruentRegionDissection N) (hm : C1.model = C2.model)
    (hd : Disjoint (interior C1.region) (interior C2.region)) (idx1 : Fin M → Equiv.Perm (Fin 3)) (idx2 : Fin N → Equiv.Perm (Fin 3))
    (X : Plane) (l : Fin 3) :
    cntR (unionCongruentRegion C1 C2 hm hd) (Fin.append idx1 idx2) X l = cntR C1 idx1 X l + cntR C2 idx2 X l := by
  unfold cntR
  simp only [Finset.card_filter, Fintype.sum_prod_type, Fin.sum_univ_add]
  congr 1
  · refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun k _ => ?_))
    rw [union_tile_left, Fin.append_left]
  · refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun k _ => ?_))
    rw [union_tile_right, Fin.append_right]

theorem regular_union {M N : ℕ} (C1 : CongruentRegionDissection M) (C2 : CongruentRegionDissection N) (hm : C1.model = C2.model)
    (hd : Disjoint (interior C1.region) (interior C2.region)) (h1 : RegularPQ C1) (h2 : RegularPQ C2) :
    RegularPQ (unionCongruentRegion C1 C2 hm hd) := by
  obtain ⟨idx1, ha1, hc1⟩ := h1
  obtain ⟨idx2, ha2, hc2⟩ := h2
  refine ⟨Fin.append idx1 idx2, fun i v => ?_, fun X => ?_⟩
  · induction i using Fin.addCases with
    | left j =>
      rw [union_tile_left, Fin.append_left]
      exact ha1 j v
    | right j =>
      rw [union_tile_right, Fin.append_right]
      show angleAt C1.model _ = _
      rw [hm]; exact ha2 j v
  · rw [cntR_union, cntR_union, hc1 X, hc2 X]

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.cellD_regular
#print axioms Erdos634.Draft.LaczFormal.RG.regular_union
