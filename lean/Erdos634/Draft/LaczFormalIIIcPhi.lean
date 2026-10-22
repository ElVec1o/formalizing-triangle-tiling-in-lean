-- Draft/LaczFormalIIIcPhi.lean -- Laczkovich DCG 48 (2012), Sect. 7.3 (IIIc), items (d2)+(d3a): `Phi(A) = 0`.
--   `iiic_phi_zero`: for a regular PolyTiling T of a convex polygon A by congruent copies of the tile (alpha, pi/3-alpha, 2pi/3) with alpha/pi irrational, a, b commensurable, c not
--   commensurable with a:  `T.P.Phi alpha = 0`  (Phi anchored at side 0 of A).
-- Route (this is the printed eq. (20) + 'd_i = k_i c' + 'k = 0', with the NON-printed steps made explicit):
--   Phi(A) = sum of tile fluxes (`Phi_additive`) = sum over the boundary c-tiles (`iiic_interior_pairs_cancel`);
--   `iiic_sideEdges_all_or_none`: either NO side edge has length c (then no tile has its c-side on the boundary, sum = 0), or ALL side edges do (then d_j = n_j c, n_j = number of side edges,
--   and the boundary c-tiles are in bijection with the side edges: sum = (c + a - b) * sum_j n_j W_j, while Phi(A) = c * sum_j n_j W_j, so (a - b) sum_j n_j W_j = 0, a != b, Phi(A) = 0).
-- `a != b` is proved from alpha/pi irrational (a = b => alpha = beta = pi/6).
-- NOTE, UNAUDITED.  Non-vacuity: NAMED only (same hypotheses as `iiic_interior_pairs_cancel`; an irrational-alpha parallelogram of two congruent triangles, sin(pi/3-alpha) = 2 sin alpha).
-- Printed gap closed: 'Q_i tile A, or some c-tile is on the boundary' is the dichotomy B = empty / all-c; 'some side covered by c-edges, hence every side' is `iiic_sideEdges_all_or_none`.
-- Credit: Laczkovich (DCG 48 (2012), Sect. 7.3, Lemmas 4.5-4.8), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIIcSide

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement Erdos634.Draft.LaczFormal.RG

namespace Erdos634.Draft.LaczFormal.IIIc

theorem openSegment_eUV (T : Tri) (k : Fin 3) : openSegment ℝ (eU T k) (eV T k) = openSegment ℝ (T.pts k) (T.pts (k + 1)) := by
  unfold eU eV; split_ifs
  · rfl
  · exact openSegment_symm ℝ _ _

/-- `a != b` for a placement with `alpha/pi` irrational (otherwise `a = b` forces `alpha = beta = pi/6`). -/
theorem iiic_a_ne_b {T : Tri} {α a b c : ℝ} (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (h : T.TwoPiThreeData α a b c) : a ≠ b := by
  intro hab
  obtain ⟨σ, h0, o0, h1, o1, h2, o2⟩ := h
  have hne : σ 0 ≠ σ 1 := fun e => absurd (σ.injective e) (by decide)
  have := T.angle_eq_of_oppLen_eq hne (by rw [o0, o1]; exact hab)
  rw [h0, h1] at this
  apply hα
  exact ⟨1 / 6, by push_cast; linarith⟩

set_option maxHeartbeats 800000 in
/-- **(d2)+(d3a): the polygon flux of the weight anchored at ANY `θ₀` is `0`** (in particular `Phi(A) = 0`, `iiic_phi_zero`). -/
theorem iiic_flux_zero {N M : ℕ} [NeZero M] (T : PolyTiling N M) (hreg : RegularPQ T.C) {α : ℝ} (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (hmodel : T.C.model.TwoPiThreeData α (slen T.C 0) (slen T.C 1) (slen T.C 2))
    (hab : Comm (slen T.C 0) (slen T.C 1)) (hac : ¬ Comm (slen T.C 0) (slen T.C 2)) (θ₀ : Real.Angle) :
    T.P.flux (fAlphaAt α hα θ₀).weight = 0 := by
  classical
  haveI : HasFansC T.C.toRegionDissection := hasFansC_poly _ T.P T.region_eq
  have hT : ∀ i, (T.C.tile i).TwoPiThreeData α (slen T.C 0) (slen T.C 1) (slen T.C 2) :=
    fun i => Tri.TwoPiThreeData.of_congruent (T.C.tiles_congruent i) hmodel
  have hca : slen T.C 2 ≠ slen T.C 0 := by
    intro h; apply hac; exact ⟨1, 1, one_pos, one_pos, by rw [h]⟩
  have hcb : slen T.C 2 ≠ slen T.C 1 := by
    intro h; apply hac
    obtain ⟨p, q, hp, hq, hpq⟩ := hab
    exact ⟨p, q, hp, hq, by rw [h]; exact hpq⟩
  have hne := iiic_a_ne_b hα hmodel
  choose kg hkg' using fun i => (hT i).gamma_unique
  have hkg : ∀ i, (T.C.tile i).angleAt (kg i) = 2 * Real.pi / 3 := fun i => (hkg' i).1
  set R := T.C.toRegionDissection with hR
  set w := (fAlphaAt α hα θ₀).weight with hw
  set K := slen T.C 2 + slen T.C 0 - slen T.C 1 with hK
  have hAdd : ∑ i, (T.C.tile i).flux w = T.P.flux w := T.P.flux_cancel R T.region_eq _ (fAlphaAt α hα θ₀).weight_odd
  have hCancel := iiic_interior_pairs_cancel T hreg hα hmodel hab hac θ₀ kg hkg
  set B := Finset.univ.filter (fun i => ∀ m ∈ openSegment ℝ (eU (T.C.tile i) (kg i + 1)) (eV (T.C.tile i) (kg i + 1)), m ∉ interior T.C.region) with hB
  have hflux : ∀ i, (T.C.tile i).flux w = w (R.eDir (i, kg i + 1)) * K := fun i =>
    (T.C.tile i).flux_cedge_at hα (hT i) θ₀ (kg i) (hkg i)
  have hsucc : ∀ j : Fin 3, j ≠ j + 1 := by decide
  -- a boundary c-tile has its c-edge on a side
  have hBside : ∀ i ∈ B, ∃ j, (i, kg i + 1) ∈ T.P.sideEdges R j := by
    intro i hi
    have hi' := (Finset.mem_filter.mp hi).2
    have hpts : (T.C.tile i).pts (kg i + 1) ≠ (T.C.tile i).pts (kg i + 1 + 1) := fun h => hsucc _ ((T.C.tile i).indep.injective h)
    obtain ⟨hxT, hxa, hxb⟩ := mem_ne_ends_of_avg hpts (left_mem_segment ℝ _ _) (right_mem_segment ℝ _ _)
    have hxn : ((1:ℝ)/2) • (T.C.tile i).pts (kg i + 1) + ((1:ℝ)/2) • (T.C.tile i).pts (kg i + 1 + 1) ∉ interior T.P.carrier := by
      rw [← T.region_eq]
      apply hi'
      rw [openSegment_eUV]
      exact ⟨1/2, 1/2, by norm_num, by norm_num, by norm_num, rfl⟩
    obtain ⟨j, hj⟩ := T.P.edge_on_side R T.region_eq (i, kg i + 1) hxT hxa hxb hxn
    exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩⟩
  have hcl : ∀ i, R.eLen (i, kg i + 1) = slen T.C 2 := fun i => cedge_dist (hT i) (kg i) (hkg i)
  rcases iiic_sideEdges_all_or_none T hreg hmodel hab hac with hall | hnone
  · -- every side edge is a c-edge
    have hE : ∀ j, ∀ e ∈ T.P.sideEdges R j, e.2 = kg e.1 + 1 := by
      intro j e he
      exact cedge_index (hT e.1) hca hcb (kg e.1) (hkg e.1) e.2 (hall j e he)
    have hBmem : ∀ j, ∀ e ∈ T.P.sideEdges R j, e.1 ∈ B := by
      intro j e he
      have hsub : R.eSet e ⊆ T.P.sideSet j := (Finset.mem_filter.mp he).2
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun m hm hmi => ?_⟩
      rw [openSegment_eUV] at hm
      have hm' : m ∈ R.eSet e := by
        have : e = (e.1, kg e.1 + 1) := Prod.ext rfl (hE j e he)
        rw [this]
        exact openSegment_subset_segment ℝ _ _ hm
      rw [T.region_eq] at hmi
      exact T.P.not_interior_of_sideSet (hsub hm') hmi
    set g : Fin N × Fin 3 → ℝ := fun e => w (R.eDir e) with hg
    have hBE : B.image (fun i => (i, kg i + 1)) = Finset.univ.biUnion (fun j => T.P.sideEdges R j) := by
      ext e
      simp only [Finset.mem_image, Finset.mem_biUnion, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨i, hi, rfl⟩
        exact hBside i hi
      · rintro ⟨j, hj⟩
        exact ⟨e.1, hBmem j e hj, (Prod.ext rfl (hE j e hj).symm)⟩
    have hinj : Function.Injective (fun i : Fin N => (i, kg i + 1)) := fun i i' h => congrArg Prod.fst h
    have hsumB : ∑ i ∈ B, (T.C.tile i).flux w = K * ∑ j, ((T.P.sideEdges R j).card : ℝ) * w (T.P.sideDir j) := by
      have h1 : ∑ i ∈ B, (T.C.tile i).flux w = ∑ i ∈ B, g (i, kg i + 1) * K := Finset.sum_congr rfl (fun i _ => hflux i)
      rw [h1, ← Finset.sum_mul, ← Finset.sum_image (f := g) (g := fun i => (i, kg i + 1)) (fun x _ y _ h => hinj h), hBE,
        Finset.sum_biUnion (fun j _ j' _ hjj' => T.P.sideEdges_disjoint R hjj')]
      rw [mul_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      have hsc : ∑ e ∈ T.P.sideEdges R j, w (R.eDir e) = ∑ e ∈ T.P.sideEdges R j, w (T.P.sideDir j) :=
        Finset.sum_congr rfl (fun e he => congrArg w (T.P.eDir_of_side R T.region_eq (Finset.mem_filter.mp he).2))
      rw [hsc, Finset.sum_const, nsmul_eq_mul]
    have hside : ∀ j, T.P.side j = ((T.P.sideEdges R j).card : ℝ) * slen T.C 2 := by
      intro j
      rw [← T.P.side_len_sum R T.region_eq j, Finset.sum_congr rfl (fun e he => hall j e he), Finset.sum_const, nsmul_eq_mul]
    have hPhi : T.P.flux w = slen T.C 2 * ∑ j, ((T.P.sideEdges R j).card : ℝ) * w (T.P.sideDir j) := by
      unfold ConvPoly.flux
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [hside j, smul_eq_mul]; ring
    set kt := ∑ j, ((T.P.sideEdges R j).card : ℝ) * w (T.P.sideDir j) with hkt
    have heq : T.P.flux w = K * kt := by rw [← hAdd, hCancel, hsumB]
    have h0 : (slen T.C 0 - slen T.C 1) * kt = 0 := by
      have := hPhi.symm.trans heq
      rw [hK] at this
      linarith
    have hkt0 : kt = 0 := (mul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr hne)
    rw [hPhi, hkt0, mul_zero]
  · -- no side edge is a c-edge: no boundary c-tile
    have hB0 : ∑ i ∈ B, (T.C.tile i).flux w = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      obtain ⟨j, hj⟩ := hBside i hi
      exact absurd (hcl i) (hnone j _ hj)
    rw [← hAdd, hCancel, hB0]

/-- **`Phi(A) = 0`** (anchored at side 0). -/
theorem iiic_phi_zero {N M : ℕ} [NeZero M] (T : PolyTiling N M) (hreg : RegularPQ T.C) {α : ℝ} (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (hmodel : T.C.model.TwoPiThreeData α (slen T.C 0) (slen T.C 1) (slen T.C 2))
    (hab : Comm (slen T.C 0) (slen T.C 1)) (hac : ¬ Comm (slen T.C 0) (slen T.C 2)) : T.P.Phi α hα = 0 :=
  iiic_flux_zero T hreg hα hmodel hab hac (T.P.sideDir 0).angle

end Erdos634.Draft.LaczFormal.IIIc

#print axioms Erdos634.Draft.LaczFormal.IIIc.iiic_a_ne_b
#print axioms Erdos634.Draft.LaczFormal.IIIc.iiic_flux_zero
#print axioms Erdos634.Draft.LaczFormal.IIIc.iiic_phi_zero
