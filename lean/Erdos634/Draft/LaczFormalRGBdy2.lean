-- Draft/LaczFormalRGBdy2.lean -- S4 of PLAN_THM21: the fans at the boundary vertices of a dissection of a CONVEX POLYGON, with the directions of the virtual sectors identified
-- with the edge directions: at an interior point of the edge `i` one virtual straight sector `(-pT, pT)` with `pT` parallel to the edge vector `e_i`; at the vertex `v_{k+1}`
-- two virtual sectors, the cone `inCone pT qT` with `pT` parallel to `e_{k+1}` and `qT` parallel to `-e_k`.
-- UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 4, Lemma 4.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalRGBdy1
import Erdos634.Draft.LaczFormalRGHalf
import Erdos634.Draft.LaczFormalThm21Loc

open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ} [NeZero M]

/-- Two nonzero vectors whose closed left half-planes coincide are positively parallel. -/
theorem par_of_halfplanes {a b : V2} (ha : a ≠ 0) (hb : b ≠ 0) (h : ∀ z : V2, 0 ≤ crs a z ↔ 0 ≤ crs b z) : Par a b := by
  have h1 : 0 ≤ crs a b := (h b).mpr (by unfold crs; ring_nf; exact le_rfl)
  have h2 : 0 ≤ crs a (-b.1, -b.2) := (h _).mpr (by unfold crs; ring_nf; exact le_rfl)
  have h3 : crs b a = 0 := by unfold crs at h1 h2 ⊢; simp only at h2; linarith
  rcases par_or_par_neg_of_crs_zero hb ha h3 with hp | hp
  · exact hp
  · exfalso
    obtain ⟨c, hc, hca⟩ := hp.smul
    have hn := nsq_pos hb
    unfold nsq at hn
    have hz := (h (-b.2, b.1)).mpr ?_
    · rw [hca] at hz
      unfold crs at hz
      simp only at hz
      nlinarith [mul_pos hc hn]
    · unfold crs; simp only; nlinarith

open Erdos634.CertCoord in
theorem crs_toV2_mkPt (u : Plane) (z : V2) : crs (toV2 u) z = cross2 u (mkPt z.1 z.2) := by
  unfold crs toV2 cross2 mkPt
  simp

/-- Near an interior point `V` of the edge `i`, the polygon is the closed left half-plane of the edge. -/
theorem poly_near_edge (P : ConvPoly M) (i : Fin M) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    ∃ ρ > 0, ∀ y, dist y ((1 - t) • P.v i + t • P.v (i + 1)) < ρ →
      (y ∈ P.carrier ↔ 0 ≤ cross2 (P.e i) (y - ((1 - t) • P.v i + t • P.v (i + 1)))) := by
  set V : Plane := (1 - t) • P.v i + t • P.v (i + 1) with hV
  have htI : t ∈ Set.Icc (0:ℝ) 1 := ⟨ht0.le, ht1.le⟩
  have hstrict : ∀ j, j ≠ i → 0 < P.c j V := fun j hj => P.c_edge_pos P.three_le i htI hj (fun _ => ht1) (fun _ => ht0)
  have hev : ∀ᶠ y in nhds V, ∀ j, j ≠ i → 0 < P.c j y := by
    refine Filter.eventually_all.2 fun j => ?_
    by_cases hj : j = i
    · exact Filter.Eventually.of_forall (fun y hy => absurd hj hy)
    · exact ((P.continuous_c j).continuousAt.eventually (lt_mem_nhds (hstrict j hj))).mono (fun y hy _ => hy)
  obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨ρ, hρ, fun y hy => ?_⟩
  have hci : P.c i y = cross2 (P.e i) (y - V) := by
    have e1 : y - P.v i = (y - V) + t • P.e i := by
      unfold ConvPoly.e; rw [hV]; module
    unfold ConvPoly.c
    rw [e1, cross2_add_right, cross2_smul_right, cross2_self]; ring
  constructor
  · intro hyP; rw [← hci]; exact hyP i
  · intro h j
    by_cases hj : j = i
    · subst hj; show 0 ≤ P.c j y; rw [hci]; exact h
    · exact (hball hy j hj).le

/-- **The fan at an interior point of an edge** of the polygon: one virtual straight sector `(-pT, pT)` with `pT` parallel to the edge vector. -/
theorem fan_open_edge (D : RegionDissection N) (P : ConvPoly M) (hreg : D.region = P.carrier) (i : Fin M) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (hvert : ∃ j k, (D.tile j).pts k = (1 - t) • P.v i + t • P.v (i + 1)) :
    ∃ (pT : V2) (F : ExtFan D ((1 - t) • P.v i + t • P.v (i + 1)) Unit), Par pT (toV2 (P.e i)) ∧ F.pe () = (-pT.1, -pT.2) ∧ F.qe () = pT ∧
      F.Tgt = {z | inCone pT (-pT.1, -pT.2) z} := by
  set V : Plane := (1 - t) • P.v i + t • P.v (i + 1) with hV
  obtain ⟨ρ, hρ, hiff⟩ := P.open_edge_local_T P.three_le i ht0 ht1
  have hiffD : ∀ y, dist y V < ρ → (y ∈ D.region ↔ y ∈ (P.locTri P.three_le i).carrier) := by
    intro y hy; rw [hreg]; exact hiff y hy
  set T := P.locTri P.three_le i with hT
  have hco : ∀ k, T.basis.coord k V = ![1 - t, t, 0] k := by
    intro k
    refine Erdos634.Subdivision.Tri.coord_eq_of_combo T V ![1 - t, t, 0] ?_ ?_ k
    · simp
    · simp [hT, ConvPoly.locTri, triOf, hV]
  have h0 : T.basis.coord 2 V = 0 := by rw [hco]; rfl
  have hpos : ∀ j, j ≠ 2 → 0 < T.basis.coord j V := by
    intro j hj
    rw [hco]
    fin_cases j
    · show 0 < 1 - t; linarith
    · show 0 < t; exact ht0
    · exact absurd rfl hj
  obtain ⟨pT, F, hpT, hpe, hqe, hTgt⟩ := extFan_side_shape D V T 2 h0 hpos hρ hiffD hvert
  refine ⟨pT, F, ?_, hpe, hqe, hTgt⟩
  obtain ⟨ρ2, hρ2, hnear⟩ := poly_near_edge P i ht0 ht1
  apply par_of_halfplanes hpT (toV2_ne_zero (P.e_ne_zero P.three_le i))
  intro z
  obtain ⟨ε, hε, hd⟩ := exists_ptOf_small V z (lt_min hρ2 F.hR)
  have hd1 : dist (ptOf V z ε) V < ρ2 := lt_of_lt_of_le hd (min_le_left _ _)
  have hd2 : dist (ptOf V z ε) V < F.R := lt_of_lt_of_le hd (min_le_right _ _)
  have ha := F.hT _ hd2
  rw [hTgt, toV2_ptOf, Set.mem_setOf_eq, inCone_straight_iff] at ha
  have hb := hnear _ hd1
  rw [← hreg] at hb
  have hyV : ptOf V z ε - V = ε • Erdos634.CertCoord.mkPt z.1 z.2 := by simp [ptOf]
  rw [hyV, cross2_smul_right, ← crs_toV2_mkPt] at hb
  have hc : crs pT (ε * z.1, ε * z.2) = ε * crs pT z := by unfold crs; simp only; ring
  rw [hc] at ha
  have := ha.symm.trans hb
  constructor
  · intro h; exact (mul_nonneg_iff_of_pos_left hε).mp (this.mp ((mul_nonneg_iff_of_pos_left hε).mpr h))
  · intro h; exact (mul_nonneg_iff_of_pos_left hε).mp (this.mpr ((mul_nonneg_iff_of_pos_left hε).mpr h))

/-- **The fan at a vertex `v_{k+1}` of the polygon:** two virtual sectors, the cone `inCone pT qT` with `pT` parallel to the outgoing edge `e_{k+1}` and `qT` parallel to the
reversed incoming edge `v_k - v_{k+1}`. -/
theorem fan_vertex_poly (D : RegionDissection N) (P : ConvPoly M) (hreg : D.region = P.carrier) (k : Fin M)
    (hvert : ∃ j k', (D.tile j).pts k' = P.v (k + 1)) :
    ∃ (pT qT : V2) (F : ExtFan D (P.v (k + 1)) Bool), Par pT (toV2 (P.e (k + 1))) ∧ Par qT (toV2 (P.v k - P.v (k + 1))) ∧ 0 < crs pT qT ∧
      F.pe true = (-qT.1, -qT.2) ∧ F.qe true = pT ∧ F.pe false = qT ∧ F.qe false = (-qT.1, -qT.2) ∧ F.Tgt = {z | inCone pT qT z} := by
  obtain ⟨ρ, hρ, hiff⟩ := P.vertex_local_T P.three_le k
  have hiffD : ∀ y, dist y ((P.locTri P.three_le k).pts 1) < ρ → (y ∈ D.region ↔ y ∈ (P.locTri P.three_le k).carrier) := by
    intro y hy; rw [hreg]; exact hiff y hy
  obtain ⟨pT, qT, F, hcrs, h1, h2, h3, h4, h5, hspec⟩ := extFan_corner_shape D (P.locTri P.three_le k) 1 hρ hiffD hvert
  have hfacts := (ConvPoly.fin_facts P.three_le k)
  have hk2 : k + 1 + 1 = k + 2 := hfacts.2.2.2.2.2
  rcases hspec with ⟨k0, hk0, halt⟩ | ⟨hnv, -⟩
  · have hk01 : k0 = 1 := (P.locTri P.three_le k).indep.injective hk0
    subst hk01
    have hori := P.ori_pos P.three_le k
    have e1 : (P.locTri P.three_le k).pts (1 + 1) = P.v (k + 2) := rfl
    have e2 : (P.locTri P.three_le k).pts (1 + 2) = P.v k := rfl
    have e3 : (P.locTri P.three_le k).pts 1 = P.v (k + 1) := rfl
    rcases halt with ⟨hp, hq⟩ | ⟨hp, hq⟩
    · rw [e1, e3] at hp; rw [e2, e3] at hq
      have hpe : pT = toV2 (P.e (k + 1)) := by rw [hp]; unfold ConvPoly.e; rw [hk2]
      have hv1 : toV2 (P.e (k + 1)) ≠ 0 := toV2_ne_zero (P.e_ne_zero P.three_le (k + 1))
      refine ⟨pT, qT, F, ?_, ?_, hcrs, h1, h2, h3, h4, h5⟩
      · rw [hpe]; exact par_refl hv1
      · rw [hq]
        have : toV2 (P.v k - P.v (k + 1)) ≠ 0 := by
          apply toV2_ne_zero
          intro h
          apply P.e_ne_zero P.three_le k
          unfold ConvPoly.e
          rw [← neg_sub, h]; simp
        exact par_refl this
    · exfalso
      rw [e2, e3] at hp; rw [e1, e3] at hq
      rw [hp, hq] at hcrs
      rw [crs_toV2] at hcrs
      have : cross (P.v k - P.v (k + 1)) (P.v (k + 2) - P.v (k + 1)) = - cross2 (P.v (k + 1) - P.v k) (P.v (k + 2) - P.v k) := by
        unfold cross cross2; simp; ring
      rw [this] at hcrs
      linarith
  · exact absurd rfl (hnv 1)

end Erdos634.Draft.LaczFormal.RG
