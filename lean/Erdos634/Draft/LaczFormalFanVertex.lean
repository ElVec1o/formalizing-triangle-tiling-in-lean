import Erdos634.Draft.LaczFormalFanSucc

/-!
# Fans at a vertex: arms of a tile sector, the side fan with its direction, tiles at a boundary vertex

Erdős #634, rule W2.  Credit: AI assistant (item 3, band program), Laczkovich (DCG 48 (2012), Sect. 4), Beeson–Roșu,
Beeson, Paliy.  UNAUDITED.

* `arms_of_cross`: a tile sector at a vertex of the tile has the two edge vectors as rays, ordered by the sign of the
  cross product;
* `extFan_of'`, `extFan_side'`: `extFan_of`, `extFan_side` with the virtual sector and its direction exposed
  (`pT` is a side vector of the target, the target near `V` is `{z | cross pT z ≥ 0}`);
* `ExtFan.atV_eq_of_three`: see below.
-/

namespace Erdos634.Draft.LaczFormal.Graph

open Erdos634.Geometry

variable {N : ℕ}

/-- **Arms of a tile sector.**  If `T` has a vertex `V = T.pts kk` and the other two vertices are `T.pts k1`, `T.pts k2`
with `cross (T.pts k1 - V) (T.pts k2 - V) > 0`, then the admissible sector `(p, q)` of `T` at `V` has the rays
`p = T.pts k1 - V`, `q = T.pts k2 - V`. -/
theorem arms_of_cross {T : Tri} {V : Plane} {p q : V2} (hok : SecOK p q) (hspec : SectorSpec T V p q)
    {kk k1 k2 : Fin 3} (hkk : T.pts kk = V) (h1 : k1 ≠ kk) (h2 : k2 ≠ kk) (h12 : k1 ≠ k2)
    (hc : 0 < cross (T.pts k1 - V) (T.pts k2 - V)) :
    p = toV2 (T.pts k1 - V) ∧ q = toV2 (T.pts k2 - V) := by
  obtain ⟨kk', fl, hk', hp, hq⟩ := spec_corner_data hspec ⟨kk, hkk⟩
  have hkk' : kk' = kk := T.indep.injective (hk'.trans hkk.symm)
  subst hkk'
  have hpos : 0 < crs p q := crs_pos_of_corner hok hspec ⟨kk', hkk⟩
  rcases arm_cases kk' fl k1 h1 with e1 | e1 <;> rcases arm_cases kk' fl k2 h2 with e2 | e2
  · exact absurd (e1.trans e2.symm) h12
  · rw [hp, hq, ← e1, ← e2]; exact ⟨rfl, rfl⟩
  · exfalso
    rw [hp, hq, ← e1, ← e2] at hpos
    rw [crs_toV2, cross_swap] at hpos
    linarith
  · exact absurd (e1.trans e2.symm) h12

/-- `extFan_of` with the virtual sectors exposed. -/
theorem extFan_of' (D : Dissection N) (V : Plane) (hvert : ∃ i k, (D.tile i).pts k = V)
    (Tgt : Set V2) (R : ℝ) (hR : 0 < R)
    (hT : ∀ y : Plane, dist y V < R → (y ∈ D.target.carrier ↔ toV2 (y - V) ∈ Tgt))
    (hTs : ∀ z ∈ Tgt, ∀ t : ℝ, 0 < t → ((t * z.1, t * z.2) : V2) ∈ Tgt)
    (hTc : ∀ x ∈ Tgt, ∀ y ∈ Tgt, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
      ((a * x.1 + b * y.1, a * x.2 + b * y.2) : V2) ∈ Tgt)
    {κ : Type} [Fintype κ] (pe qe : κ → V2)
    (hokE : ∀ j, SecOK (pe j) (qe j))
    (hcovE : ∀ z : V2, z ∉ Tgt → ∃ j, inCone (pe j) (qe j) z)
    (hdisjE : ∀ j j', j ≠ j' → ∀ z, ¬ (inInt (pe j) (qe j) z ∧ inInt (pe j') (qe j') z))
    (hextT : ∀ j z, inInt (pe j) (qe j) z → z ∉ Tgt)
    (hsumE : ∑ j, wd (pe j) (qe j) + D.target.localAngle V = 2 * Real.pi) :
    ∃ F : ExtFan D V κ, F.pe = pe ∧ F.qe = qe ∧ F.Tgt = Tgt := by
  obtain ⟨p, q, e, h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
    vertex_fan_ext D V hvert Tgt R hR hT hTs pe qe hokE hcovE hdisjE hextT hsumE
  have hsumT : ∑ s : AtV D V, wd (p s) (q s) + ∑ j, wd (pe j) (qe j) = 2 * Real.pi := by
    rw [tiles_angle_sum D V p q h3, D.sum_localAngle_eq V]
    linarith
  exact ⟨⟨Tgt, R, hR, hT, hTs, hTc, pe, qe, hokE, hextT, hdisjE, p, q, e, h1, h2, h3, hsumT, h4, h5, h6, h7, h8⟩,
    rfl, rfl, rfl⟩

/-- Cross product with the side vector, at a point of the side. -/
theorem side_cross (T : Tri) (m : Fin 3) (V : Plane) (h0 : T.basis.coord m V = 0) (y : Plane) :
    cross (T.pts (m + 2) - T.pts (m + 1)) (y - V) = T.basis.coord m y * T.det := by
  have hcd : ∀ y : Plane, T.basis.coord m y * T.det = cross (T.pts (m + 2) - T.pts (m + 1)) (y - T.pts (m + 1)) := by
    intro y
    have := T.coord_mul_det (m + 1) y
    rw [fin3_e1, fin3_e2] at this
    exact this
  have hcdV : cross (T.pts (m + 2) - T.pts (m + 1)) (V - T.pts (m + 1)) = 0 := by rw [← hcd V, h0, zero_mul]
  have : cross (T.pts (m + 2) - T.pts (m + 1)) (y - V) =
      cross (T.pts (m + 2) - T.pts (m + 1)) (y - T.pts (m + 1)) - cross (T.pts (m + 2) - T.pts (m + 1)) (V - T.pts (m + 1)) := by
    simp only [cross, PiLp.sub_apply]; ring
  rw [this, hcdV, ← hcd y]; ring

/-- **The fan at a point of a side of the target, with its exterior sector.**  `V` is in the relative interior of
the side opposite the vertex `m`; there is a fan `F` whose single virtual sector is the exterior half plane,
`(−pT, pT)`, where `pT` is a side vector of the target (`T.pts (m+2) − T.pts (m+1)` or its negative) and the target
near `V` is `{z | cross pT z ≥ 0}`. -/
theorem extFan_side' (D : Dissection N) (V : Plane) (m : Fin 3) (h0 : D.target.basis.coord m V = 0)
    (hpos : ∀ j, j ≠ m → 0 < D.target.basis.coord j V) (hvert : ∃ i k, (D.tile i).pts k = V) :
    ∃ (F : ExtFan D V Unit) (pT : V2), F.pe () = (-pT.1, -pT.2) ∧ F.qe () = pT ∧
      F.Tgt = {z | inCone pT (-pT.1, -pT.2) z} ∧
      (pT = toV2 (D.target.pts (m + 2) - D.target.pts (m + 1)) ∨
        pT = toV2 (D.target.pts (m + 1) - D.target.pts (m + 2))) ∧
      0 < crs pT (toV2 (D.target.pts m - V)) := by
  classical
  obtain ⟨pT, qT, hokT, hlocT, hwdT, hspecT⟩ := straight_sector D.target m V h0 hpos
  have hqT : qT = (-pT.1, -pT.2) := by
    rcases hspecT with ⟨k, hk, _⟩ | ⟨_, m', _, _, hq, _⟩
    · exact absurd hk (edge_coords_not_vertex D.target m V h0 hpos k)
    · exact hq
  have hdir : pT = toV2 (D.target.pts (m + 2) - D.target.pts (m + 1)) ∨
      pT = toV2 (D.target.pts (m + 1) - D.target.pts (m + 2)) := by
    rcases hspecT with ⟨k, hk, _⟩ | ⟨_, m', hm0, hmp, _, hp⟩
    · exact absurd hk (edge_coords_not_vertex D.target m V h0 hpos k)
    · have hmm : m' = m := by
        by_contra hne
        exact (hpos m' hne).ne' hm0
      subst hmm
      exact hp
  subst hqT
  have hpT : pT ≠ 0 := hokT.ne_p
  obtain ⟨R, hR, hRT⟩ := hlocT
  have hcov : ∀ z : V2, z ∉ {z | inCone pT (-pT.1, -pT.2) z} → ∃ j : Unit, inCone (-pT.1, -pT.2) pT z := by
    intro z hz
    simp only [Set.mem_setOf_eq, inCone_straight_iff, not_le] at hz
    refine ⟨(), ?_, ?_⟩
    · show 0 ≤ crs (-pT.1, -pT.2) z; unfold crs at hz ⊢; nlinarith
    · show 0 ≤ crs z pT; unfold crs at hz ⊢; nlinarith
  have hdis : ∀ j j' : Unit, j ≠ j' → ∀ z : V2, ¬ (inInt (-pT.1, -pT.2) pT z ∧ inInt (-pT.1, -pT.2) pT z) := by
    intro j j' hne; exact absurd (Subsingleton.elim j j') hne
  have hext : ∀ (j : Unit) (z : V2), inInt (-pT.1, -pT.2) pT z → z ∉ {z | inCone pT (-pT.1, -pT.2) z} := by
    intro j z hz hin
    simp only [Set.mem_setOf_eq, inCone_straight_iff] at hin
    have := hz.1
    unfold crs at this hin; simp only at this hin; nlinarith
  have hsum : ∑ j : Unit, wd (-pT.1, -pT.2) pT + D.target.localAngle V = 2 * Real.pi := by
    rw [Fintype.sum_unique]
    rw [wd_ext hpT, localAngle_of_edge_coords D.target m V h0 hpos]; ring
  obtain ⟨F, hF1, hF2, hF3⟩ := extFan_of' D V hvert {z | inCone pT (-pT.1, -pT.2) z} R hR
    (fun y hy => by simpa using hRT y hy)
    (fun z hz t ht => (inCone_smul_iff ht).mpr hz)
    (fun x hx y hy a b ha hb hab => inCone_convex hx hy ha hb hab)
    (fun _ : Unit => (-pT.1, -pT.2)) (fun _ : Unit => pT) (fun _ => secOK_ext hpT) hcov hdis hext hsum
  refine ⟨F, pT, congrFun hF1 (), congrFun hF2 (), hF3, hdir, ?_⟩
  -- the third vertex lies on the target side of the line
  have hdet : D.target.det ≠ 0 := D.target.det_ne_zero
  have hC : D.target.basis.coord m (D.target.pts m) = 1 := D.target.basis.coord_apply_eq _
  have hcr := side_cross D.target m V h0 (D.target.pts m)
  rw [hC, one_mul] at hcr
  have hVmem : V ∈ D.target.carrier := by
    rw [D.target.carrier_eq_nonneg_coord]
    intro i
    by_cases him : i = m
    · rw [him, h0]
    · exact (hpos i him).le
  have hCmem : D.target.pts m ∈ D.target.carrier := subset_convexHull ℝ _ (Set.mem_range_self m)
  set w : Plane := D.target.pts m - V with hw
  set δ : ℝ := min 1 (F.R / (‖w‖ + 1)) with hδ
  have hδpos : 0 < δ := lt_min one_pos (div_pos F.hR (by positivity))
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδR : δ * ‖w‖ < F.R := by
    have h1 : δ ≤ F.R / (‖w‖ + 1) := min_le_right _ _
    have h2 : δ * (‖w‖ + 1) ≤ F.R := by
      calc δ * (‖w‖ + 1) ≤ F.R / (‖w‖ + 1) * (‖w‖ + 1) := by gcongr
        _ = F.R := by field_simp
    nlinarith [norm_nonneg w]
  have hymem : V + δ • w ∈ D.target.carrier := by
    have := D.target.convex hVmem hCmem (show (0:ℝ) ≤ 1 - δ by linarith) hδpos.le (by ring)
    convert this using 1
    rw [hw]; simp only [smul_sub, sub_smul, one_smul]; abel
  have hd : dist (V + δ • w) V < F.R := by
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hδpos]; exact hδR
  have hT := (F.hT _ hd).mp hymem
  rw [hF3] at hT
  have hv2 : toV2 (V + δ • w - V) = (δ * (toV2 w).1, δ * (toV2 w).2) := by
    simp [toV2]
  rw [hv2] at hT
  simp only [Set.mem_setOf_eq, inCone] at hT
  have h1 : 0 ≤ crs pT (toV2 w) := by
    have := hT.1
    unfold crs at this ⊢; simp only at this ⊢
    nlinarith
  have h2 : crs pT (toV2 w) ≠ 0 := by
    rcases hdir with h | h
    · rw [h, crs_toV2, hcr]; exact hdet
    · rw [h]
      have : crs (toV2 (D.target.pts (m + 1) - D.target.pts (m + 2))) (toV2 w) =
          - cross (D.target.pts (m + 2) - D.target.pts (m + 1)) w := by
        simp only [crs_toV2, cross, PiLp.sub_apply]; ring
      rw [this, hcr]; exact neg_ne_zero.mpr hdet
  exact lt_of_le_of_ne h1 (Ne.symm h2)

end Erdos634.Draft.LaczFormal.Graph
