-- Draft/LaczFormalRGExt.lean -- S2 of PLAN_THM21: the UNIFORM fan `ExtFan` at any vertex of a dissection of a POLYGON (convex region), and the ray principle.
-- Port of LaczFormalGraphExt (`Dissection N`, triangle target) to `RegionDissection N`.  The target's local cone and angle come from a LOCAL TRIANGLE
-- (`ConvPoly.polygon_local`): a vertex/side-point of the polygon is a vertex/side-point of a triangle equal to the polygon near it.
-- UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 4: maximal segments; the vertices of A), Beeson, Beeson-Zhang; port of the project's LaczFormalGraphExt.
import Erdos634.Draft.LaczFormalGraphExt
import Erdos634.Draft.LaczFormalRGLoc
import Erdos634.Draft.LaczFormalThm21Loc

open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21

namespace Erdos634.Draft.LaczFormal.RG

variable {N : ℕ}

/-- The uniform cyclic fan at the vertex `V`. -/
structure ExtFan (D : RegionDissection N) (V : Plane) (κ : Type) [Fintype κ] where
  Tgt : Set V2
  R : ℝ
  hR : 0 < R
  hT : ∀ y : Plane, dist y V < R → (y ∈ D.region ↔ toV2 (y - V) ∈ Tgt)
  hTs : ∀ z ∈ Tgt, ∀ t : ℝ, 0 < t → ((t * z.1, t * z.2) : V2) ∈ Tgt
  hTc : ∀ x ∈ Tgt, ∀ y ∈ Tgt, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
    ((a * x.1 + b * y.1, a * x.2 + b * y.2) : V2) ∈ Tgt
  pe : κ → V2
  qe : κ → V2
  hokE : ∀ j, SecOK (pe j) (qe j)
  hextT : ∀ j z, inInt (pe j) (qe j) z → z ∉ Tgt
  hdisjE : ∀ j j', j ≠ j' → ∀ z, ¬ (inInt (pe j) (qe j) z ∧ inInt (pe j') (qe j') z)
  p : AtV D V → V2
  q : AtV D V → V2
  e : ℕ → AtV D V ⊕ κ
  hok : ∀ s, SecOK (p s) (q s)
  hloc : ∀ s, LocalCone (D.tile s.1) V (p s) (q s)
  hwd : ∀ s, wd (p s) (q s) = (D.tile s.1).localAngle V
  hsum : ∑ s, wd (p s) (q s) + ∑ j, wd (pe j) (qe j) = 2 * Real.pi
  hspec : ∀ s, SectorSpec (D.tile s.1) V (p s) (q s)
  hP : ∀ n, Par (Sum.elim p pe (e (n + 1))) (Sum.elim q qe (e n))
  hper : ∀ n, e (n + Fintype.card (AtV D V ⊕ κ)) = e n
  hinj : Set.InjOn e (Set.Iio (Fintype.card (AtV D V ⊕ κ)))
  hsurj : ∀ o, ∃ j < Fintype.card (AtV D V ⊕ κ), e j = o

/-- **Fan with virtual sectors.** -/
theorem vertex_fan_ext (D : RegionDissection N) (V : Plane) (hvert : ∃ i k, (D.tile i).pts k = V)
    (Tgt : Set V2) (R : ℝ) (hR : 0 < R)
    (hT : ∀ y : Plane, dist y V < R → (y ∈ D.region ↔ toV2 (y - V) ∈ Tgt))
    (hTs : ∀ z ∈ Tgt, ∀ t : ℝ, 0 < t → ((t * z.1, t * z.2) : V2) ∈ Tgt)
    {κ : Type} [Fintype κ] (pe qe : κ → V2)
    (hokE : ∀ j, SecOK (pe j) (qe j))
    (hcovE : ∀ z : V2, z ∉ Tgt → ∃ j, inCone (pe j) (qe j) z)
    (hdisjE : ∀ j j', j ≠ j' → ∀ z, ¬ (inInt (pe j) (qe j) z ∧ inInt (pe j') (qe j') z))
    (hextT : ∀ j z, inInt (pe j) (qe j) z → z ∉ Tgt)
    (hangle : ∑ i, (D.tile i).localAngle V + ∑ j, wd (pe j) (qe j) = 2 * Real.pi) :
    ∃ (p q : AtV D V → V2) (e : ℕ → AtV D V ⊕ κ),
      (∀ s, SecOK (p s) (q s)) ∧ (∀ s, LocalCone (D.tile s.1) V (p s) (q s)) ∧
      (∀ s, wd (p s) (q s) = (D.tile s.1).localAngle V) ∧ (∀ s, SectorSpec (D.tile s.1) V (p s) (q s)) ∧
      (∀ n, Par (Sum.elim p pe (e (n + 1))) (Sum.elim q qe (e n))) ∧
      (∀ n, e (n + Fintype.card (AtV D V ⊕ κ)) = e n) ∧
      Set.InjOn e (Set.Iio (Fintype.card (AtV D V ⊕ κ))) ∧
      (∀ o, ∃ j < Fintype.card (AtV D V ⊕ κ), e j = o) := by
  classical
  have hex : ∀ s : AtV D V, ∃ pq : V2 × V2, SecOK pq.1 pq.2 ∧ LocalCone (D.tile s.1) V pq.1 pq.2 ∧
      wd pq.1 pq.2 = (D.tile s.1).localAngle V ∧ SectorSpec (D.tile s.1) V pq.1 pq.2 := by
    intro s
    obtain ⟨p, q, h1, h2, h3, h4⟩ := local_sector (D.tile s.1) s.2 (not_interior_of_vertex D hvert s.1)
    exact ⟨(p, q), h1, h2, h3, h4⟩
  choose pq hok hloc hwd hspec using hex
  set p : AtV D V → V2 := fun s => (pq s).1
  set q : AtV D V → V2 := fun s => (pq s).2
  obtain ⟨i0, k0, hk0⟩ := hvert
  haveI : Nonempty (AtV D V) := ⟨⟨i0, hk0 ▸ subset_convexHull ℝ _ ⟨k0, rfl⟩⟩⟩
  haveI : Nonempty (AtV D V ⊕ κ) := ⟨Sum.inl (Classical.arbitrary _)⟩
  have hok' : AllOK (Sum.elim p pe) (Sum.elim q qe) := by
    intro o; rcases o with s | j
    · exact hok s
    · exact hokE j
  have hcov : Covers (Sum.elim p pe) (Sum.elim q qe) := by
    intro z
    by_cases hz : z ∈ Tgt
    · obtain ⟨s, hs⟩ := tiles_cover D V p q hloc Tgt R hR hT hTs z hz
      exact ⟨Sum.inl s, hs⟩
    · obtain ⟨j, hj⟩ := hcovE z hz
      exact ⟨Sum.inr j, hj⟩
  have hext : ∀ (t : AtV D V) (j : κ) (z : V2), inInt (pe j) (qe j) z → inInt (p t) (q t) z → False := by
    intro t j z hz1 hz2
    obtain ⟨rt, hrt, ht⟩ := hloc t
    obtain ⟨ε, hε, hd⟩ := exists_ptOf_small V z (lt_min hrt hR)
    have hds : dist (ptOf V z ε) V < rt := lt_of_lt_of_le hd (min_le_left _ _)
    have hdR : dist (ptOf V z ε) V < R := lt_of_lt_of_le hd (min_le_right _ _)
    have hz2' := hz2
    rw [← inInt_smul_iff hε, ← toV2_ptOf V z ε] at hz2'
    have h1 := mem_interior_of_inInt ht hds hz2'
    have h2 : ptOf V z ε ∈ D.region := by
      rw [← D.covers]
      exact Set.mem_iUnion.mpr ⟨t.1, interior_subset h1⟩
    have h3 := (hT _ hdR).mp h2
    rw [toV2_ptOf] at h3
    -- scale back: z ∈ Tgt contradicts hextT
    apply hextT j z hz1
    have hεi := inv_pos.mpr hε
    have := hTs _ h3 ε⁻¹ hεi
    have e : ((ε⁻¹ * (ε * z.1), ε⁻¹ * (ε * z.2)) : V2) = z := by
      ext <;> simp <;> field_simp
    simpa [e] using this
  have hdisj : Disjoint' (Sum.elim p pe) (Sum.elim q qe) := by
    intro o1 o2 hne z ⟨hz1, hz2⟩
    rcases o1 with s | j <;> rcases o2 with t | j'
    · exact tiles_disjoint D V p q hloc s t (fun h => hne (by rw [h])) z ⟨hz1, hz2⟩
    · exact hext s j' z hz2 hz1
    · exact hext t j z hz1 hz2
    · exact hdisjE j j' (fun h => hne (by rw [h])) z ⟨hz1, hz2⟩
  have hsum : ∑ o, wd (Sum.elim p pe o) (Sum.elim q qe o) = 2 * Real.pi := by
    rw [Fintype.sum_sum_type]
    have e1 : ∑ s : AtV D V, wd (Sum.elim p pe (Sum.inl s)) (Sum.elim q qe (Sum.inl s)) = ∑ s : AtV D V, wd (p s) (q s) := rfl
    have e2 : ∑ j : κ, wd (Sum.elim p pe (Sum.inr j)) (Sum.elim q qe (Sum.inr j)) = ∑ j, wd (pe j) (qe j) := rfl
    rw [e1, e2, tiles_angle_sum D V p q hwd]
    linarith
  obtain ⟨e, h1, h2, h3, h4⟩ := fan_cycle (Sum.elim p pe) (Sum.elim q qe) hok' hcov hdisj hsum
  exact ⟨p, q, e, hok, hloc, hwd, hspec, h1, h2, h3, h4⟩


/-- Building an `ExtFan` from the data of `vertex_fan_ext` and convexity of `Tgt`. -/
theorem extFan_of (D : RegionDissection N) (V : Plane) (hvert : ∃ i k, (D.tile i).pts k = V)
    (Tgt : Set V2) (R : ℝ) (hR : 0 < R)
    (hT : ∀ y : Plane, dist y V < R → (y ∈ D.region ↔ toV2 (y - V) ∈ Tgt))
    (hTs : ∀ z ∈ Tgt, ∀ t : ℝ, 0 < t → ((t * z.1, t * z.2) : V2) ∈ Tgt)
    (hTc : ∀ x ∈ Tgt, ∀ y ∈ Tgt, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
      ((a * x.1 + b * y.1, a * x.2 + b * y.2) : V2) ∈ Tgt)
    {κ : Type} [Fintype κ] (pe qe : κ → V2)
    (hokE : ∀ j, SecOK (pe j) (qe j))
    (hcovE : ∀ z : V2, z ∉ Tgt → ∃ j, inCone (pe j) (qe j) z)
    (hdisjE : ∀ j j', j ≠ j' → ∀ z, ¬ (inInt (pe j) (qe j) z ∧ inInt (pe j') (qe j') z))
    (hextT : ∀ j z, inInt (pe j) (qe j) z → z ∉ Tgt)
    (hangle : ∑ i, (D.tile i).localAngle V + ∑ j, wd (pe j) (qe j) = 2 * Real.pi) :
    Nonempty (ExtFan D V κ) := by
  obtain ⟨p, q, e, h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
    vertex_fan_ext D V hvert Tgt R hR hT hTs pe qe hokE hcovE hdisjE hextT hangle
  have hsumT : ∑ s : AtV D V, wd (p s) (q s) + ∑ j, wd (pe j) (qe j) = 2 * Real.pi := by
    rw [tiles_angle_sum D V p q h3]; exact hangle
  exact ⟨⟨Tgt, R, hR, hT, hTs, hTc, pe, qe, hokE, hextT, hdisjE, p, q, e, h1, h2, h3, hsumT, h4, h5, h6, h7, h8⟩⟩

/-- `extFan_of` with the shape of the result: the fan has the prescribed target cone and virtual sectors. -/
theorem extFan_of' (D : RegionDissection N) (V : Plane) (hvert : ∃ i k, (D.tile i).pts k = V)
    (Tgt : Set V2) (R : ℝ) (hR : 0 < R)
    (hT : ∀ y : Plane, dist y V < R → (y ∈ D.region ↔ toV2 (y - V) ∈ Tgt))
    (hTs : ∀ z ∈ Tgt, ∀ t : ℝ, 0 < t → ((t * z.1, t * z.2) : V2) ∈ Tgt)
    (hTc : ∀ x ∈ Tgt, ∀ y ∈ Tgt, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
      ((a * x.1 + b * y.1, a * x.2 + b * y.2) : V2) ∈ Tgt)
    {κ : Type} [Fintype κ] (pe qe : κ → V2)
    (hokE : ∀ j, SecOK (pe j) (qe j))
    (hcovE : ∀ z : V2, z ∉ Tgt → ∃ j, inCone (pe j) (qe j) z)
    (hdisjE : ∀ j j', j ≠ j' → ∀ z, ¬ (inInt (pe j) (qe j) z ∧ inInt (pe j') (qe j') z))
    (hextT : ∀ j z, inInt (pe j) (qe j) z → z ∉ Tgt)
    (hangle : ∑ i, (D.tile i).localAngle V + ∑ j, wd (pe j) (qe j) = 2 * Real.pi) :
    ∃ F : ExtFan D V κ, F.Tgt = Tgt ∧ F.pe = pe ∧ F.qe = qe := by
  obtain ⟨p, q, e, h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
    vertex_fan_ext D V hvert Tgt R hR hT hTs pe qe hokE hcovE hdisjE hextT hangle
  have hsumT : ∑ s : AtV D V, wd (p s) (q s) + ∑ j, wd (pe j) (qe j) = 2 * Real.pi := by
    rw [tiles_angle_sum D V p q h3]; exact hangle
  exact ⟨⟨Tgt, R, hR, hT, hTs, hTc, pe, qe, hokE, hextT, hdisjE, p, q, e, h1, h2, h3, hsumT, h4, h5, h6, h7, h8⟩, rfl, rfl, rfl⟩

/-- Interior vertex. -/
theorem extFan_interior (D : RegionDissection N) (V : Plane) (hvert : ∃ i k, (D.tile i).pts k = V)
    (hV : V ∈ interior D.region) : Nonempty (ExtFan D V Empty) := by
  have hN : 0 < N := by obtain ⟨i, _⟩ := hvert; exact Fin.pos i
  obtain ⟨R, hR, hball⟩ := Metric.isOpen_iff.mp isOpen_interior V hV
  refine extFan_of D V hvert Set.univ R hR ?_ (fun _ _ _ _ => Set.mem_univ _) (fun _ _ _ _ _ _ _ _ _ => Set.mem_univ _)
    (fun e => e.elim) (fun e => e.elim) (fun j => j.elim) (fun z _ => ?_) (fun j => j.elim) (fun j => j.elim) ?_
  · intro y hy
    simp only [Set.mem_univ, iff_true]
    exact interior_subset (hball (by simpa [Metric.mem_ball] using hy))
  · exact absurd (Set.mem_univ z) ‹_›
  · simp [sum_localAngle_interior D hN hV]

/-- Vertex in the relative interior of a side of the target. -/
theorem extFan_side_tri (D : RegionDissection N) (V : Plane) (T : Tri) (m : Fin 3) (h0 : T.basis.coord m V = 0)
    (hpos : ∀ j, j ≠ m → 0 < T.basis.coord j V) {ρ : ℝ} (hρ : 0 < ρ)
    (hiff : ∀ y, dist y V < ρ → (y ∈ D.region ↔ y ∈ T.carrier)) (hvert : ∃ i k, (D.tile i).pts k = V) :
    Nonempty (ExtFan D V Unit) := by
  classical
  have hN : 0 < N := by obtain ⟨i, _⟩ := hvert; exact Fin.pos i
  obtain ⟨pT, qT, hokT, hlocT, hwdT, hspecT⟩ := straight_sector T m V h0 hpos
  have hqT : qT = (-pT.1, -pT.2) := by
    rcases hspecT with ⟨k, hk, _⟩ | ⟨_, m', _, _, hq, _⟩
    · exact absurd hk (edge_coords_not_vertex T m V h0 hpos k)
    · exact hq
  subst hqT
  have hpT : pT ≠ 0 := hokT.ne_p
  obtain ⟨R, hR, hRT⟩ := hlocT
  refine extFan_of D V hvert {z | inCone pT (-pT.1, -pT.2) z} (min ρ R) (lt_min hρ hR)
    (fun y hy => by rw [hiff y (lt_of_lt_of_le hy (min_le_left _ _))]; simpa using hRT y (lt_of_lt_of_le hy (min_le_right _ _)))
    (fun z hz t ht => (inCone_smul_iff ht).mpr hz)
    (fun x hx y hy a b ha hb hab => inCone_convex hx hy ha hb hab)
    (fun _ : Unit => (-pT.1, -pT.2)) (fun _ : Unit => pT) (fun _ => secOK_ext hpT) ?_ ?_ ?_ ?_
  · intro z hz
    simp only [Set.mem_setOf_eq, inCone_straight_iff, not_le] at hz
    refine ⟨(), ?_, ?_⟩
    · show 0 ≤ crs (-pT.1, -pT.2) z; unfold crs at hz ⊢; nlinarith
    · show 0 ≤ crs z pT; unfold crs at hz ⊢; nlinarith
  · intro j j' hne; exact absurd (Subsingleton.elim j j') hne
  · intro j z hz hin
    simp only [Set.mem_setOf_eq, inCone_straight_iff] at hin
    have := hz.1
    unfold crs at this hin; simp only at this hin; nlinarith
  · rw [sum_localAngle_tri D hN T hρ hiff, Fintype.sum_unique]
    show T.localAngle V + wd (-pT.1, -pT.2) pT = 2 * Real.pi
    rw [wd_ext hpT, localAngle_of_edge_coords T m V h0 hpos]; ring

/-- Corner of the target. -/
theorem extFan_corner_tri (D : RegionDissection N) (T : Tri) (j : Fin 3) {ρ : ℝ} (hρ : 0 < ρ)
    (hiff : ∀ y, dist y (T.pts j) < ρ → (y ∈ D.region ↔ y ∈ T.carrier)) (hvert : ∃ i k, (D.tile i).pts k = T.pts j) :
    Nonempty (ExtFan D (T.pts j) Bool) := by
  classical
  have hN : 0 < N := by obtain ⟨i, _⟩ := hvert; exact Fin.pos i
  obtain ⟨pT, qT, hokT, hlocT, hwdT, hspecT⟩ := corner_sector T j
  have hcrs : 0 < crs pT qT := crs_pos_of_corner hokT hspecT ⟨j, rfl⟩
  have hpT : pT ≠ 0 := hokT.ne_p
  have hqT : qT ≠ 0 := hokT.ne_q
  obtain ⟨R, hR, hRT⟩ := hlocT
  set pe : Bool → V2 := fun b => if b then (-qT.1, -qT.2) else qT with hpe
  set qe : Bool → V2 := fun b => if b then pT else (-qT.1, -qT.2) with hqe
  have hok1 : SecOK qT (-qT.1, -qT.2) := Or.inr ⟨crs_straight qT, dt_straight_neg hqT⟩
  have hok2 : SecOK (-qT.1, -qT.2) pT := by
    left
    have : crs (-qT.1, -qT.2) pT = crs pT qT := by unfold crs; ring
    rw [this]; exact hcrs
  refine extFan_of D _ hvert {z | inCone pT qT z} (min ρ R) (lt_min hρ hR)
    (fun y hy => by rw [hiff y (lt_of_lt_of_le hy (min_le_left _ _))]; simpa using hRT y (lt_of_lt_of_le hy (min_le_right _ _)))
    (fun z hz t ht => (inCone_smul_iff ht).mpr hz)
    (fun x hx y hy a b ha hb hab => inCone_convex hx hy ha hb hab) pe qe
    (by intro b; cases b <;> simp [hpe, hqe, hok1, hok2]) ?_ ?_ ?_ ?_
  · intro z hz
    simp only [Set.mem_setOf_eq, inCone, not_and_or, not_le] at hz
    by_cases h : 0 ≤ crs qT z
    · exact ⟨false, by
        simp only [hpe, hqe, Bool.false_eq_true, if_false]
        exact (inCone_straight_iff qT z).mpr h⟩
    · push Not at h
      refine ⟨true, ?_, ?_⟩
      · simp only [hpe, hqe, if_true, eq_self_iff_true]
        unfold crs at h hz ⊢
        rcases hz with hz | hz <;> nlinarith
      · simp only [hpe, hqe, if_true, eq_self_iff_true]
        unfold crs at h hz ⊢
        rcases hz with hz | hz <;> nlinarith
  · intro b b' hbb z ⟨hz1, hz2⟩
    cases b <;> cases b' <;> simp only [hpe, hqe, Bool.false_eq_true, Bool.true_eq_false, if_true, if_false, eq_self_iff_true] at hz1 hz2
    · exact hbb rfl
    · obtain ⟨a1, a2⟩ := hz1
      obtain ⟨b1, b2⟩ := hz2
      unfold crs at a1 a2 b1 b2; nlinarith
    · obtain ⟨a1, a2⟩ := hz1
      obtain ⟨b1, b2⟩ := hz2
      unfold crs at a1 a2 b1 b2; nlinarith
    · exact hbb rfl
  · intro b z hz hin
    simp only [Set.mem_setOf_eq, inCone] at hin
    cases b <;> simp only [hpe, hqe, Bool.false_eq_true, Bool.true_eq_false, if_true, if_false, eq_self_iff_true] at hz
    · obtain ⟨a1, a2⟩ := hz; obtain ⟨b1, b2⟩ := hin
      unfold crs at a1 a2 b1 b2; nlinarith
    · obtain ⟨a1, a2⟩ := hz; obtain ⟨b1, b2⟩ := hin
      unfold crs at a1 a2 b1 b2; nlinarith
  · rw [sum_localAngle_tri D hN T hρ hiff, Fintype.sum_bool]
    simp only [hpe, hqe, Bool.false_eq_true, Bool.true_eq_false, if_true, if_false, eq_self_iff_true]
    rw [wd_straight hqT, wd_neg_left hcrs, ← hwdT]
    ring

/-- **Every tiling vertex of a dissection of a convex polygon has a uniform fan.** -/
theorem extFan_exists_poly {M : ℕ} [NeZero M] (D : RegionDissection N) (P : ConvPoly M) (hreg : D.region = P.carrier)
    (V : Plane) (hvert : ∃ i k, (D.tile i).pts k = V) :
    ∃ (κ : Type) (_ : Fintype κ), Nonempty (ExtFan D V κ) := by
  classical
  have hVP : V ∈ P.carrier := by
    obtain ⟨i, k, hk⟩ := hvert
    rw [← hreg, ← D.covers]
    exact Set.mem_iUnion.mpr ⟨i, hk ▸ subset_convexHull ℝ _ ⟨k, rfl⟩⟩
  rcases P.polygon_local P.three_le hVP with hint | ⟨T, hVT, ρ, hρ, hiff'⟩
  · exact ⟨Empty, inferInstance, extFan_interior D V hvert (hreg ▸ hint)⟩
  · have hiff : ∀ y, dist y V < ρ → (y ∈ D.region ↔ y ∈ T.carrier) := by
      intro y hy; rw [hreg]; exact hiff' y hy
    by_cases hcor : ∃ j, V = T.pts j
    · obtain ⟨j, rfl⟩ := hcor
      exact ⟨Bool, inferInstance, extFan_corner_tri D T j hρ hiff hvert⟩
    · push Not at hcor
      rcases T.classify (fun k h => hcor k h) with hpos | ⟨k, hk0, hk⟩ | ⟨k, hkneg⟩
      · refine ⟨Empty, inferInstance, extFan_interior D V hvert ?_⟩
        have hTint : V ∈ interior T.carrier := (T.mem_interior_iff_coord_pos V).mpr hpos
        obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isOpen_interior V hTint
        rw [mem_interior]
        refine ⟨Metric.ball V (min r ρ), fun y hy => ?_, Metric.isOpen_ball, Metric.mem_ball_self (lt_min hr hρ)⟩
        have hy1 : dist y V < r := lt_of_lt_of_le (Metric.mem_ball.mp hy) (min_le_left _ _)
        have hy2 : dist y V < ρ := lt_of_lt_of_le (Metric.mem_ball.mp hy) (min_le_right _ _)
        exact (hiff y hy2).mpr (interior_subset (hball (Metric.mem_ball.mpr hy1)))
      · exact ⟨Unit, inferInstance, extFan_side_tri D V T k hk0 hk hρ hiff hvert⟩
      · rw [T.carrier_eq_nonneg_coord] at hVT; exact absurd (hVT k) (not_le.mpr hkneg)

/-- Every tiling vertex has a uniform fan (hypothesis threaded through the ported graph lemmas; holds for polygons, `hasFans_poly`). -/
def HasFans (D : RegionDissection N) : Prop :=
  ∀ V : Plane, (∃ i k, (D.tile i).pts k = V) → ∃ (κ : Type) (_ : Fintype κ), Nonempty (ExtFan D V κ)

theorem hasFans_poly {M : ℕ} [NeZero M] (D : RegionDissection N) (P : ConvPoly M) (hreg : D.region = P.carrier) : HasFans D :=
  fun V hvert => extFan_exists_poly D P hreg V hvert

/-- The class form of `HasFans`, so that the ported lemmas do not need explicit fan hypotheses at every call. -/
class HasFansC (D : RegionDissection N) : Prop where
  fans : ∀ V : Plane, (∃ i k, (D.tile i).pts k = V) → ∃ (κ : Type) (_ : Fintype κ), Nonempty (ExtFan D V κ)

theorem hasFansC_poly {M : ℕ} [NeZero M] (D : RegionDissection N) (P : ConvPoly M) (hreg : D.region = P.carrier) : HasFansC D :=
  ⟨fun V hvert => extFan_exists_poly D P hreg V hvert⟩

/-! ## The ray principle -/

namespace ExtFan

variable {D : RegionDissection N} {V : Plane} {κ : Type} [Fintype κ]

theorem Tgt_inv (F : ExtFan D V κ) {z : V2} {c : ℝ} (hc : 0 < c) (h : ((c * z.1, c * z.2) : V2) ∈ F.Tgt) : z ∈ F.Tgt := by
  have := F.hTs _ h c⁻¹ (inv_pos.mpr hc)
  have e : ((c⁻¹ * (c * z.1), c⁻¹ * (c * z.2)) : V2) = z := by
    ext <;> simp <;> field_simp
  simpa [e] using this

/-- The closed cone of a tile sector lies in the target cone. -/
theorem tile_cone_sub (F : ExtFan D V κ) (s : AtV D V) {z : V2} (hz : inCone (F.p s) (F.q s) z) : z ∈ F.Tgt := by
  obtain ⟨r, hr, hiff⟩ := F.hloc s
  obtain ⟨ε, hε, hd⟩ := exists_ptOf_small V z (lt_min hr F.hR)
  have hd1 : dist (ptOf V z ε) V < r := lt_of_lt_of_le hd (min_le_left _ _)
  have hd2 : dist (ptOf V z ε) V < F.R := lt_of_lt_of_le hd (min_le_right _ _)
  have h1 : ptOf V z ε ∈ (D.tile s.1).carrier := by
    rw [hiff _ hd1, toV2_ptOf]; exact (inCone_smul_iff hε).mpr hz
  have h2 : ptOf V z ε ∈ D.region := by
    rw [← D.covers]; exact Set.mem_iUnion.mpr ⟨s.1, h1⟩
  have h3 := (F.hT _ hd2).mp h2
  rw [toV2_ptOf] at h3
  exact F.Tgt_inv hε h3

/-- Distinct sectors of the full family have disjoint open cones. -/
theorem disj_all (F : ExtFan D V κ) {o1 o2 : AtV D V ⊕ κ} (h : o1 ≠ o2) (z : V2) :
    ¬ (inInt (Sum.elim F.p F.pe o1) (Sum.elim F.q F.qe o1) z ∧ inInt (Sum.elim F.p F.pe o2) (Sum.elim F.q F.qe o2) z) := by
  rintro ⟨h1, h2⟩
  rcases o1 with s | j <;> rcases o2 with t | j'
  · exact tiles_disjoint D V F.p F.q F.hloc s t (fun e => h (by rw [e])) z ⟨h1, h2⟩
  · exact F.hextT j' z h2 (F.tile_cone_sub s ⟨h1.1.le, h1.2.le⟩)
  · exact F.hextT j z h1 (F.tile_cone_sub t ⟨h2.1.le, h2.2.le⟩)
  · exact F.hdisjE j j' (fun e => h (by rw [e])) z ⟨h1, h2⟩

/-- **Ray principle, left version.**  A left corner tile arrives at `V` along `-d` (its sector ends along `-d`) and some tile sector ends along `d`;
then some tile corner starts along `d`. -/
theorem ray_left (F : ExtFan D V κ) {d : V2} (a b : AtV D V) (hcrsA : 0 < crs (F.p a) (F.q a))
    (hqa : Par (F.q a) (-d.1, -d.2)) (hqb : Par (F.q b) d) :
    ∃ c : AtV D V, 0 < crs (F.p c) (F.q c) ∧ Par (F.p c) d := by
  classical
  have hd0 : d ≠ 0 := hqb.ne_right
  obtain ⟨δa, hδa, Ha⟩ := minus_ray_int (F.hok a)
  set zA := zminus (F.q a) (δa / 2) with hzA
  have hzAint : inInt (F.p a) (F.q a) zA := Ha _ (by positivity) (by linarith)
  have hzA_left : 0 < crs d zA := by
    obtain ⟨c', hc', hq'⟩ := hqa.smul
    have h := hzAint.2
    rw [hq'] at h
    by_contra hX; push Not at hX
    unfold crs at h hX
    try simp only at h hX
    nlinarith [mul_nonneg hc'.le (neg_nonneg.mpr hX)]
  obtain ⟨n, hn, hen⟩ := F.hsurj (Sum.inl b)
  have hPn := F.hP n
  rw [hen] at hPn
  simp only [Sum.elim_inl] at hPn
  have hsucc : Par (Sum.elim F.p F.pe (F.e (n + 1))) d := hPn.trans hqb
  rcases hnext : F.e (n + 1) with c | j
  · rw [hnext] at hsucc
    simp only [Sum.elim_inl] at hsucc
    refine ⟨c, ?_, hsucc⟩
    by_contra hnot
    push Not at hnot
    have hcs : crs (F.p c) (F.q c) = 0 ∧ dt (F.p c) (F.q c) < 0 := by
      rcases F.hok c with h | h
      · linarith
      · exact h
    obtain ⟨c1, hc1, hp1⟩ := hsucc.smul
    have hpar : Par (F.q c) (-(F.p c).1, -(F.p c).2) := by
      refine ⟨?_, ?_⟩
      · unfold crs at hcs ⊢; simp only; linarith [hcs.1]
      · unfold dt at hcs ⊢; simp only; linarith [hcs.2]
    obtain ⟨l, hl, hq1⟩ := hpar.smul
    have hzC : inInt (F.p c) (F.q c) zA := by
      constructor
      · rw [hp1]; unfold crs at hzA_left ⊢; try simp only at hzA_left ⊢; nlinarith [mul_pos hc1 hzA_left]
      · rw [hq1, hp1]; unfold crs at hzA_left ⊢; try simp only at hzA_left ⊢; nlinarith [mul_pos (mul_pos hl hc1) hzA_left]
    have hac : a ≠ c := by rintro rfl; linarith
    exact tiles_disjoint D V F.p F.q F.hloc a c hac zA ⟨hzAint, hzC⟩
  · exfalso
    rw [hnext] at hsucc
    simp only [Sum.elim_inr] at hsucc
    -- d ∈ Tgt, zA ∈ Tgt, convex combinations near d lie in the open cone of the virtual sector
    obtain ⟨c2, hc2, hqb2⟩ := hqb.smul
    have hqbT : F.q b ∈ F.Tgt := F.tile_cone_sub b ⟨(F.hok b).elim (fun h => h.le) (fun h => h.1.ge), by
      unfold crs; nlinarith [mul_comm (F.q b).1 (F.q b).2]⟩
    have hdT : d ∈ F.Tgt := F.Tgt_inv hc2 (by rw [← hqb2]; exact hqbT)
    have hzAT : zA ∈ F.Tgt := F.tile_cone_sub a ⟨hzAint.1.le, hzAint.2.le⟩
    obtain ⟨c3, hc3, hp3⟩ := hsucc.smul
    have hok := F.hokE j
    -- the virtual sector near d
    have key : ∃ μ : ℝ, 0 < μ ∧ μ < 1 ∧ inInt (F.pe j) (F.qe j) ((1 - μ) * d.1 + μ * zA.1, (1 - μ) * d.2 + μ * zA.2) := by
      rcases hok with hs | ⟨hs0, hsd⟩
      · -- crs p* q* > 0, so crs d q* > 0
        have hdq : 0 < crs d (F.qe j) := by
          rw [hp3] at hs
          unfold crs at hs ⊢; try simp only at hs ⊢
          by_contra hX; push Not at hX
          nlinarith [mul_nonneg hc3.le (neg_nonneg.mpr hX)]
        obtain ⟨δ, hδ, H⟩ := affine_pos_small (crs d (F.qe j)) (crs zA (F.qe j) - crs d (F.qe j)) hdq
        refine ⟨min (δ / 2) (1 / 2), by positivity, by
          have := min_le_right (δ / 2) (1 / 2 : ℝ); linarith, ⟨?_, ?_⟩⟩
        · rw [hp3]
          unfold crs at hzA_left ⊢; try simp only at hzA_left ⊢
          have hμ : 0 < min (δ / 2) (1 / 2 : ℝ) := by positivity
          nlinarith [mul_pos (mul_pos hc3 hμ) hzA_left]
        · have := H (min (δ / 2) (1 / 2)) (by positivity) (by
            have := min_le_left (δ / 2) (1 / 2 : ℝ); linarith)
          unfold crs at this ⊢; try simp only at this ⊢
          nlinarith [this]
      · -- straight virtual sector: q* = -l d
        have hpar : Par (F.qe j) (-d.1, -d.2) := by
          rw [hp3] at hs0 hsd
          refine ⟨?_, ?_⟩
          · unfold crs at hs0 ⊢; try simp only at hs0 ⊢; nlinarith [hs0, hc3]
          · unfold dt at hsd ⊢; try simp only at hsd ⊢; nlinarith [hsd, hc3]
        obtain ⟨l, hl, hq1⟩ := hpar.smul
        refine ⟨1 / 2, by norm_num, by norm_num, ⟨?_, ?_⟩⟩
        · rw [hp3]
          unfold crs at hzA_left ⊢; try simp only at hzA_left ⊢
          nlinarith [mul_pos hc3 hzA_left]
        · rw [hq1]
          unfold crs at hzA_left ⊢; try simp only at hzA_left ⊢
          nlinarith [mul_pos hl hzA_left]
    obtain ⟨μ, hμ0, hμ1, hμin⟩ := key
    have hmemT : ((1 - μ) * d.1 + μ * zA.1, (1 - μ) * d.2 + μ * zA.2) ∈ F.Tgt :=
      F.hTc d hdT zA hzAT (1 - μ) μ (by linarith) hμ0.le (by ring)
    exact F.hextT j _ hμin hmemT

/-- **Ray principle, right version.**  A right corner tile arrives at `V` along `-d` (its sector starts along `-d`) and some tile sector starts along `d`;
then some tile corner ends along `d`. -/
theorem ray_right (F : ExtFan D V κ) {d : V2} (a b : AtV D V) (hcrsA : 0 < crs (F.p a) (F.q a))
    (hpa : Par (F.p a) (-d.1, -d.2)) (hpb : Par (F.p b) d) :
    ∃ c : AtV D V, 0 < crs (F.p c) (F.q c) ∧ Par (F.q c) d := by
  classical
  have hd0 : d ≠ 0 := hpb.ne_right
  obtain ⟨δa, hδa, Ha⟩ := plus_ray_int (F.hok a)
  set zA := zplus (F.p a) (δa / 2) with hzA
  have hzAint : inInt (F.p a) (F.q a) zA := Ha _ (by positivity) (by linarith)
  have hzA_right : crs d zA < 0 := by
    obtain ⟨c', hc', hp'⟩ := hpa.smul
    have h := hzAint.1
    rw [hp'] at h
    by_contra hX; push Not at hX
    unfold crs at h hX
    try simp only at h hX
    nlinarith [mul_nonneg hc'.le hX]
  obtain ⟨n, hn, hen⟩ := F.hsurj (Sum.inl b)
  have hkpos : 0 < Fintype.card (AtV D V ⊕ κ) := lt_of_le_of_lt (Nat.zero_le _) hn
  have hPn := F.hP (n + (Fintype.card (AtV D V ⊕ κ) - 1))
  have hshift : n + (Fintype.card (AtV D V ⊕ κ) - 1) + 1 = n + Fintype.card (AtV D V ⊕ κ) := by omega
  rw [hshift, F.hper n, hen] at hPn
  simp only [Sum.elim_inl] at hPn
  have hpred : Par (Sum.elim F.q F.qe (F.e (n + (Fintype.card (AtV D V ⊕ κ) - 1)))) d := hPn.symm.trans hpb
  rcases hprev : F.e (n + (Fintype.card (AtV D V ⊕ κ) - 1)) with c | j
  · rw [hprev] at hpred
    simp only [Sum.elim_inl] at hpred
    refine ⟨c, ?_, hpred⟩
    by_contra hnot
    push Not at hnot
    have hcs : crs (F.p c) (F.q c) = 0 ∧ dt (F.p c) (F.q c) < 0 := by
      rcases F.hok c with h | h
      · linarith
      · exact h
    obtain ⟨c1, hc1, hq1⟩ := hpred.smul
    have hpar : Par (F.p c) (-(F.q c).1, -(F.q c).2) := by
      refine ⟨?_, ?_⟩
      · unfold crs at hcs ⊢; try simp only; linarith [hcs.1]
      · unfold dt at hcs ⊢; try simp only; linarith [hcs.2]
    obtain ⟨l, hl, hp1⟩ := hpar.smul
    have hzC : inInt (F.p c) (F.q c) zA := by
      constructor
      · rw [hp1, hq1]; unfold crs at hzA_right ⊢; try simp only at hzA_right ⊢; nlinarith [mul_pos (mul_pos hl hc1) (neg_pos.mpr hzA_right)]
      · rw [hq1]; unfold crs at hzA_right ⊢; try simp only at hzA_right ⊢; nlinarith [mul_pos hc1 (neg_pos.mpr hzA_right)]
    have hac : a ≠ c := by rintro rfl; linarith
    exact tiles_disjoint D V F.p F.q F.hloc a c hac zA ⟨hzAint, hzC⟩
  · exfalso
    rw [hprev] at hpred
    simp only [Sum.elim_inr] at hpred
    obtain ⟨c2, hc2, hpb2⟩ := hpb.smul
    have hpbT : F.p b ∈ F.Tgt := F.tile_cone_sub b ⟨by unfold crs; nlinarith [mul_comm (F.p b).1 (F.p b).2],
      (F.hok b).elim (fun h => h.le) (fun h => h.1.ge)⟩
    have hdT : d ∈ F.Tgt := F.Tgt_inv hc2 (by rw [← hpb2]; exact hpbT)
    have hzAT : zA ∈ F.Tgt := F.tile_cone_sub a ⟨hzAint.1.le, hzAint.2.le⟩
    obtain ⟨c3, hc3, hq3⟩ := hpred.smul
    have hok := F.hokE j
    have key : ∃ μ : ℝ, 0 < μ ∧ μ < 1 ∧ inInt (F.pe j) (F.qe j) ((1 - μ) * d.1 + μ * zA.1, (1 - μ) * d.2 + μ * zA.2) := by
      rcases hok with hs | ⟨hs0, hsd⟩
      · have hpd : 0 < crs (F.pe j) d := by
          rw [hq3] at hs
          unfold crs at hs ⊢; try simp only at hs ⊢
          by_contra hX; push Not at hX
          nlinarith [mul_nonneg hc3.le (neg_nonneg.mpr hX)]
        obtain ⟨δ, hδ, H⟩ := affine_pos_small (crs (F.pe j) d) (crs (F.pe j) zA - crs (F.pe j) d) hpd
        refine ⟨min (δ / 2) (1 / 2), by positivity, by
          have := min_le_right (δ / 2) (1 / 2 : ℝ); linarith, ⟨?_, ?_⟩⟩
        · have := H (min (δ / 2) (1 / 2)) (by positivity) (by
            have := min_le_left (δ / 2) (1 / 2 : ℝ); linarith)
          unfold crs at this ⊢; try simp only at this ⊢
          nlinarith [this]
        · rw [hq3]
          unfold crs at hzA_right ⊢; try simp only at hzA_right ⊢
          have hμ : 0 < min (δ / 2) (1 / 2 : ℝ) := by positivity
          nlinarith [mul_pos (mul_pos hc3 hμ) (neg_pos.mpr hzA_right)]
      · have hpar : Par (F.pe j) (-d.1, -d.2) := by
          rw [hq3] at hs0 hsd
          refine ⟨?_, ?_⟩
          · unfold crs at hs0 ⊢; try simp only at hs0 ⊢; nlinarith [hs0, hc3]
          · unfold dt at hsd ⊢; try simp only at hsd ⊢; nlinarith [hsd, hc3]
        obtain ⟨l, hl, hp1⟩ := hpar.smul
        refine ⟨1 / 2, by norm_num, by norm_num, ⟨?_, ?_⟩⟩
        · rw [hp1]
          unfold crs at hzA_right ⊢; try simp only at hzA_right ⊢
          nlinarith [mul_pos hl (neg_pos.mpr hzA_right)]
        · rw [hq3]
          unfold crs at hzA_right ⊢; try simp only at hzA_right ⊢
          nlinarith [mul_pos hc3 (neg_pos.mpr hzA_right)]
    obtain ⟨μ, hμ0, hμ1, hμin⟩ := key
    have hmemT : ((1 - μ) * d.1 + μ * zA.1, (1 - μ) * d.2 + μ * zA.2) ∈ F.Tgt :=
      F.hTc d hdT zA hzAT (1 - μ) μ (by linarith) hμ0.le (by ring)
    exact F.hextT j _ hμin hmemT

end ExtFan



end Erdos634.Draft.LaczFormal.RG
