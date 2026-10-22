-- Draft/LaczFormalGraphGen.lean -- D0 (part 6): the cyclic fan at ANY vertex, with a finite family of VIRTUAL sectors filling the complement of the
-- target's local cone.  `vertex_fan_ext` is the common generalisation of `vertex_fan_interior` (no virtual sector), `vertex_fan_side` (one straight
-- virtual sector) and the target-CORNER case (two virtual sectors, `vertex_fan_corner`): the exterior reflex angle `2 pi - theta` is cut into
-- the straight sector `(qT, -qT)` and the sector `(-qT, pT)` of width `pi - theta`.  UNAUDITED.
-- Credit: Laczkovich (DCG 48 (2012), Sect. 4: vertices of A, the equations at the vertices of A).
import Erdos634.Draft.LaczFormalGraphSide

namespace Erdos634.Draft.LaczFormal.Graph

open Erdos634.Geometry

variable {N : ℕ}

/-- **Fan with virtual sectors.** -/
theorem vertex_fan_ext (D : Dissection N) (V : Plane) (hvert : ∃ i k, (D.tile i).pts k = V)
    (Tgt : Set V2) (R : ℝ) (hR : 0 < R)
    (hT : ∀ y : Plane, dist y V < R → (y ∈ D.target.carrier ↔ toV2 (y - V) ∈ Tgt))
    (hTs : ∀ z ∈ Tgt, ∀ t : ℝ, 0 < t → ((t * z.1, t * z.2) : V2) ∈ Tgt)
    {κ : Type} [Fintype κ] (pe qe : κ → V2)
    (hokE : ∀ j, SecOK (pe j) (qe j))
    (hcovE : ∀ z : V2, z ∉ Tgt → ∃ j, inCone (pe j) (qe j) z)
    (hdisjE : ∀ j j', j ≠ j' → ∀ z, ¬ (inInt (pe j) (qe j) z ∧ inInt (pe j') (qe j') z))
    (hextT : ∀ j z, inInt (pe j) (qe j) z → z ∉ Tgt)
    (hsumE : ∑ j, wd (pe j) (qe j) + D.target.localAngle V = 2 * Real.pi) :
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
    have h2 : ptOf V z ε ∈ D.target.carrier := by
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
    rw [e1, e2, tiles_angle_sum D V p q hwd, D.sum_localAngle_eq V]
    linarith
  obtain ⟨e, h1, h2, h3, h4⟩ := fan_cycle (Sum.elim p pe) (Sum.elim q qe) hok' hcov hdisj hsum
  exact ⟨p, q, e, hok, hloc, hwd, hspec, h1, h2, h3, h4⟩

end Erdos634.Draft.LaczFormal.Graph
