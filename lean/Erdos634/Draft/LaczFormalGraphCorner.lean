-- Draft/LaczFormalGraphCorner.lean -- D0 (part 7): the cyclic fan at a CORNER of the target.  The exterior reflex angle is cut into the two
-- virtual sectors `(qT, -qT)` (straight) and `(-qT, pT)` (width `pi - theta`).  UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 4).
import Erdos634.Draft.LaczFormalGraphGen

namespace Erdos634.Draft.LaczFormal.Graph

open Erdos634.Geometry

variable {N : ℕ}

/-- Supplementary angle: `wd (-q) p = pi - wd p q` for a strictly convex sector. -/
theorem wd_neg_left {p q : V2} (h : 0 < crs p q) : wd (-q.1, -q.2) p = Real.pi - wd p q := by
  unfold wd
  have hz : (⟨dt p q, crs p q⟩ : ℂ) ≠ 0 := by
    intro h0
    have := congrArg Complex.im h0
    simp at this
    linarith
  have h2 : (⟨dt (-q.1, -q.2) p, crs (-q.1, -q.2) p⟩ : ℂ) = ⟨-dt p q, crs p q⟩ := by
    apply Complex.ext
    · simp [dt]; ring
    · simp [crs]; ring
  rw [h2, Complex.arg_of_im_pos (by simpa using h), Complex.arg_of_im_pos (by simpa using h)]
  have hn : ‖(⟨-dt p q, crs p q⟩ : ℂ)‖ = ‖(⟨dt p q, crs p q⟩ : ℂ)‖ := by
    have e : ‖(⟨-dt p q, crs p q⟩ : ℂ)‖ ^ 2 = ‖(⟨dt p q, crs p q⟩ : ℂ)‖ ^ 2 := by
      rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_mk, Complex.normSq_mk]; ring
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp e
  rw [hn]
  simp only [Complex.re_ofReal_mul]
  rw [show (-dt p q) / ‖(⟨dt p q, crs p q⟩ : ℂ)‖ = -(dt p q / ‖(⟨dt p q, crs p q⟩ : ℂ)‖) by ring, Real.arccos_neg]

/-- At a corner spec, the two generators are the edge vectors, so their cross is `± det` and strictly positive when the sector is admissible. -/
theorem crs_pos_of_corner {T : Tri} {V : Plane} {p q : V2} (hok : SecOK p q)
    (hspec : SectorSpec T V p q) (hv : ∃ k, T.pts k = V) : 0 < crs p q := by
  rcases hspec with ⟨k, hk, hpq⟩ | ⟨hnv, _⟩
  · have hD : cross (T.pts (k + 1) - T.pts k) (T.pts (k + 2) - T.pts k) = T.det := T.det_cyclic k
    have hdet : T.det ≠ 0 := T.det_ne_zero
    subst hk
    rcases hpq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · subst h1 h2
      rcases hok with h | ⟨h0, _⟩
      · exact h
      · rw [crs_toV2, hD] at h0; exact absurd h0 hdet
    · subst h1 h2
      rcases hok with h | ⟨h0, _⟩
      · exact h
      · rw [crs_toV2, cross_swap, hD] at h0
        exact absurd (neg_eq_zero.mp h0) hdet
  · obtain ⟨k, hk⟩ := hv
    exact absurd hk (hnv k)

/-- **D0, corner of the target.**  -/
theorem vertex_fan_corner (D : Dissection N) (j : Fin 3) (hvert : ∃ i k, (D.tile i).pts k = D.target.pts j) :
    ∃ (pT qT : V2) (p q : AtV D (D.target.pts j) → V2)
      (e : ℕ → AtV D (D.target.pts j) ⊕ Bool),
      SecOK pT qT ∧ 0 < crs pT qT ∧ LocalCone D.target (D.target.pts j) pT qT ∧ wd pT qT = D.target.localAngle (D.target.pts j) ∧
      SectorSpec D.target (D.target.pts j) pT qT ∧
      (∀ s, SecOK (p s) (q s)) ∧ (∀ s, LocalCone (D.tile s.1) (D.target.pts j) (p s) (q s)) ∧
      (∀ s, wd (p s) (q s) = (D.tile s.1).localAngle (D.target.pts j)) ∧
      (∀ s, SectorSpec (D.tile s.1) (D.target.pts j) (p s) (q s)) ∧
      (∀ n, Par (Sum.elim p (fun b : Bool => if b then (-qT.1, -qT.2) else qT) (e (n + 1)))
        (Sum.elim q (fun b : Bool => if b then pT else (-qT.1, -qT.2)) (e n))) ∧
      (∀ n, e (n + Fintype.card (AtV D (D.target.pts j) ⊕ Bool)) = e n) ∧
      Set.InjOn e (Set.Iio (Fintype.card (AtV D (D.target.pts j) ⊕ Bool))) ∧
      (∀ o, ∃ n < Fintype.card (AtV D (D.target.pts j) ⊕ Bool), e n = o) := by
  classical
  set V := D.target.pts j with hVdef
  obtain ⟨pT, qT, hokT, hlocT, hwdT, hspecT⟩ := corner_sector D.target j
  have hcrs : 0 < crs pT qT := crs_pos_of_corner hokT hspecT ⟨j, rfl⟩
  have hpT : pT ≠ 0 := hokT.ne_p
  have hqT : qT ≠ 0 := hokT.ne_q
  obtain ⟨R, hR, hRT⟩ := hlocT
  -- virtual sectors: Bool.true = (-qT, pT), Bool.false = (qT, -qT)
  set pe : Bool → V2 := fun b => if b then (-qT.1, -qT.2) else qT with hpe
  set qe : Bool → V2 := fun b => if b then pT else (-qT.1, -qT.2) with hqe
  have hok1 : SecOK qT (-qT.1, -qT.2) := Or.inr ⟨crs_straight qT, dt_straight_neg hqT⟩
  have hok2 : SecOK (-qT.1, -qT.2) pT := by
    left
    have : crs (-qT.1, -qT.2) pT = crs pT qT := by unfold crs; ring
    rw [this]; exact hcrs
  obtain ⟨p, q, e, h1, h2, h3, h4, h5, h6, h7, h8⟩ := vertex_fan_ext D V hvert
    {z | inCone pT qT z} R hR (fun y hy => by simpa using hRT y hy)
    (fun z hz t ht => (inCone_smul_iff ht).mpr hz) pe qe
    (by intro b; cases b <;> simp [hpe, hqe, hok1, hok2])
    (by
      intro z hz
      simp only [Set.mem_setOf_eq, inCone, not_and_or, not_le] at hz
      by_cases h : 0 ≤ crs qT z
      · exact ⟨false, by
          simp only [hpe, hqe, Bool.false_eq_true, if_false]
          exact (inCone_straight_iff qT z).mpr h⟩
      · push_neg at h
        refine ⟨true, ?_, ?_⟩
        · simp only [hpe, hqe, if_true, eq_self_iff_true]
          unfold crs at h hz ⊢
          rcases hz with hz | hz <;> nlinarith
        · simp only [hpe, hqe, if_true, eq_self_iff_true]
          unfold crs at h hz ⊢
          rcases hz with hz | hz <;> nlinarith)
    (by
      intro b b' hbb z ⟨hz1, hz2⟩
      cases b <;> cases b' <;> simp only [hpe, hqe, Bool.false_eq_true, Bool.true_eq_false, if_true, if_false, eq_self_iff_true] at hz1 hz2
      · exact hbb rfl
      · obtain ⟨a1, a2⟩ := hz1
        obtain ⟨b1, b2⟩ := hz2
        unfold crs at a1 a2 b1 b2; nlinarith
      · obtain ⟨a1, a2⟩ := hz1
        obtain ⟨b1, b2⟩ := hz2
        unfold crs at a1 a2 b1 b2; nlinarith
      · exact hbb rfl)
    (by
      intro b z hz hin
      simp only [Set.mem_setOf_eq, inCone] at hin
      cases b <;> simp only [hpe, hqe, Bool.false_eq_true, Bool.true_eq_false, if_true, if_false, eq_self_iff_true] at hz
      · obtain ⟨a1, a2⟩ := hz; obtain ⟨b1, b2⟩ := hin
        unfold crs at a1 a2 b1 b2; nlinarith
      · obtain ⟨a1, a2⟩ := hz; obtain ⟨b1, b2⟩ := hin
        unfold crs at a1 a2 b1 b2; nlinarith)
    (by
      rw [Fintype.sum_bool]
      simp only [hpe, hqe, Bool.false_eq_true, Bool.true_eq_false, if_true, if_false, eq_self_iff_true]
      rw [wd_straight hqT, wd_neg_left hcrs, ← hwdT]
      ring)
  exact ⟨pT, qT, p, q, e, hokT, hcrs, ⟨R, hR, hRT⟩, hwdT, hspecT, h1, h2, h3, h4, h5, h6, h7, h8⟩

end Erdos634.Draft.LaczFormal.Graph
