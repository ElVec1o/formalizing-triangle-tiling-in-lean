-- Draft/LaczFormalRGSideStep.lean -- S3 of PLAN_THM21: port of LaczFormalGraphSideStep to `RegionDissection` (dissection-dependent declarations only; the rest is used
-- from the original module).  UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 4), Beeson, Beeson-Zhang; port of the project's LaczFormalGraphSideStep.
import Erdos634.Draft.LaczFormalRGTypes
import Erdos634.Draft.LaczFormalGraphSideStep

open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph

namespace Erdos634.Draft.LaczFormal.RG

variable {N : ℕ}


/-! ## Corner data of a sector -/

/-- Lengths of the first sides at a corner, in terms of the model sides opposite the arm types. -/
theorem arm_lens (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    (i : Fin N) (kk : Fin 3) (fl : Bool) :
    nsq (toV2 ((D.tile i).pts (armP kk fl) - (D.tile i).pts kk)) = slen D (idx i (armQ kk fl)) ^ 2 ∧
    nsq (toV2 ((D.tile i).pts (armQ kk fl) - (D.tile i).pts kk)) = slen D (idx i (armP kk fl)) ^ 2 := by
  rw [nsq_toV2_sub, nsq_toV2_sub]
  have h1 := side_len_01 D idx hidx i kk
  have h2 := side_len_02 D idx hidx i kk
  cases fl
  · simp only [armP, armQ, Bool.false_eq_true, if_false]
    rw [dist_comm, h1, dist_comm, h2]; exact ⟨rfl, rfl⟩
  · simp only [armP, armQ, if_true]
    rw [dist_comm, h2, dist_comm, h1]; exact ⟨rfl, rfl⟩


/-- Packaged conclusions of `side_fan_three`. -/
structure SideFan3 (D : RegionDissection N) (V : Plane) (pT : V2) (p q : AtV D V → V2) (s1 s2 s3 : AtV D V) : Prop where
  pT_ne : pT ≠ 0
  ok : ∀ s, SecOK (p s) (q s)
  loc : ∀ s, LocalCone (D.tile s.1) V (p s) (q s)
  spec : ∀ s, SectorSpec (D.tile s.1) V (p s) (q s)
  d12 : s1 ≠ s2
  d13 : s1 ≠ s3
  d23 : s2 ≠ s3
  all : ∀ s, s = s1 ∨ s = s2 ∨ s = s3
  r1 : Par (p s1) pT
  r2 : Par (p s2) (q s1)
  r3 : Par (p s3) (q s2)
  r4 : Par (-pT.1, -pT.2) (q s3)


theorem slen_pos (D : CongruentRegionDissection N) (t : Fin 3) : 0 < slen D t := by
  unfold slen
  apply dist_pos.mpr
  intro h
  exact fin3_add_ne t (D.model.indep.injective h)


theorem slen_sq_eq_iff (D : CongruentRegionDissection N) (hab : slen D 0 ≠ slen D 1) (hac : slen D 0 ≠ slen D 2) (t : Fin 3) :
    slen D t ^ 2 = slen D 0 ^ 2 ↔ t = 0 := by
  constructor
  · intro h
    have h' : slen D t = slen D 0 := by
      have := slen_pos D t
      have := slen_pos D 0
      nlinarith [sq_nonneg (slen D t - slen D 0), sq_nonneg (slen D t + slen D 0)]
    fin_cases t
    · rfl
    · exact absurd h'.symm hab
    · exact absurd h'.symm hac
  · rintro rfl; rfl


/-- **D4, the translate step at a normal side vertex (real).**  In the three-tile fan at a vertex `V` on a side of the target with the line
tiles `s1` (starting along `pT`) and `s3` (ending along `-pT`): if the types at `V` are distinct (normal), no inner ray has differing first
sides (no `Γ_a` edge), `a` differs from `b` and `c`, and the left tile `s3` has `β, γ` on the line, then the right tile `s1` has the same
type pair on the line: Laczkovich Lemma 4.3 (ii), local step. -/
theorem side_step (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    (V : Plane) {pT : V2} {p q : AtV D.toRegionDissection V → V2} {s1 s2 s3 : AtV D.toRegionDissection V}
    (hF : SideFan3 D.toRegionDissection V pT p q s1 s2 s3)
    (hcorner2 : ∃ k, (D.tile s2.1).pts k = V)
    (hab : slen D 0 ≠ slen D 1) (hac : slen D 0 ≠ slen D 2)
    (hnorm : ∀ k1 k2 k3, (D.tile s1.1).pts k1 = V → (D.tile s2.1).pts k2 = V → (D.tile s3.1).pts k3 = V →
      idx s1.1 k1 ≠ idx s2.1 k2 ∧ idx s1.1 k1 ≠ idx s3.1 k3 ∧ idx s2.1 k2 ≠ idx s3.1 k3)
    (hno1 : nsq (q s1) = slen D 0 ^ 2 ↔ nsq (p s2) = slen D 0 ^ 2)
    (hno2 : nsq (q s2) = slen D 0 ^ 2 ↔ nsq (p s3) = slen D 0 ^ 2)
    (kR fR kL fL : Fin 3) (hR1 : (D.tile s1.1).pts kR = V)
    (hR2 : Par (toV2 ((D.tile s1.1).pts fR - V)) pT)
    (hL1 : (D.tile s3.1).pts kL = V)
    (hL2 : Par (toV2 ((D.tile s3.1).pts fL - V)) (-pT.1, -pT.2))
    (hβγ : (idx s3.1 fL = 1 ∧ idx s3.1 kL = 2) ∨ (idx s3.1 fL = 2 ∧ idx s3.1 kL = 1)) :
    idx s1.1 kR = idx s3.1 fL ∧ idx s1.1 fR = idx s3.1 kL := by
  classical
  obtain ⟨kk1, fl1, hk1, hp1, hq1⟩ := spec_corner_data (hF.spec s1) ⟨kR, hR1⟩
  obtain ⟨kk2, fl2, hk2, hp2, hq2⟩ := spec_corner_data (hF.spec s2) hcorner2
  obtain ⟨kk3, fl3, hk3, hp3, hq3⟩ := spec_corner_data (hF.spec s3) ⟨kL, hL1⟩
  have e1 : kR = kk1 := (D.tile s1.1).indep.injective (hR1.trans hk1.symm)
  have e3 : kL = kk3 := (D.tile s3.1).indep.injective (hL1.trans hk3.symm)
  subst e1 e3
  -- the far vertices
  have hfR : fR = armP kR fl1 := by
    refine arm_unique (D.tile s1.1) V kR hR1 fR (armP kR fl1) ?_ (armP_ne kR fl1) pT hR2 ?_
    · intro h
      have := hR2.ne_left
      apply this
      rw [h, hR1]; simp [toV2]
    · have := hF.r1; rw [hp1] at this; exact this
  have hfL : fL = armQ kL fl3 := by
    refine arm_unique (D.tile s3.1) V kL hL1 fL (armQ kL fl3) ?_ (armQ_ne kL fl3) (-pT.1, -pT.2) hL2 ?_
    · intro h
      have := hL2.ne_left
      apply this
      rw [h, hL1]; simp [toV2]
    · have := hF.r4; rw [hq3] at this; exact this.symm
  subst hfR hfL
  -- codes
  set c1 := codeOf (idx s1.1) kR fl1 with hc1
  set c2 := codeOf (idx s2.1) kk2 fl2 with hc2
  set c3 := codeOf (idx s3.1) kL fl3 with hc3
  obtain ⟨t1, u1, w1, l1⟩ := codeOf_spec' (idx s1.1) kR fl1
  obtain ⟨t2, u2, w2, l2⟩ := codeOf_spec' (idx s2.1) kk2 fl2
  obtain ⟨t3, u3, w3, l3⟩ := codeOf_spec' (idx s3.1) kL fl3
  rw [← hc1] at t1 u1 w1 l1
  rw [← hc2] at t2 u2 w2 l2
  rw [← hc3] at t3 u3 w3 l3
  have hnm := hnorm kR kk2 kL hR1 hk2 hL1
  -- lengths in terms of types
  have hlen1 := arm_lens D idx hidx s1.1 kR fl1
  have hlen2 := arm_lens D idx hidx s2.1 kk2 fl2
  have hlen3 := arm_lens D idx hidx s3.1 kL fl3
  rw [hk1] at hlen1; rw [hk2] at hlen2; rw [hk3] at hlen3
  rw [← hp1, ← hq1] at hlen1
  rw [← hp2, ← hq2] at hlen2
  rw [← hp3, ← hq3] at hlen3
  have hs := slen_sq_eq_iff D hab hac
  -- no differing first sides
  have g1 : (RegFan.tU c1 == 0) = (RegFan.tW c2 == 0) := by
    have h := hno1
    rw [hlen1.2, hlen2.1, hs, hs] at h
    have e1' : (RegFan.tU c1 = 0) ↔ (idx s1.1 (armP kR fl1) = 0) := by
      rw [u1]
      constructor
      · intro h'; exact Fin.ext (by simpa using h')
      · intro h'; rw [h']; rfl
    have e2' : (RegFan.tW c2 = 0) ↔ (idx s2.1 (armQ kk2 fl2) = 0) := by
      rw [w2]
      constructor
      · intro h'; exact Fin.ext (by simpa using h')
      · intro h'; rw [h']; rfl
    rw [Bool.eq_iff_iff]
    simp only [beq_iff_eq]
    exact e1'.trans (h.trans e2'.symm)
  have g2 : (RegFan.tU c2 == 0) = (RegFan.tW c3 == 0) := by
    have h := hno2
    rw [hlen2.2, hlen3.1, hs, hs] at h
    have e1' : (RegFan.tU c2 = 0) ↔ (idx s2.1 (armP kk2 fl2) = 0) := by
      rw [u2]
      constructor
      · intro h'; exact Fin.ext (by simpa using h')
      · intro h'; rw [h']; rfl
    have e2' : (RegFan.tW c3 = 0) ↔ (idx s3.1 (armQ kL fl3) = 0) := by
      rw [w3]
      constructor
      · intro h'; exact Fin.ext (by simpa using h')
      · intro h'; rw [h']; rfl
    rw [Bool.eq_iff_iff]
    simp only [beq_iff_eq]
    exact e1'.trans (h.trans e2'.symm)
  set l : List ℕ := [c1, c2, c3] with hl
  have hlen : l.length = 3 := rfl
  have hlt : ∀ x ∈ l, x < 6 := by
    intro x hx
    simp only [hl, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  have hc : ∀ j : Fin 3, RegFan.cnt l j = 1 := by
    intro j
    rw [hl, cnt3_eq, t1, t2, t3]
    exact perm3_cnt (idx s1.1 kR) (idx s2.1 kk2) (idx s3.1 kL) hnm.1 hnm.2.1 hnm.2.2 j
  have hga1 : RegFan.gaEdge l 1 = false := by
    simp only [RegFan.gaEdge, RegFan.Lc, RegFan.Rc, hl, hlen]
    simp [g1]
  have hga2 : RegFan.gaEdge l 2 = false := by
    simp only [RegFan.gaEdge, RegFan.Lc, RegFan.Rc, hl, hlen]
    simp [g2]
  have hstep : RegFan.stepHyp l = true := by
    have h0 := hc 0
    have h1 := hc 1
    have h2 := hc 2
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two] at h0 h1 h2
    unfold RegFan.stepHyp
    simp [h0, h1, h2, hga1, hga2]
  have hline : RegFan.line12' l = true := by
    show ((RegFan.tT c3 == 1 && RegFan.tW c3 == 2) || (RegFan.tT c3 == 2 && RegFan.tW c3 == 1)) = true
    rw [t3, w3]
    rcases hβγ with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · simp [h1, h2]
    · simp [h1, h2]
  have htr := RegFan.boundary_step_beta_gamma' l hlen hlt hstep hline
  have htr' : c3 = RegFan.code (RegFan.tU c1) (RegFan.tW c1) (RegFan.tT c1) := beq_iff_eq.mp htr
  rw [t1, u1, w1] at htr'
  have hd1 : idx s1.1 (armP kR fl1) ≠ idx s1.1 (armQ kR fl1) := (idx s1.1).injective.ne (armPQ_ne kR fl1)
  have hd2 : idx s1.1 (armP kR fl1) ≠ idx s1.1 kR := (idx s1.1).injective.ne (armP_ne kR fl1)
  have hd3 : idx s1.1 (armQ kR fl1) ≠ idx s1.1 kR := (idx s1.1).injective.ne (armQ_ne kR fl1)
  obtain ⟨A, B, C, -⟩ := code_spec (idx s1.1 (armP kR fl1)) (idx s1.1 (armQ kR fl1)) (idx s1.1 kR) hd1 hd2 hd3
  have x1 : RegFan.tT c3 = idx s1.1 (armP kR fl1) := by rw [htr']; exact A
  have x2 : RegFan.tW c3 = idx s1.1 kR := by rw [htr']; exact C
  refine ⟨?_, ?_⟩
  · apply Fin.ext
    rw [← x2, w3]
  · apply Fin.ext
    rw [← x1, t3]


#print axioms Erdos634.Draft.LaczFormal.Graph.side_step
#print axioms Erdos634.Draft.LaczFormal.Graph.side_fan_three_struct

end Erdos634.Draft.LaczFormal.RG
