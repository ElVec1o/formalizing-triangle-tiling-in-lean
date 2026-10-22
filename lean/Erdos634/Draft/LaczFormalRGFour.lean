-- Draft/LaczFormalRGFour.lean -- S3 of PLAN_THM21: port of LaczFormalGraphFour to `RegionDissection` (dissection-dependent declarations only; the rest is used
-- from the original module).  UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 4), Beeson, Beeson-Zhang; port of the project's LaczFormalGraphFour.
import Erdos634.Draft.LaczFormalRGHeadFan
import Erdos634.Draft.LaczFormalGraphFour

open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph

namespace Erdos634.Draft.LaczFormal.RG

variable {N : ℕ}


/-- `Γ_k`: `Z → X` iff `ZX` is a common side of two distinct tiles, both with `γ` (type 2) at `Z` and `β` (type 1) at `X`. -/
def GkEdge (D : RegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) (Z X : Plane) : Prop :=
  ∃ (i j : Fin N) (k1 k2 k1' k2' : Fin 3), i ≠ j ∧ (D.tile i).pts k1 = Z ∧ (D.tile i).pts k2 = X ∧
    (D.tile j).pts k1' = Z ∧ (D.tile j).pts k2' = X ∧ idx i k1 = 2 ∧ idx i k2 = 1 ∧ idx j k1' = 2 ∧ idx j k2' = 1


theorem NoBack.of_par {D : RegionDissection N} {d d' : V2} {X : Plane} (hd : Par d' d) (h : NoBack D d X) : NoBack D d' X := by
  have hn : Par (neg2 d') (neg2 d) := par_neg hd
  refine ⟨fun i A B σ hS h0 h1 => h.1 i A B σ (TriStep.of_par hd.symm hS) h0 h1, fun i A B σ hS h0 h1 => ?_⟩
  exact h.2 i A B σ (TriStep.of_par hn.symm hS) h0 h1


theorem ExtFan.corner_of_crs {D : RegionDissection N} {V : Plane} {κ : Type} [Fintype κ] (F : ExtFan D V κ) (x : AtV D V)
    (hc : 0 < crs (F.p x) (F.q x)) : ∃ k, (D.tile x.1).pts k = V := by
  rcases F.hspec x with ⟨k, hk, -⟩ | ⟨-, m', -, -, hq, -⟩
  · exact ⟨k, hk⟩
  · exfalso; rw [hq] at hc; unfold crs at hc; try simp only at hc; nlinarith


/-- Length of the `q`-arm of a corner sector, in terms of the type at the `p`-arm vertex. -/
theorem nsq_q_iff (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    (hab : slen D 0 ≠ slen D 1) (hac : slen D 0 ≠ slen D 2) {H : Plane} {i : Fin N} {kk : Fin 3} (fl : Bool)
    (hk : (D.tile i).pts kk = H) {q : V2} (hq : q = toV2 ((D.tile i).pts (armQ kk fl) - H)) :
    nsq q = slen D 0 ^ 2 ↔ idx i (armP kk fl) = 0 := by
  rw [hq, ← hk, (arm_lens D idx hidx i kk fl).2]
  exact slen_sq_eq_iff D hab hac _


theorem nsq_p_iff (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    (hab : slen D 0 ≠ slen D 1) (hac : slen D 0 ≠ slen D 2) {H : Plane} {i : Fin N} {kk : Fin 3} (fl : Bool)
    (hk : (D.tile i).pts kk = H) {p : V2} (hp : p = toV2 ((D.tile i).pts (armP kk fl) - H)) :
    nsq p = slen D 0 ^ 2 ↔ idx i (armQ kk fl) = 0 := by
  rw [hp, ← hk, (arm_lens D idx hidx i kk fl).1]
  exact slen_sq_eq_iff D hab hac _


/-- **A `Γ_k` edge along a ray of the fan**: two adjacent corner sectors `x` (clockwise) and `y` (counterclockwise) with `γ` at `H` and `β` at the end of their arms along the common ray. -/
theorem gk_of_ray (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    (hab : slen D 0 ≠ slen D 1) (hac : slen D 0 ≠ slen D 2) {H : Plane} {κ : Type} [Fintype κ] (F : ExtFan D.toRegionDissection H κ)
    (x y : AtV D.toRegionDissection H) (hxy : Par (F.p y) (F.q x)) (hne : x ≠ y)
    {kx ky : Fin 3} {flx fly : Bool} (hkx : (D.tile x.1).pts kx = H) (hky : (D.tile y.1).pts ky = H)
    (hpx : F.p x = toV2 ((D.tile x.1).pts (armP kx flx) - H)) (hqx : F.q x = toV2 ((D.tile x.1).pts (armQ kx flx) - H))
    (hpy : F.p y = toV2 ((D.tile y.1).pts (armP ky fly) - H)) (hqy : F.q y = toV2 ((D.tile y.1).pts (armQ ky fly) - H))
    (t2x : idx x.1 kx = 2) (t1x : idx x.1 (armQ kx flx) = 1) (t2y : idx y.1 ky = 2) (t1y : idx y.1 (armP ky fly) = 1) :
    ∃ Z, GkEdge D.toRegionDissection idx H Z := by
  have hxA : idx x.1 (armP kx flx) = 0 :=
    perm_third (idx x.1) kx (armQ kx flx) (armP kx flx) (armQ_ne kx flx).symm (armP_ne kx flx).symm (armPQ_ne kx flx).symm t2x t1x
  have hyA : idx y.1 (armQ ky fly) = 0 :=
    perm_third (idx y.1) ky (armP ky fly) (armQ ky fly) (armP_ne ky fly).symm (armQ_ne ky fly).symm (armPQ_ne ky fly) t2y t1y
  have hnx : nsq (F.q x) = slen D 0 ^ 2 := (nsq_q_iff D idx hidx hab hac flx hkx hqx).mpr hxA
  have hny : nsq (F.p y) = slen D 0 ^ 2 := (nsq_p_iff D idx hidx hab hac fly hky hpy).mpr hyA
  have heq : F.p y = F.q x := par_eq_of_nsq hxy (by rw [hnx, hny])
  have hPP : (D.tile x.1).pts (armQ kx flx) = (D.tile y.1).pts (armP ky fly) := by
    apply pt_eq_of_toV2 (H := H)
    rw [← hqx, ← hpy, heq]
  refine ⟨(D.tile x.1).pts (armQ kx flx), x.1, y.1, kx, armQ kx flx, ky, armP ky fly, fun h => hne (Subtype.ext h), hkx, rfl, hky, hPP.symm,
    t2x, t1x, t2y, t1y⟩


/-- **`Γ_a` edge from the code-level difference of the first sides.** -/
theorem ga_of_codes (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    (hnc : NotComb (slen D 0) (slen D 1) (slen D 2)) (hab : slen D 0 ≠ slen D 1) (hac : slen D 0 ≠ slen D 2)
    {H : Plane} {κ : Type} [Fintype κ] (F : ExtFan D.toRegionDissection H κ)
    (x y : AtV D.toRegionDissection H) (hcx : 0 < crs (F.p x) (F.q x)) (hcy : 0 < crs (F.p y) (F.q y))
    (hxy : Par (F.p y) (F.q x)) (hnb : NoBack D.toRegionDissection (F.q x) H)
    {kx ky : Fin 3} {flx fly : Bool} (hkx : (D.tile x.1).pts kx = H) (hky : (D.tile y.1).pts ky = H)
    (hqx : F.q x = toV2 ((D.tile x.1).pts (armQ kx flx) - H)) (hpy : F.p y = toV2 ((D.tile y.1).pts (armP ky fly) - H))
    (hg : ((RegFan.tU (codeOf (idx x.1) kx flx) == 0) != (RegFan.tW (codeOf (idx y.1) ky fly) == 0)) = true) :
    ∃ H', GaEdge D.toRegionDissection (slen D 0) H H' := by
  obtain ⟨-, tx2, -, -⟩ := codeOf_spec' (idx x.1) kx flx
  obtain ⟨-, -, ty3, -⟩ := codeOf_spec' (idx y.1) ky fly
  have q1 := nsq_q_iff D idx hidx hab hac flx hkx hqx
  have p1 := nsq_p_iff D idx hidx hab hac fly hky hpy
  refine ga_edge_of_ray D idx hidx hnc F x y hcx hcy hxy hnb ?_
  rcases hb1 : (RegFan.tU (codeOf (idx x.1) kx flx) == 0) <;> rcases hb2 : (RegFan.tW (codeOf (idx y.1) ky fly) == 0) <;>
    simp [hb1, hb2] at hg
  · -- tU ≠ 0, tW = 0 : right side not a, left side a
    right
    have c1 : idx y.1 (armQ ky fly) = 0 := (beq_zero_iff _ _ ty3).mp hb2
    have c2 : ¬ idx x.1 (armP kx flx) = 0 := fun h => by
      have := (beq_zero_iff _ _ tx2).mpr h
      rw [hb1] at this; exact Bool.false_ne_true this
    exact ⟨fun h => c2 (q1.mp h), p1.mpr c1⟩
  · left
    have c1 : idx x.1 (armP kx flx) = 0 := (beq_zero_iff _ _ tx2).mp hb1
    have c2 : ¬ idx y.1 (armQ ky fly) = 0 := fun h => by
      have := (beq_zero_iff _ _ ty3).mpr h
      rw [hb2] at this; exact Bool.false_ne_true this
    exact ⟨q1.mpr c1, fun h => c2 (p1.mp h)⟩


/-- **`Γ_k` edge from the code-level `gkEdge` condition.** -/
theorem gk_of_codes (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    (hab : slen D 0 ≠ slen D 1) (hac : slen D 0 ≠ slen D 2) {H : Plane} {κ : Type} [Fintype κ] (F : ExtFan D.toRegionDissection H κ)
    (x y : AtV D.toRegionDissection H) (hxy : Par (F.p y) (F.q x)) (hne : x ≠ y)
    {kx ky : Fin 3} {flx fly : Bool} (hkx : (D.tile x.1).pts kx = H) (hky : (D.tile y.1).pts ky = H)
    (hpx : F.p x = toV2 ((D.tile x.1).pts (armP kx flx) - H)) (hqx : F.q x = toV2 ((D.tile x.1).pts (armQ kx flx) - H))
    (hpy : F.p y = toV2 ((D.tile y.1).pts (armP ky fly) - H)) (hqy : F.q y = toV2 ((D.tile y.1).pts (armQ ky fly) - H))
    (hg : (RegFan.tT (codeOf (idx x.1) kx flx) == 2 && RegFan.tT (codeOf (idx y.1) ky fly) == 2 &&
           RegFan.tW (codeOf (idx x.1) kx flx) == 1 && RegFan.tU (codeOf (idx y.1) ky fly) == 1) = true) :
    ∃ Z, GkEdge D.toRegionDissection idx H Z := by
  obtain ⟨tx1, -, tx3, -⟩ := codeOf_spec' (idx x.1) kx flx
  obtain ⟨ty1, ty2, -, -⟩ := codeOf_spec' (idx y.1) ky fly
  simp only [Bool.and_eq_true, beq_iff_eq] at hg
  obtain ⟨⟨⟨g1, g2⟩, g3⟩, g4⟩ := hg
  have e1 : idx x.1 kx = 2 := by apply Fin.ext; rw [← tx1] at *; simpa using g1
  have e2 : idx y.1 ky = 2 := by apply Fin.ext; simpa [ty1] using g2
  have e3 : idx x.1 (armQ kx flx) = 1 := by apply Fin.ext; simpa [tx3] using g3
  have e4 : idx y.1 (armP ky fly) = 1 := by apply Fin.ext; simpa [ty2] using g4
  exact gk_of_ray D idx hidx hab hac F x y hxy hne hkx hky hpx hqx hpy hqy e1 e3 e2 e4


/-- **Lemma 4.2 for real tilings (head with three corner tiles).**  At a head `H` (configuration `HeadCfg`) whose three corner tiles have pairwise distinct types
(a normal vertex, `α+β+γ = π`) or are all of type `γ` (`3γ = π`), an edge of `Γ_a` or of `Γ_k` starts at `H`. -/
theorem head_out_edge (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    (hnc : NotComb (slen D 0) (slen D 1) (slen D 2)) (hab : slen D 0 ≠ slen D 1) (hac : slen D 0 ≠ slen D 2)
    {H : Plane} {κ : Type} [Fintype κ] (F : ExtFan D.toRegionDissection H κ) {e : V2} {u v s : AtV D.toRegionDissection H}
    (hc : HeadCfg D F e u v s) (hcard : Fintype.card (AtV D.toRegionDissection H) = 4)
    (hN : (∀ t₁ t₂ : AtV D.toRegionDissection H, t₁ ≠ s → t₂ ≠ s → t₁ ≠ t₂ → ∀ k₁ k₂, (D.tile t₁.1).pts k₁ = H →
            (D.tile t₂.1).pts k₂ = H → idx t₁.1 k₁ ≠ idx t₂.1 k₂) ∨
          (∀ t : AtV D.toRegionDissection H, t ≠ s → ∀ k, (D.tile t.1).pts k = H → idx t.1 k = 2)) :
    (∃ H', GaEdge D.toRegionDissection (slen D 0) H H') ∨ ∃ Z, GkEdge D.toRegionDissection idx H Z := by
  classical
  obtain ⟨hc1, hc2, hc3, hc4, hc5, hc6, hc7⟩ := hc
  obtain ⟨hemp, hint, m, huv, hus, hvs, hmu, hmv, hms, hall, hmv', hum', hvs', hsu', hcm⟩ :=
    F.head_four hc1 hc2 hc3 hc4 hc5 hc6 hcard
  have hnb := F.head_inner_noBack hc1 hc2 hc3 hc4 hc5 hc6 hall hmv' hum'
  have hnb2 : NoBack D.toRegionDissection (F.q m) H := NoBack.of_par hum'.symm hnb.2
  obtain ⟨kv0, hkv0⟩ := F.corner_of_crs v hc3
  obtain ⟨km0, hkm0⟩ := F.corner_of_crs m hcm
  obtain ⟨ku0, hku0⟩ := F.corner_of_crs u hc1
  obtain ⟨kv, flv, hkv, hpv, hqv⟩ := spec_corner_data (F.hspec v) ⟨kv0, hkv0⟩
  obtain ⟨km, flm, hkm, hpm, hqm⟩ := spec_corner_data (F.hspec m) ⟨km0, hkm0⟩
  obtain ⟨ku, flu, hku, hpu, hqu⟩ := spec_corner_data (F.hspec u) ⟨ku0, hku0⟩
  set cv := codeOf (idx v.1) kv flv with hcv
  set cm := codeOf (idx m.1) km flm with hcm'
  set cu := codeOf (idx u.1) ku flu with hcu
  obtain ⟨tv1, tv2, tv3, lv⟩ := codeOf_spec' (idx v.1) kv flv
  obtain ⟨tm1, tm2, tm3, lm⟩ := codeOf_spec' (idx m.1) km flm
  obtain ⟨tu1, tu2, tu3, lu⟩ := codeOf_spec' (idx u.1) ku flu
  rw [← hcv] at tv1 tv2 tv3 lv
  rw [← hcm'] at tm1 tm2 tm3 lm
  rw [← hcu] at tu1 tu2 tu3 lu
  have qu := nsq_q_iff D idx hidx hab hac flu hku hqu
  have pv := nsq_p_iff D idx hidx hab hac flv hkv hpv
  set l : List ℕ := [cv, cm, cu] with hl
  have hlen : l.length = 3 := rfl
  have hlt : ∀ x ∈ l, x < 6 := by
    intro x hx
    simp only [hl, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  have hinc : RegFan.incoming l = true := by
    show ((RegFan.tW cv == 0 && RegFan.tU cu != 0) || (RegFan.tU cu == 0 && RegFan.tW cv != 0)) = true
    rcases hc7 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have a1 : idx u.1 (armP ku flu) = 0 := (qu).mp h1
      have a2 : ¬ idx v.1 (armQ kv flv) = 0 := fun h => h2 ((pv).mpr h)
      have b1 : (RegFan.tU cu == 0) = true := (beq_zero_iff _ _ tu2).mpr a1
      have b2 : (RegFan.tW cv == 0) = false := by
        by_contra hh
        have hh' : (RegFan.tW cv == 0) = true := by simpa using hh
        exact a2 ((beq_zero_iff _ _ tv3).mp hh')
      simp only [bne, b1, b2]; rfl
    · have a1 : idx v.1 (armQ kv flv) = 0 := (pv).mp h2
      have a2 : ¬ idx u.1 (armP ku flu) = 0 := fun h => h1 ((qu).mpr h)
      have b1 : (RegFan.tW cv == 0) = true := (beq_zero_iff _ _ tv3).mpr a1
      have b2 : (RegFan.tU cu == 0) = false := by
        by_contra hh
        have hh' : (RegFan.tU cu == 0) = true := by simpa using hh
        exact a2 ((beq_zero_iff _ _ tu2).mp hh')
      simp only [bne, b1, b2]; rfl
  have hkvH := hkv
  -- bridging a code-level edge at ray `i`
  have ray1ga : RegFan.gaEdge l 1 = true → ∃ H', GaEdge D.toRegionDissection (slen D 0) H H' := by
    intro hg
    have hg' : ((RegFan.tU cv == 0) != (RegFan.tW cm == 0)) = true := by
      simpa [RegFan.gaEdge, RegFan.Lc, RegFan.Rc, hl] using hg
    exact ga_of_codes D idx hidx hnc hab hac F v m hc3 hcm hmv' hnb.1 hkv hkm hqv hpm hg'
  have ray2ga : RegFan.gaEdge l 2 = true → ∃ H', GaEdge D.toRegionDissection (slen D 0) H H' := by
    intro hg
    have hg' : ((RegFan.tU cm == 0) != (RegFan.tW cu == 0)) = true := by
      simpa [RegFan.gaEdge, RegFan.Lc, RegFan.Rc, hl] using hg
    exact ga_of_codes D idx hidx hnc hab hac F m u hcm hc1 hum' hnb2 hkm hku hqm hpu hg'
  have ray1gk : RegFan.gkEdge l 1 = true → ∃ Z, GkEdge D.toRegionDissection idx H Z := by
    intro hg
    have hg' : (RegFan.tT cv == 2 && RegFan.tT cm == 2 && RegFan.tW cv == 1 && RegFan.tU cm == 1) = true := by
      simpa [RegFan.gkEdge, RegFan.Lc, RegFan.Rc, hl] using hg
    exact gk_of_codes D idx hidx hab hac F v m hmv' (Ne.symm hmv) hkv hkm hpv hqv hpm hqm hg'
  have ray2gk : RegFan.gkEdge l 2 = true → ∃ Z, GkEdge D.toRegionDissection idx H Z := by
    intro hg
    have hg' : (RegFan.tT cm == 2 && RegFan.tT cu == 2 && RegFan.tW cm == 1 && RegFan.tU cu == 1) = true := by
      simpa [RegFan.gkEdge, RegFan.Lc, RegFan.Rc, hl] using hg
    exact gk_of_codes D idx hidx hab hac F m u hum' hmu hkm hku hpm hqm hpu hqu hg'
  rcases hN with hN1 | hN2
  · -- normal vertex: three distinct types
    have d12 : idx v.1 kv ≠ idx m.1 km := hN1 v m hvs hms (Ne.symm hmv) kv km hkv hkm
    have d13 : idx v.1 kv ≠ idx u.1 ku := hN1 v u hvs hus (Ne.symm huv) kv ku hkv hku
    have d23 : idx m.1 km ≠ idx u.1 ku := hN1 m u hms hus hmu km ku hkm hku
    have hhyp : RegFan.piNormalHyp l = true := by
      unfold RegFan.piNormalHyp
      have c0 := perm3_cnt (idx v.1 kv) (idx m.1 km) (idx u.1 ku) d12 d13 d23 0
      have c1 := perm3_cnt (idx v.1 kv) (idx m.1 km) (idx u.1 ku) d12 d13 d23 1
      have c2 := perm3_cnt (idx v.1 kv) (idx m.1 km) (idx u.1 ku) d12 d13 d23 2
      have e0 : RegFan.cnt l 0 = 1 := by rw [hl, cnt3_eq, tv1, tm1, tu1]; simpa using c0
      have e1 : RegFan.cnt l 1 = 1 := by rw [hl, cnt3_eq, tv1, tm1, tu1]; simpa using c1
      have e2 : RegFan.cnt l 2 = 1 := by rw [hl, cnt3_eq, tv1, tm1, tu1]; simpa using c2
      simp [e0, e1, e2, hinc]
    have hconcl := RegFan.pi_fan_normal l hlen hlt hhyp
    unfold RegFan.piNormalConcl at hconcl
    simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at hconcl
    obtain ⟨i, hi, hi1, hgi⟩ := hconcl
    left
    interval_cases i
    · exact ray1ga hgi
    · exact ray2ga hgi
  · -- three gammas
    have g1 : idx v.1 kv = 2 := hN2 v hvs kv hkv
    have g2 : idx m.1 km = 2 := hN2 m hms km hkm
    have g3 : idx u.1 ku = 2 := hN2 u hus ku hku
    have hhyp : RegFan.pi003Hyp l = true := by
      unfold RegFan.pi003Hyp
      have e0 : RegFan.cnt l 0 = 0 := by rw [hl, cnt3_eq, tv1, tm1, tu1, g1, g2, g3]; simp
      have e1 : RegFan.cnt l 1 = 0 := by rw [hl, cnt3_eq, tv1, tm1, tu1, g1, g2, g3]; simp
      have e2 : RegFan.cnt l 2 = 3 := by rw [hl, cnt3_eq, tv1, tm1, tu1, g1, g2, g3]; simp
      simp [e0, e1, e2, hinc]
    have hconcl := RegFan.pi_fan_3gamma l hlen hlt hhyp
    unfold RegFan.pi003Concl at hconcl
    simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hconcl
    obtain ⟨i, hi, hi1, hgi⟩ := hconcl
    interval_cases i
    · rcases hgi with hga | hgk
      · exact Or.inl (ray1ga hga)
      · exact Or.inr (ray1gk hgk)
    · rcases hgi with hga | hgk
      · exact Or.inl (ray2ga hga)
      · exact Or.inr (ray2gk hgk)


end Erdos634.Draft.LaczFormal.RG
