-- Draft/LaczFormalGraphWalk.lean -- D4 (global): the WALK of tiles along a side of the target.  `TriStep T d U U'`: the tile `T` has a side `U -> U'`
-- along `d` and lies on the left of `d`; `WalkL` is a chain of such steps.  Lemma 4.3(ii) of Laczkovich along the side of A, in the form
-- "a walk whose first tile has type pair (beta,gamma) or (gamma,beta) on the line consists of tiles with the same type pair", from the local translate
-- step `side_step` and the identification of the walk tiles with the end tiles of the side fans.  UNAUDITED.
-- Credit: Laczkovich (DCG 48 (2012), Lemma 4.3 and its proof by Fig. 3); Beeson (1206.2229, boundary walks).
import Erdos634.Draft.LaczFormalGraphSideStep
import Erdos634.Draft.LaczFormalGraphCorner
import Erdos634.TileAt

open Erdos634.Geometry

namespace Erdos634.Draft.LaczFormal.Graph

variable {N : ℕ}

/-- The tile `T` has a side from `U` to `U'` along `d` (positive multiple) and lies on the left of `d`. -/
def TriStep (T : Tri) (d : V2) (U U' : Plane) : Prop :=
  ∃ kk f g : Fin 3, T.pts kk = U ∧ T.pts f = U' ∧ f ≠ kk ∧ g ≠ kk ∧ g ≠ f ∧
    Par (toV2 (U' - U)) d ∧ 0 < crs d (toV2 (T.pts g - U))

theorem TriStep.of_eq {T : Tri} {d : V2} {U U₂ U' : Plane} (h : TriStep T d U U') (e : U = U₂) : TriStep T d U₂ U' := e ▸ h

theorem arm_cases (kk : Fin 3) (fl : Bool) (f : Fin 3) (h : f ≠ kk) : f = armP kk fl ∨ f = armQ kk fl := by
  rcases fin3_arm kk f h with h1 | h1 <;> cases fl <;> simp [armP, armQ, h1]

/-- If the tile's sector at `U` has its arms as vertex vectors and the tile has a left side along `d` from `U`, the sector starts along `d`. -/
theorem triStep_start {T : Tri} {d : V2} {U U' : Plane} (hS : TriStep T d U U') {p q : V2}
    (kk' : Fin 3) (fl : Bool) (hk' : T.pts kk' = U)
    (hp : p = toV2 (T.pts (armP kk' fl) - U)) (hq : q = toV2 (T.pts (armQ kk' fl) - U)) (hok : SecOK p q) :
    Par p d := by
  obtain ⟨kk, f, g, hk, hf, hfk, hgk, hgf, hpar, hleft⟩ := hS
  have hkk : kk = kk' := T.indep.injective (hk.trans hk'.symm)
  subst hkk
  rcases arm_cases kk fl f hfk with h | h
  · rw [hp, ← h, hf]; exact hpar
  · -- f is the q-arm; then g is the p-arm
    have hg : g = armP kk fl := by
      rcases arm_cases kk fl g hgk with h' | h'
      · exact h'
      · exact absurd (h'.trans h.symm) hgf
    exfalso
    have hqpar : Par q d := by rw [hq, ← h, hf]; exact hpar
    obtain ⟨c, hc, hcq⟩ := hqpar.smul
    have hpl : 0 < crs d p := by rw [hp, ← hg]; exact hleft
    have hcrs : crs p q = -(c * crs d p) := by
      rw [hcq]; unfold crs; ring
    rcases hok with h1 | ⟨h1, _⟩
    · nlinarith [mul_pos hc hpl]
    · nlinarith [mul_pos hc hpl]

/-- At the head `U'` of a left side the tile's sector ends along `-d`. -/
theorem triStep_end {T : Tri} {d : V2} {U U' : Plane} (hS : TriStep T d U U') {p q : V2}
    (kk' : Fin 3) (fl : Bool) (hk' : T.pts kk' = U')
    (hp : p = toV2 (T.pts (armP kk' fl) - U')) (hq : q = toV2 (T.pts (armQ kk' fl) - U')) (hok : SecOK p q) :
    Par q (-d.1, -d.2) := by
  obtain ⟨kk, f, g, hk, hf, hfk, hgk, hgf, hpar, hleft⟩ := hS
  have hff : f = kk' := T.indep.injective (hf.trans hk'.symm)
  subst hff
  obtain ⟨c, hc, hcw⟩ := hpar.smul
  have hd0 : d ≠ 0 := hpar.ne_right
  have ha1 : toV2 (T.pts kk - T.pts f) = (-(toV2 (U' - U)).1, -(toV2 (U' - U)).2) := by
    rw [← hk, ← hf]; unfold toV2; ext <;> simp
  have ha2 : toV2 (T.pts g - T.pts f) = ((toV2 (T.pts g - U)).1 - (toV2 (U' - U)).1,
      (toV2 (T.pts g - U)).2 - (toV2 (U' - U)).2) := by
    rw [← hf]; unfold toV2; ext <;> simp [← hk]
    all_goals ring
  have hl2 : 0 < crs d (toV2 (T.pts g - T.pts f)) := by
    rw [ha2, hcw]
    unfold crs at hleft ⊢
    simp only at hleft ⊢
    nlinarith [hleft]
  rw [← hf] at hp hq
  rcases arm_cases f fl kk hfk.symm with h1 | h1 <;> rcases arm_cases f fl g hgf with h2 | h2
  · exact absurd (h1.trans h2.symm) hgk.symm
  · -- kk = armP, g = armQ : p = a1, q = a2
    exfalso
    have hpq : crs p q = -(c * crs d (toV2 (T.pts g - T.pts f))) := by
      rw [hp, hq, ← h1, ← h2, ha1, hcw]
      unfold crs
      simp only
      ring
    rcases hok with h | ⟨h, _⟩
    · nlinarith [mul_pos hc hl2]
    · nlinarith [mul_pos hc hl2]
  · -- kk = armQ, g = armP : q = a1
    rw [hq, ← h1, ha1, hcw]
    apply smul_par hc (by intro h; apply hd0; have h1' : -d.1 = 0 := congrArg Prod.fst h; have h2' : -d.2 = 0 := congrArg Prod.snd h; exact Prod.ext (show d.1 = 0 by linarith) (show d.2 = 0 by linarith))
    ext <;> simp
  · exact absurd (h1.trans h2.symm) hgk.symm

/-! ## Start rays are distinct (the mirror of `end_inj`) -/

/-- Just after the start ray `p` of a sector one is in its open cone. -/
theorem plus_ray_int {p q : V2} (hs : SecOK p q) :
    ∃ δ > 0, ∀ ε : ℝ, 0 < ε → ε < δ → inInt p q (zplus p ε) := by
  have hp := nsq_pos hs.ne_p
  have e1 : ∀ ε, crs p (zplus p ε) = ε * nsq p := by
    intro ε; unfold crs zplus nsq; ring
  have e2 : ∀ ε, crs (zplus p ε) q = crs p q + ε * (-(dt p q)) := by
    intro ε; unfold crs dt zplus; ring
  rcases hs with h | ⟨h0, hd⟩
  · obtain ⟨δ, hδ, H⟩ := affine_pos_small (crs p q) (-(dt p q)) h
    refine ⟨δ, hδ, fun ε hε hεδ => ⟨?_, ?_⟩⟩
    · rw [e1]; positivity
    · rw [e2]; exact H ε hε hεδ
  · refine ⟨1, one_pos, fun ε hε _ => ⟨?_, ?_⟩⟩
    · rw [e1]; positivity
    · rw [e2, h0]; nlinarith

theorem start_inj {ι : Type*} (p q : ι → V2) (hok : ∀ s, SecOK (p s) (q s))
    (hdis : ∀ s t, s ≠ t → ∀ z, ¬ (inInt (p s) (q s) z ∧ inInt (p t) (q t) z)) {s t : ι} (hst : s ≠ t) :
    ¬ Par (p t) (p s) := by
  intro hpar
  obtain ⟨c, hc, hcq⟩ := hpar.smul
  obtain ⟨d1, hd1, H1⟩ := plus_ray_int (hok s)
  obtain ⟨d2, hd2, H2⟩ := plus_ray_int (hok t)
  set ε := min d1 d2 / 2 with hε
  have hεpos : 0 < ε := by have := lt_min hd1 hd2; positivity
  have hε1 : ε < d1 := by have := min_le_left d1 d2; linarith [lt_min hd1 hd2]
  have hε2 : ε < d2 := by have := min_le_right d1 d2; linarith [lt_min hd1 hd2]
  have h1 := H1 ε hεpos hε1
  have h2 := H2 ε hεpos hε2
  have hz : zplus (p t) ε = (c * (zplus (p s) ε).1, c * (zplus (p s) ε).2) := by
    rw [hcq]; unfold zplus; ext <;> simp <;> ring
  rw [hz] at h2
  exact hdis s t hst (zplus (p s) ε) ⟨h1, (inInt_smul_iff hc).mp h2⟩

/-- Same for end rays (restated for a family without `Fintype`). -/
theorem end_inj' {ι : Type*} (p q : ι → V2) (hok : ∀ s, SecOK (p s) (q s))
    (hdis : ∀ s t, s ≠ t → ∀ z, ¬ (inInt (p s) (q s) z ∧ inInt (p t) (q t) z)) {s t : ι} (hst : s ≠ t) :
    ¬ Par (q t) (q s) := by
  intro hpar
  obtain ⟨c, hc, hcq⟩ := hpar.smul
  obtain ⟨d1, hd1, H1⟩ := minus_ray_int (hok s)
  obtain ⟨d2, hd2, H2⟩ := minus_ray_int (hok t)
  set ε := min d1 d2 / 2 with hε
  have hεpos : 0 < ε := by have := lt_min hd1 hd2; positivity
  have hε1 : ε < d1 := by have := min_le_left d1 d2; linarith [lt_min hd1 hd2]
  have hε2 : ε < d2 := by have := min_le_right d1 d2; linarith [lt_min hd1 hd2]
  have h1 := H1 ε hεpos hε1
  have h2 := H2 ε hεpos hε2
  have hz : zminus (q t) ε = (c * (zminus (q s) ε).1, c * (zminus (q s) ε).2) := by
    rw [hcq]; unfold zminus; ext <;> simp <;> ring
  rw [hz] at h2
  exact hdis s t hst (zminus (q s) ε) ⟨h1, (inInt_smul_iff hc).mp h2⟩

theorem par_neg {u v : V2} (h : Par u v) : Par (-u.1, -u.2) (-v.1, -v.2) := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, ?_⟩
  · unfold crs at h1 ⊢; simp only; linarith
  · unfold dt at h2 ⊢; simp only; linarith

theorem par_not_secok {p q : V2} (h : SecOK p q) : ¬ Par q p := by
  rintro ⟨h1, h2⟩
  have e1 : crs q p = -crs p q := by unfold crs; ring
  have e2 : dt q p = dt p q := by unfold dt; ring
  rcases h with h | ⟨h0, h3⟩
  · linarith
  · linarith

/-- The tile with a left side along `d` starting at `V` is the first tile of the side fan. -/
theorem fan_start_unique {D : Dissection N} {V : Plane} {pT : V2} {p q : AtV D V → V2} {s1 s2 s3 : AtV D V}
    (hF : SideFan3 D V pT p q s1 s2 s3) {d : V2} (hd : Par pT d) {i : Fin N} {U' : Plane}
    (hS : TriStep (D.tile i) d V U') (hi : V ∈ (D.tile i).carrier) : (⟨i, hi⟩ : AtV D V) = s1 := by
  classical
  set s : AtV D V := ⟨i, hi⟩ with hs
  obtain ⟨kk, f, g, hk, -⟩ := id hS
  obtain ⟨kk', fl, hk', hp, hq⟩ := spec_corner_data (hF.spec s) ⟨kk, hk⟩
  have hstart : Par (p s) d := triStep_start hS kk' fl hk' hp hq (hF.ok s)
  have hdis := tiles_disjoint D V p q hF.loc
  have hsp : Par (p s) pT := hstart.trans hd.symm
  rcases hF.all s with h | h | h
  · exact h
  · exfalso
    rw [h] at hsp
    have h1 : Par (q s1) pT := hF.r2.symm.trans hsp
    exact par_not_secok (hF.ok s1) (h1.trans hF.r1.symm)
  · exfalso
    rw [h] at hsp
    exact start_inj p q hF.ok hdis hF.d13 (hsp.trans hF.r1.symm)

/-- The tile with a left side along `d` ending at `V` is the last tile of the side fan. -/
theorem fan_end_unique {D : Dissection N} {V : Plane} {pT : V2} {p q : AtV D V → V2} {s1 s2 s3 : AtV D V}
    (hF : SideFan3 D V pT p q s1 s2 s3) {d : V2} (hd : Par pT d) {i : Fin N} {U : Plane}
    (hS : TriStep (D.tile i) d U V) (hi : V ∈ (D.tile i).carrier) : (⟨i, hi⟩ : AtV D V) = s3 := by
  classical
  set s : AtV D V := ⟨i, hi⟩ with hs
  obtain ⟨kk, f, g, hk, hf, -⟩ := id hS
  obtain ⟨kk', fl, hk', hp, hq⟩ := spec_corner_data (hF.spec s) ⟨f, hf⟩
  have hend : Par (q s) (-d.1, -d.2) := triStep_end hS kk' fl hk' hp hq (hF.ok s)
  have hdis := tiles_disjoint D V p q hF.loc
  have hsq : Par (q s) (-pT.1, -pT.2) := hend.trans (par_neg hd).symm
  rcases hF.all s with h | h | h
  · exfalso
    rw [h] at hsq
    exact end_inj' p q hF.ok hdis (Ne.symm hF.d13) (hsq.trans hF.r4)
  · exfalso
    rw [h] at hsq
    exact end_inj' p q hF.ok hdis (Ne.symm hF.d23) (hsq.trans hF.r4)
  · exact h

/-! ## The side direction determines the fan direction -/

theorem convex_leftHalf (d : V2) (X0 : Plane) : Convex ℝ {y : Plane | 0 ≤ crs d (toV2 (y - X0))} := by
  intro x hx y hy a b ha hb hab
  simp only [Set.mem_setOf_eq] at hx hy ⊢
  unfold crs toV2 at *
  simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul] at hx hy ⊢
  have : a = 1 - b := by linarith
  subst this
  nlinarith [mul_nonneg ha hx, mul_nonneg hb hy]

theorem fin3_three (kk f g : Fin 3) (h1 : f ≠ kk) (h2 : g ≠ kk) (h3 : g ≠ f) (j : Fin 3) :
    j = kk ∨ j = f ∨ j = g := by
  revert kk f g j; decide

/-- A tile with a left side `X0 -> Y0` along `d` lies in the closed left half-plane of that side. -/
theorem triStep_left_half {T : Tri} {d : V2} {X0 Y0 : Plane} (hS : TriStep T d X0 Y0) :
    T.carrier ⊆ {y : Plane | 0 ≤ crs d (toV2 (y - X0))} := by
  obtain ⟨kk, f, g, hk, hf, hfk, hgk, hgf, hpar, hleft⟩ := hS
  obtain ⟨c, hc, hcw⟩ := hpar.smul
  have hv : ∀ j, T.pts j ∈ {y : Plane | 0 ≤ crs d (toV2 (y - X0))} := by
    intro j
    simp only [Set.mem_setOf_eq]
    rcases fin3_three kk f g hfk hgk hgf j with rfl | rfl | rfl
    · rw [hk]; unfold crs toV2; simp
    · rw [hf, hcw]; unfold crs; simp only; ring_nf; exact le_refl _
    · exact hleft.le
  exact convexHull_min (by rintro _ ⟨j, rfl⟩; exact hv j) (convex_leftHalf d X0)

/-- **The fan direction at a point of a left side is the side direction.** -/
theorem pT_par_d {T : Tri} {d : V2} {X0 Y0 : Plane} (hS : TriStep T d X0 Y0) {V : Plane}
    (hV : crs d (toV2 (V - X0)) = 0) {pT : V2} (hpT : pT ≠ 0)
    (hloc : LocalCone T V pT (-pT.1, -pT.2)) : Par pT d := by
  obtain ⟨r, hr, hiff⟩ := hloc
  have hd0 : d ≠ 0 := by obtain ⟨-, -, -, -, -, -, -, -, hpar, -⟩ := hS; exact hpar.ne_right
  have key : ∀ z : V2, 0 ≤ crs pT z → 0 ≤ crs d z := by
    intro z hz
    obtain ⟨ε, hε, hdist⟩ := exists_ptOf_small V z hr
    have h1 : ptOf V z ε ∈ T.carrier := by
      rw [hiff _ hdist, toV2_ptOf, inCone_straight_iff]
      unfold crs at hz ⊢; simp only; nlinarith [mul_nonneg hε.le hz]
    have h2 := triStep_left_half hS h1
    simp only [Set.mem_setOf_eq] at h2
    have h3 : toV2 (ptOf V z ε - X0) = ((toV2 (ptOf V z ε - V)).1 + (toV2 (V - X0)).1,
        (toV2 (ptOf V z ε - V)).2 + (toV2 (V - X0)).2) := by
      unfold toV2; ext <;> simp
    rw [h3, toV2_ptOf] at h2
    unfold crs at h2 hV ⊢
    simp only at h2 hV ⊢
    by_contra hcon
    push_neg at hcon
    nlinarith [mul_pos hε (neg_pos.mpr hcon)]
  have a1 := key pT (by unfold crs; ring_nf; exact le_refl _)
  have a2 := key (-pT.1, -pT.2) (by unfold crs; simp only; ring_nf; exact le_refl _)
  have hcr : crs pT d = 0 := by
    unfold crs at a1 a2 ⊢; simp only at a1 a2; linarith
  have a3 := key (-pT.2, pT.1) (by
    have := nsq_pos hpT
    unfold crs nsq at *; simp only; nlinarith)
  refine ⟨hcr, ?_⟩
  have hnn : 0 ≤ dt pT d := by unfold crs dt at *; simp only at a3 ⊢; nlinarith
  rcases hnn.eq_or_lt with h | h
  · exfalso; exact hpT (eq_zero_of_crs_dt hd0 hcr h.symm)
  · exact h

/-- `U` lies in the relative interior of the target side opposite vertex `m`. -/
def OnOpenSide (T : Tri) (m : Fin 3) (U : Plane) : Prop :=
  T.basis.coord m U = 0 ∧ ∀ j, j ≠ m → 0 < T.basis.coord j U

/-- **Normal side vertex without a differing inner ray**: three tiles, pairwise distinct types at `V`, and the first sides along the two inner
rays are both `a` or both not `a` (so no edge of `Γ_a` starts along an inner ray). -/
def SideNormal (D : CongruentDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) (V : Plane) : Prop :=
  Fintype.card (AtV D.toDissection V) = 3 ∧
  ∀ (pT : V2) (p q : AtV D.toDissection V → V2) (s1 s2 s3 : AtV D.toDissection V),
    SideFan3 D.toDissection V pT p q s1 s2 s3 →
    (∃ k, (D.tile s2.1).pts k = V) ∧
    (∀ k1 k2 k3, (D.tile s1.1).pts k1 = V → (D.tile s2.1).pts k2 = V → (D.tile s3.1).pts k3 = V →
      idx s1.1 k1 ≠ idx s2.1 k2 ∧ idx s1.1 k1 ≠ idx s3.1 k3 ∧ idx s2.1 k2 ≠ idx s3.1 k3) ∧
    (nsq (q s1) = slen D 0 ^ 2 ↔ nsq (p s2) = slen D 0 ^ 2) ∧
    (nsq (q s2) = slen D 0 ^ 2 ↔ nsq (p s3) = slen D 0 ^ 2)

/-- **Consecutive tiles of a walk (Lemma 4.3 translate step, real).**  Two tiles `i`, `i2` with left sides `U -> V` and `V -> U''` along `d` meeting at
the normal side vertex `V`: if the first has type pair `(β,γ)` or `(γ,β)` (types at `U`, `V`), the second has the same pair. -/
theorem consec_step (D : CongruentDissection N) (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    (hab : slen D 0 ≠ slen D 1) (hac : slen D 0 ≠ slen D 2)
    {m : Fin 3} {d : V2} {X0 Y0 : Plane} (hside : TriStep D.target d X0 Y0)
    {V : Plane} (hV : OnOpenSide D.target m V) (hVline : crs d (toV2 (V - X0)) = 0)
    (hSN : SideNormal D idx V)
    {i i2 : Fin N} {U U'' : Plane} (h1 : TriStep (D.tile i) d U V) (h2 : TriStep (D.tile i2) d V U'')
    (kR fR kL fL : Fin 3) (hR1 : (D.tile i2).pts kR = V) (hR2 : (D.tile i2).pts fR = U'')
    (hL1 : (D.tile i).pts kL = V) (hL2 : (D.tile i).pts fL = U)
    (hβγ : (idx i fL = 1 ∧ idx i kL = 2) ∨ (idx i fL = 2 ∧ idx i kL = 1)) :
    idx i2 kR = idx i fL ∧ idx i2 fR = idx i kL := by
  classical
  have hvert : ∃ j k, (D.tile j).pts k = V := ⟨i, kL, hL1⟩
  obtain ⟨pT, p, q, s1, s2, s3, hlocT, hF⟩ :=
    side_fan_three_struct D.toDissection V m hV.1 hV.2 hvert hSN.1
  have hpd : Par pT d := pT_par_d hside hVline hF.pT_ne hlocT
  have hi : V ∈ (D.tile i).carrier := hL1 ▸ subset_convexHull ℝ _ ⟨kL, rfl⟩
  have hi2 : V ∈ (D.tile i2).carrier := hR1 ▸ subset_convexHull ℝ _ ⟨kR, rfl⟩
  have e1 := fan_start_unique hF hpd h2 hi2
  have e3 := fan_end_unique hF hpd h1 hi
  obtain ⟨c2, hnorm, hno1, hno2⟩ := hSN.2 pT p q s1 s2 s3 hF
  have hR2' : Par (toV2 ((D.tile s1.1).pts fR - V)) pT := by
    rw [← e1]
    show Par (toV2 ((D.tile i2).pts fR - V)) pT
    rw [hR2]
    obtain ⟨-, -, -, -, -, -, -, -, hpar, -⟩ := h2
    exact hpar.trans hpd.symm
  have hL2' : Par (toV2 ((D.tile s3.1).pts fL - V)) (-pT.1, -pT.2) := by
    rw [← e3]
    show Par (toV2 ((D.tile i).pts fL - V)) (-pT.1, -pT.2)
    rw [hL2]
    obtain ⟨-, -, -, -, -, -, -, -, hpar, -⟩ := h1
    have hneg : toV2 (U - V) = (-(toV2 (V - U)).1, -(toV2 (V - U)).2) := by
      unfold toV2; ext <;> simp
    rw [hneg]
    exact (par_neg hpar).trans (par_neg hpd).symm
  have := side_step D idx hidx V hF c2 hab hac hnorm hno1 hno2 kR fR kL fL
    (by rw [← e1]; exact hR1) hR2' (by rw [← e3]; exact hL1) hL2' (by rw [← e3]; exact hβγ)
  rw [← e1, ← e3] at this
  exact this

/-! ## Walks along a side -/

/-- A chain of left steps along `d`, recorded as triples `(tile, tail, head)`. -/
inductive WalkT (D : Dissection N) (d : V2) : Plane → Plane → List (Fin N × Plane × Plane) → Prop
  | nil (X : Plane) : WalkT D d X X []
  | cons {i : Fin N} {X X' Y : Plane} {L : List (Fin N × Plane × Plane)} :
      TriStep (D.tile i) d X X' → WalkT D d X' Y L → WalkT D d X Y ((i, X, X') :: L)

/-- The type pair of a tile on a side `U -> U'`: types at the tail and at the head. -/
def PairIs (D : CongruentDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) (i : Fin N) (U U' : Plane) (ℓ : Fin 3 × Fin 3) : Prop :=
  ∀ k k', (D.tile i).pts k = U → (D.tile i).pts k' = U' → (idx i k, idx i k') = ℓ

theorem walkT_progress {D : Dissection N} {d : V2} {X Y : Plane} {L : List (Fin N × Plane × Plane)}
    (W : WalkT D d X Y L) : ∃ T : ℝ, 0 ≤ T ∧ toV2 (Y - X) = (T * d.1, T * d.2) ∧ (L ≠ [] → 0 < T) := by
  induction W with
  | nil X => exact ⟨0, le_rfl, by unfold toV2; ext <;> simp, fun h => absurd rfl h⟩
  | @cons i X X' Y L hS W ih =>
    obtain ⟨-, -, -, -, -, -, -, -, hpar, -⟩ := hS
    obtain ⟨c, hc, hcw⟩ := hpar.smul
    obtain ⟨T, hT, hTe, -⟩ := ih
    refine ⟨c + T, by positivity, ?_, fun _ => by positivity⟩
    have : toV2 (Y - X) = ((toV2 (Y - X')).1 + (toV2 (X' - X)).1, (toV2 (Y - X')).2 + (toV2 (X' - X)).2) := by
      unfold toV2; ext <;> simp
    rw [this, hTe, hcw]
    ext <;> simp <;> ring

theorem fin3_pair (kk f g : Fin 3) (h1 : f ≠ kk) (h2 : g ≠ kk) (h3 : g ≠ f) :
    (kk = g + 1 ∧ f = g + 2) ∨ (kk = g + 2 ∧ f = g + 1) := by
  revert kk f g; decide

theorem fin3_third (a b c m : Fin 3) (hab : b ≠ a) (hac : c ≠ a) (hbc : c ≠ b) (hmb : m ≠ b) (hmc : m ≠ c) : m = a := by
  revert a b c m; decide

/-- A point whose coordinates at two distinct indices vanish is the remaining vertex. -/
theorem eq_vertex_of_coords (T : Tri) {V : Plane} {a b c : Fin 3} (hab : b ≠ a) (hac : c ≠ a) (hbc : c ≠ b)
    (hb : T.basis.coord b V = 0) (hc : T.basis.coord c V = 0) : V = T.pts a := by
  obtain ⟨m, hm⟩ := T.eq_vertex_of_two_coords_zero hbc.symm hb hc
  have hcoord : ∀ i j : Fin 3, T.basis.coord i (T.pts j) = if i = j then 1 else 0 := by
    intro i j
    by_cases hij : i = j
    · subst hij; rw [if_pos rfl]; exact T.basis.coord_apply_eq i
    · rw [if_neg hij]; exact T.basis.coord_apply_ne hij
  have hmb : m ≠ b := by
    intro h; subst h; rw [hm, hcoord] at hb; simp at hb
  have hmc : m ≠ c := by
    intro h; subst h; rw [hm, hcoord] at hc; simp at hc
  rw [hm, fin3_third a b c m hab hac hbc hmb hmc]

/-- A line point of the closed side other than its endpoints lies in the relative interior of the side. -/
theorem open_side_of_triStep {T : Tri} {d : V2} {X0 Y0 : Plane} (hS : TriStep T d X0 Y0) {V : Plane}
    (hVT : V ∈ T.carrier) (hline : crs d (toV2 (V - X0)) = 0) (h1 : V ≠ X0) (h2 : V ≠ Y0) :
    ∃ m, OnOpenSide T m V := by
  obtain ⟨kk, f, g, hk, hf, hfk, hgk, hgf, hpar, hleft⟩ := hS
  obtain ⟨c, hc, hcw⟩ := hpar.smul
  have hdet : T.det ≠ 0 := T.det_ne_zero
  have hY : toV2 (Y0 - X0) = (c * d.1, c * d.2) := hcw
  have hY0 : Y0 0 - X0 0 = c * d.1 := by have := congrArg Prod.fst hY; simpa [toV2] using this
  have hY1 : Y0 1 - X0 1 = c * d.2 := by have := congrArg Prod.snd hY; simpa [toV2] using this
  have hg0 : T.basis.coord g V = 0 := by
    have hmain : T.basis.coord g V * T.det = cross (T.pts (g + 1 + 1) - T.pts (g + 1)) (V - T.pts (g + 1)) := by
      have := T.coord_mul_det (g + 1) V
      rw [fin3_e1] at this
      exact this
    rw [fin3_e2] at hmain
    have hcase := fin3_pair kk f g hfk hgk hgf
    have hz : cross (T.pts (g + 2) - T.pts (g + 1)) (V - T.pts (g + 1)) = 0 := by
      rcases hcase with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · rw [← e1, ← e2, hk, hf]
        rw [← crs_toV2]
        have e3 : toV2 (Y0 - X0) = (c * d.1, c * d.2) := hY
        rw [e3]
        unfold crs at hline ⊢; simp only at hline ⊢; nlinarith [hline]
      · rw [← e1, ← e2, hk, hf]
        rw [← crs_toV2]
        have e3 : toV2 (V - Y0) = ((toV2 (V - X0)).1 - c * d.1, (toV2 (V - X0)).2 - c * d.2) := by
          ext <;> simp [toV2] <;> linarith
        have e4 : toV2 (X0 - Y0) = (-(c * d.1), -(c * d.2)) := by
          ext <;> simp [toV2] <;> linarith
        rw [e3, e4]
        unfold crs at hline ⊢; simp only at hline ⊢; nlinarith [hline]
    rw [hz] at hmain
    exact (mul_eq_zero.mp hmain).resolve_right hdet
  refine ⟨g, hg0, ?_⟩
  have hnn : ∀ j, 0 ≤ T.basis.coord j V := by
    have := hVT; rw [T.carrier_eq_nonneg_coord] at this; exact this
  intro j hj
  rcases fin3_three kk f g hfk hgk hgf j with h | h | h
  · rw [h]
    apply lt_of_le_of_ne (hnn _)
    intro h0
    have := eq_vertex_of_coords T (V := V) (a := f) (b := kk) (c := g) hfk.symm hgf hgk h0.symm hg0
    exact h2 (by rw [this, hf])
  · rw [h]
    apply lt_of_le_of_ne (hnn _)
    intro h0
    have := eq_vertex_of_coords T (V := V) (a := kk) (b := f) (c := g) hfk hgk hgf h0.symm hg0
    exact h1 (by rw [this, hk])
  · exact absurd h hj

/-- **D4 (global): Lemma 4.3 (ii) along a side, real.**  Along a walk of left tiles from `X0` to `Y0` on a side of the target (with `X0 -> Y0` a left
side of the target tile along `d`), if every interior vertex of the walk is a normal side vertex with no differing inner ray (`SideNormal`), and
the first tile has type pair `(β,γ)` or `(γ,β)` on the line, then all tiles of the walk have that type pair. -/
theorem walk_pairs (D : CongruentDissection N) (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    (hab : slen D 0 ≠ slen D 1) (hac : slen D 0 ≠ slen D 2) {d : V2} {X0 Y0 : Plane}
    (hside : TriStep D.target d X0 Y0)
    (hnorm : ∀ V, V ≠ X0 → V ≠ Y0 → (∃ j k, (D.tile j).pts k = V) → crs d (toV2 (V - X0)) = 0 → SideNormal D idx V)
    (ℓ : Fin 3 × Fin 3) (hℓ : ℓ = (1, 2) ∨ ℓ = (2, 1)) {X Y : Plane} {L : List (Fin N × Plane × Plane)}
    (hYeq : Y = Y0) (W : WalkT D.toDissection d X Y L) :
    ∀ {e : Fin N × Plane × Plane} {L' : List (Fin N × Plane × Plane)}, L = e :: L' →
      (∃ t : ℝ, 0 ≤ t ∧ toV2 (X - X0) = (t * d.1, t * d.2)) →
      PairIs D idx e.1 e.2.1 e.2.2 ℓ → ∀ e' ∈ L, PairIs D idx e'.1 e'.2.1 e'.2.2 ℓ := by
  classical
  have hd0 : d ≠ 0 := by obtain ⟨-, -, -, -, -, -, -, -, hpar, -⟩ := hside; exact hpar.ne_right
  induction W with
  | nil X => intro e L' h; exact absurd h (by simp)
  | @cons i X X' Y L hS W' ih =>
    intro e L' hL hInv hPair e' he'
    simp only [List.cons.injEq] at hL
    obtain ⟨rfl, rfl⟩ := hL
    rcases List.mem_cons.mp he' with rfl | hmem
    · exact hPair
    · -- the tail walk is nonempty
      obtain ⟨t, ht, hXt⟩ := hInv
      obtain ⟨-, -, -, -, -, -, -, -, hpar, -⟩ := id hS
      obtain ⟨c, hc, hcw⟩ := hpar.smul
      have hX' : toV2 (X' - X0) = ((t + c) * d.1, (t + c) * d.2) := by
        have : toV2 (X' - X0) = ((toV2 (X' - X)).1 + (toV2 (X - X0)).1, (toV2 (X' - X)).2 + (toV2 (X - X0)).2) := by
          unfold toV2; ext <;> simp
        rw [this, hcw, hXt]; ext <;> simp <;> ring
      cases L with
      | nil => exact absurd hmem (by simp)
      | cons e2 L2 =>
        cases W' with
        | @cons i2 X2 X'' Y2 L3 hS2 W'' =>
          -- the junction vertex X'
          obtain ⟨T, hT, hTe, hTpos⟩ := walkT_progress (WalkT.cons hS2 W'')
          have hTp := hTpos (by simp)
          have hX'ne0 : X' ≠ X0 := by
            intro h
            rw [h] at hX'
            have h1 : (t + c) * d.1 = 0 := by have := congrArg Prod.fst hX'; simpa [toV2] using this.symm
            have h2 : (t + c) * d.2 = 0 := by have := congrArg Prod.snd hX'; simpa [toV2] using this.symm
            have : (t + c) ≠ 0 := by positivity
            exact hd0 (Prod.ext ((mul_eq_zero.mp h1).resolve_left this) ((mul_eq_zero.mp h2).resolve_left this))
          have hX'neY : X' ≠ Y0 := by
            intro h
            have hYX : Y = X' := hYeq.trans h.symm
            rw [hYX] at hTe
            have h1 : T * d.1 = 0 := by have := congrArg Prod.fst hTe; simpa [toV2] using this.symm
            have h2 : T * d.2 = 0 := by have := congrArg Prod.snd hTe; simpa [toV2] using this.symm
            exact hd0 (Prod.ext ((mul_eq_zero.mp h1).resolve_left hTp.ne') ((mul_eq_zero.mp h2).resolve_left hTp.ne'))
          obtain ⟨kkS, fS, gS, hkS, hfS, -⟩ := id hS
          obtain ⟨kk2, f2, g2, hk2, hf2, -⟩ := id hS2
          have hvert : ∃ j k, (D.tile j).pts k = X' := ⟨i, fS, hfS⟩
          have hmemT : X' ∈ D.target.carrier := by
            rw [← D.covers]
            exact Set.mem_iUnion.mpr ⟨i, hfS ▸ subset_convexHull ℝ _ ⟨fS, rfl⟩⟩
          have hline : crs d (toV2 (X' - X0)) = 0 := by
            rw [hX']; unfold crs; simp only; ring
          obtain ⟨m, hm⟩ := open_side_of_triStep hside hmemT hline hX'ne0 hX'neY
          have hSN := hnorm X' hX'ne0 hX'neY hvert hline
          -- pair of the second tile
          have hpair2 : PairIs D idx i2 X' X'' ℓ := by
            intro k k' hk hk'
            have e1 : k = kk2 := (D.tile i2).indep.injective (hk.trans hk2.symm)
            have e2' : k' = f2 := (D.tile i2).indep.injective (hk'.trans hf2.symm)
            have hP := hPair kkS fS hkS hfS
            have hβγ : (idx i kkS = 1 ∧ idx i fS = 2) ∨ (idx i kkS = 2 ∧ idx i fS = 1) := by
              rcases hℓ with rfl | rfl
              · left; simp [Prod.ext_iff] at hP; exact hP
              · right; simp [Prod.ext_iff] at hP; exact hP
            have hcs := consec_step D idx hidx hab hac hside hm hline hSN hS hS2 kk2 f2 fS kkS hk2 hf2 hfS hkS hβγ
            rw [e1, e2', hcs.1, hcs.2]
            exact hP
          have hInv' : ∃ t' : ℝ, 0 ≤ t' ∧ toV2 (X' - X0) = (t' * d.1, t' * d.2) := ⟨t + c, by positivity, hX'⟩
          exact ih hYeq rfl hInv' hpair2 e' hmem

/-! ## Existence of the walk -/

/-- A strictly convex corner sector whose clockwise ray points along `d` gives a left step. -/
theorem triStep_of_start {T : Tri} {d : V2} {U : Plane} (kk : Fin 3) (fl : Bool) (hk : T.pts kk = U) {p q : V2}
    (hp : p = toV2 (T.pts (armP kk fl) - U)) (hq : q = toV2 (T.pts (armQ kk fl) - U))
    (hcrs : 0 < crs p q) (hpar : Par p d) : TriStep T d U (T.pts (armP kk fl)) := by
  obtain ⟨c, hc, hcp⟩ := hpar.smul
  refine ⟨kk, armP kk fl, armQ kk fl, hk, rfl, armP_ne kk fl, armQ_ne kk fl, (armPQ_ne kk fl).symm, ?_, ?_⟩
  · rw [← hp]; exact hpar
  · have h1 : crs p q = c * crs d q := by rw [hcp]; unfold crs; ring
    rw [← hq]
    rw [h1] at hcrs
    exact (mul_pos_iff_of_pos_left hc).mp hcrs

theorem no_straight_of_sum {ι : Type*} [Fintype ι] (p q : ι → V2) (hok : ∀ s, SecOK (p s) (q s))
    {s t : ι} (hst : s ≠ t) (hs : wd (p s) (q s) = Real.pi) (hsum : ∑ x, wd (p x) (q x) ≤ Real.pi) : False := by
  classical
  have h1 : wd (p s) (q s) + wd (p t) (q t) ≤ ∑ x, wd (p x) (q x) := by
    have hpair : wd (p s) (q s) + wd (p t) (q t) = ∑ x ∈ ({s, t} : Finset ι), wd (p x) (q x) :=
      (Finset.sum_pair (f := fun x => wd (p x) (q x)) hst).symm
    rw [hpair]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun x _ _ => (wd_pos (hok x)).le)
  have := wd_pos (hok t)
  linarith

/-- **A target corner lying in a tile is a vertex of that tile.** -/
theorem target_corner_tile_vertex (D : Dissection N) (j : Fin 3) {i : Fin N}
    (hi : D.target.pts j ∈ (D.tile i).carrier) : ∃ k, (D.tile i).pts k = D.target.pts j := by
  rcases D.tile_angle_dichotomy_at_vertex j hi with ⟨k, hk, -⟩ | hpi
  · exact ⟨k, hk.symm⟩
  · exfalso
    obtain ⟨pT, qT, hokT, -, hwdT, hspecT⟩ := corner_sector D.target j
    have hcrs : 0 < crs pT qT := crs_pos_of_corner hokT hspecT ⟨j, rfl⟩
    have hlt : wd pT qT < Real.pi := by
      unfold wd
      rw [Complex.arg_lt_pi_iff]
      right
      simpa using hcrs.ne'
    have hsum := D.sum_localAngle_eq (D.target.pts j)
    have hle : (D.tile i).localAngle (D.target.pts j) ≤ ∑ i', (D.tile i').localAngle (D.target.pts j) :=
      Finset.single_le_sum (f := fun i' => (D.tile i').localAngle (D.target.pts j))
        (fun i' _ => (D.tile i').localAngle_nonneg _) (Finset.mem_univ i)
    rw [hsum, ← hwdT, hpi] at hle
    linarith

theorem target_corner_is_tile_vertex (D : Dissection N) (j : Fin 3) : ∃ i k, (D.tile i).pts k = D.target.pts j := by
  have hk : D.target.pts j ∈ D.target.carrier := subset_convexHull ℝ _ (Set.mem_range_self j)
  obtain ⟨i, hi⟩ := D.exists_tile_mem hk
  obtain ⟨k, hk'⟩ := target_corner_tile_vertex D j hi
  exact ⟨i, k, hk'⟩

/-- **A left step starts at every non-final vertex of the side:  open side vertex case.** -/
theorem step_exists_open (D : Dissection N) {d : V2} {X0 Y0 : Plane} (hside : TriStep D.target d X0 Y0)
    {m : Fin 3} {V : Plane} (hV : OnOpenSide D.target m V) (hVline : crs d (toV2 (V - X0)) = 0)
    (hvert : ∃ i k, (D.tile i).pts k = V) : ∃ i U', TriStep (D.tile i) d V U' := by
  classical
  obtain ⟨pT, p, q, e, hpT, hlocT, hok, hloc, hwd, hspec, hP, hper, hinj, hsurj⟩ :=
    vertex_fan_side D V m hV.1 hV.2 hvert
  have hpd : Par pT d := pT_par_d hside hVline hpT hlocT
  obtain ⟨j0, -, hnone⟩ := hsurj none
  have hP0 := hP j0
  rw [hnone] at hP0
  rcases hnext : e (j0 + 1) with _ | s
  · exfalso
    rw [hnext] at hP0
    simp only [extP, extQ] at hP0
    have := hP0.2
    have h2 := dt_straight_neg hpT
    unfold dt at this h2; simp only at this h2; linarith
  · rw [hnext] at hP0
    simp only [extP, extQ] at hP0
    have hsp : Par (p s) d := hP0.trans hpd
    -- s is a corner
    obtain ⟨i0, k0, hk0⟩ := hvert
    have hsum : ∑ x : AtV D V, wd (p x) (q x) ≤ Real.pi := by
      rw [tiles_angle_sum D V p q hwd, D.sum_localAngle_eq V, localAngle_of_edge_coords D.target m V hV.1 hV.2]
    have hcorner : ∃ k, (D.tile s.1).pts k = V := by
      rcases hspec s with ⟨k, hk, -⟩ | ⟨hnv, m', -, -, hq, -⟩
      · exact ⟨k, hk⟩
      · exfalso
        have ht : (⟨i0, hk0 ▸ subset_convexHull ℝ _ ⟨k0, rfl⟩⟩ : AtV D V) ≠ s := by
          intro h
          have := congrArg Subtype.val h
          simp only at this
          rw [this] at hk0
          exact hnv k0 hk0
        refine no_straight_of_sum p q hok (Ne.symm ht) ?_ hsum
        rw [hq]; exact wd_straight (hok s).ne_p
    obtain ⟨kk, fl, hk, hp', hq'⟩ := spec_corner_data (hspec s) hcorner
    have hcrs := crs_pos_of_corner (hok s) (hspec s) hcorner
    exact ⟨s.1, (D.tile s.1).pts (armP kk fl), triStep_of_start kk fl hk hp' hq' hcrs hsp⟩

/-- **A left step starts at the first corner of the side.** -/
theorem step_exists_corner (D : Dissection N) {d : V2} {X0 Y0 : Plane} (hside : TriStep D.target d X0 Y0) :
    ∃ i U', TriStep (D.tile i) d X0 U' := by
  classical
  obtain ⟨kk, f, g, hk, -⟩ := id hside
  have hvert := target_corner_is_tile_vertex D kk
  rw [hk] at hvert
  have hvert' : ∃ i k, (D.tile i).pts k = D.target.pts kk := by rw [hk]; exact hvert
  obtain ⟨pT, qT, p, q, e, hokT, hcrsT, hlocT, hwdT, hspecT, hok, hloc, hwd, hspec, hP, hper, hinj, hsurj⟩ :=
    vertex_fan_corner D kk hvert'
  -- the corner direction is `d`
  obtain ⟨kk', fl', hk', hpT', hqT'⟩ := spec_corner_data hspecT ⟨kk, rfl⟩
  have hpd : Par pT d := by
    have := triStep_start hside kk' fl' (by rw [hk', ← hk]) (by rw [hpT', hk]) (by rw [hqT', hk]) hokT
    exact this
  obtain ⟨j0, -, htrue⟩ := hsurj (Sum.inr true)
  have hP0 := hP j0
  rw [htrue] at hP0
  rcases hnext : e (j0 + 1) with s | b
  · rw [hnext] at hP0
    simp only [Sum.elim_inl, Sum.elim_inr] at hP0
    have hsp : Par (p s) d := hP0.trans hpd
    have hsum : ∑ x : AtV D (D.target.pts kk), wd (p x) (q x) ≤ Real.pi := by
      rw [tiles_angle_sum D _ p q hwd, D.sum_localAngle_eq _, ← hwdT]
      exact (by
        have hlt : wd pT qT < Real.pi := by
          unfold wd; rw [Complex.arg_lt_pi_iff]; right; simpa using hcrsT.ne'
        exact hlt.le)
    have hcorner : ∃ k, (D.tile s.1).pts k = D.target.pts kk :=
      target_corner_tile_vertex D kk s.2
    obtain ⟨kk2, fl2, hk2, hp2, hq2⟩ := spec_corner_data (hspec s) hcorner
    have hcrs := crs_pos_of_corner (hok s) (hspec s) hcorner
    have hstep := triStep_of_start (T := D.tile s.1) (d := d) kk2 fl2 hk2 hp2 hq2 hcrs hsp
    exact ⟨s.1, _, TriStep.of_eq hstep hk⟩
  · exfalso
    rw [hnext] at hP0
    simp only [Sum.elim_inl, Sum.elim_inr] at hP0
    have h0 := hP0.1
    cases b
    · simp only [Bool.false_eq_true, if_false, ite_true, if_true, ite_false] at h0
      unfold crs at h0 hcrsT; nlinarith
    · simp only [Bool.false_eq_true, if_false, ite_true, if_true, ite_false] at h0
      unfold crs at h0 hcrsT; nlinarith

theorem step_exists_corner_vertex (D : Dissection N) {d : V2} {X0 Y0 : Plane} (hside : TriStep D.target d X0 Y0) :
    ∃ j k, (D.tile j).pts k = X0 := by
  obtain ⟨kk, f, g, hk, -⟩ := id hside
  obtain ⟨j, k, h⟩ := target_corner_is_tile_vertex D kk
  exact ⟨j, k, h.trans hk⟩

/-- **The walk along a side exists**: from the first corner `X0` to the last corner `Y0`. -/
theorem side_walk_exists (D : Dissection N) {d : V2} {X0 Y0 : Plane} (hside : TriStep D.target d X0 Y0) :
    ∃ L, WalkT D d X0 Y0 L := by
  classical
  have hd0 : d ≠ 0 := by obtain ⟨-, -, -, -, -, -, -, -, hpar, -⟩ := hside; exact hpar.ne_right
  have hnd : 0 < nsq d := nsq_pos hd0
  set A : Finset Plane := (Finset.univ : Finset (Fin N × Fin 3)).image (fun p => (D.tile p.1).pts p.2) with hA
  have hAmem : ∀ U, (∃ j k, (D.tile j).pts k = U) → U ∈ A := by
    rintro U ⟨j, k, h⟩
    exact Finset.mem_image.mpr ⟨(j, k), Finset.mem_univ _, h⟩
  set F : Plane → Finset Plane := fun U => A.filter (fun v => dt d (toV2 (v - X0)) > dt d (toV2 (U - X0))) with hF
  have key : ∀ n : ℕ, ∀ U : Plane, (F U).card = n → (∃ j k, (D.tile j).pts k = U) →
      crs d (toV2 (U - X0)) = 0 → ∃ L, WalkT D d U Y0 L := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro U hcard hvert hline
      by_cases hUY : U = Y0
      · exact ⟨[], hUY ▸ WalkT.nil U⟩
      · -- a step exists
        have hstep : ∃ i U', TriStep (D.tile i) d U U' := by
          by_cases hUX : U = X0
          · rw [hUX]; exact step_exists_corner D hside
          · have hUT : U ∈ D.target.carrier := by
              obtain ⟨j, k, hjk⟩ := hvert
              rw [← D.covers]
              exact Set.mem_iUnion.mpr ⟨j, hjk ▸ subset_convexHull ℝ _ ⟨k, rfl⟩⟩
            obtain ⟨m, hm⟩ := open_side_of_triStep hside hUT hline hUX hUY
            exact step_exists_open D hside hm hline hvert
        obtain ⟨i, U', hS⟩ := hstep
        obtain ⟨kk, f, g, hk, hf, -, -, -, hpar, -⟩ := id hS
        obtain ⟨c, hc, hcw⟩ := hpar.smul
        have hdec : toV2 (U' - X0) = ((toV2 (U' - U)).1 + (toV2 (U - X0)).1, (toV2 (U' - U)).2 + (toV2 (U - X0)).2) := by
          unfold toV2; ext <;> simp
        have hline' : crs d (toV2 (U' - X0)) = 0 := by
          rw [hdec, hcw]
          unfold crs at hline ⊢; simp only at hline ⊢; nlinarith [hline]
        have hdt : dt d (toV2 (U' - X0)) > dt d (toV2 (U - X0)) := by
          rw [hdec, hcw]
          unfold dt nsq at *; simp only; nlinarith [mul_pos hc hnd]
        have hvert' : ∃ j k, (D.tile j).pts k = U' := ⟨i, f, hf⟩
        have hsub : F U' ⊂ F U := by
          refine ⟨?_, ?_⟩
          · intro v hv
            simp only [hF, Finset.mem_filter] at hv ⊢
            exact ⟨hv.1, lt_trans hdt hv.2⟩
          · intro hsub
            have hU'mem : U' ∈ F U := by
              simp only [hF, Finset.mem_filter]
              exact ⟨hAmem U' hvert', hdt⟩
            have := hsub hU'mem
            simp only [hF, Finset.mem_filter] at this
            exact lt_irrefl _ this.2
        have hlt : (F U').card < n := hcard ▸ Finset.card_lt_card hsub
        obtain ⟨L, hL⟩ := ih (F U').card hlt U' rfl hvert' hline'
        exact ⟨(i, U, U') :: L, WalkT.cons hS hL⟩
  obtain ⟨j, k, hjk⟩ := step_exists_corner_vertex D hside
  exact key _ X0 rfl ⟨j, k, hjk⟩ (by unfold crs toV2; simp)

/-! ## Lengths along a walk; the final D4 statement -/

theorem dist_of_toV2 {x y : Plane} {c : ℝ} (hc : 0 ≤ c) {d : V2} (h : toV2 (y - x) = (c * d.1, c * d.2)) :
    dist y x = c * Real.sqrt (nsq d) := by
  have h1 : dist y x ^ 2 = (c * Real.sqrt (nsq d)) ^ 2 := by
    rw [← nsq_toV2_sub, h, mul_pow, Real.sq_sqrt (nsq_nonneg d)]
    unfold nsq; simp only; ring
  exact (pow_left_inj₀ dist_nonneg (mul_nonneg hc (Real.sqrt_nonneg _)) two_ne_zero).mp h1

theorem walkT_dist_sum {D : Dissection N} {d : V2} {X Y : Plane} {L : List (Fin N × Plane × Plane)}
    (W : WalkT D d X Y L) : (L.map fun e => dist e.2.1 e.2.2).sum = dist X Y := by
  induction W with
  | nil X => simp
  | @cons i X X' Y L hS W ih =>
    obtain ⟨-, -, -, -, -, -, -, -, hpar, -⟩ := id hS
    obtain ⟨c, hc, hcw⟩ := hpar.smul
    obtain ⟨T, hT, hTe, -⟩ := walkT_progress W
    have hXY : toV2 (Y - X) = ((c + T) * d.1, (c + T) * d.2) := by
      have : toV2 (Y - X) = ((toV2 (Y - X')).1 + (toV2 (X' - X)).1, (toV2 (Y - X')).2 + (toV2 (X' - X)).2) := by
        unfold toV2; ext <;> simp
      rw [this, hTe, hcw]; ext <;> simp <;> ring
    have d1 := dist_of_toV2 hc.le hcw
    have d2 := dist_of_toV2 hT hTe
    have d3 := dist_of_toV2 (by positivity : 0 ≤ c + T) hXY
    simp only [List.map_cons, List.sum_cons]
    rw [ih, dist_comm X X', d1, dist_comm X' Y, d2, dist_comm X Y, d3]
    ring

/-- A tile with a left step `U -> U'` of type pair `(β,γ)` or `(γ,β)` has that side of length `a`. -/
theorem step_len_a (D : CongruentDissection N) (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    {i : Fin N} {U U' : Plane} {d : V2} (hS : TriStep (D.tile i) d U U') {ℓ : Fin 3 × Fin 3}
    (hℓ : ℓ = (1, 2) ∨ ℓ = (2, 1)) (hP : PairIs D idx i U U' ℓ) : dist U U' = slen D 0 := by
  obtain ⟨kk, f, g, hk, hf, -⟩ := id hS
  have := hP kk f hk hf
  rw [← hk, ← hf, hidx]
  unfold slen
  rcases hℓ with rfl | rfl
  · simp only [Prod.ext_iff] at this
    rw [this.1, this.2]; rfl
  · simp only [Prod.ext_iff] at this
    rw [this.1, this.2, dist_comm]; rfl

theorem walkT_mem_step {D : Dissection N} {d : V2} {X Y : Plane} {L : List (Fin N × Plane × Plane)}
    (W : WalkT D d X Y L) : ∀ e ∈ L, TriStep (D.tile e.1) d e.2.1 e.2.2 := by
  induction W with
  | nil X => intro e he; exact absurd he (by simp)
  | @cons i X X' Y L hS W ih =>
    intro e he
    rcases List.mem_cons.mp he with rfl | h
    · exact hS
    · exact ih e h

/-- **D4, Lemma 4.3 (ii) of Laczkovich along a side of the target: real statement.**  Let `X0 -> Y0` be a left side of the target along `d` and suppose every
interior tiling vertex on the open side is a normal side vertex with no differing inner ray (`SideNormal`).  Then there is a walk of tiles
`T_1, .., T_k` along the side (first tile `T_1` at `X0`), and if `T_1` has the type pair `(β,γ)` or `(γ,β)` on the side, then every tile of the walk has that same
pair, and `|X0 Y0| = k * a`. -/
theorem lemma43_ii (D : CongruentDissection N) (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    (hab : slen D 0 ≠ slen D 1) (hac : slen D 0 ≠ slen D 2) {d : V2} {X0 Y0 : Plane}
    (hside : TriStep D.target d X0 Y0)
    (hnorm : ∀ V, V ≠ X0 → V ≠ Y0 → (∃ j k, (D.tile j).pts k = V) → crs d (toV2 (V - X0)) = 0 → SideNormal D idx V)
    (ℓ : Fin 3 × Fin 3) (hℓ : ℓ = (1, 2) ∨ ℓ = (2, 1)) :
    ∃ L : List (Fin N × Plane × Plane), WalkT D.toDissection d X0 Y0 L ∧ L ≠ [] ∧
      ∀ e L', L = e :: L' → PairIs D idx e.1 e.2.1 e.2.2 ℓ →
        (∀ e' ∈ L, PairIs D idx e'.1 e'.2.1 e'.2.2 ℓ) ∧ dist X0 Y0 = L.length * slen D 0 := by
  obtain ⟨L, hL⟩ := side_walk_exists D.toDissection hside
  refine ⟨L, hL, ?_, ?_⟩
  · rintro rfl
    obtain ⟨-, -, -, -, -, -, -, -, hpar, -⟩ := id hside
    have : X0 = Y0 := by cases hL; rfl
    rw [this] at hpar
    have := hpar.2
    unfold dt toV2 at this; simp at this
  · intro e L' hLe hPe
    have hInv : ∃ t : ℝ, 0 ≤ t ∧ toV2 (X0 - X0) = (t * d.1, t * d.2) := ⟨0, le_rfl, by unfold toV2; ext <;> simp⟩
    have hall := walk_pairs D idx hidx hab hac hside hnorm ℓ hℓ rfl hL hLe hInv hPe
    refine ⟨hall, ?_⟩
    rw [← walkT_dist_sum hL]
    -- every tile has side length a
    have hlen : ∀ e' ∈ L, dist e'.2.1 e'.2.2 = slen D 0 := fun e' he' =>
      step_len_a D idx hidx (walkT_mem_step hL e' he') hℓ (hall e' he')
    have hsum : (L.map fun e => dist e.2.1 e.2.2).sum = (L.map fun e => dist e.2.1 e.2.2).length • slen D 0 := by
      apply List.sum_eq_card_nsmul
      intro x hx
      obtain ⟨e', he', rfl⟩ := List.mem_map.mp hx
      exact hlen e' he'
    rw [hsum, List.length_map, nsmul_eq_mul]

end Erdos634.Draft.LaczFormal.Graph

#print axioms Erdos634.Draft.LaczFormal.Graph.lemma43_ii
#print axioms Erdos634.Draft.LaczFormal.Graph.side_walk_exists
#print axioms Erdos634.Draft.LaczFormal.Graph.walk_pairs
