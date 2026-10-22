-- Draft/LaczFormalRGHeadFan.lean -- S3 of PLAN_THM21: port of LaczFormalGraphHeadFan to `RegionDissection` (dissection-dependent declarations only; the rest is used
-- from the original module).  UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 4), Beeson, Beeson-Zhang; port of the project's LaczFormalGraphHeadFan.
import Erdos634.Draft.LaczFormalRGHead
import Erdos634.Draft.LaczFormalGraphHeadFan

open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph

namespace Erdos634.Draft.LaczFormal.RG

variable {N : ℕ}


namespace ExtFan

variable {D : RegionDissection N} {V : Plane} {κ : Type} [Fintype κ]

/-- **No ray along `-d` among the tile sectors implies `NoBack`.** -/
theorem noBack_of_none (F : ExtFan D V κ) {d : V2}
    (hnone : ∀ s : AtV D V, ¬ Par (F.p s) (neg2 d) ∧ ¬ Par (F.q s) (neg2 d)) : NoBack D d V := by
  classical
  constructor
  · intro i A B σ hS h0 h1 hV
    obtain ⟨kk, f, g, hk, hf, hfk, hgk, hgf, hpar, hleft⟩ := id hS
    by_cases hσ : σ = 1
    · -- V = B, the head: the tile has an arm along -d at V
      subst hσ
      have hVB : V = B := by rw [hV]; simp
      have hmem : V ∈ (D.tile i).carrier := by rw [hVB, ← hf]; exact subset_convexHull ℝ _ ⟨f, rfl⟩
      set s : AtV D V := ⟨i, hmem⟩
      obtain ⟨kk', fl', hk', hp, hq⟩ := spec_corner_data (F.hspec s) ⟨f, by rw [hf, hVB]⟩
      have hS' : TriStep (D.tile i) d A V := by rw [hVB]; exact hS
      have := triStep_end hS' kk' fl' hk' hp hq (F.hok s)
      exact (hnone s).2 this
    · have hσ1 : σ < 1 := lt_of_le_of_ne h1 hσ
      obtain ⟨hmemV, hnv, hline⟩ := step_interior_pt hS h0 hσ1
      rw [← hV] at hmemV hnv hline
      set s : AtV D V := ⟨i, hmemV⟩
      obtain ⟨hpar', hq⟩ := straight_dir s (F.hok s) (F.hloc s) (F.hspec s) hnv hS hline
      refine (hnone s).2 ?_
      rw [hq]
      have := par_neg hpar'
      exact this
  · intro i A B σ hS h0 h1 hV
    obtain ⟨kk, f, g, hk, hf, hfk, hgk, hgf, hpar, hleft⟩ := id hS
    by_cases hσ : σ = 1
    · -- V = A, the tail: the tile has an arm along -d at V
      subst hσ
      have hVA : V = A := by rw [hV]; simp
      have hmem : V ∈ (D.tile i).carrier := by rw [hVA, ← hk]; exact subset_convexHull ℝ _ ⟨kk, rfl⟩
      set s : AtV D V := ⟨i, hmem⟩
      obtain ⟨kk', fl', hk', hp, hq⟩ := spec_corner_data (F.hspec s) ⟨kk, by rw [hk, hVA]⟩
      have hS' : TriStep (D.tile i) (neg2 d) V B := by rw [hVA]; exact hS
      have := triStep_start hS' kk' fl' hk' hp hq (F.hok s)
      exact (hnone s).1 this
    · have hσ1 : σ < 1 := lt_of_le_of_ne h1 hσ
      -- V = B + σ • (A - B) = A + (1 - σ) • (B - A)
      have hV' : V = A + (1 - σ) • (B - A) := by rw [hV]; ext i; simp; ring
      obtain ⟨hmemV, hnv, hline⟩ := step_interior_pt hS (by linarith : 0 < 1 - σ) (by linarith : 1 - σ < 1)
      rw [← hV'] at hmemV hnv hline
      set s : AtV D V := ⟨i, hmemV⟩
      obtain ⟨hpar', hq⟩ := straight_dir s (F.hok s) (F.hloc s) (F.hspec s) hnv hS hline
      exact (hnone s).1 hpar'


/-- A straight tile sector together with a tile sector reaching the other side forces `Tgt = univ`. -/
theorem tgt_univ_of_straight (F : ExtFan D V κ) (s t : AtV D V)
    (hs : F.q s = (-(F.p s).1, -(F.p s).2)) {z0 : V2} (hz0 : inInt (F.p t) (F.q t) z0)
    (hz0' : crs (F.p s) z0 < 0) : ∀ z : V2, z ∈ F.Tgt := by
  have hHs : ∀ z : V2, 0 ≤ crs (F.p s) z → z ∈ F.Tgt := by
    intro z hz
    apply F.tile_cone_sub s
    rw [hs]
    exact (inCone_straight_iff _ _).mpr hz
  have hz0T : z0 ∈ F.Tgt := F.tile_cone_sub t ⟨hz0.1.le, hz0.2.le⟩
  intro z
  by_cases hz : 0 ≤ crs (F.p s) z
  · exact hHs z hz
  · push_neg at hz
    set lam : ℝ := crs (F.p s) z / crs (F.p s) z0 with hlam
    have hlam0 : 0 < lam := div_pos_of_neg_of_neg hz hz0'
    set r : V2 := (z.1 - lam * z0.1, z.2 - lam * z0.2) with hr
    have hcr : crs (F.p s) r = 0 := by
      have : crs (F.p s) r = crs (F.p s) z - lam * crs (F.p s) z0 := by
        unfold crs; simp only [hr]; ring
      have h2 : lam * crs (F.p s) z0 = crs (F.p s) z := by rw [hlam]; exact div_mul_cancel₀ _ hz0'.ne
      rw [this, h2]; ring
    have hrT : r ∈ F.Tgt := hHs r (by rw [hcr])
    have hw := F.hTc z0 hz0T r hrT (lam / (lam + 1)) (1 / (lam + 1)) (by positivity) (by positivity) (by field_simp)
    have hz' := F.hTs _ hw (lam + 1) (by positivity)
    have e : ((lam + 1) * (lam / (lam + 1) * z0.1 + 1 / (lam + 1) * r.1),
        (lam + 1) * (lam / (lam + 1) * z0.2 + 1 / (lam + 1) * r.2)) = z := by
      ext <;> simp only [hr] <;> field_simp <;> ring
    rw [e] at hz'
    exact hz'


theorem isEmpty_of_univ (F : ExtFan D V κ) (h : ∀ z : V2, z ∈ F.Tgt) : IsEmpty κ := by
  constructor
  intro j
  obtain ⟨δ, hδ, H⟩ := minus_ray_int (F.hokE j)
  exact F.hextT j _ (H (δ / 2) (by positivity) (by linarith)) (h _)


theorem interior_of_univ (F : ExtFan D V κ) (h : ∀ z : V2, z ∈ F.Tgt) : V ∈ interior D.region := by
  apply interior_maximal (t := Metric.ball V F.R)
  · intro y hy
    exact (F.hT y (by simpa [Metric.mem_ball] using hy)).mpr (h _)
  · exact Metric.isOpen_ball
  · exact Metric.mem_ball_self F.hR


/-- **The fan at a head.**  Sectors: `a` (a left corner ending along `-d`), `b` (a corner starting along `d`) and `s` (a straight sector, clockwise ray along `-d`).  Then there are no
virtual sectors, `H` is interior to the target, and cyclically `s` is followed by `b` and preceded by `a`. -/
theorem head_cyc (F : ExtFan D V κ) {d : V2} (a b s : AtV D V)
    (hca : 0 < crs (F.p a) (F.q a)) (hqa : Par (F.q a) (neg2 d))
    (hcb : 0 < crs (F.p b) (F.q b)) (hpb : Par (F.p b) d)
    (hps : Par (F.p s) (neg2 d)) (hqs : F.q s = (-(F.p s).1, -(F.p s).2)) :
    IsEmpty κ ∧ V ∈ interior D.region ∧ a ≠ s ∧ b ≠ s ∧ a ≠ b ∧
      ∃ j0 < Fintype.card (AtV D V ⊕ κ), F.e j0 = Sum.inl s ∧ F.e (j0 + 1) = Sum.inl b ∧
        F.e (j0 + (Fintype.card (AtV D V ⊕ κ) - 1)) = Sum.inl a := by
  classical
  -- a point of the open cone of `a`, strictly left of `d`
  obtain ⟨δa, hδa, Ha⟩ := minus_ray_int (F.hok a)
  set zA := zminus (F.q a) (δa / 2) with hzA
  have hzAint : inInt (F.p a) (F.q a) zA := Ha _ (by positivity) (by linarith)
  have hzA_left : 0 < crs d zA := by
    obtain ⟨c', hc', hq'⟩ := hqa.smul
    have h := hzAint.2
    rw [hq'] at h
    by_contra hX; push_neg at hX
    unfold crs at h hX
    unfold neg2 at h
    try simp only at h hX
    nlinarith [mul_nonneg hc'.le (neg_nonneg.mpr hX)]
  have hz0' : crs (F.p s) zA < 0 := by
    obtain ⟨c1, hc1, hp1⟩ := hps.smul
    rw [hp1]
    unfold crs at hzA_left ⊢
    unfold neg2
    try simp only at hzA_left ⊢
    nlinarith [mul_pos hc1 hzA_left]
  have huniv := F.tgt_univ_of_straight s a hqs hzAint hz0'
  have hemp := F.isEmpty_of_univ huniv
  have hint := F.interior_of_univ huniv
  have hdis := tiles_disjoint D V F.p F.q F.hloc
  -- a ≠ s, b ≠ s (corner vs straight), a ≠ b
  have hcs : crs (F.p s) (F.q s) = 0 := by rw [hqs]; exact crs_straight _
  have has : a ≠ s := by rintro rfl; linarith
  have hbs : b ≠ s := by rintro rfl; linarith
  have hab : a ≠ b := by
    rintro rfl
    -- a sector starting along d and ending along -d would be straight
    obtain ⟨c1, hc1, hp1⟩ := hpb.smul
    obtain ⟨c2, hc2, hq2⟩ := hqa.smul
    have : crs (F.p a) (F.q a) = 0 := by
      rw [hp1, hq2]; unfold crs neg2; ring
    linarith
  refine ⟨hemp, hint, has, hbs, hab, ?_⟩
  obtain ⟨j0, hj0, hej0⟩ := F.hsurj (Sum.inl s)
  have hP0 := F.hP j0
  rw [hej0] at hP0
  simp only [Sum.elim_inl] at hP0
  rw [hqs] at hP0
  have hsucc : Par (Sum.elim F.p F.pe (F.e (j0 + 1))) d := hP0.trans (by
    have := par_neg hps
    rw [neg2_neg2] at this
    exact this)
  have hnext : F.e (j0 + 1) = Sum.inl b := by
    rcases hn : F.e (j0 + 1) with c | j
    · rw [hn] at hsucc
      simp only [Sum.elim_inl] at hsucc
      by_contra hne
      have hcb' : c ≠ b := by intro h; apply hne; rw [h]
      exact start_inj F.p F.q F.hok hdis (Ne.symm hcb') (hsucc.trans hpb.symm)
    · exact (hemp.false j).elim
  have hkpos : 0 < Fintype.card (AtV D V ⊕ κ) := lt_of_le_of_lt (Nat.zero_le _) hj0
  have hP1 := F.hP (j0 + (Fintype.card (AtV D V ⊕ κ) - 1))
  have hshift : j0 + (Fintype.card (AtV D V ⊕ κ) - 1) + 1 = j0 + Fintype.card (AtV D V ⊕ κ) := by omega
  rw [hshift, F.hper j0, hej0] at hP1
  simp only [Sum.elim_inl] at hP1
  have hpred : Par (Sum.elim F.q F.qe (F.e (j0 + (Fintype.card (AtV D V ⊕ κ) - 1)))) (neg2 d) := hP1.symm.trans hps
  have hprev : F.e (j0 + (Fintype.card (AtV D V ⊕ κ) - 1)) = Sum.inl a := by
    rcases hn : F.e (j0 + (Fintype.card (AtV D V ⊕ κ) - 1)) with c | j
    · rw [hn] at hpred
      simp only [Sum.elim_inl] at hpred
      by_contra hne
      have hca : c ≠ a := by intro h; apply hne; rw [h]
      exact end_inj' F.p F.q F.hok hdis (Ne.symm hca) (hpred.trans hqa.symm)
    · exact (hemp.false j).elim
  exact ⟨j0, hj0, hej0, hnext, hprev⟩


end ExtFan

/-- **Head sectors (left case)**: the sectors of the fan `F` at the head `H` of a left-case edge. -/
theorem ga_head_sectors_left (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    (hnc : NotComb (slen D 0) (slen D 1) (slen D 2)) {d : V2} (hd : d ≠ 0) {X Y H : Plane}
    {L1 L2 : List (Fin N × Plane × Plane)} (W1 : WalkT D.toRegionDissection d X Y L1) (W2 : WalkR D.toRegionDissection d X Y L2)
    (hRun : RunEnd (slen D 0) L1 H) (hR2 : ∀ e ∈ L2.head?, dist e.2.1 e.2.2 ≠ slen D 0)
    {κ : Type} [Fintype κ] (F : ExtFan D.toRegionDissection H κ) :
    ∃ a b s : AtV D.toRegionDissection H,
      0 < crs (F.p a) (F.q a) ∧ Par (F.q a) (neg2 d) ∧ 0 < crs (F.p b) (F.q b) ∧ Par (F.p b) d ∧
      Par (F.p s) (neg2 d) ∧ F.q s = (-(F.p s).1, -(F.p s).2) ∧
      nsq (F.q a) = slen D 0 ^ 2 ∧ nsq (F.p b) ≠ slen D 0 ^ 2 ∧ H ≠ X := by
  classical
  obtain ⟨iA, HA, iB, HB, iS, V, V', σ, hSA, hdA, hSB, hdB, hSS, hσ0, hσ1, hHV, hHX⟩ :=
    ga_head_left D idx hidx hnc hd W1 W2 hRun hR2
  have hmemA : H ∈ (D.tile iA).carrier := by
    obtain ⟨kk, f, g, hk, hf, -⟩ := id hSA
    rw [← hf]; exact subset_convexHull ℝ _ ⟨f, rfl⟩
  have hmemB : H ∈ (D.tile iB).carrier := by
    obtain ⟨kk, f, g, hk, hf, -⟩ := id hSB
    rw [← hk]; exact subset_convexHull ℝ _ ⟨kk, rfl⟩
  obtain ⟨hmemS, hnvS, hlineS⟩ := step_interior_pt hSS (σ := 1 - σ) (by linarith) (by linarith)
  have hHS : V' + (1 - σ) • (V - V') = H := by rw [hHV]; ext i; simp; ring
  rw [hHS] at hmemS hnvS hlineS
  set a : AtV D.toRegionDissection H := ⟨iA, hmemA⟩
  set b : AtV D.toRegionDissection H := ⟨iB, hmemB⟩
  set s : AtV D.toRegionDissection H := ⟨iS, hmemS⟩
  refine ⟨a, b, s, ?_⟩
  -- A
  obtain ⟨kkA, fA, gA, hkA, hfA, hfkA, hgkA, hgfA, hparA, hleftA⟩ := id hSA
  obtain ⟨kk', fl', hk', hp, hq⟩ := spec_corner_data (F.hspec a) ⟨fA, hfA⟩
  have hqa : Par (F.q a) (neg2 d) := triStep_end hSA kk' fl' hk' hp hq (F.hok a)
  have hca : 0 < crs (F.p a) (F.q a) := crs_pos_of_corner (F.hok a) (F.hspec a) ⟨kk', hk'⟩
  have hkkA : kk' = fA := (D.tile iA).indep.injective (hk'.trans hfA.symm)
  have hnA : nsq (F.q a) = slen D 0 ^ 2 := by
    have hq' : Par (toV2 ((D.tile iA).pts (armQ kk' fl') - H)) (neg2 d) := hq ▸ hqa
    have hHA : Par (toV2 (HA - H)) (neg2 d) := par_neg_arm hparA
    have := qarm_eq (T := D.tile iA) fl' hk' (W := HA) (w := kkA) hkA (by rw [hkkA]; exact hfkA.symm) hq' hHA
    rw [hq, nsq_toV2_sub, this, hdA]
  -- B
  obtain ⟨kkB, fB, gB, hkB, hfB, hfkB, hgkB, hgfB, hparB, hleftB⟩ := id hSB
  obtain ⟨kk2, fl2, hk2, hp2, hq2⟩ := spec_corner_data (F.hspec b) ⟨kkB, hkB⟩
  have hpb : Par (F.p b) d := triStep_start hSB kk2 fl2 hk2 hp2 hq2 (F.hok b)
  have hcb : 0 < crs (F.p b) (F.q b) := crs_pos_of_corner (F.hok b) (F.hspec b) ⟨kk2, hk2⟩
  have hkkB : kk2 = kkB := (D.tile iB).indep.injective (hk2.trans hkB.symm)
  have hnB : nsq (F.p b) ≠ slen D 0 ^ 2 := by
    have hp' : Par (toV2 ((D.tile iB).pts (armP kk2 fl2) - H)) d := hp2 ▸ hpb
    have := parm_eq (T := D.tile iB) fl2 hk2 (W := HB) (w := fB) hfB (by rw [hkkB]; exact hfkB) hp' hparB
    rw [hp2, nsq_toV2_sub, this, dist_comm]
    exact sq_ne_of_ne dist_nonneg (slen_pos D 0).le hdB
  -- S
  obtain ⟨hpS, hqS⟩ := straight_dir s (F.hok s) (F.hloc s) (F.hspec s) hnvS hSS hlineS
  exact ⟨hca, hqa, hcb, hpb, hpS, hqS, hnA, hnB, hHX⟩


/-- **Head sectors (right case)**. -/
theorem ga_head_sectors_right (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    (hnc : NotComb (slen D 0) (slen D 1) (slen D 2)) {d : V2} (hd : d ≠ 0) {X Y H : Plane}
    {L1 L2 : List (Fin N × Plane × Plane)} (W1 : WalkT D.toRegionDissection d X Y L1) (W2 : WalkR D.toRegionDissection d X Y L2)
    (hRun : RunEnd (slen D 0) L2 H) (hL1 : ∀ e ∈ L1.head?, dist e.2.1 e.2.2 ≠ slen D 0)
    {κ : Type} [Fintype κ] (F : ExtFan D.toRegionDissection H κ) :
    ∃ a b s : AtV D.toRegionDissection H,
      0 < crs (F.p a) (F.q a) ∧ Par (F.p a) (neg2 d) ∧ 0 < crs (F.p b) (F.q b) ∧ Par (F.q b) d ∧
      Par (F.p s) d ∧ F.q s = (-(F.p s).1, -(F.p s).2) ∧
      nsq (F.p a) = slen D 0 ^ 2 ∧ nsq (F.q b) ≠ slen D 0 ^ 2 ∧ H ≠ X := by
  classical
  obtain ⟨iA, HA, iB, HB, iS, V, V', σ, hSA, hdA, hSB, hdB, hSS, hσ0, hσ1, hHV, hHX⟩ :=
    ga_head_right D idx hidx hnc hd W1 W2 hRun hL1
  have hmemA : H ∈ (D.tile iA).carrier := by
    obtain ⟨kk, f, g, hk, hf, -⟩ := id hSA
    rw [← hk]; exact subset_convexHull ℝ _ ⟨kk, rfl⟩
  have hmemB : H ∈ (D.tile iB).carrier := by
    obtain ⟨kk, f, g, hk, hf, -⟩ := id hSB
    rw [← hf]; exact subset_convexHull ℝ _ ⟨f, rfl⟩
  obtain ⟨hmemS, hnvS, hlineS⟩ := step_interior_pt hSS hσ0 hσ1
  rw [← hHV] at hmemS hnvS hlineS
  set a : AtV D.toRegionDissection H := ⟨iA, hmemA⟩
  set b : AtV D.toRegionDissection H := ⟨iB, hmemB⟩
  set s : AtV D.toRegionDissection H := ⟨iS, hmemS⟩
  refine ⟨a, b, s, ?_⟩
  -- A: tail H of a step along -d; its p-arm points to HA
  obtain ⟨kkA, fA, gA, hkA, hfA, hfkA, hgkA, hgfA, hparA, hleftA⟩ := id hSA
  obtain ⟨kk', fl', hk', hp, hq⟩ := spec_corner_data (F.hspec a) ⟨kkA, hkA⟩
  have hpa : Par (F.p a) (neg2 d) := triStep_start hSA kk' fl' hk' hp hq (F.hok a)
  have hca : 0 < crs (F.p a) (F.q a) := crs_pos_of_corner (F.hok a) (F.hspec a) ⟨kk', hk'⟩
  have hkkA : kk' = kkA := (D.tile iA).indep.injective (hk'.trans hkA.symm)
  have hnA : nsq (F.p a) = slen D 0 ^ 2 := by
    have hp' : Par (toV2 ((D.tile iA).pts (armP kk' fl') - H)) (neg2 d) := hp ▸ hpa
    -- hparA : Par (toV2 (HA - H)) (neg2 d)
    have := parm_eq (T := D.tile iA) fl' hk' (W := HA) (w := fA) hfA (by rw [hkkA]; exact hfkA) hp' hparA
    rw [hp, nsq_toV2_sub, this, hdA]
  -- B: head H of a step along -d; its q-arm points to HB along d
  obtain ⟨kkB, fB, gB, hkB, hfB, hfkB, hgkB, hgfB, hparB, hleftB⟩ := id hSB
  obtain ⟨kk2, fl2, hk2, hp2, hq2⟩ := spec_corner_data (F.hspec b) ⟨fB, hfB⟩
  have hqb0 : Par (F.q b) (-(neg2 d).1, -(neg2 d).2) := triStep_end hSB kk2 fl2 hk2 hp2 hq2 (F.hok b)
  have hqb : Par (F.q b) d := by rw [neg2_neg2] at hqb0; exact hqb0
  have hcb : 0 < crs (F.p b) (F.q b) := crs_pos_of_corner (F.hok b) (F.hspec b) ⟨kk2, hk2⟩
  have hkkB : kk2 = fB := (D.tile iB).indep.injective (hk2.trans hfB.symm)
  have hnB : nsq (F.q b) ≠ slen D 0 ^ 2 := by
    have hq' : Par (toV2 ((D.tile iB).pts (armQ kk2 fl2) - H)) d := hq2 ▸ hqb
    have hHB : Par (toV2 (HB - H)) d := par_arm_neg hparB
    have := qarm_eq (T := D.tile iB) fl2 hk2 (W := HB) (w := kkB) hkB (by rw [hkkB]; exact Ne.symm hfkB) hq' hHB
    rw [hq2, nsq_toV2_sub, this, dist_comm]
    exact sq_ne_of_ne dist_nonneg (slen_pos D 0).le hdB
  obtain ⟨hpS, hqS⟩ := straight_dir s (F.hok s) (F.hloc s) (F.hspec s) hnvS hSS hlineS
  exact ⟨hca, hpa, hcb, hqb, hpS, hqS, hnA, hnB, hHX⟩


/-- The head configuration at a vertex: `u` a corner ending along `-e`, `v` a corner starting along `e`, `s` a straight sector (`p s` along `-e`); exactly one of the two
line sides (`q`-arm of `u`, `p`-arm of `v`) has length `a`. -/
def HeadCfg (D : CongruentRegionDissection N) {H : Plane} {κ : Type} [Fintype κ] (F : ExtFan D.toRegionDissection H κ) (e : V2)
    (u v s : AtV D.toRegionDissection H) : Prop :=
  0 < crs (F.p u) (F.q u) ∧ Par (F.q u) (neg2 e) ∧ 0 < crs (F.p v) (F.q v) ∧ Par (F.p v) e ∧
  Par (F.p s) (neg2 e) ∧ F.q s = (-(F.p s).1, -(F.p s).2) ∧
  ((nsq (F.q u) = slen D 0 ^ 2 ∧ nsq (F.p v) ≠ slen D 0 ^ 2) ∨ (nsq (F.q u) ≠ slen D 0 ^ 2 ∧ nsq (F.p v) = slen D 0 ^ 2))


theorem HeadCfg.of_left (D : CongruentRegionDissection N) {H : Plane} {κ : Type} [Fintype κ] (F : ExtFan D.toRegionDissection H κ) {d : V2}
    (a b s : AtV D.toRegionDissection H) (h1 : 0 < crs (F.p a) (F.q a)) (h2 : Par (F.q a) (neg2 d)) (h3 : 0 < crs (F.p b) (F.q b))
    (h4 : Par (F.p b) d) (h5 : Par (F.p s) (neg2 d)) (h6 : F.q s = (-(F.p s).1, -(F.p s).2))
    (h7 : nsq (F.q a) = slen D 0 ^ 2) (h8 : nsq (F.p b) ≠ slen D 0 ^ 2) : HeadCfg D F d a b s :=
  ⟨h1, h2, h3, h4, h5, h6, Or.inl ⟨h7, h8⟩⟩


theorem HeadCfg.of_right (D : CongruentRegionDissection N) {H : Plane} {κ : Type} [Fintype κ] (F : ExtFan D.toRegionDissection H κ) {d : V2}
    (a b s : AtV D.toRegionDissection H) (h1 : 0 < crs (F.p a) (F.q a)) (h2 : Par (F.p a) (neg2 d)) (h3 : 0 < crs (F.p b) (F.q b))
    (h4 : Par (F.q b) d) (h5 : Par (F.p s) d) (h6 : F.q s = (-(F.p s).1, -(F.p s).2))
    (h7 : nsq (F.p a) = slen D 0 ^ 2) (h8 : nsq (F.q b) ≠ slen D 0 ^ 2) : HeadCfg D F (neg2 d) b a s := by
  refine ⟨h3, ?_, h1, h2, ?_, h6, Or.inr ⟨h8, h7⟩⟩
  · rw [neg2_neg2']; exact h4
  · rw [neg2_neg2']; exact h5


namespace ExtFan

variable {D : RegionDissection N} {V : Plane} {κ : Type} [Fintype κ]

/-- **The four sectors of a head with three corners.** -/
theorem head_four (F : ExtFan D V κ) {e : V2} {u v s : AtV D V}
    (hca : 0 < crs (F.p u) (F.q u)) (hqa : Par (F.q u) (neg2 e)) (hcb : 0 < crs (F.p v) (F.q v)) (hpb : Par (F.p v) e)
    (hps : Par (F.p s) (neg2 e)) (hqs : F.q s = (-(F.p s).1, -(F.p s).2))
    (hcard : Fintype.card (AtV D V) = 4) :
    IsEmpty κ ∧ V ∈ interior D.region ∧
    ∃ m : AtV D V, u ≠ v ∧ u ≠ s ∧ v ≠ s ∧ m ≠ u ∧ m ≠ v ∧ m ≠ s ∧ (∀ x, x = u ∨ x = v ∨ x = m ∨ x = s) ∧
      Par (F.p m) (F.q v) ∧ Par (F.p u) (F.q m) ∧ Par (F.p v) (F.q s) ∧ Par (F.p s) (F.q u) ∧
      0 < crs (F.p m) (F.q m) := by
  classical
  obtain ⟨hemp, hint, hus, hvs, huv, j0, hj0, hes, hev, heu⟩ := F.head_cyc u v s hca hqa hcb hpb hps hqs
  have hκ : Fintype.card κ = 0 := Fintype.card_eq_zero_iff.mpr hemp
  have hk4 : Fintype.card (AtV D V ⊕ κ) = 4 := by rw [Fintype.card_sum, hκ, hcard]
  rw [hk4] at hj0 heu
  have hper := F.hper
  have hinj := F.hinj
  have hsurj := F.hsurj
  rw [hk4] at hper hinj hsurj
  have hmod := cyc_mod F.e 4 hper
  have hP0 := F.hP j0
  have hP1 := F.hP (j0 + 1)
  have hP2 := F.hP (j0 + 2)
  have hP3 := F.hP (j0 + 3)
  -- position j0 + 2
  obtain ⟨m, hm⟩ : ∃ m : AtV D V, F.e (j0 + 2) = Sum.inl m := by
    rcases hn : F.e (j0 + 2) with m | j
    · exact ⟨m, rfl⟩
    · exact (hemp.false j).elim
  have heu' : F.e (j0 + 3) = Sum.inl u := by simpa using heu
  have e4 : F.e (j0 + 3 + 1) = Sum.inl s := by
    rw [show j0 + 3 + 1 = j0 + 4 from rfl, hper j0, hes]
  rw [show j0 + 1 + 1 = j0 + 2 from rfl, hm, hev] at hP1
  rw [show j0 + 2 + 1 = j0 + 3 from rfl, heu', hm] at hP2
  rw [e4, heu'] at hP3
  rw [hev, hes] at hP0
  simp only [Sum.elim_inl] at hP0 hP1 hP2 hP3
  have hdist : ∀ i i', i ≤ 3 → i' ≤ 3 → i ≠ i' → F.e (j0 + i) ≠ F.e (j0 + i') := by
    intro i i' h1 h2 hne h
    rw [hmod (j0 + i), hmod (j0 + i')] at h
    have := hinj (Set.mem_Iio.mpr (Nat.mod_lt _ (by norm_num))) (Set.mem_Iio.mpr (Nat.mod_lt _ (by norm_num))) h
    omega
  have hmv : m ≠ v := by
    intro h; apply hdist 2 1 (by norm_num) (by norm_num) (by norm_num); rw [hm, hev, h]
  have hmu : m ≠ u := by
    intro h; apply hdist 2 3 (by norm_num) (by norm_num) (by norm_num); rw [hm, heu', h]
  have hms : m ≠ s := by
    intro h; apply hdist 2 0 (by norm_num) (by norm_num) (by norm_num); rw [hm, add_zero, hes, h]
  have hall : ∀ x : AtV D V, x = u ∨ x = v ∨ x = m ∨ x = s := by
    intro x
    obtain ⟨j, hj, hjx⟩ := hsurj (Sum.inl x)
    have hcases : j = (j0 + 0) % 4 ∨ j = (j0 + 1) % 4 ∨ j = (j0 + 2) % 4 ∨ j = (j0 + 3) % 4 := by omega
    rcases hcases with h | h | h | h
    · right; right; right
      have : F.e (j0 + 0) = Sum.inl x := by rw [hmod (j0 + 0), ← h]; exact hjx
      rw [add_zero, hes] at this; exact (Sum.inl.inj this).symm
    · right; left
      have : F.e (j0 + 1) = Sum.inl x := by rw [hmod (j0 + 1), ← h]; exact hjx
      rw [hev] at this; exact (Sum.inl.inj this).symm
    · right; right; left
      have : F.e (j0 + 2) = Sum.inl x := by rw [hmod (j0 + 2), ← h]; exact hjx
      rw [hm] at this; exact (Sum.inl.inj this).symm
    · left
      have : F.e (j0 + 3) = Sum.inl x := by rw [hmod (j0 + 3), ← h]; exact hjx
      rw [heu'] at this; exact (Sum.inl.inj this).symm
  -- m is a corner: otherwise two straight sectors and `u` exceed the total angle
  have hmc : 0 < crs (F.p m) (F.q m) := by
    by_contra hnot
    push_neg at hnot
    have hcs : crs (F.p m) (F.q m) = 0 ∧ dt (F.p m) (F.q m) < 0 := by
      rcases F.hok m with h | h
      · linarith
      · exact h
    have hwm : wd (F.p m) (F.q m) = Real.pi := by
      unfold wd
      rw [Complex.arg_eq_pi_iff]
      exact ⟨hcs.2, hcs.1⟩
    have hws : wd (F.p s) (F.q s) = Real.pi := by
      rw [hqs]; exact wd_straight (F.hok s).ne_p
    have hsum := F.hsum
    have hvirt : ∑ j, wd (F.pe j) (F.qe j) = 0 := by
      haveI := hemp
      simp
    rw [hvirt, add_zero] at hsum
    have h3 : wd (F.p s) (F.q s) + wd (F.p m) (F.q m) + wd (F.p u) (F.q u) ≤ ∑ x, wd (F.p x) (F.q x) := by
      have hsub : ({s, m, u} : Finset (AtV D V)) ⊆ Finset.univ := Finset.subset_univ _
      have := Finset.sum_le_sum_of_subset_of_nonneg (f := fun x => wd (F.p x) (F.q x)) hsub
        (fun x _ _ => (wd_pos (F.hok x)).le)
      rw [Finset.sum_insert (by simp [Ne.symm hms, Ne.symm hus]), Finset.sum_pair hmu] at this
      linarith
    have := wd_pos (F.hok u)
    linarith
  exact ⟨hemp, hint, m, huv, hus, hvs, hmu, hmv, hms, hall, hP1, hP2, hP0, hP3, hmc⟩


theorem crs_pos_of_par {e w w' : V2} (h : Par w w') (hw' : 0 < crs e w') : 0 < crs e w := by
  obtain ⟨c, hc, hcw⟩ := h.smul
  rw [hcw]
  unfold crs at hw' ⊢
  try simp only at hw' ⊢
  nlinarith [mul_pos hc hw']


theorem crs_zero_of_par {e w w' : V2} (h : Par w w') (hw' : crs e w' = 0) : crs e w = 0 := by
  obtain ⟨c, hc, hcw⟩ := h.smul
  rw [hcw]
  unfold crs at hw' ⊢
  try simp only at hw' ⊢
  nlinarith [hw']


theorem crs_neg_of_par {e d w : V2} (h : Par w (neg2 d)) (hd : 0 < crs e d) : crs e w < 0 := by
  obtain ⟨c, hc, hcw⟩ := h.smul
  rw [hcw]
  unfold crs at hd ⊢
  unfold neg2
  try simp only at hd ⊢
  nlinarith [mul_pos hc hd]


/-- **No ray along `-h` at the inner rays of a head.** -/
theorem head_inner_noBack (F : ExtFan D V κ) {e : V2} {u v s m : AtV D V}
    (hca : 0 < crs (F.p u) (F.q u)) (hqa : Par (F.q u) (neg2 e)) (hcb : 0 < crs (F.p v) (F.q v)) (hpb : Par (F.p v) e)
    (hps : Par (F.p s) (neg2 e)) (hqs : F.q s = (-(F.p s).1, -(F.p s).2))
    (hall : ∀ x, x = u ∨ x = v ∨ x = m ∨ x = s)
    (hmv : Par (F.p m) (F.q v)) (hum : Par (F.p u) (F.q m)) :
    NoBack D (F.q v) V ∧ NoBack D (F.p u) V := by
  -- `crs e` of the rays
  have hvq : 0 < crs e (F.q v) := by
    obtain ⟨c, hc, hcp⟩ := hpb.smul
    have h := hcb
    rw [hcp] at h
    unfold crs at h ⊢; try simp only at h ⊢
    by_contra hX; push_neg at hX
    nlinarith [mul_nonneg hc.le (neg_nonneg.mpr hX)]
  have hup : 0 < crs e (F.p u) := by
    obtain ⟨c, hc, hcq⟩ := hqa.smul
    have h := hca
    rw [hcq] at h
    unfold crs at h ⊢; unfold neg2 at h; try simp only at h ⊢
    by_contra hX; push_neg at hX
    nlinarith [mul_nonneg hc.le (neg_nonneg.mpr hX)]
  have hmp : 0 < crs e (F.p m) := crs_pos_of_par hmv hvq
  have hmq : 0 < crs e (F.q m) := by
    obtain ⟨c, hc, hcp⟩ := hum.smul
    have h := hup
    rw [hcp] at h
    unfold crs at h ⊢; try simp only at h ⊢
    by_contra hX; push_neg at hX
    nlinarith [mul_nonneg hc.le (neg_nonneg.mpr hX)]
  have hsp : crs e (F.p s) = 0 := by
    obtain ⟨c, hc, hcp⟩ := hps.smul
    rw [hcp]; unfold crs neg2; ring
  have hsq : crs e (F.q s) = 0 := by
    rw [hqs]; unfold crs at hsp ⊢; try simp only at hsp ⊢; nlinarith [hsp]
  have hvp : crs e (F.p v) = 0 := by
    obtain ⟨c, hc, hcp⟩ := hpb.smul
    rw [hcp]; unfold crs; ring
  have huq : crs e (F.q u) = 0 := by
    obtain ⟨c, hc, hcq⟩ := hqa.smul
    rw [hcq]; unfold crs neg2; ring
  have hnn : ∀ x : AtV D V, 0 ≤ crs e (F.p x) ∧ 0 ≤ crs e (F.q x) := by
    intro x
    rcases hall x with rfl | rfl | rfl | rfl
    · exact ⟨hup.le, huq.ge⟩
    · exact ⟨hvp.ge, hvq.le⟩
    · exact ⟨hmp.le, hmq.le⟩
    · exact ⟨hsp.ge, hsq.ge⟩
  constructor
  · apply F.noBack_of_none
    intro x
    obtain ⟨h1, h2⟩ := hnn x
    refine ⟨fun h => ?_, fun h => ?_⟩
    · have := crs_neg_of_par h hvq; linarith
    · have := crs_neg_of_par h hvq; linarith
  · apply F.noBack_of_none
    intro x
    obtain ⟨h1, h2⟩ := hnn x
    refine ⟨fun h => ?_, fun h => ?_⟩
    · have := crs_neg_of_par h hup; linarith
    · have := crs_neg_of_par h hup; linarith


end ExtFan

end Erdos634.Draft.LaczFormal.RG
