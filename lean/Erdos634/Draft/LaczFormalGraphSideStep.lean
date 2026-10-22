-- Draft/LaczFormalGraphSideStep.lean -- D4 (local): the THREE-TILE fan at a normal vertex on a side of the target, in linear order, with the
-- line rays `pT` (toward the interior side of the side direction) and `-pT`, and the translate step of Laczkovich's Lemma 4.3 (via `RegFan`).
-- UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Lemma 4.3 and Fig. 3; Lemma 4.2 proof).
import Erdos634.Draft.LaczFormalGraphTypes

open Erdos634.Geometry

namespace Erdos634.Draft.LaczFormal.Graph

variable {N : ℕ}

/-- Periodicity reduces any position of the cyclic list to `[0, k)`. -/
theorem cyc_mod {ι : Type*} (e : ℕ → ι) (k : ℕ) (hper : ∀ n, e (n + k) = e n) (x : ℕ) : e x = e (x % k) := by
  have hmul : ∀ q' x, e (x + q' * k) = e x := by
    intro q'
    induction q' with
    | zero => intro x; simp
    | succ q ih => intro x; rw [Nat.succ_mul, ← add_assoc, hper (x + q * k), ih]
  have := hmul (x / k) (x % k)
  rw [show x % k + x / k * k = x by rw [mul_comm]; exact Nat.mod_add_div x k] at this
  exact this

/-- **The three corner tiles of a side vertex with a 3-tile fan, in order.** -/
theorem side_fan_three (D : Dissection N) (V : Plane) (m : Fin 3) (h0 : D.target.basis.coord m V = 0)
    (hpos : ∀ j, j ≠ m → 0 < D.target.basis.coord j V) (hvert : ∃ i k, (D.tile i).pts k = V)
    (hcard : Fintype.card (AtV D V) = 3) :
    ∃ (pT : V2) (p q : AtV D V → V2) (s1 s2 s3 : AtV D V),
      pT ≠ 0 ∧ LocalCone D.target V pT (-pT.1, -pT.2) ∧
      (∀ s, SecOK (p s) (q s)) ∧ (∀ s, LocalCone (D.tile s.1) V (p s) (q s)) ∧
      (∀ s, wd (p s) (q s) = (D.tile s.1).localAngle V) ∧ (∀ s, SectorSpec (D.tile s.1) V (p s) (q s)) ∧
      s1 ≠ s2 ∧ s1 ≠ s3 ∧ s2 ≠ s3 ∧ (∀ s, s = s1 ∨ s = s2 ∨ s = s3) ∧
      Par (p s1) pT ∧ Par (p s2) (q s1) ∧ Par (p s3) (q s2) ∧ Par (-pT.1, -pT.2) (q s3) := by
  classical
  obtain ⟨pT, p, q, e, hpT, hlocT, hok, hloc, hwd, hspec, hP, hper, hinj, hsurj⟩ :=
    vertex_fan_side D V m h0 hpos hvert
  have hk4 : Fintype.card (Option (AtV D V)) = 4 := by simp [Fintype.card_option, hcard]
  rw [hk4] at hper hinj hsurj
  have hmod := cyc_mod e 4 hper
  obtain ⟨j0, hj0, hnone⟩ := hsurj none
  have hne : ∀ i, 1 ≤ i → i ≤ 3 → e (j0 + i) ≠ none := by
    intro i hi1 hi3 h
    rw [hmod (j0 + i)] at h
    have := hinj (Set.mem_Iio.mpr (Nat.mod_lt _ (by norm_num))) (Set.mem_Iio.mpr hj0) (h.trans hnone.symm)
    omega
  obtain ⟨s1, hs1⟩ := Option.ne_none_iff_exists'.mp (hne 1 (by norm_num) (by norm_num))
  obtain ⟨s2, hs2⟩ := Option.ne_none_iff_exists'.mp (hne 2 (by norm_num) (by norm_num))
  obtain ⟨s3, hs3⟩ := Option.ne_none_iff_exists'.mp (hne 3 (by norm_num) (by norm_num))
  have hdist : ∀ i i', i ≤ 3 → i' ≤ 3 → 1 ≤ i → 1 ≤ i' → i ≠ i' → e (j0 + i) ≠ e (j0 + i') := by
    intro i i' h1 h2 h3 h4 hne' h
    rw [hmod (j0 + i), hmod (j0 + i')] at h
    have := hinj (Set.mem_Iio.mpr (Nat.mod_lt _ (by norm_num))) (Set.mem_Iio.mpr (Nat.mod_lt _ (by norm_num))) h
    omega
  have hP0 := hP j0
  have hP1 := hP (j0 + 1)
  have hP2 := hP (j0 + 2)
  have hP3 := hP (j0 + 3)
  rw [hnone, show j0 + 1 = j0 + 1 from rfl, hs1] at hP0
  rw [show j0 + 1 + 1 = j0 + 2 from rfl, hs2, hs1] at hP1
  rw [show j0 + 2 + 1 = j0 + 3 from rfl, hs3, hs2] at hP2
  have he4 : e (j0 + 3 + 1) = none := by
    rw [show j0 + 3 + 1 = j0 + 4 from rfl, hper j0, hnone]
  rw [he4, hs3] at hP3
  refine ⟨pT, p, q, s1, s2, s3, hpT, hlocT, hok, hloc, hwd, hspec, ?_, ?_, ?_, ?_, hP0, hP1, hP2, hP3⟩
  · intro h; apply hdist 1 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    rw [hs1, hs2, h]
  · intro h; apply hdist 1 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    rw [hs1, hs3, h]
  · intro h; apply hdist 2 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    rw [hs2, hs3, h]
  · intro s
    obtain ⟨j, hj, hjs⟩ := hsurj (some s)
    have hjne : j ≠ j0 := by
      intro h; rw [h, hnone] at hjs; exact absurd hjs (by simp)
    have hcases : j = (j0 + 1) % 4 ∨ j = (j0 + 2) % 4 ∨ j = (j0 + 3) % 4 := by omega
    rcases hcases with h | h | h
    · left
      have : e (j0 + 1) = some s := by rw [hmod (j0 + 1), ← h]; exact hjs
      rw [hs1] at this; exact (Option.some.inj this).symm
    · right; left
      have : e (j0 + 2) = some s := by rw [hmod (j0 + 2), ← h]; exact hjs
      rw [hs2] at this; exact (Option.some.inj this).symm
    · right; right
      have : e (j0 + 3) = some s := by rw [hmod (j0 + 3), ← h]; exact hjs
      rw [hs3] at this; exact (Option.some.inj this).symm

/-! ## Corner data of a sector -/

/-- The arm index of the clockwise (previous) ray of a corner at `kk`. -/
def armP (kk : Fin 3) (fl : Bool) : Fin 3 := if fl then kk + 2 else kk + 1
/-- The arm index of the counterclockwise (next) ray. -/
def armQ (kk : Fin 3) (fl : Bool) : Fin 3 := if fl then kk + 1 else kk + 2

theorem spec_corner_data {T : Tri} {V : Plane} {p q : V2} (hspec : SectorSpec T V p q) (hv : ∃ k, T.pts k = V) :
    ∃ (kk : Fin 3) (fl : Bool), T.pts kk = V ∧ p = toV2 (T.pts (armP kk fl) - V) ∧ q = toV2 (T.pts (armQ kk fl) - V) := by
  rcases hspec with ⟨k, hk, hpq⟩ | ⟨hnv, -⟩
  · rcases hpq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨k, false, hk, by simp [armP, h1], by simp [armQ, h2]⟩
    · exact ⟨k, true, hk, by simp [armP, h1], by simp [armQ, h2]⟩
  · obtain ⟨k, hk⟩ := hv
    exact absurd hk (hnv k)

/-- Lengths of the first sides at a corner, in terms of the model sides opposite the arm types. -/
theorem arm_lens (D : CongruentDissection N) (idx : Fin N → Equiv.Perm (Fin 3))
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

theorem armP_ne (kk : Fin 3) (fl : Bool) : armP kk fl ≠ kk := by
  cases fl
  · exact fin3_ne_one kk
  · exact fin3_ne_two kk

theorem armQ_ne (kk : Fin 3) (fl : Bool) : armQ kk fl ≠ kk := by
  cases fl
  · exact fin3_ne_two kk
  · exact fin3_ne_one kk

theorem armPQ_ne (kk : Fin 3) (fl : Bool) : armP kk fl ≠ armQ kk fl := by
  cases fl
  · exact fin3_add_ne kk
  · exact (fin3_add_ne kk).symm

theorem codeOf_spec' (σ : Equiv.Perm (Fin 3)) (kk : Fin 3) (fl : Bool) :
    RegFan.tT (codeOf σ kk fl) = σ kk ∧ RegFan.tU (codeOf σ kk fl) = σ (armP kk fl) ∧
    RegFan.tW (codeOf σ kk fl) = σ (armQ kk fl) ∧ codeOf σ kk fl < 6 := by
  obtain ⟨h1, h2, h3, h4⟩ := codeOf_spec σ kk fl
  refine ⟨h1, ?_, ?_, h4⟩
  · rw [h2]; cases fl <;> simp [armP]
  · rw [h3]; cases fl <;> simp [armQ]

/-- Packaged conclusions of `side_fan_three`. -/
structure SideFan3 (D : Dissection N) (V : Plane) (pT : V2) (p q : AtV D V → V2) (s1 s2 s3 : AtV D V) : Prop where
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

theorem side_fan_three_struct (D : Dissection N) (V : Plane) (m : Fin 3) (h0 : D.target.basis.coord m V = 0)
    (hpos : ∀ j, j ≠ m → 0 < D.target.basis.coord j V) (hvert : ∃ i k, (D.tile i).pts k = V)
    (hcard : Fintype.card (AtV D V) = 3) :
    ∃ (pT : V2) (p q : AtV D V → V2) (s1 s2 s3 : AtV D V),
      LocalCone D.target V pT (-pT.1, -pT.2) ∧ SideFan3 D V pT p q s1 s2 s3 := by
  obtain ⟨pT, p, q, s1, s2, s3, hpT, hlocT, hok, hloc, -, hspec, d12, d13, d23, hall, r1, r2, r3, r4⟩ :=
    side_fan_three D V m h0 hpos hvert hcard
  exact ⟨pT, p, q, s1, s2, s3, hlocT, ⟨hpT, hok, hloc, hspec, d12, d13, d23, hall, r1, r2, r3, r4⟩⟩

theorem fin3_arm (kk a : Fin 3) (h : a ≠ kk) : a = kk + 1 ∨ a = kk + 2 := by
  revert kk a; decide

/-- Two arms of a tile corner pointing in the same direction coincide. -/
theorem arm_unique (T : Tri) (V : Plane) (kk : Fin 3) (hk : T.pts kk = V) (a b : Fin 3) (ha : a ≠ kk) (hb : b ≠ kk)
    (d : V2) (h1 : Par (toV2 (T.pts a - V)) d) (h2 : Par (toV2 (T.pts b - V)) d) : a = b := by
  by_contra hab
  have hD : cross (T.pts (kk + 1) - T.pts kk) (T.pts (kk + 2) - T.pts kk) = T.det := T.det_cyclic kk
  have hdet : T.det ≠ 0 := T.det_ne_zero
  have hpar := h1.trans h2.symm
  have hcrs := hpar.1
  rw [crs_toV2] at hcrs
  subst hk
  rcases fin3_arm kk a ha with rfl | rfl <;> rcases fin3_arm kk b hb with rfl | rfl
  · exact hab rfl
  · exact hdet (hD ▸ hcrs)
  · rw [cross_swap, neg_eq_zero] at hcrs; exact hdet (hD ▸ hcrs)
  · exact hab rfl

theorem slen_pos (D : CongruentDissection N) (t : Fin 3) : 0 < slen D t := by
  unfold slen
  apply dist_pos.mpr
  intro h
  exact fin3_add_ne t (D.model.indep.injective h)

theorem slen_sq_eq_iff (D : CongruentDissection N) (hab : slen D 0 ≠ slen D 1) (hac : slen D 0 ≠ slen D 2) (t : Fin 3) :
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

theorem cnt3_eq (c1 c2 c3 j : ℕ) :
    RegFan.cnt [c1, c2, c3] j = (if RegFan.tT c1 = j then 1 else 0) + (if RegFan.tT c2 = j then 1 else 0) +
      (if RegFan.tT c3 = j then 1 else 0) := by
  by_cases h1 : RegFan.tT c1 = j <;> by_cases h2 : RegFan.tT c2 = j <;> by_cases h3 : RegFan.tT c3 = j <;>
    simp [RegFan.cnt, List.filter_cons, h1, h2, h3]

theorem perm3_cnt (a b c : Fin 3) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (j : Fin 3) :
    (if (a : ℕ) = j then 1 else 0) + (if (b : ℕ) = j then 1 else 0) + (if (c : ℕ) = j then 1 else 0) = 1 := by
  revert a b c j; decide

/-- **D4, the translate step at a normal side vertex (real).**  In the three-tile fan at a vertex `V` on a side of the target with the line
tiles `s1` (starting along `pT`) and `s3` (ending along `-pT`): if the types at `V` are distinct (normal), no inner ray has differing first
sides (no `Γ_a` edge), `a` differs from `b` and `c`, and the left tile `s3` has `β, γ` on the line, then the right tile `s1` has the same
type pair on the line: Laczkovich Lemma 4.3 (ii), local step. -/
theorem side_step (D : CongruentDissection N) (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    (V : Plane) {pT : V2} {p q : AtV D.toDissection V → V2} {s1 s2 s3 : AtV D.toDissection V}
    (hF : SideFan3 D.toDissection V pT p q s1 s2 s3)
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

end Erdos634.Draft.LaczFormal.Graph

#print axioms Erdos634.Draft.LaczFormal.Graph.side_step
#print axioms Erdos634.Draft.LaczFormal.Graph.side_fan_three_struct
