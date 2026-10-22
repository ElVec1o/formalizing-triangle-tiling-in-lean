-- Draft/LaczFormalGraphBack.lean -- D4 backward: the translate step and the walk propagation run from the LAST tile of a walk along a side to the first.
-- `side_step_back` (local step with the hypothesis on the tile after the vertex), `consec_step_back`, `walk_pairs_back`.  UNAUDITED.
-- Credit: Laczkovich (DCG 48 (2012), Lemma 4.3 (ii), "every triangle supported by V1V2 is a translated copy of T_1").
import Erdos634.Draft.LaczFormalGraphWalk
import Erdos634.Draft.LaczFormalGraphSideStep
import Erdos634.Draft.LaczFormalGraphHead

open scoped Classical
open Erdos634.Geometry

namespace Erdos634.Draft.LaczFormal.Graph

variable {N : ℕ}

theorem side_step_back (D : CongruentDissection N) (idx : Fin N → Equiv.Perm (Fin 3))
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
    (hβγ : (idx s1.1 kR = 1 ∧ idx s1.1 fR = 2) ∨ (idx s1.1 kR = 2 ∧ idx s1.1 fR = 1)) :
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
  have hline : RegFan.line12 l = true := by
    show ((RegFan.tT c1 == 1 && RegFan.tU c1 == 2) || (RegFan.tT c1 == 2 && RegFan.tU c1 == 1)) = true
    rw [t1, u1]
    rcases hβγ with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · simp [h1, h2]
    · simp [h1, h2]
  have htr := RegFan.boundary_step_beta_gamma l hlen hlt hstep hline
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


theorem consec_step_back (D : CongruentDissection N) (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    (hab : slen D 0 ≠ slen D 1) (hac : slen D 0 ≠ slen D 2)
    {m : Fin 3} {d : V2} {X0 Y0 : Plane} (hside : TriStep D.target d X0 Y0)
    {V : Plane} (hV : OnOpenSide D.target m V) (hVline : crs d (toV2 (V - X0)) = 0)
    (hSN : SideNormal D idx V)
    {i i2 : Fin N} {U U'' : Plane} (h1 : TriStep (D.tile i) d U V) (h2 : TriStep (D.tile i2) d V U'')
    (kR fR kL fL : Fin 3) (hR1 : (D.tile i2).pts kR = V) (hR2 : (D.tile i2).pts fR = U'')
    (hL1 : (D.tile i).pts kL = V) (hL2 : (D.tile i).pts fL = U)
    (hβγ : (idx i2 kR = 1 ∧ idx i2 fR = 2) ∨ (idx i2 kR = 2 ∧ idx i2 fR = 1)) :
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
  have := side_step_back D idx hidx V hF c2 hab hac hnorm hno1 hno2 kR fR kL fL
    (by rw [← e1]; exact hR1) hR2' (by rw [← e3]; exact hL1) hL2' (by rw [← e1]; exact hβγ)
  rw [← e1, ← e3] at this
  exact this


/-- **D4 backward (global)**: along a walk of left tiles from `X` to `Y0` on a side of the target, if the LAST tile has the type pair `(β,γ)` or `(γ,β)` on the
line, then every tile of the walk has that pair. -/
theorem walk_pairs_back (D : CongruentDissection N) (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    (hab : slen D 0 ≠ slen D 1) (hac : slen D 0 ≠ slen D 2) {d : V2} {X0 Y0 : Plane}
    (hside : TriStep D.target d X0 Y0)
    (hnorm : ∀ V, V ≠ X0 → V ≠ Y0 → (∃ j k, (D.tile j).pts k = V) → crs d (toV2 (V - X0)) = 0 → SideNormal D idx V)
    (ℓ : Fin 3 × Fin 3) (hℓ : ℓ = (1, 2) ∨ ℓ = (2, 1)) {X Y : Plane} {L : List (Fin N × Plane × Plane)}
    (hYeq : Y = Y0) (W : WalkT D.toDissection d X Y L) :
    ∀ {e : Fin N × Plane × Plane} {L' : List (Fin N × Plane × Plane)}, L = L' ++ [e] →
      (∃ t : ℝ, 0 ≤ t ∧ toV2 (X - X0) = (t * d.1, t * d.2)) →
      PairIs D idx e.1 e.2.1 e.2.2 ℓ → ∀ e' ∈ L, PairIs D idx e'.1 e'.2.1 e'.2.2 ℓ := by
  classical
  have hd0 : d ≠ 0 := by obtain ⟨-, -, -, -, -, -, -, -, hpar, -⟩ := hside; exact hpar.ne_right
  induction W with
  | nil X => intro e L' h; exact absurd h (by simp)
  | @cons i X X' Y L0 hS W' ih =>
    intro e L' hL hInv hPair e' he'
    rcases L0 with _ | ⟨e2, L2⟩
    · -- single tile
      have : e = (i, X, X') := by
        rcases L' with _ | ⟨h, L''⟩
        · simpa using hL.symm
        · simp at hL
      rw [this] at hPair
      have : e' = (i, X, X') := by simpa using he'
      rw [this]; exact hPair
    · -- the tail is nonempty: its last element is `e`
      have hL0 : (e2 :: L2) = (L'.drop 1) ++ [e] := by
        rcases L' with _ | ⟨h, L''⟩
        · simp at hL
        · simp only [List.cons_append, List.cons.injEq] at hL
          simpa using hL.2
      obtain ⟨t, ht, hXt⟩ := hInv
      obtain ⟨-, -, -, -, -, -, -, -, hpar, -⟩ := id hS
      obtain ⟨c, hc, hcw⟩ := hpar.smul
      have hX' : toV2 (X' - X0) = ((t + c) * d.1, (t + c) * d.2) := by
        have : toV2 (X' - X0) = ((toV2 (X' - X)).1 + (toV2 (X - X0)).1, (toV2 (X' - X)).2 + (toV2 (X - X0)).2) := by
          unfold toV2; ext <;> simp
        rw [this, hcw, hXt]; ext <;> simp <;> ring
      have hInv' : ∃ t' : ℝ, 0 ≤ t' ∧ toV2 (X' - X0) = (t' * d.1, t' * d.2) := ⟨t + c, by positivity, hX'⟩
      have hall0 := ih hYeq hL0 hInv' hPair
      rcases List.mem_cons.mp he' with rfl | hmem
      · -- the head tile: use the second tile and `consec_step_back`
        cases W' with
        | @cons i2 X2 X'' Y2 L3 hS2 W'' =>
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
          have hP2 : PairIs D idx i2 X' X'' ℓ := hall0 (i2, X', X'') (by simp)
          intro k k' hk hk'
          have e1 : k = kkS := (D.tile i).indep.injective (hk.trans hkS.symm)
          have e2' : k' = fS := (D.tile i).indep.injective (hk'.trans hfS.symm)
          have hP := hP2 kk2 f2 hk2 hf2
          have hβγ : (idx i2 kk2 = 1 ∧ idx i2 f2 = 2) ∨ (idx i2 kk2 = 2 ∧ idx i2 f2 = 1) := by
            rcases hℓ with rfl | rfl
            · left; simp [Prod.ext_iff] at hP; exact hP
            · right; simp [Prod.ext_iff] at hP; exact hP
          have hcs := consec_step_back D idx hidx hab hac hside hm hline hSN hS hS2 kk2 f2 fS kkS hk2 hf2 hfS hkS hβγ
          rw [e1, e2', ← hcs.1, ← hcs.2]
          exact hP
      · exact hall0 e' hmem

/-- **Lemma 4.3 (ii) backward, real**: if the last tile of the walk along a side has type pair `(β,γ)` or `(γ,β)` on the side, so does every tile. -/
theorem lemma43_back (D : CongruentDissection N) (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    (hab : slen D 0 ≠ slen D 1) (hac : slen D 0 ≠ slen D 2) {d : V2} {X0 Y0 : Plane}
    (hside : TriStep D.target d X0 Y0)
    (hnorm : ∀ V, V ≠ X0 → V ≠ Y0 → (∃ j k, (D.tile j).pts k = V) → crs d (toV2 (V - X0)) = 0 → SideNormal D idx V)
    (ℓ : Fin 3 × Fin 3) (hℓ : ℓ = (1, 2) ∨ ℓ = (2, 1)) :
    ∃ L : List (Fin N × Plane × Plane), WalkT D.toDissection d X0 Y0 L ∧ L ≠ [] ∧
      ∀ e L', L = L' ++ [e] → PairIs D idx e.1 e.2.1 e.2.2 ℓ → ∀ e' ∈ L, PairIs D idx e'.1 e'.2.1 e'.2.2 ℓ := by
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
    exact walk_pairs_back D idx hidx hab hac hside hnorm ℓ hℓ rfl hL hLe hInv hPe

theorem fin3_e3 (m : Fin 3) : (m + 2) + 1 = m := by revert m; decide
theorem fin3_e4 (m : Fin 3) : (m + 2) + 2 = m + 1 := by revert m; decide
theorem fin3_e5 (m : Fin 3) : (m + 1) + 1 = m + 2 := by revert m; decide

/-- **The two directed sides of a target at a corner `j` (target on the left)**: an outgoing one from `T.pts j` to `T.pts fo` and an incoming one from `T.pts fi`
to `T.pts j`, with `fo ≠ fi` the other two vertices. -/
theorem exists_corner_sides (T : Tri) (j : Fin 3) :
    ∃ fo fi : Fin 3, fo ≠ j ∧ fi ≠ j ∧ fo ≠ fi ∧ ∃ d1 d2 : V2, TriStep T d1 (T.pts j) (T.pts fo) ∧ TriStep T d2 (T.pts fi) (T.pts j) ∧
      crs d1 d2 ≠ 0 := by
  have hdet : T.det ≠ 0 := T.det_ne_zero
  have c0 := T.det_cyclic j
  have c1 := T.det_cyclic (j + 1)
  have c2 := T.det_cyclic (j + 2)
  rw [fin3_e5 j, fin3_e1 j] at c1
  rw [fin3_e3 j, fin3_e4 j] at c2
  have n1 := fin3_ne_one j
  have n2 := fin3_ne_two j
  have n12 := fin3_add_ne j
  have hne : ∀ a b : Plane, a ≠ b → toV2 (a - b) ≠ 0 := fun a b h => toV2_ne_zero (sub_ne_zero.mpr h)
  have hinj : ∀ a b : Fin 3, a ≠ b → T.pts a ≠ T.pts b := fun a b h e => h (T.indep.injective e)
  rcases lt_or_gt_of_ne hdet with hneg | hpos
  · refine ⟨j + 2, j + 1, n2, n1, n12.symm, toV2 (T.pts (j + 2) - T.pts j), toV2 (T.pts j - T.pts (j + 1)),
      ⟨j, j + 2, j + 1, rfl, rfl, n2, n1, n12, ?_, ?_⟩,
      ⟨j + 1, j, j + 2, rfl, rfl, n1.symm, n12.symm, n2, ?_, ?_⟩, ?_⟩
    · exact par_refl (hne _ _ (hinj _ _ n2))
    · rw [crs_toV2]; unfold cross at c0 ⊢; simp only [PiLp.sub_apply] at c0 ⊢; nlinarith
    · exact par_refl (hne _ _ (hinj _ _ n1.symm))
    · rw [crs_toV2]; unfold cross at c1 ⊢; simp only [PiLp.sub_apply] at c1 ⊢; nlinarith
    · rw [crs_toV2]; unfold cross at c0 ⊢; simp only [PiLp.sub_apply] at c0 ⊢; intro h; nlinarith
  · refine ⟨j + 1, j + 2, n1, n2, n12, toV2 (T.pts (j + 1) - T.pts j), toV2 (T.pts j - T.pts (j + 2)),
      ⟨j, j + 1, j + 2, rfl, rfl, n1, n2, n12.symm, ?_, ?_⟩,
      ⟨j + 2, j, j + 1, rfl, rfl, n2.symm, n12, n1, ?_, ?_⟩, ?_⟩
    · exact par_refl (hne _ _ (hinj _ _ n1))
    · rw [crs_toV2]; unfold cross at c0 ⊢; simp only [PiLp.sub_apply] at c0 ⊢; nlinarith
    · exact par_refl (hne _ _ (hinj _ _ n2.symm))
    · rw [crs_toV2]; unfold cross at c2 ⊢; simp only [PiLp.sub_apply] at c2 ⊢; nlinarith
    · rw [crs_toV2]; unfold cross at c0 ⊢; simp only [PiLp.sub_apply] at c0 ⊢; intro h; nlinarith

end Erdos634.Draft.LaczFormal.Graph
