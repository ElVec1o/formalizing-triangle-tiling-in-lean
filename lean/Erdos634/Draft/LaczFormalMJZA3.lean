import Erdos634.Draft.LaczFormalMJZA2

/-!
# Claims Z and A: the stage steps

Erdős #634, base-`β` band, rule `M(j)`.  Credit: AI assistant (item 3, band program, Claims Z and A), Beeson–Roșu,
Beeson, Laczkovich, Paliy.  UNAUDITED.  Axiom-clean; no `sorry`.
-/

namespace Erdos634.LaczMJ

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.LaczJunction Erdos634.LaczJunction.Walk
  Erdos634.LaczJunction.Grammar Erdos634.Draft.TraceCovering Set

variable {N : ℕ} {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ} {p q r : Fin 3}

namespace LFrame

variable (F : LFrame D e f α β γ p q r)

/-- The tiles at `D_{s'+1}` known from the standard rows. -/
theorem Dstage {H m lv s' : ℕ} (E : F.Env H m lv) (hs : s' + 1 ≤ m) (hStd : F.Std lv m s') :
    F.Dp m lv ((s' : ℝ) + 1) ∈ interior D.target.carrier ∧
    (∃ (iN : Fin N), (D.tile iN).localAngle (F.Dp m lv ((s' : ℝ) + 1)) = γ ∧
      ∃ k : Fin 3, cross (F.v - F.e0) (F.pt ((m : ℝ) + 1) (lv : ℝ)) <
        cross (F.v - F.e0) ((D.tile iN).pts k)) ∧
    ∃ iD : Fin N, (D.tile iD).localAngle (F.Dp m lv ((s' : ℝ) + 1)) = β := by
  have hHr : (lv : ℝ) + m + 1 ≤ H := by exact_mod_cast E.hrH
  have hsr : (s' : ℝ) + 1 ≤ m := by exact_mod_cast hs
  have hs0 : (0 : ℝ) ≤ s' := Nat.cast_nonneg s'
  have hl0 : (0 : ℝ) ≤ lv := Nat.cast_nonneg lv
  refine ⟨?_, ?_, ?_⟩
  · apply F.pt_interior (by linarith) (by linarith)
    exact (F.latOK E.hB (by linarith) (by linarith) (by linarith)).2.2
  · obtain ⟨iN, A, B, hv, hB', hang, hnear, -⟩ := F.stage_N hStd (by omega)
    refine ⟨iN, hang, ?_⟩
    obtain ⟨k, hk⟩ := (show TileVerts (D.tile iN) A B _ from hv).vertex_A
    exact ⟨k, by rw [hk]; exact hnear⟩
  · obtain ⟨iD, hang, -⟩ := F.stage_D hStd hs
    exact ⟨iD, hang⟩

/-- **After the row step, nothing straddles `D_{s'+2}`, or the claim is already false.**  The common ending of the Z and
A steps: if no far edge passes through `D_{s'+2}` and rows `lv, …, lv+s'+1` are standard, no far edge passes through
`D_{s'+1}`. -/
theorem no_pass_of_cover {H m lv s' : ℕ} (E : F.Env H m lv) (hs : s' + 1 ≤ m) (hStd1 : F.Std lv m (s' + 1))
    (hns2 : ¬ F.StrL ((m : ℝ) + 1) (lv : ℝ) (F.Dp m lv ((s' : ℝ) + 1 + 1))) :
    ¬ F.StrL ((m : ℝ) + 1) (lv : ℝ) (F.Dp m lv ((s' : ℝ) + 1)) := by
  intro hpass
  obtain ⟨e1, he1, hy1⟩ := hpass
  have hc : (((s' + 1 : ℕ) : ℝ) + 1) = (s' : ℝ) + 1 + 1 := by push_cast; ring
  have hcov := F.lcov (s' := s' + 1) E (by omega) hStd1 (by rw [hc]; exact hns2)
  -- the straddling edge lies inside `[J, D_{s'+2}]`
  have hmem : F.pt ((m : ℝ) + 1) (lv : ℝ) + ((s' : ℝ) + 1) • (F.v - F.e0) ∈
      openSegment ℝ ((D.tile e1.1).pts e1.2) ((D.tile e1.1).pts (e1.2 + 1)) := by
    rw [← F.Dp_eq']; exact hy1
  have hsub := edge_inside_of_ns (D := D.toDissection) (X := F.pt ((m : ℝ) + 1) (lv : ℝ)) (u := F.v - F.e0)
    (f := crossL (F.v - F.e0)) (c := cross (F.v - F.e0) (F.pt ((m : ℝ) + 1) (lv : ℝ))) F.crossL_u_ne rfl
    (by simp [crossL_apply, Erdos634.Geometry.cross_self]) F.u_ne he1
    (s := (s' : ℝ) + 1) (t := (s' : ℝ) + 1 + 1) (by positivity) (by linarith) hmem E.hnsJ
    (by rw [← F.Dp_eq']; exact hns2)
  have hsub' : (D.tile e1.1).edge e1.2 ⊆ segment ℝ (F.pt ((m : ℝ) + 1) (lv : ℝ))
      (F.Dp m lv (((s' + 1 : ℕ) : ℝ) + 1)) := by
    rw [hc, F.Dp_eq']; exact hsub
  obtain ⟨k, hk, hends⟩ := hcov.1 e1 he1 hsub'
  have hnot := F.Dp_not_mem_open (m := (m : ℝ)) (lv := (lv : ℝ)) F.u_ne (k := k) (s := s' + 1)
  push_cast at hnot
  rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2] at hy1
    exact hnot hy1
  · rw [h1, h2, openSegment_symm] at hy1
    exact hnot hy1

/-- Beyond the leg the line `l` leaves the target: nothing straddles `D_j`, `j ≥ m+1`. -/
theorem ns_Dend (m lv : ℕ) {j : ℝ} (hj : (m : ℝ) + 1 ≤ j) :
    ¬ F.StrL ((m : ℝ) + 1) (lv : ℝ) (F.Dp m lv j) := by
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  refine F.ns_end_x (x1 := (m : ℝ) + 1) (y1 := (lv : ℝ)) (x2 := (m : ℝ) + 1 - j) (y2 := (lv : ℝ) + j)
    (by linarith) (by linarith) (crossL (F.v - F.e0)) (cross (F.v - F.e0) (F.pt ((m : ℝ) + 1) (lv : ℝ)))
    F.crossL_u_ne rfl ?_
  show cross (F.v - F.e0) (F.Dp m lv j) = _
  rw [F.Dp_eq', cross_add_right, cross_smul_right, Erdos634.Geometry.cross_self]; ring

/-- **Claim Z, one stage.**  A far edge passing through `D_{s'+1}` is impossible, given the claim at `D_{s'+2}`. -/
theorem Zstep {H m lv s' : ℕ} (E : F.Env H m lv) (hs : s' + 1 ≤ m) (hStd : F.Std lv m s')
    (hpass : F.StrL ((m : ℝ) + 1) (lv : ℝ) (F.Dp m lv ((s' : ℝ) + 1)))
    (IHZ : s' + 2 ≤ m → F.Std lv m (s' + 1) →
      F.StrL ((m : ℝ) + 1) (lv : ℝ) (F.Dp m lv ((s' : ℝ) + 1 + 1)) → False) : False := by
  classical
  obtain ⟨hint, ⟨iN, hγN, hnear⟩, iD, hβD⟩ := F.Dstage E hs hStd
  obtain ⟨e1, he1, hy1⟩ := hpass
  have hπ1 := localAngle_pi_of_openSegment (D.tile e1.1) e1.2 hy1
  have c1 := cnt_ge_one hγN
  have c2 := cnt_ge_one hβD
  have c3 := cnt_ge_one hπ1
  have hfig := ifig F.S hint
  have hcπ : cnt D.toDissection (F.Dp m lv ((s' : ℝ) + 1)) Real.pi = 1 := by omega
  have hnsH : ¬ F.StrH ((lv : ℝ) + ((s' + 1 : ℕ) : ℝ))
      (F.pt ((m : ℝ) + 1 - ((s' + 1 : ℕ) : ℝ)) ((lv : ℝ) + ((s' + 1 : ℕ) : ℝ))) := by
    intro hH
    obtain ⟨e2, he2, hy2⟩ := hH
    have hc : ((s' + 1 : ℕ) : ℝ) = (s' : ℝ) + 1 := by push_cast; ring
    rw [hc] at hy2
    have hπ2 := localAngle_pi_of_openSegment (D.tile e2.1) e2.2 hy2
    have heq : e1.1 = e2.1 := cnt_eq_of_one hcπ hπ1 hπ2
    obtain ⟨i1, k1⟩ := e1
    obtain ⟨i2, k2⟩ := e2
    simp only at heq hy1 hy2 he1 he2
    subst heq
    have hk : k1 = k2 := edge_unique (D.tile i1) hy1 hy2
    subst hk
    obtain ⟨a1, a2, -⟩ := Dissection.mem_lineChain.mp he1
    obtain ⟨b1, b2, -⟩ := Dissection.mem_lineChain.mp he2
    simp only [crossL_apply] at a1 a2 b1 b2
    have := F.lines_meet_once a1 a2 b1 b2
    exact (D.tile i1).indep.injective.ne (fin3_succ_ne k1) this
  have hStd1 : F.Std lv m (s' + 1) :=
    F.adv E.hB E.hrH E.hme (s := s' + 1) (by omega) hs E.IHT E.IHA (by simpa using hStd) hnsH
  have hns2 : ¬ F.StrL ((m : ℝ) + 1) (lv : ℝ) (F.Dp m lv ((s' : ℝ) + 1 + 1)) := by
    by_cases hlast : s' + 2 ≤ m
    · intro h; exact IHZ hlast hStd1 h
    · have : (m : ℝ) + 1 ≤ (s' : ℝ) + 1 + 1 := by
        have : m ≤ s' + 1 := by omega
        have h2 : (m : ℝ) ≤ (s' : ℝ) + 1 := by exact_mod_cast this
        linarith
      exact F.ns_Dend m lv this
  exact F.no_pass_of_cover E hs hStd1 hns2 ⟨e1, he1, hy1⟩

theorem dist_Dp (m lv : ℕ) (j : ℝ) : dist (F.Dp m lv j) (F.Dp m lv (j + 1)) = (tb e f : ℝ) := by
  rw [F.Dp_eq', F.Dp_eq', dist_eq_norm]
  have : F.pt ((m : ℝ) + 1) (lv : ℝ) + j • (F.v - F.e0) - (F.pt ((m : ℝ) + 1) (lv : ℝ) + (j + 1) • (F.v - F.e0)) =
      -(F.v - F.e0) := by module
  rw [this, norm_neg, F.hu]

/-- The up tile of the next row with `α` at `D_{s'+1}`. -/
theorem stage_W {m lv s' : ℕ} (hStd1 : F.Std lv m (s' + 1)) (hs : s' + 1 ≤ m) :
    ∃ iW : Fin N, (D.tile iW).localAngle (F.Dp m lv ((s' : ℝ) + 1)) = α := by
  obtain ⟨hU, -⟩ := hStd1 (s' + 1) le_rfl
  obtain ⟨iW, hiW⟩ := hU (m - (s' + 1)) (by omega)
  have hx : ((m - (s' + 1) : ℕ) : ℝ) = (m : ℝ) - ((s' : ℝ) + 1) := by
    rw [Nat.cast_sub hs]; push_cast; ring
  have hc : ((s' + 1 : ℕ) : ℝ) = (s' : ℝ) + 1 := by push_cast; ring
  rw [hx, hc] at hiW
  have hang := (F.up_angles hiW).2.1
  have pB : F.pt ((m : ℝ) - ((s' : ℝ) + 1) + 1) ((lv : ℝ) + ((s' : ℝ) + 1)) = F.Dp m lv ((s' : ℝ) + 1) := by
    unfold Dp; congr 1; ring
  rw [pB] at hang
  exact ⟨iW, hang⟩

theorem Abase {H m lv : ℕ} (E : F.Env H m lv) (hStd : F.Std lv m m) (hFar : F.FarB m lv m) : False := by
  classical
  obtain ⟨iN, A, B, hv, hB', hang, hnear, -⟩ := F.stage_N hStd (le_refl _)
  obtain ⟨iF, ZF, hvF, hcF, hγF⟩ := hFar
  have hNF : iN ≠ iF := by
    intro h
    obtain ⟨k, hk⟩ := (show TileVerts (D.tile iN) A B _ from hv).vertex_A
    have := hcF k
    rw [← h] at this
    simp only [crossL_apply] at this
    rw [hk] at this
    linarith
  have hy : (lv : ℝ) + ((m : ℝ) + 1) < F.mu := by
    have : (lv : ℝ) + m + 1 ≤ H := by exact_mod_cast E.hrH
    linarith [E.hB.2]
  have hDp : F.Dp m lv ((m : ℝ) + 1) = F.pt 0 ((lv : ℝ) + ((m : ℝ) + 1)) := by
    unfold Dp; congr 1; ring
  have hang' : (D.tile iN).localAngle (F.Dp m lv ((m : ℝ) + 1)) = γ := hang
  rw [hDp] at hang' hγF
  obtain ⟨hfr, hnv⟩ := F.leg_front (by positivity) hy
  exact no_double_gamma_S F.S hfr hnv hNF hang' hγF

/-- **Claim A, one stage.** -/
theorem Astep {H m lv s' : ℕ} (E : F.Env H m lv) (hs : s' + 1 ≤ m) (hStd : F.Std lv m s')
    (hFar : F.FarB m lv s')
    (IHZ : s' + 2 ≤ m → F.Std lv m (s' + 1) →
      F.StrL ((m : ℝ) + 1) (lv : ℝ) (F.Dp m lv ((s' : ℝ) + 1 + 1)) → False)
    (IHA : F.Std lv m (s' + 1) → F.FarB m lv (s' + 1) → False) : False := by
  classical
  obtain ⟨hint, ⟨iN, hγN, hnear⟩, iD, hβD⟩ := F.Dstage E hs hStd
  obtain ⟨iF, ZF, hvF, hcF, hγF⟩ := hFar
  have hNF : iN ≠ iF := by
    intro h
    obtain ⟨k, hk⟩ := hnear
    have := hcF k
    rw [← h] at this
    simp only [crossL_apply] at this
    linarith
  have c1 := cnt_ge_two hNF hγN hγF
  have c2 := cnt_ge_one hβD
  have hfig := ifig F.S hint
  have hπ0 : cnt D.toDissection (F.Dp m lv ((s' : ℝ) + 1)) Real.pi = 0 := by omega
  have hnsH : ¬ F.StrH ((lv : ℝ) + ((s' + 1 : ℕ) : ℝ))
      (F.pt ((m : ℝ) + 1 - ((s' + 1 : ℕ) : ℝ)) ((lv : ℝ) + ((s' + 1 : ℕ) : ℝ))) := by
    intro hH
    have hc : ((s' + 1 : ℕ) : ℝ) = (s' : ℝ) + 1 := by push_cast; ring
    rw [hc] at hH
    obtain ⟨i2, hi2⟩ := LFrame.straddled_pi hH
    have : 1 ≤ cnt D.toDissection (F.Dp m lv ((s' : ℝ) + 1)) Real.pi := cnt_ge_one hi2
    omega
  have hStd1 : F.Std lv m (s' + 1) :=
    F.adv E.hB E.hrH E.hme (s := s' + 1) (by omega) hs E.IHT E.IHA (by simpa using hStd) hnsH
  obtain ⟨iW, hαW⟩ := F.stage_W hStd1 hs
  have c3 := cnt_ge_one hαW
  have hγ2 : cnt D.toDissection (F.Dp m lv ((s' : ℝ) + 1)) γ = 2 := by omega
  have hns2 : ¬ F.StrL ((m : ℝ) + 1) (lv : ℝ) (F.Dp m lv ((s' : ℝ) + 1 + 1)) := by
    by_cases hlast : s' + 2 ≤ m
    · intro h; exact IHZ hlast hStd1 h
    · have : (m : ℝ) + 1 ≤ (s' : ℝ) + 1 + 1 := by
        have : m ≤ s' + 1 := by omega
        have h2 : (m : ℝ) ≤ (s' : ℝ) + 1 := by exact_mod_cast this
        linarith
      exact F.ns_Dend m lv this
  have hc : (((s' + 1 : ℕ) : ℝ) + 1) = (s' : ℝ) + 1 + 1 := by push_cast; ring
  have hcov := F.lcov (s' := s' + 1) E (by omega) hStd1 (by rw [hc]; exact hns2)
  obtain ⟨e', he', hends⟩ := hcov.2 (s' + 1) (by omega)
  have hc1 : ((s' + 1 : ℕ) : ℝ) = (s' : ℝ) + 1 := by push_cast; ring
  simp only [hc1] at hends
  obtain ⟨hvF', hcF'⟩ := chain_tileVerts he' (A := F.Dp m lv ((s' : ℝ) + 1)) (B := F.Dp m lv ((s' : ℝ) + 1 + 1))
    (by
      rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨h1, h2⟩
      · exact Or.inr ⟨h1, h2⟩)
  have hdist : dist (F.Dp m lv ((s' : ℝ) + 1)) (F.Dp m lv ((s' : ℝ) + 1 + 1)) = (tb e f : ℝ) :=
    F.dist_Dp m lv ((s' : ℝ) + 1)
  rcases tv_bedge F.S hvF' hdist with ⟨h1, h2, -, -, -⟩ | ⟨h1, h2, -, -, -⟩
  · -- `α` at `D_{s'+1}`, `γ` at `D_{s'+2}`: the next far tile of type A
    refine IHA hStd1 ⟨e'.1, (D.tile e'.1).pts (e'.2 + 2), ?_, hcF', ?_⟩
    · rw [hc1]; exact hvF'
    · rw [hc1]; exact h2
  · -- `γ` at `D_{s'+1}`: a third `γ`
    exfalso
    have hN' : iN ≠ e'.1 := by
      intro h
      obtain ⟨k, hk⟩ := hnear
      have := hcF' k
      rw [← h] at this
      simp only [crossL_apply] at this
      linarith
    have hF' : iF ≠ e'.1 := by
      intro h
      rw [← h] at hvF'
      obtain ⟨k, hk⟩ := hvF'.vertex_B
      rcases hvF.pts_mem k with h0 | h0 | h0
      · rw [hk] at h0
        have := F.Dp_inj h0
        linarith
      · rw [hk] at h0
        have := F.Dp_inj h0
        linarith
      · have hZ : ZF = F.Dp m lv ((s' : ℝ) + 1 + 1) := h0.symm.trans hk
        have hcr := tv_cross_ne hvF
        rw [hZ] at hcr
        apply hcr
        rw [F.Dp_eq', F.Dp_eq', F.Dp_eq']
        simp only [cross, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
        ring
    have c4 := cnt_ge_three hNF hN' hF' hγN hγF h1
    omega

end LFrame

end Erdos634.LaczMJ
