import Erdos634.Draft.LaczFormalColumnZA2

/-!
# Column Lemma, wall frame: copy of `LaczFormalMJZA3` (LFrame blocks) for `WFrame`

Credit: AI assistant (Column Lemma proposal), Beeson–Roșu, Beeson, Laczkovich, Paliy.  UNAUDITED.  Generated from the audited
module by renaming `LFrame` to `WFrame`; the leg-specific facts are replaced as documented in `LaczFormalColumnLat`.
-/

namespace Erdos634.LaczCol

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.LaczJunction Erdos634.LaczJunction.Walk
  Erdos634.LaczJunction.Grammar Erdos634.Draft.TraceCovering Erdos634.LaczMJ Erdos634.LaczWall Set

variable {N : ℕ} {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ} {p q r : Fin 3}

namespace WFrame


variable (F : WFrame D e f α β γ p q r)

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

/-- At the wall point `D_{m+1}` the line `l` is not straddled (the wall is crossed by no tile). -/
theorem ns_Dend {H : ℕ} (m lv : ℕ) (hB : F.Bnd H) (hrH : lv + m + 1 ≤ H) :
    ¬ F.StrL ((m : ℝ) + 1) (lv : ℝ) (F.Dp m lv ((m : ℝ) + 1)) := by
  have hHr : (lv : ℝ) + m + 1 ≤ H := by exact_mod_cast hrH
  have hlv0 : (0 : ℝ) ≤ lv := Nat.cast_nonneg lv
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hD : F.Dp m lv ((m : ℝ) + 1) = F.pt 0 ((lv : ℝ) + ((m : ℝ) + 1)) := by
    unfold Dp; congr 1 <;> ring
  rw [hD]
  exact F.ns_wall (crossL (F.v - F.e0)) _ F.trans_u (by linarith) (by linarith [hB.2])

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
      have hj : (s' : ℝ) + 1 + 1 = (m : ℝ) + 1 := by
        have h1 : s' + 1 ≤ m := hs
        have h2 : ¬ (s' + 2 ≤ m) := hlast
        have : s' + 1 = m := by omega
        have : (s' : ℝ) + 1 = (m : ℝ) := by exact_mod_cast this
        linarith
      rw [hj]
      exact F.ns_Dend m lv E.hB E.hrH
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
  have h0 : (0 : ℝ) < (lv : ℝ) + ((m : ℝ) + 1) := by positivity
  have hiN : iN ∈ Side D.toDissection F.wg F.wc :=
    F.tile_mem_Side h0 hy (x' := (m : ℝ) + 1 - (m : ℝ)) (y' := (lv : ℝ) + (m : ℝ)) (by linarith)
      (by
        obtain ⟨k, hk⟩ := (show TileVerts (D.tile iN) A B _ from hv).vertex_C
        exact ⟨k, by rw [hk, sub_self]⟩)
      (by
        obtain ⟨k, hk⟩ := (show TileVerts (D.tile iN) A B _ from hv).vertex_B
        exact ⟨k, by rw [hk, hB']⟩)
  have hiF : iF ∈ Side D.toDissection F.wg F.wc :=
    F.tile_mem_Side h0 hy (x' := (m : ℝ) + 1 - (m : ℝ)) (y' := (lv : ℝ) + (m : ℝ)) (by linarith)
      (by
        obtain ⟨k, hk⟩ := hvF.vertex_B
        refine ⟨k, ?_⟩
        rw [hk]
        exact hDp)
      (by
        obtain ⟨k, hk⟩ := hvF.vertex_A
        refine ⟨k, ?_⟩
        rw [hk]
        unfold Dp; congr 1 <;> ring)
  have c2 := scnt_ge_two hNF hiN hiF hang' hγF
  rcases wall_figure_sum F.S F.wg F.wc (F.hsum' h0 hy) with h | h | h <;> omega

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
    obtain ⟨i2, hi2⟩ := WFrame.straddled_pi hH
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
      have hj : (s' : ℝ) + 1 + 1 = (m : ℝ) + 1 := by
        have h1 : s' + 1 ≤ m := hs
        have h2 : ¬ (s' + 2 ≤ m) := hlast
        have : s' + 1 = m := by omega
        have : (s' : ℝ) + 1 = (m : ℝ) := by exact_mod_cast this
        linarith
      rw [hj]
      exact F.ns_Dend m lv E.hB E.hrH
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


end WFrame

end Erdos634.LaczCol
