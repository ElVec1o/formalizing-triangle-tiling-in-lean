import Erdos634.Draft.LaczFormalALZA2

/-!
# Claim Z, the stage step (a-lattice, Lemma A(j))

Erdős \#634, base-`β` row, thick analogue of `M(j)` (Lemma A(j)).  Credit: AI assistant (Lemma A(k) proposal), Beeson–Roșu,
Beeson, Laczkovich, Paliy.  UNAUDITED.  Axiom-clean; no `sorry`.  Port of `LaczFormalMJZA3.lean` to the exchanged frame
`AF` (`e0` of length `a` along the base, `v` of length `c` along the left leg).
-/

namespace Erdos634.LaczAL

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.LaczJunction Erdos634.LaczJunction.Walk
  Erdos634.LaczJunction.Grammar Erdos634.Draft.TraceCovering Erdos634.LaczMJ Set

variable {N : ℕ} {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ} {p q r : Fin 3}

namespace AF

variable (F : AF D e f α β γ p q r)

/-- The tiles at `D_{s'+1}` known from the standard rows. -/
theorem Dstage {H m lv s' : ℕ} (E : F.Env H m lv) (hs : s' + 1 ≤ m) (hStd : F.Std lv m s') :
    F.Dp m lv ((s' : ℝ) + 1) ∈ interior D.target.carrier ∧
    (∃ (iN : Fin N), (D.tile iN).localAngle (F.Dp m lv ((s' : ℝ) + 1)) = α ∧
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
  obtain ⟨hint, ⟨iN, hαN, hnear⟩, iD, hβD⟩ := F.Dstage E hs hStd
  obtain ⟨e1, he1, hy1⟩ := hpass
  have hπ1 := localAngle_pi_of_openSegment (D.tile e1.1) e1.2 hy1
  have c1 := cnt_ge_one hαN
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

end AF

end Erdos634.LaczAL
