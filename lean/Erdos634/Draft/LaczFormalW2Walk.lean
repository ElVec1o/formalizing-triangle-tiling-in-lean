import Erdos634.Draft.LaczFormalW2Final
import Erdos634.Draft.LaczFormalUDims

/-!
# Theorem U2 for real tilings: no `CongruentDissection` of `T_M(e,f)` with `2Me ≤ f + 2`

Erdős #634, band program, rule W2 and Theorem U2 (`PROOF_U.md`, `PROOF_W2.md`).  Credit: AI assistant (item 3, band
program), Beeson–Roșu (the tile, the relation lattice, Lemma 34), Beeson, Laczkovich (fans, chord covers), Paliy,
Zhang.  UNAUDITED.

* `walk_noW2`, `walk_noW2m`: neither `W2` nor `W2m` occurs in the word of the base walk (from `w2_holds`);
* `no_tiling_U2_oriented`, `no_tiling_U2`: for `e ≥ 2` coprime `e < f`, `M ≥ 1`, `2Me ≤ f + 2` no
  `CongruentDissection` of `T_M(e,f)` (base `Me(3f²−e²)`, legs `Mf³`) by the tile `(ef, f²−e², f²)`.  Ingredients:
  Band Lemma, `thm_siderunall`, corner rules `C0`, `C0m`, rule `W2` and its mirror, `U2_core'`.
-/

namespace Erdos634.LaczJunction.Walk

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.LaczJunction Erdos634.LaczJunction.Grammar
open Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.W2E1 Erdos634.Draft.SideRunG
  Erdos634.BaseBetaTargetCoord Erdos634.Draft.FDBBaseBetaE1

variable {N : ℕ}

theorem walk_noW2 {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ} {p q r : Fin 3}
    (S : BandSetup D e f α β γ p q r) (he2 : 2 ≤ e) (hf3 : 3 ≤ f)
    (hL2 : 2 * (ta e f : ℝ) < dist (D.target.pts p) (D.target.pts r))
    (hori : 0 < crs (toV2 (D.target.pts q - D.target.pts p)) (toV2 (D.target.pts r - D.target.pts p)))
    {L : List (Fin N × Plane × Plane)}
    (hL : WalkT D.toDissection (toV2 (D.target.pts q - D.target.pts p)) (D.target.pts p)
      (D.target.pts q) L)
    (hpar : ∀ x ∈ L, ∃ s t : ℝ, 0 ≤ s ∧ s < t ∧ t ≤ 1 ∧
        x.2.1 = D.target.pts p + s • (D.target.pts q - D.target.pts p) ∧
        x.2.2 = D.target.pts p + t • (D.target.pts q - D.target.pts p))
    (hstep : ∀ x ∈ L, StepData D e f α β γ p q x) :
    ¬ winW2 (L.map (elemTok D α β)) := by
  rintro ⟨Y, hY, s, hs⟩
  obtain ⟨x0, x1, x2, L', hLeq⟩ : ∃ x0 x1 x2 L', L = x0 :: x1 :: x2 :: L' := by
    rcases hc : L with _ | ⟨x0, _ | ⟨x1, _ | ⟨x2, L'⟩⟩⟩
    · rw [hc] at hs; simp at hs
    · rw [hc] at hs; simp at hs
    · rw [hc] at hs; simp at hs
    · exact ⟨x0, x1, x2, L', rfl⟩
  rw [hLeq] at hs
  simp only [List.map_cons, List.cons_append, List.nil_append, List.cons.injEq] at hs
  obtain ⟨e0, e1, e2, -⟩ := hs
  have hne : D.target.pts p ≠ D.target.pts q := by
    intro h
    have : crs (toV2 (D.target.pts q - D.target.pts p)) (toV2 (D.target.pts r - D.target.pts p)) = 0 := by
      rw [← h]; simp [crs, toV2]
    linarith
  have hx0 : x0.2.1 = D.target.pts p := walk_first hL x0 (x1 :: x2 :: L') hLeq
  have hadj01 : x0.2.2 = x1.2.1 := walk_adjacent hL [] (x2 :: L') x0 x1 (by simpa using hLeq)
  have hadj12 : x1.2.2 = x2.2.1 := walk_adjacent hL [x0] L' x1 x2 (by simpa using hLeq)
  have hne2 : x2.1 ≠ x1.1 := walk_adjacent_tile_ne hne hL [x0] L' x1 x2 (by simpa using hLeq)
  have sd0 := hstep x0 (by rw [hLeq]; simp)
  have sd1 := hstep x1 (by rw [hLeq]; simp)
  have sd2 := hstep x2 (by rw [hLeq]; simp)
  have hp0 := hpar x0 (by rw [hLeq]; simp)
  obtain ⟨kk, fi, g, hfk, hgk, hgf, hk, hf, hleft, hbt0⟩ := sd0
  obtain ⟨kk1, fi1, g1, -, -, -, -, -, -, hbt1⟩ := sd1
  obtain ⟨kk2, fi2, g2, -, -, -, -, -, -, hbt2⟩ := sd2
  have hc : dist x0.2.1 x0.2.2 = sideOpp D.model 2 :=
    tok_len_c S (t := elemTok D α β x0) hbt0 (by rw [← e0]; rfl)
  obtain ⟨g', hseg, kk', fi', hfk', hgk', hgf', hk', hf', hbt0'⟩ :=
    first_apex S hori hx0 hp0 ⟨kk, fi, g, hfk, hgk, hgf, hk, hf, hleft, hbt0⟩ hc
  have t1 : BaseTok D p q (angOf α β γ) (lenOf (ta e f) (tb e f) (tc e f)) .c .B .A x0.1
      (D.target.pts p) x0.2.2 ((D.tile x0.1).pts g') := by
    have := hbt0'
    rw [← e0] at this
    rw [hx0] at this
    exact this
  have t2 : BaseTok D p q (angOf α β γ) (lenOf (ta e f) (tb e f) (tc e f)) .c .B .A x1.1
      x0.2.2 x1.2.2 ((D.tile x1.1).pts g1) := by
    have := hbt1
    rw [← e1] at this
    rw [hadj01]
    exact this
  have t3 : BaseTok D p q (angOf α β γ) (lenOf (ta e f) (tb e f) (tc e f))
      (elemTok D α β x2).side (elemTok D α β x2).left (elemTok D α β x2).right x2.1
      x1.2.2 x2.2.2 ((D.tile x2.1).pts g2) := by
    rw [hadj12]; exact hbt2
  have hlr : ((elemTok D α β x2).side = .b ∧ (elemTok D α β x2).left = .A) ∨
      ((elemTok D α β x2).side = .c ∧ (elemTok D α β x2).left = .A) ∨
      ((elemTok D α β x2).side = .b ∧ (elemTok D α β x2).left = .G ∧ (elemTok D α β x2).right = .A) := by
    rw [← e2]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hY
    rcases hY with rfl | rfl | rfl <;> simp [Tok.left, Tok.side, Tok.right]
  exact w2_holds S he2 hf3 hL2 hne2 hlr t1 t2 t3

theorem walk_noW2m {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ} {p q r : Fin 3}
    (S : BandSetup D e f α β γ p q r) (he2 : 2 ≤ e) (hf3 : 3 ≤ f)
    (hR2 : 2 * (ta e f : ℝ) < dist (D.target.pts q) (D.target.pts r))
    (hori : 0 < crs (toV2 (D.target.pts q - D.target.pts p)) (toV2 (D.target.pts r - D.target.pts p)))
    {L : List (Fin N × Plane × Plane)}
    (hL : WalkT D.toDissection (toV2 (D.target.pts q - D.target.pts p)) (D.target.pts p)
      (D.target.pts q) L)
    (hpar : ∀ x ∈ L, ∃ s t : ℝ, 0 ≤ s ∧ s < t ∧ t ≤ 1 ∧
        x.2.1 = D.target.pts p + s • (D.target.pts q - D.target.pts p) ∧
        x.2.2 = D.target.pts p + t • (D.target.pts q - D.target.pts p))
    (hstep : ∀ x ∈ L, StepData D e f α β γ p q x) :
    ¬ winW2m (L.map (elemTok D α β)) := by
  rintro ⟨Y, hY, s, hs⟩
  obtain ⟨L', x1, x2, x3, hLeq⟩ : ∃ L' x1 x2 x3, L = L' ++ [x1, x2, x3] := by
    rcases hc : L.reverse with _ | ⟨x3, _ | ⟨x2, _ | ⟨x1, r'⟩⟩⟩
    · have : L = [] := by simpa using congrArg List.reverse hc
      rw [this] at hs; simp at hs
    · have : L = [x3] := by simpa using congrArg List.reverse hc
      rw [this] at hs
      have := congrArg List.length hs; simp at this
    · have : L = [x2, x3] := by simpa using congrArg List.reverse hc
      rw [this] at hs
      have := congrArg List.length hs; simp at this
    · exact ⟨r'.reverse, x1, x2, x3, by simpa using congrArg List.reverse hc⟩
  rw [hLeq, List.map_append] at hs
  have hsuf := List.append_inj_right' hs (by simp)
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hsuf
  obtain ⟨e1, e2, e3⟩ := hsuf
  have hne : D.target.pts p ≠ D.target.pts q := by
    intro h
    have : crs (toV2 (D.target.pts q - D.target.pts p)) (toV2 (D.target.pts r - D.target.pts p)) = 0 := by
      rw [← h]; simp [crs, toV2]
    linarith
  have hx3 : x3.2.2 = D.target.pts q := walk_last hL (L' ++ [x1, x2]) x3 (by rw [hLeq]; simp)
  have hadj12 : x1.2.2 = x2.2.1 := walk_adjacent hL L' [x3] x1 x2 (by simpa using hLeq)
  have hadj23 : x2.2.2 = x3.2.1 := walk_adjacent hL (L' ++ [x1]) [] x2 x3 (by simpa using hLeq)
  have hne12 : x2.1 ≠ x1.1 := walk_adjacent_tile_ne hne hL L' [x3] x1 x2 (by simpa using hLeq)
  have hne23 : x3.1 ≠ x2.1 := walk_adjacent_tile_ne hne hL (L' ++ [x1]) [] x2 x3 (by simpa using hLeq)
  have sd1 := hstep x1 (by rw [hLeq]; simp)
  have sd2 := hstep x2 (by rw [hLeq]; simp)
  have sd3 := hstep x3 (by rw [hLeq]; simp)
  have hp3 := hpar x3 (by rw [hLeq]; simp)
  obtain ⟨kk, fi, g, hfk, hgk, hgf, hk, hf, hleft, hbt3⟩ := sd3
  obtain ⟨kk1, fi1, g1, -, -, -, -, -, -, hbt1⟩ := sd1
  obtain ⟨kk2, fi2, g2, -, -, -, -, -, -, hbt2⟩ := sd2
  have hc : dist x3.2.1 x3.2.2 = sideOpp D.model 2 :=
    tok_len_c S (t := elemTok D α β x3) hbt3 (by rw [← e3]; rfl)
  obtain ⟨g', hseg, kk', fi', hfk', hgk', hgf', hk', hf', hbt3'⟩ :=
    last_apex S hori hx3 hp3 ⟨kk, fi, g, hfk, hgk, hgf, hk, hf, hleft, hbt3⟩ hc
  have t1 : BaseTok D p q (angOf α β γ) (lenOf (ta e f) (tb e f) (tc e f)) .c .A .B x3.1
      x3.2.1 (D.target.pts q) ((D.tile x3.1).pts g') := by
    have := hbt3'
    rw [← e3] at this
    rw [hx3] at this
    exact this
  have t2 : BaseTok D p q (angOf α β γ) (lenOf (ta e f) (tb e f) (tc e f)) .c .A .B x2.1
      x2.2.1 x3.2.1 ((D.tile x2.1).pts g2) := by
    have := hbt2
    rw [← e2] at this
    rw [← hadj23]
    exact this
  have t3 : BaseTok D p q (angOf α β γ) (lenOf (ta e f) (tb e f) (tc e f))
      (elemTok D α β x1).side (elemTok D α β x1).left (elemTok D α β x1).right x1.1
      x1.2.1 x2.2.1 ((D.tile x1.1).pts g1) := by
    rw [← hadj12]; exact hbt1
  have hlr : ((elemTok D α β x1).side = .b ∧ (elemTok D α β x1).right = .A) ∨
      ((elemTok D α β x1).side = .c ∧ (elemTok D α β x1).right = .A) ∨
      ((elemTok D α β x1).side = .b ∧ (elemTok D α β x1).right = .G ∧ (elemTok D α β x1).left = .A) := by
    rw [← e1]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hY
    rcases hY with rfl | rfl | rfl <;> simp [Tok.left, Tok.side, Tok.right]
  have t1' := t1.reflect
  have t2' := t2.reflect
  have t3' := t3.reflect
  exact w2_holds S.swap he2 hf3 hR2 hne12.symm hlr t1' t2' t3'

#print axioms walk_noW2
#print axioms walk_noW2m


/-- **Theorem U2 (oriented form).** No `CongruentDissection` of `T_M(e,f)` by `(ef, f²−e², f²)` with `e ≥ 2` and
`2Me ≤ f + 2`, the target positively oriented on `p → q`. -/
theorem no_tiling_U2_oriented (D : CongruentDissection N) (e f M : ℕ) (he : 2 ≤ e) (hef : e < f)
    (hcop : Nat.Coprime e f) (hM : 1 ≤ M)
    (hsa : sideOpp D.model 0 = (ta e f : ℝ)) (hsb : sideOpp D.model 1 = (tb e f : ℝ))
    (hsc : sideOpp D.model 2 = (tc e f : ℝ))
    {p q r : Fin 3} (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (hbase : dist (D.target.pts p) (D.target.pts q) = ((M * e * (3 * f ^ 2 - e ^ 2) : ℕ) : ℝ))
    (hlegL : dist (D.target.pts p) (D.target.pts r) = ((M * f ^ 3 : ℕ) : ℝ))
    (hlegR : dist (D.target.pts q) (D.target.pts r) = ((M * f ^ 3 : ℕ) : ℝ))
    (hori : 0 < cross (D.target.pts q - D.target.pts p) (D.target.pts r - D.target.pts p))
    (hd : 2 * M * e ≤ f + 2) : False := by
  classical
  have hf3 : 3 ≤ f := by omega
  have S := BandSetup.of_dims D e f M (by omega) hef hcop hM hsa hsb hsc hpq hpr hqr hbase hlegL hlegR
  have hori' : 0 < crs (toV2 (D.target.pts q - D.target.pts p)) (toV2 (D.target.pts r - D.target.pts p)) := by
    rw [crs_toV2]; exact hori
  obtain ⟨L, hL, hpar, hnd, hstep⟩ := base_walk S hori'
  set α := modelAlpha (e : ℝ) f
  set β := modelBeta (e : ℝ) f
  set γ := 2 * α + β
  have hbt : ∀ x ∈ L, ∃ Z, BaseTok D p q (angOf α β γ) (lenOf (ta e f) (tb e f) (tc e f))
      (elemTok D α β x).side (elemTok D α β x).left (elemTok D α β x).right x.1 x.2.1 x.2.2 Z := by
    intro x hx
    obtain ⟨kk, fi, g, -, -, -, -, -, -, hb⟩ := hstep x hx
    exact ⟨_, hb⟩
  have htot := walk_total (M := M) (r := r) hL hbt hbase
  obtain ⟨τ, hτ0, hτ1, hτ2⟩ := exists_perm_pqr p q r hpq hpr hqr
  have heR : (1:ℝ) ≤ e := by exact_mod_cast (by omega : 1 ≤ e)
  have hMR : (0:ℝ) < M := by exact_mod_cast hM
  have hbaseR : dist (D.target.pts p) (D.target.pts q) =
      (M:ℝ) * ((e:ℝ) * (3 * (f:ℝ) ^ 2 - (e:ℝ) ^ 2)) := by
    rw [hbase]
    have : e ^ 2 ≤ 3 * f ^ 2 := by nlinarith
    push_cast [Nat.cast_sub this]; ring
  have hlegLR : dist (D.target.pts p) (D.target.pts r) = (M:ℝ) * (f:ℝ) ^ 3 := by rw [hlegL]; push_cast; ring
  have hlegRR : dist (D.target.pts q) (D.target.pts r) = (M:ℝ) * (f:ℝ) ^ 3 := by rw [hlegR]; push_cast; ring
  have hMod : HasSides D.model ((e:ℝ) * f) ((f:ℝ) ^ 2 - (e:ℝ) ^ 2) ((f:ℝ) ^ 2) := by
    refine ⟨Equiv.refl _, ?_, ?_, ?_⟩
    · show sideOpp D.model 0 = _
      rw [hsa]; simp [ta]
    · show sideOpp D.model 1 = _
      rw [hsb, tb_real e f hef]
    · show sideOpp D.model 2 = _
      rw [hsc]; simp [tc]
  obtain ⟨x₀, t, h0, hend, hrun, -⟩ := thm_siderunall_T_pinned e f (by omega) hef hcop (s := (M:ℝ)) hMR D
    τ (by rw [hτ1, hτ2]; exact hlegRR) (by rw [hτ2, hτ0, dist_comm]; exact hlegLR)
    (by rw [hτ0, hτ1]; exact hbaseR) hMod
  rw [hτ0, hτ1] at hrun
  rw [← hbaseR] at hend
  have hrc := run_count S hori hL hnd h0 hend hrun
  have hC : f ≤ countC (L.map (elemTok D α β)) := by
    have := count_add_le_countC (L.map (elemTok D α β))
    rcases hrc with h | h <;> omega
  by_cases hlt : 2 * M * e < f
  · exact b1_thin e f M (by omega) hef hcop hM hlt _ htot hC
  have hlo : f ≤ 2 * M * e := by omega
  have hhi : 2 * M * e < f + e := by
    by_contra hh
    have he2' : e = 2 := by omega
    subst he2'
    have h2f : 2 ∣ f := ⟨2 * M - 1, by omega⟩
    have := Nat.Coprime.eq_one_of_dvd hcop h2f
    omega
  obtain ⟨hno, hcount⟩ := b1_of_total e f M (by omega) hef hcop hM hlo hhi _ htot hC
  have hlen : 3 ≤ (L.map (elemTok D α β)).length := by
    have := countC_le_length (L.map (elemTok D α β))
    omega
  obtain ⟨x, L1, hxL⟩ : ∃ x L1, L = x :: L1 := by
    rcases L with _ | ⟨x, L1⟩
    · simp at hlen
    · exact ⟨x, L1, rfl⟩
  obtain ⟨L2, y, hyL⟩ : ∃ L2 y, L = L2 ++ [y] := by
    rcases List.eq_nil_or_concat L with h | ⟨L2, y, h⟩
    · rw [h] at hxL; simp at hxL
    · exact ⟨L2, y, by rw [h, List.concat_eq_append]⟩
  have hx0 : x.2.1 = D.target.pts p := walk_first hL x L1 hxL
  have hy1 : y.2.2 = D.target.pts q := walk_last hL L2 y hyL
  have hfirst : ∃ t, (L.map (elemTok D α β)).head? = some t ∧ okFirst t :=
    ⟨elemTok D α β x, by rw [hxL]; rfl, (okFirst_iff _).2 (first_left_B S hx0 (hstep x (by rw [hxL]; simp)))⟩
  have hlast : ∃ t, (L.map (elemTok D α β)).getLast? = some t ∧ okLast t :=
    ⟨elemTok D α β y, by rw [hyL]; simp, (okLast_iff _).2 (last_right_B S hy1 (hstep y (by rw [hyL]; simp)))⟩
  have h2a : 2 * (ta e f : ℝ) < ((M * f ^ 3 : ℕ) : ℝ) := by
    unfold ta
    have h : 2 * (e * f) < M * f ^ 3 := by
      have h1 : e * f < f * f := Nat.mul_lt_mul_of_pos_right hef (by omega)
      have h2 : 2 * (f * f) ≤ f ^ 3 := by
        have : f ^ 3 = f * (f * f) := by ring
        rw [this]; nlinarith [Nat.mul_le_mul_right (f * f) hf3]
      have h3 : f ^ 3 ≤ M * f ^ 3 := Nat.le_mul_of_pos_left _ hM
      omega
    exact_mod_cast h
  rcases U2_core' f (2 * M * e) _ hno hfirst hlast hrc hcount hlen hd with h | h | h | h
  · exact walk_noC0 S hori' hL hpar hstep h
  · exact walk_noC0m S hori' hL hpar hstep h
  · exact walk_noW2 S he hf3 (by rw [hlegL]; exact h2a) hori' hL hpar hstep h
  · exact walk_noW2m S he hf3 (by rw [hlegR]; exact h2a) hori' hL hpar hstep h

/-- **Theorem U2.** No `CongruentDissection` of the isosceles triangle `T_M(e,f)` (base `[p,q]` of length
`M e (3f² − e²)`, legs `M f³`) by copies of `(ef, f²−e², f²)`, for `e ≥ 2`, `M ≥ 1`, `2Me ≤ f + 2` (coprime
`e < f`).  Reflections allowed, any number of tiles. -/
theorem no_tiling_U2 (D : CongruentDissection N) (e f M : ℕ) (he : 2 ≤ e) (hef : e < f)
    (hcop : Nat.Coprime e f) (hM : 1 ≤ M)
    (hsa : sideOpp D.model 0 = (ta e f : ℝ)) (hsb : sideOpp D.model 1 = (tb e f : ℝ))
    (hsc : sideOpp D.model 2 = (tc e f : ℝ))
    {p q r : Fin 3} (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (hbase : dist (D.target.pts p) (D.target.pts q) = ((M * e * (3 * f ^ 2 - e ^ 2) : ℕ) : ℝ))
    (hlegL : dist (D.target.pts p) (D.target.pts r) = ((M * f ^ 3 : ℕ) : ℝ))
    (hlegR : dist (D.target.pts q) (D.target.pts r) = ((M * f ^ 3 : ℕ) : ℝ))
    (hd : 2 * M * e ≤ f + 2) : False := by
  have hne0 := dims_cross_ne D e f M he hef hM hbase hlegL hlegR
  rcases lt_or_gt_of_ne hne0 with hneg | hpos
  · refine no_tiling_U2_oriented D e f M he hef hcop hM hsa hsb hsc (p := q) (q := p) (r := r)
      hpq.symm hqr hpr (by rw [dist_comm]; exact hbase) hlegR hlegL ?_ hd
    have : cross (D.target.pts p - D.target.pts q) (D.target.pts r - D.target.pts q) =
        - cross (D.target.pts q - D.target.pts p) (D.target.pts r - D.target.pts p) := by
      simp only [cross, PiLp.sub_apply]; ring
    rw [this]; linarith
  · exact no_tiling_U2_oriented D e f M he hef hcop hM hsa hsb hsc hpq hpr hqr hbase hlegL hlegR hpos hd

#print axioms no_tiling_U2

end Erdos634.LaczJunction.Walk
