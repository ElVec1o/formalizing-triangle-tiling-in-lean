import Erdos634.Draft.LaczFormalUDims

/-!
# The band theorem, conditional on the rule `M(j)` of the hand proof

**Update 2026-10-21 (room LEAN_MJ): the hypothesis `MRule e f` is now a theorem, `MRule_holds e f`
(`LaczFormalMJFinal`), and `band_theorem_free` there is this theorem without the hypothesis.  The text below describes
the state before that proof.**

Erdős #634, base-`β` band.  Credit: AI assistant (item 3, band program: Band Lemma, Prop. B1, the induction `M(j)`),
Beeson–Roșu (Lemmas 28–37), Beeson, Laczkovich, Paliy, Zhang.  UNAUDITED.  Axiom-clean; no `sorry`.

`PROOF_BAND.md` ((private working notes, not included); audit `AUDIT_BAND_2026-10-21`: sound with gaps):
for `e ≥ 2`, `M ≥ 2`, `f ≤ 2Me < f + e` the triangle `T_M(e,f)` has no dissection.  The proof is
(1) B1 (no `a`-token, `2Me` `c`-tokens): **now Lean** (`b1_of_total`, from `band_lemma` and `thm_siderunall`);
(2) the corner tokens, the walk, the run: **Lean** (`LaczFormalWalk*`);
(3) a counting step: **Lean** (`band_counting`): the word begins `cBA^i X` (`X ≠ cBA`) with `1 ≤ i ≤ d`, or ends
    `X cAB^k` with `1 ≤ k ≤ d`, where `d = 2Me − f ≤ e − 1`;
(4) the rule `M(j)`, `1 ≤ j ≤ e`: no base word begins `cBA^j X` with `X ∈ {bAG, cAB, bGA}` (and the mirror).
    `j = 1` is C0 (Lean, `walk_noC0`), `j = 2` is W2 (Lean since 2026-10-21: `walk_noW2`, `no_tiling_U2`) and `j = 3` is W3 (hand).  **(4) is the only hypothesis**
    of `band_theorem`, as the Prop `MRule e f`.

## Principle E (the planar chord cover), as it exists in Lean
`PROOF_BAND.md` §2 uses (E1) the far side of a wall is covered by consecutive edges starting at the start point
and summing to the length, and (E2) the cover ends exactly at an interior end where the continuation lies inside a
far-side tile.  A "fault segment" is a wall in the sense of `TraceCovering`: `hwall : ∀ x ∈ (s,t), ∀ i, X + x u ∉
interior (tile i)`.  Lean: (E1 sum) `L3_sum`, `L3_sum_of_edges`, `L3_two_b` (`LaczFormalL3`, from `TraceCovering.wall_sum`);
(E1 start) `LaczJunction.exists_start_edge` (`LaczFormalJunctionAdj`); (E2) `nstr_end_outside`, `nstr_end_across`
(`LaczFormalJunctionWall`); single-edge case `far_edge_gen`, `far_edge_exists`.  What is NOT in Lean is the *use* of E
inside `M(j)`: identifying the row tiles `A_i`, `T_i`, `N_i` and the wedge fillings along the chords `l`.  That
tile-placement layer (the induction on rows `r`, Claims Z and A, Step B) is the content of `MRule`.

`MRule` is stated only inside the band of the hand proof: `M ≥ 2`, `f ≤ 2Me < f+e` and the target of `T_M(e,f)`
(base `Me(3f²−e²)`, legs `Mf³`); tilings exist for `M ≥ f`, outside this range.

The hypotheses of `MRule` are those under which the hand proof is argued: `a < b` (the hand proof needs it;
it fails for `M = 1` with `f/e < φ`, so the band theorem is stated for `M ≥ 2`, where `band_a_lt_b` gives it),
no `a`-token on the base, and the legs longer than `j·a`.
-/

namespace Erdos634.LaczJunction.Walk

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.LaczJunction Erdos634.LaczJunction.Grammar
open Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.W2E1 Erdos634.Draft.SideRunG
  Erdos634.BaseBetaTargetCoord Erdos634.Draft.FDBBaseBetaE1

variable {N : ℕ}

/-- **The rule `M(j)`, `1 ≤ j ≤ e`, with its mirror (HAND RULE: `PROOF_BAND.md` §3; geometry NOT formalized).**
In the band setting with `a < b`, no `a`-token on the base and both legs longer than `j·a`, the base walk
does not begin `cBA^j X` and does not end `X cAB^j`, `X ∈ {bAG, cAB, bGA}` resp. `{bGA, cBA, bAG}`. -/
def MRule (e f : ℕ) : Prop :=
  2 ≤ e → ta e f < tb e f → ∀ (N : ℕ) (D : CongruentDissection N) (α β γ : ℝ) (p q r : Fin 3),
    BandSetup D e f α β γ p q r →
    ∀ M : ℕ, 2 ≤ M → f ≤ 2 * M * e → 2 * M * e < f + e →
    dist (D.target.pts p) (D.target.pts q) = ((M * e * (3 * f ^ 2 - e ^ 2) : ℕ) : ℝ) →
    dist (D.target.pts p) (D.target.pts r) = ((M * f ^ 3 : ℕ) : ℝ) →
    dist (D.target.pts q) (D.target.pts r) = ((M * f ^ 3 : ℕ) : ℝ) →
    0 < crs (toV2 (D.target.pts q - D.target.pts p)) (toV2 (D.target.pts r - D.target.pts p)) →
    ∀ (L : List (Fin N × Plane × Plane)),
      WalkT D.toDissection (toV2 (D.target.pts q - D.target.pts p)) (D.target.pts p)
        (D.target.pts q) L →
      (∀ x ∈ L, StepData D e f α β γ p q x) →
      (∀ t ∈ L.map (elemTok D α β), t.side ≠ .a) →
      ∀ j : ℕ, 1 ≤ j → j ≤ e →
        (j : ℝ) * ta e f < dist (D.target.pts p) (D.target.pts r) →
        (j : ℝ) * ta e f < dist (D.target.pts q) (D.target.pts r) →
        ¬ winM j (L.map (elemTok D α β)) ∧ ¬ winMm j (L.map (elemTok D α β))

/-- **The band theorem, conditional on `MRule e f` (oriented form).**  For `e ≥ 2`, `M ≥ 2`, `f ≤ 2Me < f + e`
(coprime `e < f`) there is no `CongruentDissection` of `T_M(e,f)` by `(ef, f²−e², f²)`. -/
theorem band_theorem_oriented (D : CongruentDissection N) (e f M : ℕ) (hMrule : MRule e f) (he : 2 ≤ e) (hef : e < f)
    (hcop : Nat.Coprime e f) (hM2 : 2 ≤ M)
    (hsa : sideOpp D.model 0 = (ta e f : ℝ)) (hsb : sideOpp D.model 1 = (tb e f : ℝ))
    (hsc : sideOpp D.model 2 = (tc e f : ℝ))
    {p q r : Fin 3} (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (hbase : dist (D.target.pts p) (D.target.pts q) = ((M * e * (3 * f ^ 2 - e ^ 2) : ℕ) : ℝ))
    (hlegL : dist (D.target.pts p) (D.target.pts r) = ((M * f ^ 3 : ℕ) : ℝ))
    (hlegR : dist (D.target.pts q) (D.target.pts r) = ((M * f ^ 3 : ℕ) : ℝ))
    (hori : 0 < cross (D.target.pts q - D.target.pts p) (D.target.pts r - D.target.pts p))
    (hlo : f ≤ 2 * M * e) (hhi : 2 * M * e < f + e) : False := by
  classical
  have hM : 1 ≤ M := by omega
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
  -- the run
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
  obtain ⟨hno, hcount⟩ := b1_of_total e f M (by omega) hef hcop hM hlo hhi _ htot hC
  have hlen : 2 ≤ (L.map (elemTok D α β)).length := by
    have := countC_le_length (L.map (elemTok D α β))
    have h2 : 2 ≤ f := by omega
    have : 2 * 2 ≤ 2 * M * e := by nlinarith
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
  have hab : ta e f < tb e f := band_a_lt_b e f M (by omega) hM2 hhi
  have hcnt' := band_counting f (2 * M * e - f) (2 * M * e) _ hno hfirst hlast hrc hcount (by omega)
  have hlegs : ∀ j : ℕ, 1 ≤ j → j ≤ e →
      (j : ℝ) * ta e f < dist (D.target.pts p) (D.target.pts r) ∧
      (j : ℝ) * ta e f < dist (D.target.pts q) (D.target.pts r) := by
    intro j hj1 hje
    have hnat : j * ta e f < M * f ^ 3 := by
      unfold ta
      have h1 : j * (e * f) ≤ e * (e * f) := Nat.mul_le_mul_right _ hje
      have h2 : e * (e * f) < f ^ 3 := by
        have h0 : e * e < f * f := Nat.mul_self_lt_mul_self hef
        have hf : 0 < f := by omega
        calc e * (e * f) = (e * e) * f := by ring
          _ < (f * f) * f := Nat.mul_lt_mul_of_pos_right h0 hf
          _ = f ^ 3 := by ring
      have h3 : f ^ 3 ≤ M * f ^ 3 := Nat.le_mul_of_pos_left _ (by omega)
      omega
    have hr : (j : ℝ) * ta e f < ((M * f ^ 3 : ℕ) : ℝ) := by exact_mod_cast hnat
    exact ⟨by rw [hlegL]; exact hr, by rw [hlegR]; exact hr⟩
  have hd : 2 * M * e - f ≤ e - 1 := by omega
  rcases hcnt' with ⟨i, hi1, hid, hw⟩ | ⟨k, hk1, hkd, hw⟩
  · have hl := hlegs i hi1 (by omega)
    exact (hMrule he hab N D α β γ p q r S M hM2 hlo hhi hbase hlegL hlegR hori' L hL hstep hno i hi1 (by omega) hl.1 hl.2).1 hw
  · have hl := hlegs k hk1 (by omega)
    exact (hMrule he hab N D α β γ p q r S M hM2 hlo hhi hbase hlegL hlegR hori' L hL hstep hno k hk1 (by omega) hl.1 hl.2).2 hw


/-- **The band theorem, conditional on `MRule e f`.**  For `e ≥ 2`, `M ≥ 2`, `f ≤ 2Me < f + e` (coprime `e < f`):
no `CongruentDissection` of `T_M(e,f)` (base `[p,q]` of length `M e (3f²−e²)`, legs `M f³`) by copies of
`(ef, f²−e², f²)`.  Everything except `MRule e f` is proved in Lean (uses `thm_siderunall`, the Band Lemma,
rule C0). -/
theorem band_theorem (D : CongruentDissection N) (e f M : ℕ) (hMrule : MRule e f) (he : 2 ≤ e)
    (hef : e < f) (hcop : Nat.Coprime e f) (hM2 : 2 ≤ M)
    (hsa : sideOpp D.model 0 = (ta e f : ℝ)) (hsb : sideOpp D.model 1 = (tb e f : ℝ))
    (hsc : sideOpp D.model 2 = (tc e f : ℝ))
    {p q r : Fin 3} (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (hbase : dist (D.target.pts p) (D.target.pts q) = ((M * e * (3 * f ^ 2 - e ^ 2) : ℕ) : ℝ))
    (hlegL : dist (D.target.pts p) (D.target.pts r) = ((M * f ^ 3 : ℕ) : ℝ))
    (hlegR : dist (D.target.pts q) (D.target.pts r) = ((M * f ^ 3 : ℕ) : ℝ))
    (hlo : f ≤ 2 * M * e) (hhi : 2 * M * e < f + e) : False := by
  have hne0 := dims_cross_ne D e f M he hef (by omega) hbase hlegL hlegR
  rcases lt_or_gt_of_ne hne0 with hneg | hpos
  · refine band_theorem_oriented D e f M hMrule he hef hcop hM2 hsa hsb hsc (p := q) (q := p) (r := r)
      hpq.symm hqr hpr (by rw [dist_comm]; exact hbase) hlegR hlegL ?_ hlo hhi
    have : cross (D.target.pts p - D.target.pts q) (D.target.pts r - D.target.pts q) =
        - cross (D.target.pts q - D.target.pts p) (D.target.pts r - D.target.pts p) := by
      simp only [cross, PiLp.sub_apply]; ring
    rw [this]; linarith
  · exact band_theorem_oriented D e f M hMrule he hef hcop hM2 hsa hsb hsc hpq hpr hqr hbase hlegL hlegR
      hpos hlo hhi

/-- The hypothesis `MRule e f` for `j = 1` is C0, proved: `walk_noC0` (mirror `walk_noC0m`). -/
theorem MRule_one_prefix {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ} {p q r : Fin 3}
    (S : BandSetup D e f α β γ p q r)
    (hori : 0 < crs (toV2 (D.target.pts q - D.target.pts p)) (toV2 (D.target.pts r - D.target.pts p)))
    {L : List (Fin N × Plane × Plane)}
    (hL : WalkT D.toDissection (toV2 (D.target.pts q - D.target.pts p)) (D.target.pts p)
      (D.target.pts q) L)
    (hpar : ∀ x ∈ L, ∃ s t : ℝ, 0 ≤ s ∧ s < t ∧ t ≤ 1 ∧
        x.2.1 = D.target.pts p + s • (D.target.pts q - D.target.pts p) ∧
        x.2.2 = D.target.pts p + t • (D.target.pts q - D.target.pts p))
    (hstep : ∀ x ∈ L, StepData D e f α β γ p q x) :
    ¬ winM 1 (L.map (elemTok D α β)) ∧ ¬ winMm 1 (L.map (elemTok D α β)) := by
  constructor
  · rintro ⟨X, hX, h⟩
    exact walk_noC0 S hori hL hpar hstep ⟨X, hX, by simpa using h⟩
  · rintro ⟨X, hX, h⟩
    exact walk_noC0m S hori hL hpar hstep ⟨X, hX, by simpa using h⟩

#print axioms band_theorem
#print axioms MRule_one_prefix

end Erdos634.LaczJunction.Walk
