import Erdos634.Draft.LaczFormalALBridge

/-!
# From the base walk to `aBG` token sequences, and Lemma A(j) for the walk

Erdős #634, base-`β` row, thick analogue of `M(j)`.  Credit: AI assistant (Lemma A(k) proposal), Beeson–Roșu, Beeson,
Laczkovich, Paliy.  UNAUDITED.  Axiom-clean; no `sorry`.  Port of `LaczFormalMJWalk` (`cBA`/`cAB`) to `aBG`/`aGB`.

* `walk_prefixA`: a walk whose token word begins `aBG^j X` gives `BaseTok` data for the first `j` entries and for `X`.
* `walk_suffixA`: the mirror, from the right end (`X aGB^k`).
* `winA j w`: `w` begins `aBG^j X`, `X ∈ {bAG, bGA, cAB, aGB}` (left angle `α` or `γ`); `winAm`: the mirror.
* `walk_noA`, `walk_noAm`: no base walk satisfies them (`j ≤ f − 1`, base `> j a`, legs `> j c`).
-/

namespace Erdos634.LaczAL

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.LaczJunction Erdos634.LaczJunction.Walk
  Erdos634.LaczJunction.Grammar Erdos634.Draft.TraceCovering Erdos634.LaczMJ Set Erdos634.Draft.LaczFormal.Graph

variable {N : ℕ}

/-- The base word begins `aBG^j X` with `X` a token whose left angle is `α` or `γ`. -/
def winA (j : ℕ) (w : List Tok) : Prop :=
  ∃ X ∈ [Tok.bAG, Tok.bGA, Tok.cAB, Tok.aGB], (List.replicate j Tok.aBG ++ [X]) <+: w

/-- The mirror: the base word ends `X aGB^k` with `X` a token whose right angle is `α` or `γ`. -/
def winAm (k : ℕ) (w : List Tok) : Prop :=
  ∃ X ∈ [Tok.bAG, Tok.bGA, Tok.cBA, Tok.aBG], ([X] ++ List.replicate k Tok.aGB) <:+ w

theorem walk_prefixA {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ} {p q : Fin 3} {d : V2} :
    ∀ (j : ℕ) (L : List (Fin N × Plane × Plane)) {X0 Yend : Plane},
      WalkT D.toDissection d X0 Yend L → (∀ x ∈ L, StepData D e f α β γ p q x) →
      ∀ Xt : Tok, (List.replicate j Tok.aBG ++ [Xt]) <+: L.map (elemTok D α β) →
      ∃ (tile : ℕ → Fin N) (P Z : ℕ → Plane), P 0 = X0 ∧
        (∀ k, k < j → BaseTok D p q (angOf α β γ) (lenOf (ta e f : ℝ) (tb e f : ℝ) (tc e f : ℝ))
          .a .B .G (tile k) (P k) (P (k + 1)) (Z k)) ∧
        ∃ K Zy, BaseTok D p q (angOf α β γ) (lenOf (ta e f : ℝ) (tb e f : ℝ) (tc e f : ℝ))
          Xt.side Xt.left Xt.right (tile j) (P j) K Zy := by
  intro j
  induction j with
  | zero =>
    intro L X0 Yend hL hstep Xt hpre
    rcases L with _ | ⟨x, L'⟩
    · simp at hpre
    · have hx0 : x.2.1 = X0 := walk_first hL x L' rfl
      simp only [List.replicate_zero, List.nil_append, List.map_cons] at hpre
      have htx : Xt = elemTok D α β x := (List.cons_prefix_cons.mp hpre).1
      obtain ⟨kk, fi, g, -, -, -, -, -, -, hbt⟩ := hstep x (by simp)
      refine ⟨fun _ => x.1, fun _ => x.2.1, fun _ => (D.tile x.1).pts g, hx0, fun k hk => absurd hk (by omega),
        x.2.2, (D.tile x.1).pts g, ?_⟩
      rw [htx]; exact hbt
  | succ j ih =>
    intro L X0 Yend hL hstep Xt hpre
    rcases L with _ | ⟨x, L'⟩
    · simp at hpre
    · have hx0 : x.2.1 = X0 := walk_first hL x L' rfl
      rw [List.replicate_succ, List.cons_append, List.map_cons] at hpre
      obtain ⟨hcx, hpre'⟩ := List.cons_prefix_cons.mp hpre
      obtain ⟨kk, fi, g, -, -, -, -, -, -, hbt⟩ := hstep x (by simp)
      -- the tail of the walk
      have hW' : WalkT D.toDissection d x.2.2 Yend L' := by
        cases hL with
        | cons hS W' => exact W'
      obtain ⟨tile', P', Z', hP0', htok', K, Zy, hlast⟩ :=
        ih L' hW' (fun y hy => hstep y (by simp [hy])) Xt hpre'
      refine ⟨fun k => match k with | 0 => x.1 | k + 1 => tile' k,
        fun k => match k with | 0 => x.2.1 | k + 1 => P' k,
        fun k => match k with | 0 => (D.tile x.1).pts g | k + 1 => Z' k, hx0, ?_, K, Zy, ?_⟩
      · intro k hk
        rcases k with _ | k
        · simp only []
          rw [hP0']
          have := hbt
          rw [← hcx] at this
          exact this
        · exact htok' k (by omega)
      · exact hlast


theorem walk_suffixA {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ} {p q : Fin 3} {d : V2} :
    ∀ (k : ℕ) (L : List (Fin N × Plane × Plane)) {X0 Yend : Plane},
      WalkT D.toDissection d X0 Yend L → (∀ x ∈ L, StepData D e f α β γ p q x) →
      ∀ Xt : Tok, ([Xt] ++ List.replicate k Tok.aGB) <:+ L.map (elemTok D α β) →
      ∃ (tile : ℕ → Fin N) (P Z : ℕ → Plane), P 0 = Yend ∧
        (∀ i, i < k → BaseTok D q p (angOf α β γ) (lenOf (ta e f : ℝ) (tb e f : ℝ) (tc e f : ℝ))
          .a .B .G (tile i) (P i) (P (i + 1)) (Z i)) ∧
        ∃ K Zy, BaseTok D q p (angOf α β γ) (lenOf (ta e f : ℝ) (tb e f : ℝ) (tc e f : ℝ))
          Xt.side Xt.right Xt.left (tile k) (P k) K Zy := by
  intro k
  induction k with
  | zero =>
    intro L X0 Yend hL hstep Xt hsuf
    obtain ⟨t, ht⟩ := hsuf
    rcases hc : L.reverse with _ | ⟨a, s'⟩
    · have : L = [] := by simpa using congrArg List.reverse hc
      rw [this] at ht; simp at ht
    · have hLa : L = s'.reverse ++ [a] := by simpa using congrArg List.reverse hc
      have hya : a.2.2 = Yend := walk_last hL s'.reverse a hLa
      rw [hLa, List.map_append] at ht
      simp only [List.replicate_zero, List.append_nil, List.map_cons, List.map_nil] at ht
      have h2 : [Xt] = [elemTok D α β a] := List.append_inj_right' ht (by simp)
      have hXa : Xt = elemTok D α β a := by simpa using h2
      obtain ⟨kk, fi, g, -, -, -, -, -, -, hbt⟩ := hstep a (by rw [hLa]; simp)
      refine ⟨fun _ => a.1, fun _ => a.2.2, fun _ => (D.tile a.1).pts g, hya, fun i hi => absurd hi (by omega),
        a.2.1, (D.tile a.1).pts g, ?_⟩
      rw [hXa]
      exact hbt.reflect
  | succ k ih =>
    intro L X0 Yend hL hstep Xt hsuf
    obtain ⟨t, ht⟩ := hsuf
    rcases hc : L.reverse with _ | ⟨a, s'⟩
    · have : L = [] := by simpa using congrArg List.reverse hc
      rw [this] at ht; simp at ht
    · have hLa : L = s'.reverse ++ [a] := by simpa using congrArg List.reverse hc
      have hya : a.2.2 = Yend := walk_last hL s'.reverse a hLa
      have hW' := walk_init hL s'.reverse a hLa
      rw [hLa, List.map_append] at ht
      have hrep : [Xt] ++ List.replicate (k + 1) Tok.aGB =
          ([Xt] ++ List.replicate k Tok.aGB) ++ [Tok.aGB] := by
        rw [List.replicate_succ', List.append_assoc]
      rw [hrep] at ht
      simp only [List.map_cons, List.map_nil] at ht
      have h3 : t ++ ([Xt] ++ List.replicate k Tok.aGB) ++ [Tok.aGB] = s'.reverse.map (elemTok D α β) ++ [elemTok D α β a] := by
        rw [← ht]; simp [List.append_assoc]
      have h4 : [Tok.aGB] = [elemTok D α β a] := List.append_inj_right' h3 (by simp)
      have h5 : t ++ ([Xt] ++ List.replicate k Tok.aGB) = s'.reverse.map (elemTok D α β) :=
        List.append_inj_left' h3 (by simp)
      have hca : elemTok D α β a = Tok.aGB := by simpa using h4.symm
      obtain ⟨tile', P', Z', hP0', htok', K, Zy, hlast⟩ :=
        ih s'.reverse hW' (fun y hy => hstep y (by rw [hLa]; simp [hy])) Xt ⟨t, h5⟩
      obtain ⟨kk, fi, g, -, -, -, -, -, -, hbt⟩ := hstep a (by rw [hLa]; simp)
      refine ⟨fun i => match i with | 0 => a.1 | i + 1 => tile' i,
        fun i => match i with | 0 => a.2.2 | i + 1 => P' i,
        fun i => match i with | 0 => (D.tile a.1).pts g | i + 1 => Z' i, hya, ?_, K, Zy, hlast⟩
      intro i hi
      rcases i with _ | i
      · simp only []
        rw [hP0']
        have := hbt
        rw [hca] at this
        exact this.reflect
      · exact htok' i (by omega)


open Erdos634.MirrorGauge in
/-- **Lemma A(j) for tokens, any orientation** (reflect the whole dissection if the target is clockwise). -/
theorem al_holds {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ} {p q r : Fin 3}
    (S : BandSetup D e f α β γ p q r)
    {m : ℕ} (hjf : m + 1 ≤ f - 1)
    (hbase : ((m + 1 : ℕ) : ℝ) * ta e f < dist (D.target.pts p) (D.target.pts q))
    (hleg : ((m + 1 : ℕ) : ℝ) * tc e f < dist (D.target.pts p) (D.target.pts r))
    (tile : ℕ → Fin N) (P Z : ℕ → Plane) (hP0 : P 0 = D.target.pts p)
    (htok : ∀ k, k < m + 1 → BaseTok D p q (angOf α β γ) (lenOf (ta e f : ℝ) (tb e f : ℝ) (tc e f : ℝ))
      .a .B .G (tile k) (P k) (P (k + 1)) (Z k))
    {x : Side} {l rr : Corner} {K Zy : Plane}
    (hlr : (x = .b ∧ l = .A) ∨ (x = .c ∧ l = .A) ∨ (x = .b ∧ l = .G) ∨ (x = .a ∧ l = .G))
    (hY : BaseTok D p q (angOf α β γ) (lenOf (ta e f : ℝ) (tb e f : ℝ) (tc e f : ℝ))
      x l rr (tile (m + 1)) (P (m + 1)) K Zy) : False := by
  have hne := tile_cross_ne D.target p q r S.hpq S.hpr S.hqr
  rcases lt_trichotomy (cross (D.target.pts q - D.target.pts p) (D.target.pts r - D.target.pts p)) 0 with
    hneg | hz | hpos
  · refine al_oriented (bandSetup_mirror S) ?_ hjf ?_ ?_ tile (fun k => mirrorPt (P k)) (fun k => mirrorPt (Z k))
      (by show mirrorPt (P 0) = _; rw [hP0, mirror_target_pts]) (fun k hk => basetok_mirror (htok k hk)) hlr
      (basetok_mirror hY)
    · rw [mirror_target_pts, mirror_target_pts, mirror_target_pts, mirrorPt_sub, mirrorPt_sub, cross_mirror]
      linarith
    · rw [mirror_target_pts, mirror_target_pts, mirrorPt_dist]; exact hbase
    · rw [mirror_target_pts, mirror_target_pts, mirrorPt_dist]; exact hleg
  · exact absurd hz hne
  · exact al_oriented S hpos hjf hbase hleg tile P Z hP0 htok hlr hY


/-- **No walk begins `aBG^{m+1} X`, `X ∈ {bAG, bGA, cAB, aGB}`** (Lemma A(m+1) for the base walk).
Scope note (diff audit): the statement quantifies over walks that CONTAIN an `X` token after the `aBG` run; a word that is
`aBG^n` with no following `X` satisfies it trivially.  Such an all-`aBG` word has total length `n·e·f`, and equating it with
the base `M·e·(3f²−e²)` gives `f ∣ M e²`, hence `f ∣ M` (coprimality), so it needs `M ≥ f`: it cannot occur for `M < f`,
the GAP region.  The allowed continuations after `aBG^j` (`j < f`) are exactly `aBG` or `cBA`. -/
theorem walk_noA {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ} {p q r : Fin 3}
    (S : BandSetup D e f α β γ p q r) {m : ℕ} (hjf : m + 1 ≤ f - 1)
    (hbase : ((m + 1 : ℕ) : ℝ) * ta e f < dist (D.target.pts p) (D.target.pts q))
    (hleg : ((m + 1 : ℕ) : ℝ) * tc e f < dist (D.target.pts p) (D.target.pts r))
    {L : List (Fin N × Plane × Plane)}
    (hL : WalkT D.toDissection (toV2 (D.target.pts q - D.target.pts p)) (D.target.pts p) (D.target.pts q) L)
    (hstep : ∀ x ∈ L, StepData D e f α β γ p q x) :
    ¬ winA (m + 1) (L.map (elemTok D α β)) := by
  rintro ⟨X, hX, hpre⟩
  obtain ⟨tile, P, Z, hP0, htok, K, Zy, hY⟩ := walk_prefixA (m + 1) L hL hstep X hpre
  have hlr : (X.side = .b ∧ X.left = .A) ∨ (X.side = .c ∧ X.left = .A) ∨ (X.side = .b ∧ X.left = .G) ∨
      (X.side = .a ∧ X.left = .G) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hX
    rcases hX with rfl | rfl | rfl | rfl <;> simp [Tok.left, Tok.side, Tok.right]
  exact al_holds S hjf hbase hleg tile P Z hP0 htok hlr hY

/-- **No walk ends `X aGB^{m+1}`, `X ∈ {bAG, bGA, cBA, aBG}`** (the mirror rule). -/
theorem walk_noAm {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ} {p q r : Fin 3}
    (S : BandSetup D e f α β γ p q r) {m : ℕ} (hjf : m + 1 ≤ f - 1)
    (hbase : ((m + 1 : ℕ) : ℝ) * ta e f < dist (D.target.pts p) (D.target.pts q))
    (hleg : ((m + 1 : ℕ) : ℝ) * tc e f < dist (D.target.pts q) (D.target.pts r))
    {L : List (Fin N × Plane × Plane)}
    (hL : WalkT D.toDissection (toV2 (D.target.pts q - D.target.pts p)) (D.target.pts p) (D.target.pts q) L)
    (hstep : ∀ x ∈ L, StepData D e f α β γ p q x) :
    ¬ winAm (m + 1) (L.map (elemTok D α β)) := by
  rintro ⟨X, hX, hsuf⟩
  obtain ⟨tile, P, Z, hP0, htok, K, Zy, hY⟩ := walk_suffixA (m + 1) L hL hstep X hsuf
  have hlr : (X.side = .b ∧ X.right = .A) ∨ (X.side = .c ∧ X.right = .A) ∨ (X.side = .b ∧ X.right = .G) ∨
      (X.side = .a ∧ X.right = .G) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hX
    rcases hX with rfl | rfl | rfl | rfl <;> simp [Tok.left, Tok.side, Tok.right]
  have hbase' : ((m + 1 : ℕ) : ℝ) * ta e f < dist (D.target.pts q) (D.target.pts p) := by
    rw [dist_comm]; exact hbase
  exact al_holds S.swap hjf hbase' hleg tile P Z hP0 htok hlr hY

end Erdos634.LaczAL
