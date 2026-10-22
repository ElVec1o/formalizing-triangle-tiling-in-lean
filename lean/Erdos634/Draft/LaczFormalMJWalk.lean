import Erdos634.Draft.LaczFormalMJBridge

/-!
# From the base walk to token sequences, and the rule `M(j)` for the walk

Erdős #634, base-`β` band, rule `M(j)`.  Credit: AI assistant (item 3, band program, rule `M(j)`), Beeson–Roșu, Beeson,
Laczkovich, Paliy.  UNAUDITED.  Axiom-clean; no `sorry`.

* `walk_prefix`: if the token word of a walk begins with `j` copies of `cBA` followed by a token `Xt`, there are
  sequences `tile, P, Z` of `BaseTok`s for the first `j` entries and a `BaseTok` of type `Xt` at entry `j`.
-/

namespace Erdos634.LaczMJ

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.LaczJunction Erdos634.LaczJunction.Walk
  Erdos634.LaczJunction.Grammar Erdos634.Draft.TraceCovering Set Erdos634.Draft.LaczFormal.Graph

variable {N : ℕ}

theorem walk_prefix {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ} {p q : Fin 3} {d : V2} :
    ∀ (j : ℕ) (L : List (Fin N × Plane × Plane)) {X0 Yend : Plane},
      WalkT D.toDissection d X0 Yend L → (∀ x ∈ L, StepData D e f α β γ p q x) →
      ∀ Xt : Tok, (List.replicate j Tok.cBA ++ [Xt]) <+: L.map (elemTok D α β) →
      ∃ (tile : ℕ → Fin N) (P Z : ℕ → Plane), P 0 = X0 ∧
        (∀ k, k < j → BaseTok D p q (angOf α β γ) (lenOf (ta e f : ℝ) (tb e f : ℝ) (tc e f : ℝ))
          .c .B .A (tile k) (P k) (P (k + 1)) (Z k)) ∧
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

/-- Dropping the last entry of a walk. -/
theorem walk_init {D : Dissection N} {d : V2} {X Y : Plane} {L : List (Fin N × Plane × Plane)}
    (W : WalkT D d X Y L) : ∀ (s : List (Fin N × Plane × Plane)) (a : Fin N × Plane × Plane),
    L = s ++ [a] → WalkT D d X a.2.1 s := by
  induction W with
  | nil X => intro s a h; simp at h
  | @cons i X X' Y L hS W ih =>
    intro s a h
    cases s with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at h
      obtain ⟨rfl, hL⟩ := h
      exact WalkT.nil _
    | cons y s' =>
      simp only [List.cons_append, List.cons.injEq] at h
      obtain ⟨rfl, hL⟩ := h
      exact WalkT.cons hS (ih s' a hL)

theorem walk_suffix {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ} {p q : Fin 3} {d : V2} :
    ∀ (k : ℕ) (L : List (Fin N × Plane × Plane)) {X0 Yend : Plane},
      WalkT D.toDissection d X0 Yend L → (∀ x ∈ L, StepData D e f α β γ p q x) →
      ∀ Xt : Tok, ([Xt] ++ List.replicate k Tok.cAB) <:+ L.map (elemTok D α β) →
      ∃ (tile : ℕ → Fin N) (P Z : ℕ → Plane), P 0 = Yend ∧
        (∀ i, i < k → BaseTok D q p (angOf α β γ) (lenOf (ta e f : ℝ) (tb e f : ℝ) (tc e f : ℝ))
          .c .B .A (tile i) (P i) (P (i + 1)) (Z i)) ∧
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
      have hrep : [Xt] ++ List.replicate (k + 1) Tok.cAB =
          ([Xt] ++ List.replicate k Tok.cAB) ++ [Tok.cAB] := by
        rw [List.replicate_succ', List.append_assoc]
      rw [hrep] at ht
      simp only [List.map_cons, List.map_nil] at ht
      have h3 : t ++ ([Xt] ++ List.replicate k Tok.cAB) ++ [Tok.cAB] = s'.reverse.map (elemTok D α β) ++ [elemTok D α β a] := by
        rw [← ht]; simp [List.append_assoc]
      have h4 : [Tok.cAB] = [elemTok D α β a] := List.append_inj_right' h3 (by simp)
      have h5 : t ++ ([Xt] ++ List.replicate k Tok.cAB) = s'.reverse.map (elemTok D α β) :=
        List.append_inj_left' h3 (by simp)
      have hca : elemTok D α β a = Tok.cAB := by simpa using h4.symm
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

/-- **No walk begins `cBA^{m+1} X`, `X ∈ {bAG, cAB, bGA}`** (the rule `M(m+1)` for the base walk). -/
theorem walk_noMJ {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ} {p q r : Fin 3}
    (S : BandSetup D e f α β γ p q r) {m : ℕ} (hje : m + 1 ≤ e)
    (hbase : ((m + 1 : ℕ) : ℝ) * tc e f < dist (D.target.pts p) (D.target.pts q))
    (hleg : ((m + 1 : ℕ) : ℝ) * ta e f < dist (D.target.pts p) (D.target.pts r))
    {L : List (Fin N × Plane × Plane)}
    (hL : WalkT D.toDissection (toV2 (D.target.pts q - D.target.pts p)) (D.target.pts p) (D.target.pts q) L)
    (hstep : ∀ x ∈ L, StepData D e f α β γ p q x) :
    ¬ winM (m + 1) (L.map (elemTok D α β)) := by
  rintro ⟨X, hX, hpre⟩
  obtain ⟨tile, P, Z, hP0, htok, K, Zy, hY⟩ := walk_prefix (m + 1) L hL hstep X hpre
  have hlr : (X.side = .b ∧ X.left = .A) ∨ (X.side = .c ∧ X.left = .A) ∨
      (X.side = .b ∧ X.left = .G ∧ X.right = .A) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hX
    rcases hX with rfl | rfl | rfl <;> simp [Tok.left, Tok.side, Tok.right]
  exact mj_holds S hje hbase hleg tile P Z hP0 htok hlr hY

/-- **No walk ends `X cAB^{m+1}`, `X ∈ {bGA, cBA, bAG}`** (the mirror rule). -/
theorem walk_noMJm {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ} {p q r : Fin 3}
    (S : BandSetup D e f α β γ p q r) {m : ℕ} (hje : m + 1 ≤ e)
    (hbase : ((m + 1 : ℕ) : ℝ) * tc e f < dist (D.target.pts p) (D.target.pts q))
    (hleg : ((m + 1 : ℕ) : ℝ) * ta e f < dist (D.target.pts q) (D.target.pts r))
    {L : List (Fin N × Plane × Plane)}
    (hL : WalkT D.toDissection (toV2 (D.target.pts q - D.target.pts p)) (D.target.pts p) (D.target.pts q) L)
    (hstep : ∀ x ∈ L, StepData D e f α β γ p q x) :
    ¬ winMm (m + 1) (L.map (elemTok D α β)) := by
  rintro ⟨X, hX, hsuf⟩
  obtain ⟨tile, P, Z, hP0, htok, K, Zy, hY⟩ := walk_suffix (m + 1) L hL hstep X hsuf
  have hlr : (X.side = .b ∧ X.right = .A) ∨ (X.side = .c ∧ X.right = .A) ∨
      (X.side = .b ∧ X.right = .G ∧ X.left = .A) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hX
    rcases hX with rfl | rfl | rfl <;> simp [Tok.left, Tok.side, Tok.right]
  have hbase' : ((m + 1 : ℕ) : ℝ) * tc e f < dist (D.target.pts q) (D.target.pts p) := by
    rw [dist_comm]; exact hbase
  exact mj_holds S.swap hje hbase' hleg tile P Z hP0 htok hlr hY

end Erdos634.LaczMJ
