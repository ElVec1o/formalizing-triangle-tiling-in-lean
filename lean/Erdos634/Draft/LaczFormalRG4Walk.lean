-- Draft/LaczFormalRG4Walk.lean -- Case IV (gamma = pi/3): walks of tiles along an edge of the polygon.  The junction of two consecutive tiles lies in the open edge;
-- the local step lemma `edge_consec` propagates (i) a {beta,gamma} type pair, (ii) alpha at the tail forwards, (iii) alpha at the head backwards, along the whole walk:
-- the four RULES R1 (pair copied from first to last tile), R1' (from last to first), R2 (alpha at the first tile's tail gives alpha at the last tile's tail), R3 (alpha at the last tile's head gives alpha at the first tile's head).
-- UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Lemma 4.3 and its proof, Fig. 3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalRG4Side

open scoped Classical
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ} [NeZero M]

/-- The tile `j` has type `a` at the point `U` (every corner of the tile located at `U` has type `a`). -/
def TyAt (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) (j : Fin N) (U : Plane) (a : Fin 3) : Prop :=
  ∀ k, (D.tile j).pts k = U → idx j k = a

theorem tyAt_iff {D : CongruentRegionDissection N} {idx : Fin N → Equiv.Perm (Fin 3)} {j : Fin N} {U : Plane} {k : Fin 3}
    (hk : (D.tile j).pts k = U) (a : Fin 3) : TyAt D idx j U a ↔ idx j k = a := by
  constructor
  · intro h; exact h k hk
  · intro h k' hk'
    have : k' = k := (D.tile j).indep.injective (hk'.trans hk.symm)
    rw [this]; exact h

/-- **The junction of consecutive tiles of a walk along an edge lies in the open edge.** -/
theorem junction_param (D : RegionDissection N) (P : ConvPoly M) (hreg : D.region = P.carrier) (i : Fin M) {j : Fin N} {X X' Y : Plane}
    {L' : List (Fin N × Plane × Plane)} (hY : Y = P.v (i + 1)) (hS : TriStep (D.tile j) (toV2 (P.e i)) X X')
    (W' : WalkT D (toV2 (P.e i)) X' Y L') (hL' : L' ≠ [])
    (hU : ∃ s : ℝ, 0 ≤ s ∧ toV2 (X - P.v i) = (s * (toV2 (P.e i)).1, s * (toV2 (P.e i)).2)) :
    ∃ t : ℝ, 0 < t ∧ t < 1 ∧ X' = (1 - t) • P.v i + t • P.v (i + 1) ∧
      ∃ s' : ℝ, 0 ≤ s' ∧ toV2 (X' - P.v i) = (s' * (toV2 (P.e i)).1, s' * (toV2 (P.e i)).2) := by
  classical
  obtain ⟨s, hs0, hsX⟩ := hU
  obtain ⟨-, -, -, -, -, -, -, -, hpar, -⟩ := id hS
  obtain ⟨c, hc, hcw⟩ := hpar.smul
  have hdX' : toV2 (X' - P.v i) = ((s + c) * (toV2 (P.e i)).1, (s + c) * (toV2 (P.e i)).2) := by
    have : toV2 (X' - P.v i) = ((toV2 (X' - X)).1 + (toV2 (X - P.v i)).1, (toV2 (X' - X)).2 + (toV2 (X - P.v i)).2) := by
      unfold toV2; ext <;> simp
    rw [this, hcw, hsX]; ext <;> simp <;> ring
  obtain ⟨T, hT0, hTe, hTpos⟩ := walkT_progress W'
  have hTpos' : 0 < T := hTpos hL'
  have hd0 : toV2 (P.e i) ≠ 0 := toV2_ne_zero (P.e_ne_zero P.three_le i)
  have hvert' : ∃ j k, (D.tile j).pts k = X' := by
    obtain ⟨kk, f, g, hk, hf, -⟩ := id hS
    exact ⟨j, f, hf⟩
  have hline' : crs (toV2 (P.e i)) (toV2 (X' - P.v i)) = 0 := by
    rw [hdX']; unfold crs; simp only; ring
  obtain ⟨t, ⟨ht0, ht1⟩, hXt⟩ := vertex_on_edge D P hreg i hvert' hline'
  have hne0 : t ≠ 0 := by
    rintro rfl
    have : toV2 (X' - P.v i) = 0 := by
      rw [hXt]; unfold toV2; ext <;> simp
    rw [hdX'] at this
    have h1 : (s + c) * (toV2 (P.e i)).1 = 0 := congrArg Prod.fst this
    have h2 : (s + c) * (toV2 (P.e i)).2 = 0 := congrArg Prod.snd this
    have hsc : s + c ≠ 0 := by positivity
    apply hd0
    exact Prod.ext ((mul_eq_zero.mp h1).resolve_left hsc) ((mul_eq_zero.mp h2).resolve_left hsc)
  have hne1 : t ≠ 1 := by
    rintro rfl
    have : toV2 (Y - X') = 0 := by
      rw [hY, hXt]; unfold toV2; ext <;> simp
    rw [hTe] at this
    have h1 : T * (toV2 (P.e i)).1 = 0 := congrArg Prod.fst this
    have h2 : T * (toV2 (P.e i)).2 = 0 := congrArg Prod.snd this
    apply hd0
    exact Prod.ext ((mul_eq_zero.mp h1).resolve_left hTpos'.ne') ((mul_eq_zero.mp h2).resolve_left hTpos'.ne')
  exact ⟨t, lt_of_le_of_ne ht0 (Ne.symm hne0), lt_of_le_of_ne ht1 hne1, hXt, s + c, by positivity, hdX'⟩

/-- **Forward propagation along a walk.** -/
theorem walk_prop_forward (D : RegionDissection N) (P : ConvPoly M) (hreg : D.region = P.carrier) (i : Fin M)
    (R : Fin N × Plane × Plane → Prop)
    (hstep : ∀ (e e2 : Fin N × Plane × Plane) (t : ℝ), 0 < t → t < 1 → e.2.2 = (1 - t) • P.v i + t • P.v (i + 1) → e2.2.1 = e.2.2 →
      TriStep (D.tile e.1) (toV2 (P.e i)) e.2.1 e.2.2 → TriStep (D.tile e2.1) (toV2 (P.e i)) e2.2.1 e2.2.2 → R e → R e2)
    {U Y : Plane} (hY : Y = P.v (i + 1)) {L : List (Fin N × Plane × Plane)} (W : WalkT D (toV2 (P.e i)) U Y L)
    (hU : ∃ s : ℝ, 0 ≤ s ∧ toV2 (U - P.v i) = (s * (toV2 (P.e i)).1, s * (toV2 (P.e i)).2)) :
    ∀ e0 L0, L = e0 :: L0 → R e0 → ∀ e ∈ L, R e := by
  induction W with
  | nil X => intro e0 L0 h; simp at h
  | @cons j X X' Y L' hS W' ih =>
    intro e0 L0 he0 hR e he
    simp only [List.cons.injEq] at he0
    obtain ⟨rfl, rfl⟩ := he0
    rcases List.mem_cons.mp he with h | h
    · subst h; exact hR
    · cases hL' : L' with
      | nil => rw [hL'] at h; simp at h
      | cons e2 L2 =>
        rw [hL'] at h W' ih
        obtain ⟨t, ht0, ht1, hXt, hs'⟩ := junction_param D P hreg i hY hS W' (by simp) hU
        have hX2 : e2.2.1 = X' := by cases W' with | cons _ _ => rfl
        have hS2 : TriStep (D.tile e2.1) (toV2 (P.e i)) e2.2.1 e2.2.2 := by
          cases W' with | cons hS2 _ => exact hS2
        have hR2 := hstep (j, X, X') e2 t ht0 ht1 hXt hX2 hS hS2 hR
        exact ih hY hs' e2 L2 rfl hR2 e h

/-- **Backward propagation along a walk.** -/
theorem walk_prop_backward (D : RegionDissection N) (P : ConvPoly M) (hreg : D.region = P.carrier) (i : Fin M)
    (R : Fin N × Plane × Plane → Prop)
    (hstep : ∀ (e e2 : Fin N × Plane × Plane) (t : ℝ), 0 < t → t < 1 → e.2.2 = (1 - t) • P.v i + t • P.v (i + 1) → e2.2.1 = e.2.2 →
      TriStep (D.tile e.1) (toV2 (P.e i)) e.2.1 e.2.2 → TriStep (D.tile e2.1) (toV2 (P.e i)) e2.2.1 e2.2.2 → R e2 → R e)
    {U Y : Plane} (hY : Y = P.v (i + 1)) {L : List (Fin N × Plane × Plane)} (W : WalkT D (toV2 (P.e i)) U Y L)
    (hU : ∃ s : ℝ, 0 ≤ s ∧ toV2 (U - P.v i) = (s * (toV2 (P.e i)).1, s * (toV2 (P.e i)).2)) :
    ∀ el, L.getLast? = some el → R el → ∀ e ∈ L, R e := by
  induction W with
  | nil X => intro el h; simp at h
  | @cons j X X' Y L' hS W' ih =>
    intro el hel hR e he
    rcases List.mem_cons.mp he with h | h
    · subst h
      cases hL' : L' with
      | nil =>
        rw [hL'] at hel
        simp at hel
        subst hel; exact hR
      | cons e2 L2 =>
        rw [hL'] at W' ih hel
        obtain ⟨t, ht0, ht1, hXt, hs'⟩ := junction_param D P hreg i hY hS W' (by simp) hU
        have hX2 : e2.2.1 = X' := by cases W' with | cons _ _ => rfl
        have hS2 : TriStep (D.tile e2.1) (toV2 (P.e i)) e2.2.1 e2.2.2 := by
          cases W' with | cons hS2 _ => exact hS2
        have hel' : (e2 :: L2).getLast? = some el := by
          simpa [List.getLast?_cons_cons] using hel
        have hall := ih hY hs' el hel' hR
        exact hstep _ e2 t ht0 ht1 hXt hX2 hS hS2 (hall e2 (by simp))
    · cases hL' : L' with
      | nil => rw [hL'] at h; simp at h
      | cons e2 L2 =>
        rw [hL'] at W' ih hel h
        obtain ⟨t, ht0, ht1, hXt, hs'⟩ := junction_param D P hreg i hY hS W' (by simp) hU
        have hel' : (e2 :: L2).getLast? = some el := by
          simpa [List.getLast?_cons_cons] using hel
        exact ih hY hs' el hel' hR e h

theorem step_idx {T : Tri} {d : V2} {U U' : Plane} (hS : TriStep T d U U') : ∃ kk f : Fin 3, T.pts kk = U ∧ T.pts f = U' := by
  obtain ⟨kk, f, g, hk, hf, -⟩ := hS
  exact ⟨kk, f, hk, hf⟩

/-- **The four rules along an edge** (Laczkovich Lemma 4.3 and its proof): for the walk of tiles along the edge `i` with first tile `e0` and last tile `el`:
R1 a `{β,γ}` type pair `(a,b)` (tail, head) of the first tile holds iff it holds for the last tile; R2 `α` at the tail of the first tile gives `α` at the tail of the last tile;
R3 `α` at the head of the last tile gives `α` at the head of the first tile. -/
theorem walk_rules (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (h : CaseIV D idx) (i : Fin M) {L : List (Fin N × Plane × Plane)}
    (W : WalkT D.toRegionDissection (toV2 (P.e i)) (P.v i) (P.v (i + 1)) L) {e0 el : Fin N × Plane × Plane}
    (hf : L.head? = some e0) (hl : L.getLast? = some el) :
    (∀ a b : Fin 3, ((a = 1 ∧ b = 2) ∨ (a = 2 ∧ b = 1)) →
      ((TyAt D idx e0.1 e0.2.1 a ∧ TyAt D idx e0.1 e0.2.2 b) ↔ (TyAt D idx el.1 el.2.1 a ∧ TyAt D idx el.1 el.2.2 b))) ∧
    (TyAt D idx e0.1 e0.2.1 0 → TyAt D idx el.1 el.2.1 0) ∧ (TyAt D idx el.1 el.2.2 0 → TyAt D idx e0.1 e0.2.2 0) := by
  classical
  have hU : ∃ s : ℝ, 0 ≤ s ∧ toV2 (P.v i - P.v i) = (s * (toV2 (P.e i)).1, s * (toV2 (P.e i)).2) :=
    ⟨0, le_rfl, by unfold toV2; ext <;> simp⟩
  have hL : ∃ L0, L = e0 :: L0 := by
    cases L with
    | nil => simp at hf
    | cons x L0 => simp at hf; exact ⟨L0, by rw [hf]⟩
  obtain ⟨L0, hL0⟩ := hL
  have hel_mem : el ∈ L := List.mem_of_getLast? hl
  -- the local step on a junction
  have local_step : ∀ (e e2 : Fin N × Plane × Plane) (t : ℝ), 0 < t → t < 1 → e.2.2 = (1 - t) • P.v i + t • P.v (i + 1) → e2.2.1 = e.2.2 →
      TriStep (D.tile e.1) (toV2 (P.e i)) e.2.1 e.2.2 → TriStep (D.tile e2.1) (toV2 (P.e i)) e2.2.1 e2.2.2 →
      ∀ kk1 f1 kk2 f2 : Fin 3, (D.tile e.1).pts kk1 = e.2.1 → (D.tile e.1).pts f1 = e.2.2 → (D.tile e2.1).pts kk2 = e2.2.1 → (D.tile e2.1).pts f2 = e2.2.2 →
      (((idx e.1 kk1 = 1 ∧ idx e.1 f1 = 2) ∨ (idx e.1 kk1 = 2 ∧ idx e.1 f1 = 1)) → idx e2.1 kk2 = idx e.1 kk1 ∧ idx e2.1 f2 = idx e.1 f1) ∧
      (idx e.1 kk1 = 0 → idx e2.1 kk2 = 0) ∧ (idx e2.1 f2 = 0 → idx e.1 f1 = 0) ∧
      (((idx e2.1 kk2 = 1 ∧ idx e2.1 f2 = 2) ∨ (idx e2.1 kk2 = 2 ∧ idx e2.1 f2 = 1)) → idx e2.1 kk2 = idx e.1 kk1 ∧ idx e2.1 f2 = idx e.1 f1) := by
    intro e e2 t ht0 ht1 hVt hX2 hS1 hS2 kk1 f1 kk2 f2 hk1 hf1 hk2 hf2
    exact edge_consec D P hreg idx h i ht0 ht1 hVt (U := e.2.1) (U'' := e2.2.2) (j1 := e.1) (j2 := e2.1) hS1 (by rw [← hX2]; exact hS2)
      kk2 f2 f1 kk1 (by rw [← hX2, ← hk2]) (by rw [hf2]) hf1 hk1
  have hY : P.v (i + 1) = P.v (i + 1) := rfl
  refine ⟨?_, ?_, ?_⟩
  · intro a b hab
    constructor
    · intro hR
      refine walk_prop_forward D.toRegionDissection P hreg i (fun e => TyAt D idx e.1 e.2.1 a ∧ TyAt D idx e.1 e.2.2 b) ?_ rfl W hU e0 L0 hL0 hR el hel_mem
      intro e e2 t ht0 ht1 hVt hX2 hS1 hS2 hRe
      obtain ⟨kk1, f1, hk1, hf1⟩ := step_idx hS1
      obtain ⟨kk2, f2, hk2, hf2⟩ := step_idx hS2
      have ls := local_step e e2 t ht0 ht1 hVt hX2 hS1 hS2 kk1 f1 kk2 f2 hk1 hf1 hk2 hf2
      have ha : idx e.1 kk1 = a := (tyAt_iff hk1 a).mp hRe.1
      have hb : idx e.1 f1 = b := (tyAt_iff hf1 b).mp hRe.2
      have := ls.1 (by rw [ha, hb]; exact hab)
      exact ⟨(tyAt_iff hk2 a).mpr (by rw [this.1, ha]), (tyAt_iff hf2 b).mpr (by rw [this.2, hb])⟩
    · intro hR
      refine walk_prop_backward D.toRegionDissection P hreg i (fun e => TyAt D idx e.1 e.2.1 a ∧ TyAt D idx e.1 e.2.2 b) ?_ rfl W hU el hl hR e0 (by rw [hL0]; simp)
      intro e e2 t ht0 ht1 hVt hX2 hS1 hS2 hRe2
      obtain ⟨kk1, f1, hk1, hf1⟩ := step_idx hS1
      obtain ⟨kk2, f2, hk2, hf2⟩ := step_idx hS2
      have ls := local_step e e2 t ht0 ht1 hVt hX2 hS1 hS2 kk1 f1 kk2 f2 hk1 hf1 hk2 hf2
      have ha : idx e2.1 kk2 = a := (tyAt_iff hk2 a).mp hRe2.1
      have hb : idx e2.1 f2 = b := (tyAt_iff hf2 b).mp hRe2.2
      have := ls.2.2.2 (by rw [ha, hb]; exact hab)
      exact ⟨(tyAt_iff hk1 a).mpr (by rw [← this.1, ha]), (tyAt_iff hf1 b).mpr (by rw [← this.2, hb])⟩
  · intro hR
    have := walk_prop_forward D.toRegionDissection P hreg i (fun e => TyAt D idx e.1 e.2.1 0) ?_ rfl W hU e0 L0 hL0 hR el hel_mem
    · exact this
    · intro e e2 t ht0 ht1 hVt hX2 hS1 hS2 hRe
      obtain ⟨kk1, f1, hk1, hf1⟩ := step_idx hS1
      obtain ⟨kk2, f2, hk2, hf2⟩ := step_idx hS2
      have ls := local_step e e2 t ht0 ht1 hVt hX2 hS1 hS2 kk1 f1 kk2 f2 hk1 hf1 hk2 hf2
      exact (tyAt_iff hk2 0).mpr (ls.2.1 ((tyAt_iff hk1 0).mp hRe))
  · intro hR
    have := walk_prop_backward D.toRegionDissection P hreg i (fun e => TyAt D idx e.1 e.2.2 0) ?_ rfl W hU el hl hR e0 (by rw [hL0]; simp)
    · exact this
    · intro e e2 t ht0 ht1 hVt hX2 hS1 hS2 hRe2
      obtain ⟨kk1, f1, hk1, hf1⟩ := step_idx hS1
      obtain ⟨kk2, f2, hk2, hf2⟩ := step_idx hS2
      have ls := local_step e e2 t ht0 ht1 hVt hX2 hS1 hS2 kk1 f1 kk2 f2 hk1 hf1 hk2 hf2
      exact (tyAt_iff hf1 0).mpr (ls.2.2.1 ((tyAt_iff hf2 0).mp hRe2))


/-- A tile with a step whose type pair (tail, head) is `(β,γ)` or `(γ,β)` has that step of length `a`. -/
theorem step_len_pair (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    {j : Fin N} {d : V2} {U U' : Plane} (hS : TriStep (D.tile j) d U U') {a b : Fin 3} (hab : (a = 1 ∧ b = 2) ∨ (a = 2 ∧ b = 1))
    (ha : TyAt D idx j U a) (hb : TyAt D idx j U' b) : dist U U' = slen D 0 := by
  obtain ⟨kk, f, hk, hf⟩ := step_idx hS
  have e1 := (tyAt_iff hk a).mp ha
  have e2 := (tyAt_iff hf b).mp hb
  rw [← hk, ← hf, hidx, e1, e2]
  unfold slen
  rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · rw [dist_comm]; rfl

/-- **The edge is an integer multiple of `a`** (Laczkovich Lemma 4.3 (ii)): if the first tile of the walk along the edge `i` has the type pair `(β,γ)` or `(γ,β)` (tail, head),
every tile of the walk has that pair and side `a`, so the edge has length `m a`, `m ≥ 1`. -/
theorem edge_multiple (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (h : CaseIV D idx) (i : Fin M) {L : List (Fin N × Plane × Plane)}
    (W : WalkT D.toRegionDissection (toV2 (P.e i)) (P.v i) (P.v (i + 1)) L) {e0 : Fin N × Plane × Plane} (hf : L.head? = some e0)
    {a b : Fin 3} (hab : (a = 1 ∧ b = 2) ∨ (a = 2 ∧ b = 1)) (h0 : TyAt D idx e0.1 e0.2.1 a ∧ TyAt D idx e0.1 e0.2.2 b) :
    ∃ m : ℕ, 0 < m ∧ P.side i = m * slen D 0 := by
  classical
  have hU : ∃ s : ℝ, 0 ≤ s ∧ toV2 (P.v i - P.v i) = (s * (toV2 (P.e i)).1, s * (toV2 (P.e i)).2) :=
    ⟨0, le_rfl, by unfold toV2; ext <;> simp⟩
  obtain ⟨L0, hL0⟩ : ∃ L0, L = e0 :: L0 := by
    cases L with
    | nil => simp at hf
    | cons x L0 => simp at hf; exact ⟨L0, by rw [hf]⟩
  have local_step : ∀ (e e2 : Fin N × Plane × Plane) (t : ℝ), 0 < t → t < 1 → e.2.2 = (1 - t) • P.v i + t • P.v (i + 1) → e2.2.1 = e.2.2 →
      TriStep (D.tile e.1) (toV2 (P.e i)) e.2.1 e.2.2 → TriStep (D.tile e2.1) (toV2 (P.e i)) e2.2.1 e2.2.2 →
      ∀ kk1 f1 kk2 f2 : Fin 3, (D.tile e.1).pts kk1 = e.2.1 → (D.tile e.1).pts f1 = e.2.2 → (D.tile e2.1).pts kk2 = e2.2.1 → (D.tile e2.1).pts f2 = e2.2.2 →
      (((idx e.1 kk1 = 1 ∧ idx e.1 f1 = 2) ∨ (idx e.1 kk1 = 2 ∧ idx e.1 f1 = 1)) → idx e2.1 kk2 = idx e.1 kk1 ∧ idx e2.1 f2 = idx e.1 f1) := by
    intro e e2 t ht0 ht1 hVt hX2 hS1 hS2 kk1 f1 kk2 f2 hk1 hf1 hk2 hf2
    exact (edge_consec D P hreg idx h i ht0 ht1 hVt (U := e.2.1) (U'' := e2.2.2) (j1 := e.1) (j2 := e2.1) hS1 (by rw [← hX2]; exact hS2)
      kk2 f2 f1 kk1 (by rw [← hX2, ← hk2]) (by rw [hf2]) hf1 hk1).1
  have hall := walk_prop_forward D.toRegionDissection P hreg i (fun e => TyAt D idx e.1 e.2.1 a ∧ TyAt D idx e.1 e.2.2 b) (by
      intro e e2 t ht0 ht1 hVt hX2 hS1 hS2 hRe
      obtain ⟨kk1, f1, hk1, hf1⟩ := step_idx hS1
      obtain ⟨kk2, f2, hk2, hf2⟩ := step_idx hS2
      have ls := local_step e e2 t ht0 ht1 hVt hX2 hS1 hS2 kk1 f1 kk2 f2 hk1 hf1 hk2 hf2
      have ha : idx e.1 kk1 = a := (tyAt_iff hk1 a).mp hRe.1
      have hb : idx e.1 f1 = b := (tyAt_iff hf1 b).mp hRe.2
      have := ls (by rw [ha, hb]; exact hab)
      exact ⟨(tyAt_iff hk2 a).mpr (by rw [this.1, ha]), (tyAt_iff hf2 b).mpr (by rw [this.2, hb])⟩) rfl W hU e0 L0 hL0 h0
  have hlen : ∀ e ∈ L, dist e.2.1 e.2.2 = slen D 0 := fun e he =>
    step_len_pair D idx h.hidx (walkT_mem_step W e he) hab (hall e he).1 (hall e he).2
  have hsum := walkT_dist_sum W
  have hsumA : (L.map fun e => dist e.2.1 e.2.2).sum = (L.map fun e => dist e.2.1 e.2.2).length • slen D 0 :=
    List.sum_eq_card_nsmul _ _ (fun x hx => by
      obtain ⟨e', he', rfl⟩ := List.mem_map.mp hx
      exact hlen e' he')
  rw [List.length_map, nsmul_eq_mul] at hsumA
  refine ⟨L.length, by rw [hL0]; simp, ?_⟩
  rw [ConvPoly.side, ← hsum, hsumA]


end Erdos634.Draft.LaczFormal.RG
