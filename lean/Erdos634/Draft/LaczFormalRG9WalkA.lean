-- Draft/LaczFormalRG9WalkA.lean -- Laczkovich DCG 48 (2012), Lemma 4.3 along a whole polygon side (general gamma, `Gamma_a`): the rules R1 (a {beta,gamma} type pair of the first tile holds iff it holds
-- for the last tile), R2, R3, and `edge_multiple_a` (the side is an integer multiple of `a` when its first tile has the pair {beta,gamma}).  Copies of `RG4Walk.walk_rules`/`edge_multiple` with the
-- normality and no-edge hypotheses.  UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Lemma 4.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalRG9SideA

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ} [NeZero M]

/-- **The four rules along an edge** (Laczkovich Lemma 4.3 and its proof): for the walk of tiles along the edge `i` with first tile `e0` and last tile `el`:
R1 a `{β,γ}` type pair `(a,b)` (tail, head) of the first tile holds iff it holds for the last tile; R2 `α` at the tail of the first tile gives `α` at the tail of the last tile;
R3 `α` at the head of the last tile gives `α` at the head of the first tile. -/
theorem walk_rules_a (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (h : CaseA D idx) (i : Fin M) (hnormv : ∀ V : Plane, (∃ j k, (D.tile j).pts k = V) → (∃ t : ℝ, 0 < t ∧ t < 1 ∧ V = (1 - t) • P.v i + t • P.v (i + 1)) → cnt D idx V 0 = 1 ∧ cnt D idx V 1 = 1 ∧ cnt D idx V 2 = 1)
    (hno : ∀ V : Plane, (∃ j k, (D.tile j).pts k = V) → (∃ t : ℝ, 0 < t ∧ t < 1 ∧ V = (1 - t) • P.v i + t • P.v (i + 1)) → ∀ H', ¬ GaEdge D.toRegionDissection (slen D 0) V H') {L : List (Fin N × Plane × Plane)}
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
    exact edge_consec_a D P hreg idx h i hnormv hno ht0 ht1 hVt (U := e.2.1) (U'' := e2.2.2) (j1 := e.1) (j2 := e2.1) hS1 (by rw [← hX2]; exact hS2)
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


/-- **The edge is an integer multiple of `a`** (Laczkovich Lemma 4.3 (ii)): if the first tile of the walk along the edge `i` has the type pair `(β,γ)` or `(γ,β)` (tail, head),
every tile of the walk has that pair and side `a`, so the edge has length `m a`, `m ≥ 1`. -/
theorem edge_multiple_a (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (h : CaseA D idx) (i : Fin M) (hnormv : ∀ V : Plane, (∃ j k, (D.tile j).pts k = V) → (∃ t : ℝ, 0 < t ∧ t < 1 ∧ V = (1 - t) • P.v i + t • P.v (i + 1)) → cnt D idx V 0 = 1 ∧ cnt D idx V 1 = 1 ∧ cnt D idx V 2 = 1)
    (hno : ∀ V : Plane, (∃ j k, (D.tile j).pts k = V) → (∃ t : ℝ, 0 < t ∧ t < 1 ∧ V = (1 - t) • P.v i + t • P.v (i + 1)) → ∀ H', ¬ GaEdge D.toRegionDissection (slen D 0) V H') {L : List (Fin N × Plane × Plane)}
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
    exact (edge_consec_a D P hreg idx h i hnormv hno ht0 ht1 hVt (U := e.2.1) (U'' := e2.2.2) (j1 := e.1) (j2 := e2.1) hS1 (by rw [← hX2]; exact hS2)
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
