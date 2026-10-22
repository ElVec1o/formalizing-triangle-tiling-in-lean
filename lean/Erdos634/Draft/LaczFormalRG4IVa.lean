-- Draft/LaczFormalRG4IVa.lean -- Theorem 2.1, Case IV (gamma = pi/3), Subcase IVa, the corner/edge analysis for a polygon target: every angle of the polygon is `pi/3` or `2 pi/3`; there are three
-- consecutive vertices with angles `pi/3, 2 pi/3, pi/3`, and one side adjacent to a `pi/3` vertex is an integer multiple of `a`.
-- UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 8.1), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalRG4Corner
import Erdos634.Draft.LaczFormalRG4Comb

open scoped Classical
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ} [NeZero M]

/-- The last element of a nonempty walk ends at the end of the walk and is a step. -/
theorem walkT_getLast {D : RegionDissection N} {d : V2} {X Y : Plane} {L : List (Fin N × Plane × Plane)}
    (W : WalkT D d X Y L) (hL : L ≠ []) :
    ∃ el, L.getLast? = some el ∧ el.2.2 = Y ∧ TriStep (D.tile el.1) d el.2.1 el.2.2 := by
  induction W with
  | nil X => exact absurd rfl hL
  | @cons i X X' Y L hS W ih =>
    by_cases hL' : L = []
    · subst hL'
      have hX : X' = Y := walkT_nil_eq W
      exact ⟨(i, X, X'), by simp, hX, hS⟩
    · obtain ⟨el, h1, h2, h3⟩ := ih hL'
      refine ⟨el, ?_, h2, h3⟩
      cases L with
      | nil => exact absurd rfl hL'
      | cons e2 L2 => simpa [List.getLast?_cons_cons] using h1

/-- The first and last tile of the walk along the edge `i`. -/
theorem edge_data (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier) (i : Fin M) :
    ∃ (L : List (Fin N × Plane × Plane)) (e0 el : Fin N × Plane × Plane),
      WalkT D.toRegionDissection (toV2 (P.e i)) (P.v i) (P.v (i + 1)) L ∧ L.head? = some e0 ∧ L.getLast? = some el ∧
      e0.2.1 = P.v i ∧ el.2.2 = P.v (i + 1) ∧ TriStep (D.tile e0.1) (toV2 (P.e i)) e0.2.1 e0.2.2 ∧
      TriStep (D.tile el.1) (toV2 (P.e i)) el.2.1 el.2.2 := by
  classical
  obtain ⟨L, W⟩ := side_walk_exists_poly D.toRegionDissection P hreg i
  have hne : P.v i ≠ P.v (i + 1) := by
    intro he
    apply P.e_ne_zero P.three_le i
    unfold ConvPoly.e; rw [← he]; simp
  have hL : L ≠ [] := by
    rintro rfl
    exact hne (walkT_nil_eq W)
  obtain ⟨e0, L0, hL0⟩ : ∃ e0 L0, L = e0 :: L0 := by
    cases L with
    | nil => exact absurd rfl hL
    | cons e0 L0 => exact ⟨e0, L0, rfl⟩
  obtain ⟨el, hl1, hl2, hl3⟩ := walkT_getLast W hL
  have hh := walkT_head (hL0 ▸ W)
  exact ⟨L, e0, el, W, by rw [hL0]; rfl, hl1, hh.1, hl2, hh.2, hl3⟩

/-- The types at the two ends of a step. -/
theorem ty_exists (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) {j : Fin N} {d : V2} {U U' : Plane}
    (hS : TriStep (D.tile j) d U U') :
    ∃ ft fh : Fin 3, ft ≠ fh ∧ (∀ a, TyAt D idx j U a ↔ ft = a) ∧ (∀ b, TyAt D idx j U' b ↔ fh = b) := by
  obtain ⟨kk, f, g, hk, hf, hfk, -⟩ := hS
  refine ⟨idx j kk, idx j f, fun e => hfk ((idx j).injective e).symm, fun a => ?_, fun b => ?_⟩
  · rw [tyAt_iff hk]
  · rw [tyAt_iff hf]

/-- **Subcase IVa, corner/edge analysis.**  Every angle of the polygon is `π/3` or `2π/3`; some three consecutive vertices `e+1, e+2, e+3` have angles `π/3, 2π/3, π/3`;
and the side leaving `v_{e+1}` or the side entering `v_{e+1}` is an integer multiple of `a`. -/
theorem caseIV_shape (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (h : CaseIV D idx) :
    (∀ k : Fin M, P.angle (k + 1) = Real.pi / 3 ∨ P.angle (k + 1) = 2 * Real.pi / 3) ∧
    ∃ e : Fin M, P.angle (e + 1) = Real.pi / 3 ∧ P.angle (e + 2) = 2 * Real.pi / 3 ∧ P.angle (e + 3) = Real.pi / 3 ∧
      ((∃ m : ℕ, 0 < m ∧ P.side (e + 1) = m * slen D 0) ∨ (∃ m : ℕ, 0 < m ∧ P.side e = m * slen D 0)) := by
  classical
  have hed := edge_data D P hreg
  choose L e0 el hW hh hl hs1 hs2 hT0 hT1 using hed
  have hty : ∀ i, ∃ ft fh lt lh : Fin 3, ft ≠ fh ∧ lt ≠ lh ∧ (∀ a, TyAt D idx (e0 i).1 (e0 i).2.1 a ↔ ft = a) ∧
      (∀ b, TyAt D idx (e0 i).1 (e0 i).2.2 b ↔ fh = b) ∧ (∀ a, TyAt D idx (el i).1 (el i).2.1 a ↔ lt = a) ∧
      (∀ b, TyAt D idx (el i).1 (el i).2.2 b ↔ lh = b) := by
    intro i
    obtain ⟨ft, fh, a1, a2, a3⟩ := ty_exists D idx (hT0 i)
    obtain ⟨lt, lh, b1, b2, b3⟩ := ty_exists D idx (hT1 i)
    exact ⟨ft, fh, lt, lh, a1, b1, a2, a3, b2, b3⟩
  choose ft fh lt lh hne1 hne2 hft hfh hlt hlh using hty
  have tfa : ∀ i a, TyAt D idx (e0 i).1 (P.v i) a ↔ ft i = a := by
    intro i a; rw [← hs1 i]; exact hft i a
  have tlb : ∀ i b, TyAt D idx (el i).1 (P.v (i + 1)) b ↔ lh i = b := by
    intro i b; rw [← hs2 i]; exact hlh i b
  -- the rules along each edge
  have hrules : ∀ i, (∀ a b : Fin 3, ((a = 1 ∧ b = 2) ∨ (a = 2 ∧ b = 1)) →
      ((TyAt D idx (e0 i).1 (e0 i).2.1 a ∧ TyAt D idx (e0 i).1 (e0 i).2.2 b) ↔ (TyAt D idx (el i).1 (el i).2.1 a ∧ TyAt D idx (el i).1 (el i).2.2 b))) ∧
      (TyAt D idx (e0 i).1 (e0 i).2.1 0 → TyAt D idx (el i).1 (el i).2.1 0) ∧ (TyAt D idx (el i).1 (el i).2.2 0 → TyAt D idx (e0 i).1 (e0 i).2.2 0) :=
    fun i => walk_rules D P hreg idx h i (hW i) (hh i) (hl i)
  have R1 : ∀ i, ((ft i = 1 ∧ fh i = 2) ∨ (ft i = 2 ∧ fh i = 1)) → lt i = ft i ∧ lh i = fh i := by
    intro i hp
    have := (hrules i).1 (ft i) (fh i) hp
    have hh1 := this.mp ⟨(hft i _).mpr rfl, (hfh i _).mpr rfl⟩
    exact ⟨(hlt i _).mp hh1.1, (hlh i _).mp hh1.2⟩
  have R1' : ∀ i, ((lt i = 1 ∧ lh i = 2) ∨ (lt i = 2 ∧ lh i = 1)) → ft i = lt i ∧ fh i = lh i := by
    intro i hp
    have := (hrules i).1 (lt i) (lh i) hp
    have hh1 := this.mpr ⟨(hlt i _).mpr rfl, (hlh i _).mpr rfl⟩
    exact ⟨(hft i _).mp hh1.1, (hfh i _).mp hh1.2⟩
  have R2 : ∀ i, ft i = 0 → lt i = 0 := by
    intro i hp
    exact (hlt i _).mp ((hrules i).2.1 ((hft i _).mpr hp))
  have R3 : ∀ i, lh i = 0 → fh i = 0 := by
    intro i hp
    exact (hfh i _).mp ((hrules i).2.2 ((hlh i _).mpr hp))
  -- the vertex classification
  have hvc : ∀ e : Fin M,
      (S1a ft fh lt lh e ∧ P.angle (e + 1) = Real.pi / 3) ∨ (S1b ft fh lt lh e ∧ P.angle (e + 1) = Real.pi / 3) ∨
      (S2a ft fh lt lh e ∧ P.angle (e + 1) = 2 * Real.pi / 3) ∨ (S2b ft fh lt lh e ∧ P.angle (e + 1) = 2 * Real.pi / 3) ∨
      (S2c ft fh lt lh e ∧ P.angle (e + 1) = 2 * Real.pi / 3) := by
    intro e
    have hSo : TriStep (D.tile (e0 (e + 1)).1) (toV2 (P.e (e + 1))) (P.v (e + 1)) (e0 (e + 1)).2.2 := by
      have := hT0 (e + 1); rwa [hs1 (e + 1)] at this
    have hSi : TriStep (D.tile (el e).1) (toV2 (P.e e)) (el e).2.1 (P.v (e + 1)) := by
      have := hT1 e; rwa [hs2 e] at this
    have vc := vertex_class D P hreg idx h e _ _ _ _ hSo hSi
    have a0 := tfa (e + 1)
    have a1 := hfh (e + 1)
    have a2 := hlt e
    have a3 := tlb e
    rcases vc with ⟨hang, ⟨c1, c2, c3, c4⟩ | ⟨c1, c2, c3, c4⟩⟩ | ⟨hang, ⟨c1, c2, c3⟩ | ⟨c1, c2, c3⟩ | ⟨c1, c2, c3, c4⟩⟩
    · exact Or.inl ⟨⟨(a0 2).mp c1, (a1 1).mp c2, (a3 2).mp c3, (a2 0).mp c4⟩, hang⟩
    · exact Or.inr (Or.inl ⟨⟨(a0 2).mp c1, (a1 0).mp c2, (a3 2).mp c3, (a2 1).mp c4⟩, hang⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨⟨(a0 0).mp c1, (a3 1).mp c2, (a2 2).mp c3⟩, hang⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨⟨(a0 1).mp c1, (a1 2).mp c2, (a3 0).mp c3⟩, hang⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨⟨(a0 2).mp c1, (a1 1).mp c2, (a3 2).mp c3, (a2 1).mp c4⟩, hang⟩)))
  have H : CombHyp ft fh lt lh (fun e => P.angle (e + 1)) := ⟨hne1, hne2, R1, R1', R2, R3, hvc⟩
  refine ⟨?_, ?_⟩
  · intro k
    rcases hvc k with ⟨-, h1⟩ | ⟨-, h1⟩ | ⟨-, h1⟩ | ⟨-, h1⟩ | ⟨-, h1⟩
    · exact Or.inl h1
    · exact Or.inl h1
    · exact Or.inr h1
    · exact Or.inr h1
    · exact Or.inr h1
  obtain ⟨e, he⟩ := H.triple
  have e12 := fin_e12 M e
  have e22 : e + 2 + 1 = e + 3 := fin_e23 M e
  rcases he with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · refine ⟨e, H.ang_E1 (Or.inl h1), ?_, ?_, ?_⟩
    · have := H.ang_S2a h2
      simpa only [e12] using this
    · have := H.ang_E1 (Or.inl h3)
      simpa only [e22] using this
    · left
      obtain ⟨a1, a2, -, -⟩ := h1
      exact edge_multiple D P hreg idx h (e + 1) (hW (e + 1)) (hh (e + 1)) (a := 2) (b := 1) (Or.inr ⟨rfl, rfl⟩)
        ⟨(hft (e + 1) 2).mpr a1, (hfh (e + 1) 1).mpr a2⟩
  · refine ⟨e, H.ang_E1 (Or.inr h1), ?_, ?_, ?_⟩
    · have := H.ang_S2b h2
      simpa only [e12] using this
    · have := H.ang_E1 (Or.inr h3)
      simpa only [e22] using this
    · right
      obtain ⟨-, -, a3, a4⟩ := h1
      have r := R1' e (Or.inl ⟨a4, a3⟩)
      exact edge_multiple D P hreg idx h e (hW e) (hh e) (a := 1) (b := 2) (Or.inl ⟨rfl, rfl⟩)
        ⟨(hft e 1).mpr (by rw [r.1, a4]), (hfh e 2).mpr (by rw [r.2, a3])⟩

end Erdos634.Draft.LaczFormal.RG
