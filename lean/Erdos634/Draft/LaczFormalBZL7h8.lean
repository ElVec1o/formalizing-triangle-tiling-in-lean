-- Draft/LaczFormalBZL7h8.lean -- Beeson (arXiv 1206.1974v7) Lemmas 10.5/10.6 (G5): from a left walk along a side with BOTH a c step and a non-c step to an edge of Gamma_c starting at a vertex on the open side.
--   `list_adjacent_diff`, `walkT_adjacent`, `walkT_open_side` (the junction is a point `(1-t) v_i + t v_{i+1}`, 0<t<1), `step_third` / `cstep_dist` (a step with no gamma corner has length `c`),
--   `g5_of_steps`: c step and non-c step on a side + `NotComb c a b` => a boundary vertex starts a Gamma_c edge (junction_edge on `relabelC D`).
-- NOTE, UNAUDITED.  Credit: Beeson (arXiv 1206.1974v7, Lemmas 10.5, 10.6), Laczkovich (DCG 48 (2012), Sect. 4), Beeson-Zhang.
import Erdos634.Draft.LaczFormalBZL7h7

open scoped Classical
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ} [NeZero M]

theorem toV2_inj' {a b : Plane} (h : toV2 a = toV2 b) : a = b := by
  have h0 : a 0 = b 0 := congrArg Prod.fst h
  have h1 : a 1 = b 1 := congrArg Prod.snd h
  ext i; fin_cases i
  · exact h0
  · exact h1

theorem list_adjacent_diff {α : Type*} (p : α → Prop) : ∀ (L : List α), (∃ x ∈ L, p x) → (∃ y ∈ L, ¬ p y) →
    ∃ L1 x y L2, L = L1 ++ x :: y :: L2 ∧ (p x ↔ ¬ p y) := by
  intro L
  induction L with
  | nil => rintro ⟨x, hx, -⟩; simp at hx
  | cons a L ih =>
    intro ⟨x, hx, hpx⟩ ⟨y, hy, hpy⟩
    cases L with
    | nil =>
      simp only [List.mem_singleton] at hx hy
      subst hx; subst hy; exact absurd hpx hpy
    | cons b L' =>
      by_cases hab : p a ↔ ¬ p b
      · exact ⟨[], a, b, L', rfl, hab⟩
      · have hab' : p a ↔ p b := by tauto
        have e1 : ∃ x ∈ b :: L', p x := by
          rcases List.mem_cons.mp hx with rfl | hx'
          · exact ⟨b, List.mem_cons_self .., hab'.mp hpx⟩
          · exact ⟨x, hx', hpx⟩
        have e2 : ∃ y ∈ b :: L', ¬ p y := by
          rcases List.mem_cons.mp hy with rfl | hy'
          · exact ⟨b, List.mem_cons_self .., fun h => hpy (hab'.mpr h)⟩
          · exact ⟨y, hy', hpy⟩
        obtain ⟨L1, x', y', L2, hdec, hd⟩ := ih e1 e2
        exact ⟨a :: L1, x', y', L2, by rw [hdec]; rfl, hd⟩

theorem walkT_adjacent {D : RegionDissection N} {d : V2} {X Y : Plane} {L : List (Fin N × Plane × Plane)} (W : WalkT D d X Y L) :
    ∀ {L1 : List (Fin N × Plane × Plane)} {x y : Fin N × Plane × Plane} {L2 : List (Fin N × Plane × Plane)}, L = L1 ++ x :: y :: L2 →
      x.2.2 = y.2.1 ∧ TriStep (D.tile x.1) d x.2.1 x.2.2 ∧ TriStep (D.tile y.1) d y.2.1 y.2.2 := by
  induction W with
  | nil X => intro L1 x y L2 h; simp at h
  | @cons i X X' Y L hS W ih =>
    intro L1 x y L2 h
    cases L1 with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at h
      obtain ⟨hx, hL⟩ := h
      subst hx
      subst hL
      cases W with
      | cons hS' W' => exact ⟨rfl, hS, hS'⟩
    | cons z L1' =>
      simp only [List.cons_append, List.cons.injEq] at h
      exact ih h.2

/-- The junction of two consecutive steps of a walk along a side is an interior point of the side. -/
theorem walkT_open_side (D : RegionDissection N) (P : ConvPoly M) (i : Fin M) {L : List (Fin N × Plane × Plane)}
    (W : WalkT D (toV2 (P.e i)) (P.v i) (P.v (i + 1)) L) {L1 : List (Fin N × Plane × Plane)} {x y : Fin N × Plane × Plane}
    {L2 : List (Fin N × Plane × Plane)} (h : L = L1 ++ x :: y :: L2) :
    ∃ t : ℝ, 0 < t ∧ t < 1 ∧ y.2.1 = (1 - t) • P.v i + t • P.v (i + 1) := by
  have hsp := walkT_split W (P := L1 ++ [x]) (e := y) (Q := L2) (by rw [h]; simp)
  obtain ⟨W1, W2⟩ := hsp
  obtain ⟨T, hT0, hT, hTp⟩ := walkT_progress W1
  obtain ⟨T', hT0', hT', hTp'⟩ := walkT_progress W2
  have hTpos : 0 < T := hTp (by simp)
  have hTpos' : 0 < T' := hTp' (by simp)
  have e1 : y.2.1 - P.v i = T • P.e i := by
    apply toV2_inj'
    rw [hT]; unfold toV2; ext <;> simp
  have e2 : P.v (i + 1) - y.2.1 = T' • P.e i := by
    apply toV2_inj'
    rw [hT']; unfold toV2; ext <;> simp
  have hsum : (T + T') • P.e i = P.e i := by
    have : P.e i = (y.2.1 - P.v i) + (P.v (i + 1) - y.2.1) := by unfold ConvPoly.e; abel
    rw [add_smul, ← e1, ← e2]; exact this.symm
  have hTT : T + T' = 1 := by
    have he := P.e_ne_zero P.three_le i
    have : (T + T' - 1) • P.e i = 0 := by rw [sub_smul, hsum, one_smul, sub_self]
    rcases smul_eq_zero.mp this with h0 | h0
    · linarith
    · exact absurd h0 he
  refine ⟨T, hTpos, by linarith, ?_⟩
  have : y.2.1 = P.v i + T • P.e i := by rw [← e1]; abel
  rw [this]
  unfold ConvPoly.e
  module

theorem fin3_third_bz7 : ∀ kk g : Fin 3, g ≠ kk → g ≠ kk + 1 → g = kk + 2 := by
  intro kk g; fin_cases kk <;> fin_cases g <;> simp
theorem fin3_third_bz7_bz7b : ∀ kk g : Fin 3, g ≠ kk → g ≠ kk + 2 → g = kk + 1 := by
  intro kk g; fin_cases kk <;> fin_cases g <;> simp
theorem fin3_two_ne_two : ∀ a b c : Fin 3, a ≠ b → a ≠ c → b ≠ c → a ≠ 2 → b ≠ 2 → c = 2 := by
  intro a b c; fin_cases a <;> fin_cases b <;> fin_cases c <;> simp

/-- A step is a side of its tile, of the length of the model side opposite the type of the third vertex `g`. -/
theorem step_third (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    {j : Fin N} {d : V2} {U U' : Plane} (hS : TriStep (D.tile j) d U U') :
    ∃ kk f g : Fin 3, (D.tile j).pts kk = U ∧ (D.tile j).pts f = U' ∧ f ≠ kk ∧ g ≠ kk ∧ g ≠ f ∧ dist U U' = slen D (idx j g) := by
  obtain ⟨kk, f, g, hk, hf, hfk, hgk, hgf, -⟩ := hS
  refine ⟨kk, f, g, hk, hf, hfk, hgk, hgf, ?_⟩
  rw [← hk, ← hf]
  rcases fin3_arm kk f hfk with h | h
  · subst h
    have hg : g = kk + 2 := fin3_third_bz7 kk g hgk hgf
    rw [side_len_01 D idx hidx, hg]
  · subst h
    have hg : g = kk + 1 := fin3_third_bz7_bz7b kk g hgk hgf
    rw [side_len_02 D idx hidx, hg]

/-- A step whose tile has NO gamma corner at either end has length `c = slen D 2`. -/
theorem cstep_dist (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    {j : Fin N} {d : V2} {U U' : Plane} (hS : TriStep (D.tile j) d U U')
    (hno : ∀ k, ((D.tile j).pts k = U ∨ (D.tile j).pts k = U') → idx j k ≠ 2) : dist U U' = slen D 2 := by
  obtain ⟨kk, f, g, hk, hf, hfk, hgk, hgf, hd⟩ := step_third D idx hidx hS
  rw [hd]
  have h1 : idx j kk ≠ 2 := hno kk (Or.inl hk)
  have h2 : idx j f ≠ 2 := hno f (Or.inr hf)
  have := fin3_two_ne_two (idx j kk) (idx j f) (idx j g) (fun h => hfk ((idx j).injective h).symm) (fun h => hgk ((idx j).injective h).symm)
    (fun h => hgf ((idx j).injective h).symm) h1 h2
  rw [this]

end Erdos634.Draft.LaczFormal.RG
