import Erdos634.Draft.LaczFormalWalkRun
import Erdos634.Draft.LaczFormalC0

/-!
# The corner rules C0, C0m on the base walk

Erdős #634, base-`β` band.  Credit: AI assistant (item 3, band program), Beeson–Roșu, Beeson, Laczkovich, Paliy.
UNAUDITED.  Axiom-clean; no `sorry`.  The word of the base walk avoids the windows `C0`, `C0m`
(from `band_C0_full`, `band_C0m_full`), with the corner hypotheses derived (`first_apex`, `last_apex`).
-/

namespace Erdos634.LaczJunction.Walk

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.LaczJunction Erdos634.LaczJunction.Grammar
open Erdos634.Draft.LaczFormal.Graph

variable {N : ℕ}

/-- Consecutive entries of the walk use different tiles. -/
theorem walk_adjacent_tile_ne {D : CongruentDissection N} {p q : Fin 3}
    {L : List (Fin N × Plane × Plane)} (hne : D.target.pts p ≠ D.target.pts q)
    (W : WalkT D.toDissection (toV2 (D.target.pts q - D.target.pts p)) (D.target.pts p)
      (D.target.pts q) L)
    (s t : List (Fin N × Plane × Plane)) (a b : Fin N × Plane × Plane) (h : L = s ++ a :: b :: t) :
    b.1 ≠ a.1 := by
  intro hab
  have hmem : ∀ x ∈ L, TriStep (D.tile x.1) (toV2 (D.target.pts q - D.target.pts p)) x.2.1 x.2.2 :=
    walkT_mem_step W
  have ha := hmem a (by rw [h]; simp)
  have hb := hmem b (by rw [h]; simp)
  have hadj := walk_adjacent W s t a b h
  have hpar := (walk_param hne W (t0 := 0) (t1 := 1) (by simp) (by simp)).2.1
  obtain ⟨sa, ta, h0a, ha1, ha2, ha3, ha4⟩ := hpar a (by rw [h]; simp)
  obtain ⟨sb, tb, h0b, hb1, hb2, hb3, hb4⟩ := hpar b (by rw [h]; simp)
  rw [hab] at hb
  have hw : D.target.pts q - D.target.pts p ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  have hcol : crs (toV2 (D.target.pts q - D.target.pts p)) (toV2 (b.2.1 - a.2.1)) = 0 := by
    rw [hb3, ha3]
    have : D.target.pts p + sb • (D.target.pts q - D.target.pts p) -
        (D.target.pts p + sa • (D.target.pts q - D.target.pts p)) =
        (sb - sa) • (D.target.pts q - D.target.pts p) := by module
    rw [this, crs_toV2]
    simp [cross]; ring
  obtain ⟨h1, -⟩ := tristep_unique ha hb hcol
  -- a.2.1 = b.2.1 = a.2.2 contradicts s < t
  have : a.2.1 = a.2.2 := by rw [h1, ← hadj]
  rw [ha3, ha4] at this
  have := smul_injective_of_ne hw (add_left_cancel this)
  linarith

theorem tok_len_c {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ} {p q r : Fin 3}
    (S : BandSetup D e f α β γ p q r) {t : Tok} {x : Fin N × Plane × Plane} {Z : Plane}
    (hb : BaseTok D p q (angOf α β γ) (lenOf (ta e f) (tb e f) (tc e f)) t.side t.left t.right
      x.1 x.2.1 x.2.2 Z) (hs : t.side = .c) : dist x.2.1 x.2.2 = sideOpp D.model 2 := by
  have := hb.length
  rw [hs] at this
  simpa [lenOf, S.hsc] using this

/-- **`C0` does not occur in the word of the base walk.** -/
theorem walk_noC0 {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ} {p q r : Fin 3}
    (S : BandSetup D e f α β γ p q r)
    (hori : 0 < crs (toV2 (D.target.pts q - D.target.pts p)) (toV2 (D.target.pts r - D.target.pts p)))
    {L : List (Fin N × Plane × Plane)}
    (hL : WalkT D.toDissection (toV2 (D.target.pts q - D.target.pts p)) (D.target.pts p)
      (D.target.pts q) L)
    (hpar : ∀ x ∈ L, ∃ s t : ℝ, 0 ≤ s ∧ s < t ∧ t ≤ 1 ∧
        x.2.1 = D.target.pts p + s • (D.target.pts q - D.target.pts p) ∧
        x.2.2 = D.target.pts p + t • (D.target.pts q - D.target.pts p))
    (hstep : ∀ x ∈ L, StepData D e f α β γ p q x) :
    ¬ winC0 (L.map (elemTok D α β)) := by
  rintro ⟨Y, hY, s, hs⟩
  obtain ⟨x0, x1, L', hLeq⟩ : ∃ x0 x1 L', L = x0 :: x1 :: L' := by
    rcases hc : L with _ | ⟨x0, _ | ⟨x1, L'⟩⟩
    · rw [hc] at hs; simp at hs
    · rw [hc] at hs; simp at hs
    · exact ⟨x0, x1, L', rfl⟩
  rw [hLeq] at hs
  simp only [List.map_cons, List.cons_append, List.nil_append, List.cons.injEq] at hs
  obtain ⟨e0, e1, -⟩ := hs
  have hne : D.target.pts p ≠ D.target.pts q := by
    intro h
    have : crs (toV2 (D.target.pts q - D.target.pts p)) (toV2 (D.target.pts r - D.target.pts p)) = 0 := by
      rw [← h]; simp [crs, toV2]
    linarith
  have hx0 : x0.2.1 = D.target.pts p := walk_first hL x0 (x1 :: L') hLeq
  have hadj : x0.2.2 = x1.2.1 := walk_adjacent hL [] L' x0 x1 (by simpa using hLeq)
  have hne1 : x1.1 ≠ x0.1 := walk_adjacent_tile_ne hne hL [] L' x0 x1 (by simpa using hLeq)
  have sd0 := hstep x0 (by rw [hLeq]; simp)
  have sd1 := hstep x1 (by rw [hLeq]; simp)
  have hp0 := hpar x0 (by rw [hLeq]; simp)
  obtain ⟨kk, fi, g, hfk, hgk, hgf, hk, hf, hleft, hbt0⟩ := sd0
  obtain ⟨kk1, fi1, g1, -, -, -, -, -, -, hbt1⟩ := sd1
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
  have t2 := hbt1
  rw [← hadj] at t2
  have hlr : (elemTok D α β x1).left = .A ∨ ((elemTok D α β x1).side = .b ∧
      (elemTok D α β x1).left = .G ∧ (elemTok D α β x1).right = .A) := by
    rw [← e1]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hY
    rcases hY with rfl | rfl | rfl <;> simp [Tok.left, Tok.side, Tok.right]
  exact band_C0_full D e f S.he S.hef S.hcop α β γ S.hγdef S.hrel S.hirr S.hα0 S.hβ0 S.hα' S.hβ'
    S.hγ' S.hsa S.hsb S.hsc S.hpq S.hpr S.hqr S.hcB S.haL x0.1 x1.1 hne1 _ _ _ hlr t1 hseg t2

/-- **`C0m` does not occur in the word of the base walk.** -/
theorem walk_noC0m {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ} {p q r : Fin 3}
    (S : BandSetup D e f α β γ p q r)
    (hori : 0 < crs (toV2 (D.target.pts q - D.target.pts p)) (toV2 (D.target.pts r - D.target.pts p)))
    {L : List (Fin N × Plane × Plane)}
    (hL : WalkT D.toDissection (toV2 (D.target.pts q - D.target.pts p)) (D.target.pts p)
      (D.target.pts q) L)
    (hpar : ∀ x ∈ L, ∃ s t : ℝ, 0 ≤ s ∧ s < t ∧ t ≤ 1 ∧
        x.2.1 = D.target.pts p + s • (D.target.pts q - D.target.pts p) ∧
        x.2.2 = D.target.pts p + t • (D.target.pts q - D.target.pts p))
    (hstep : ∀ x ∈ L, StepData D e f α β γ p q x) :
    ¬ winC0m (L.map (elemTok D α β)) := by
  rintro ⟨Y, hY, s, hs⟩
  obtain ⟨L', x1, x2, hLeq⟩ : ∃ L' x1 x2, L = L' ++ [x1, x2] := by
    rcases hc : L.reverse with _ | ⟨x2, _ | ⟨x1, r'⟩⟩
    · have : L = [] := by simpa using congrArg List.reverse hc
      rw [this] at hs; simp at hs
    · have : L = [x2] := by simpa using congrArg List.reverse hc
      rw [this] at hs
      have := congrArg List.length hs; simp at this
    · exact ⟨r'.reverse, x1, x2, by simpa using congrArg List.reverse hc⟩
  rw [hLeq, List.map_append] at hs
  have hsuf := List.append_inj_right' hs (by simp)
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hsuf
  obtain ⟨e1, e2⟩ := hsuf
  have hne : D.target.pts p ≠ D.target.pts q := by
    intro h
    have : crs (toV2 (D.target.pts q - D.target.pts p)) (toV2 (D.target.pts r - D.target.pts p)) = 0 := by
      rw [← h]; simp [crs, toV2]
    linarith
  have hx2 : x2.2.2 = D.target.pts q := walk_last hL (L' ++ [x1]) x2 (by rw [hLeq]; simp)
  have hadj : x1.2.2 = x2.2.1 := walk_adjacent hL L' [] x1 x2 (by simpa using hLeq)
  have hne1 : x2.1 ≠ x1.1 := walk_adjacent_tile_ne hne hL L' [] x1 x2 (by simpa using hLeq)
  have sd1 := hstep x1 (by rw [hLeq]; simp)
  have sd2 := hstep x2 (by rw [hLeq]; simp)
  have hp2 := hpar x2 (by rw [hLeq]; simp)
  obtain ⟨kk, fi, g, hfk, hgk, hgf, hk, hf, hleft, hbt2⟩ := sd2
  obtain ⟨kk1, fi1, g1, -, -, -, -, -, -, hbt1⟩ := sd1
  have hc : dist x2.2.1 x2.2.2 = sideOpp D.model 2 :=
    tok_len_c S (t := elemTok D α β x2) hbt2 (by rw [← e2]; rfl)
  obtain ⟨g', hseg, kk', fi', hfk', hgk', hgf', hk', hf', hbt2'⟩ :=
    last_apex S hori hx2 hp2 ⟨kk, fi, g, hfk, hgk, hgf, hk, hf, hleft, hbt2⟩ hc
  have t1 : BaseTok D p q (angOf α β γ) (lenOf (ta e f) (tb e f) (tc e f)) .c .A .B x2.1
      x2.2.1 (D.target.pts q) ((D.tile x2.1).pts g') := by
    have := hbt2'
    rw [← e2] at this
    rw [hx2] at this
    exact this
  have t2 := hbt1
  rw [hadj] at t2
  have hlr : (elemTok D α β x1).right = .A ∨ ((elemTok D α β x1).side = .b ∧
      (elemTok D α β x1).right = .G ∧ (elemTok D α β x1).left = .A) := by
    rw [← e1]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hY
    rcases hY with rfl | rfl | rfl <;> simp [Tok.left, Tok.side, Tok.right]
  exact band_C0m_full D e f S.he S.hef S.hcop α β γ S.hγdef S.hrel S.hirr S.hα0 S.hβ0 S.hα' S.hβ'
    S.hγ' S.hsa S.hsb S.hsc S.hpq S.hpr S.hqr S.hcB S.haR x2.1 x1.1 hne1.symm _ _ _ hlr t2 t1 hseg

#print axioms walk_noC0
#print axioms walk_noC0m

end Erdos634.LaczJunction.Walk
