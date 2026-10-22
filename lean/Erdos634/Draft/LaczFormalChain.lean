import Erdos634.Draft.LaczFormalC0
import Erdos634.Draft.LaczFormalGrammar
import Erdos634.Draft.LaczFormalW2Arith

/-!
# Base chains of a real dissection and the theorems U, U2 for real tilings

Erdős #634, base-`β` band.  Credit: AI assistant (item 3, band program), Beeson–Roșu (tiles, Lemma 34, the
template for runs), Beeson, Laczkovich, Paliy, Zhang.  Hand proofs:
(private working notes, not included), `PROOF_C0.md`, `PROOF_W2.md`.
STATUS: UNAUDITED.  Axiom-clean; no `sorry`.

## What is here
* `BaseChain`: a word of base tokens of a real `CongruentDissection`: a list of records, each a tile
  with a `BaseTok` (LaczFormalJunctionTok) on the base `[A_p, A_q]`, consecutive records sharing the
  junction point and using different tiles, the first starting at `A_p` and the last ending at `A_q`, the
  apex of the first (resp. last) tile on the left (resp. right) side of the target.
* `chain_noC0`, `chain_noC0m`: from the Lean theorems `band_C0_full`, `band_C0m_full` the word of a chain
  avoids the windows `C0`, `C0m`.
* `W2Rule`: the token-level statement of rule W2, as a `Prop`.  NOTE (2026-10-21, room LEAN_W2): it is now a THEOREM,
  `W2Rule_holds` (LaczFormalW2Final, by `w2_holds`); the conditionality below on `W2Rule e f` can be discharged.
  `chain_noW2`, `chain_noW2m` derive the two window exclusions from it (the mirror by `BaseTok.reflect`).
* `U_real` (`d ≤ 1`): **no hypothesis on W2.**  `U2_real` (`d ≤ 2`): conditional on `W2Rule e f`.

## Honest account of the hypotheses of `U_real` / `U2_real`
Unconditional given: (i) the chain (the word-to-geometry step: that the base of a real tiling is such a
chain; `side_walk_exists` in `LaczFormalGraphWalk` produces the walk of tiles, the conversion to `BaseTok`
records is not done here); (ii) `hno`: no `a`-token on the base and `hcount`: exactly `2Me` `c`-tokens
(Band Lemma + Proposition B1: hand proofs, brute-checked); (iii) `hrun`: a run of `f` equal `c`-tokens
(the Lean `thm_siderunall_T`, `LaysBaseOn`; the translation of that statement to a token run is not done
here); (iv) `hfirst`, `hlast`: the end tokens have the corner angle `β` (`ok_first`, `ok_last`).
Conditional on `W2Rule e f` for `U2_real`.
-/

namespace Erdos634.LaczJunction

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.LaczJunction.Grammar

variable {N : ℕ}

/-- The geometric and arithmetic setting of a band tiling (all hypotheses of `band_C0_full`). -/
structure BandSetup (D : CongruentDissection N) (e f : ℕ) (α β γ : ℝ) (p q r : Fin 3) : Prop where
  he : 1 ≤ e
  hef : e < f
  hcop : Nat.Coprime e f
  hγdef : γ = 2 * α + β
  hrel : 3 * α + 2 * β = Real.pi
  hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi
  hα0 : 0 < α
  hβ0 : 0 < β
  hα' : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α
  hβ' : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β
  hγ' : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ
  hsa : sideOpp D.model 0 = (ta e f : ℝ)
  hsb : sideOpp D.model 1 = (tb e f : ℝ)
  hsc : sideOpp D.model 2 = (tc e f : ℝ)
  hpq : p ≠ q
  hpr : p ≠ r
  hqr : q ≠ r
  cornerP : cornerAngle (D.target.pts q) (D.target.pts p) (D.target.pts r) = β
  cornerQ : cornerAngle (D.target.pts p) (D.target.pts q) (D.target.pts r) = β
  hcB : (tc e f : ℝ) < dist (D.target.pts p) (D.target.pts q)
  haL : (ta e f : ℝ) < dist (D.target.pts p) (D.target.pts r)
  haR : (ta e f : ℝ) < dist (D.target.pts q) (D.target.pts r)

/-- One record of a base chain: a token, its tile, its junction points and apex. -/
structure CTok (D : CongruentDissection N) (e f : ℕ) (α β γ : ℝ) (p q : Fin 3) where
  tok : Tok
  tile : Fin N
  X : Plane
  Y : Plane
  Z : Plane
  h : BaseTok D p q (angOf α β γ) (lenOf (ta e f) (tb e f) (tc e f)) tok.side tok.left tok.right
    tile X Y Z

/-- Consecutive records share the junction and use different tiles. -/
def Linked {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ} {p q : Fin 3} :
    List (CTok D e f α β γ p q) → Prop
  | [] => True
  | [_] => True
  | a :: b :: r => a.Y = b.X ∧ b.tile ≠ a.tile ∧ Linked (b :: r)

theorem Linked.append_last {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ} {p q : Fin 3}
    (s : List (CTok D e f α β γ p q)) (a b : CTok D e f α β γ p q) (h : Linked (s ++ [a, b])) :
    a.Y = b.X ∧ b.tile ≠ a.tile := by
  induction s with
  | nil => exact ⟨h.1, h.2.1⟩
  | cons c s ih =>
    cases s with
    | nil => exact ih h.2.2
    | cons c' s' => exact ih h.2.2

theorem Linked.append_three {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ} {p q : Fin 3}
    (s : List (CTok D e f α β γ p q)) (a b c : CTok D e f α β γ p q)
    (h : Linked (s ++ [a, b, c])) :
    (a.Y = b.X ∧ b.tile ≠ a.tile) ∧ (b.Y = c.X ∧ c.tile ≠ b.tile) := by
  induction s with
  | nil => exact ⟨⟨h.1, h.2.1⟩, h.2.2.1, h.2.2.2.1⟩
  | cons c' s ih =>
    cases s with
    | nil => exact ih h.2.2
    | cons c'' s' => exact ih h.2.2

/-- **A base chain**: the word of base tokens of a real dissection, from the corner `A_p` to `A_q`. -/
structure BaseChain (D : CongruentDissection N) (e f : ℕ) (α β γ : ℝ) (p q r : Fin 3) where
  cs : List (CTok D e f α β γ p q)
  linked : Linked cs
  start : ∀ c, cs.head? = some c → c.X = D.target.pts p
  stop : ∀ c, cs.getLast? = some c → c.Y = D.target.pts q
  topL : ∀ c, cs.head? = some c → c.Z ∈ segment ℝ (D.target.pts p) (D.target.pts r)
  topR : ∀ c, cs.getLast? = some c → c.Z ∈ segment ℝ (D.target.pts q) (D.target.pts r)

/-- The word of a chain. -/
def BaseChain.word {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ} {p q r : Fin 3}
    (ch : BaseChain D e f α β γ p q r) : List Tok := ch.cs.map CTok.tok

theorem word_length {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ} {p q r : Fin 3}
    (ch : BaseChain D e f α β γ p q r) : ch.word.length = ch.cs.length := by
  simp [BaseChain.word]

/-- **`C0` does not occur in the word of a chain** (from `band_C0_full`). -/
theorem chain_noC0 {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ} {p q r : Fin 3}
    (S : BandSetup D e f α β γ p q r) (ch : BaseChain D e f α β γ p q r) : ¬ winC0 ch.word := by
  rintro ⟨Y, hY, s, hs⟩
  obtain ⟨c0, c1, cs', hcs⟩ : ∃ c0 c1 cs', ch.cs = c0 :: c1 :: cs' := by
    rcases hc : ch.cs with _ | ⟨c0, _ | ⟨c1, cs'⟩⟩
    · rw [BaseChain.word, hc] at hs; simp at hs
    · rw [BaseChain.word, hc] at hs; simp at hs
    · exact ⟨c0, c1, cs', rfl⟩
  rw [BaseChain.word, hcs] at hs
  simp only [List.map_cons, List.cons_append, List.nil_append, List.cons.injEq] at hs
  obtain ⟨e0, e1, -⟩ := hs
  have hlink := ch.linked
  rw [hcs] at hlink
  obtain ⟨hY01, hne, -⟩ := hlink
  have hX0 : c0.X = D.target.pts p := ch.start c0 (by rw [hcs]; rfl)
  have hZ0 : c0.Z ∈ segment ℝ (D.target.pts p) (D.target.pts r) := ch.topL c0 (by rw [hcs]; rfl)
  have t1 : BaseTok D p q (angOf α β γ) (lenOf (ta e f) (tb e f) (tc e f)) .c .B .A c0.tile
      c0.X c0.Y c0.Z := by
    have := c0.h; rw [← e0] at this; exact this
  rw [hX0] at t1
  have t2 := c1.h
  rw [← hY01] at t2
  have hlr : c1.tok.left = .A ∨ (c1.tok.side = .b ∧ c1.tok.left = .G ∧ c1.tok.right = .A) := by
    rw [← e1]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hY
    rcases hY with rfl | rfl | rfl <;> simp [Tok.left, Tok.side, Tok.right]
  exact band_C0_full D e f S.he S.hef S.hcop α β γ S.hγdef S.hrel S.hirr S.hα0 S.hβ0 S.hα' S.hβ'
    S.hγ' S.hsa S.hsb S.hsc S.hpq S.hpr S.hqr S.hcB S.haL c0.tile c1.tile hne _ _ _ hlr t1 hZ0 t2

/-- **`C0m` does not occur in the word of a chain** (from `band_C0m_full`). -/
theorem chain_noC0m {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ} {p q r : Fin 3}
    (S : BandSetup D e f α β γ p q r) (ch : BaseChain D e f α β γ p q r) : ¬ winC0m ch.word := by
  rintro ⟨Y, hY, s, hs⟩
  obtain ⟨s', c1, c2, hcs⟩ : ∃ s' c1 c2, ch.cs = s' ++ [c1, c2] := by
    rcases hc : ch.cs.reverse with _ | ⟨c2, _ | ⟨c1, r'⟩⟩
    · have : ch.cs = [] := by simpa using congrArg List.reverse hc
      rw [BaseChain.word, this] at hs; simp at hs
    · have : ch.cs = [c2] := by simpa using congrArg List.reverse hc
      rw [BaseChain.word, this] at hs
      have := congrArg List.length hs
      simp at this
    · refine ⟨r'.reverse, c1, c2, ?_⟩
      simpa using congrArg List.reverse hc
  rw [BaseChain.word, hcs, List.map_append] at hs
  have hsuf := List.append_inj_right' hs (by simp)
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hsuf
  obtain ⟨e1, e2⟩ := hsuf
  have hlink := ch.linked
  rw [hcs] at hlink
  obtain ⟨hY12, hne⟩ := Linked.append_last s' c1 c2 hlink
  have hY2 : c2.Y = D.target.pts q := ch.stop c2 (by rw [hcs]; simp)
  have hZ2 : c2.Z ∈ segment ℝ (D.target.pts q) (D.target.pts r) := ch.topR c2 (by rw [hcs]; simp)
  have t1 : BaseTok D p q (angOf α β γ) (lenOf (ta e f) (tb e f) (tc e f)) .c .A .B c2.tile
      c2.X c2.Y c2.Z := by
    have := c2.h; rw [← e2] at this; exact this
  rw [hY2] at t1
  have t2 := c1.h
  rw [hY12] at t2
  have hlr : c1.tok.right = .A ∨ (c1.tok.side = .b ∧ c1.tok.right = .G ∧ c1.tok.left = .A) := by
    rw [← e1]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hY
    rcases hY with rfl | rfl | rfl <;> simp [Tok.left, Tok.side, Tok.right]
  exact band_C0m_full D e f S.he S.hef S.hcop α β γ S.hγdef S.hrel S.hirr S.hα0 S.hβ0 S.hα' S.hβ'
    S.hγ' S.hsa S.hsb S.hsc S.hpq S.hpr S.hqr S.hcB S.haR c2.tile c1.tile hne.symm _ _ _ hlr t2 t1 hZ2

/-- The same setting read from the other base corner. -/
theorem BandSetup.swap {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ} {p q r : Fin 3}
    (S : BandSetup D e f α β γ p q r) : BandSetup D e f α β γ q p r where
  he := S.he
  hef := S.hef
  hcop := S.hcop
  hγdef := S.hγdef
  hrel := S.hrel
  hirr := S.hirr
  hα0 := S.hα0
  hβ0 := S.hβ0
  hα' := S.hα'
  hβ' := S.hβ'
  hγ' := S.hγ'
  hsa := S.hsa
  hsb := S.hsb
  hsc := S.hsc
  hpq := S.hpq.symm
  hpr := S.hqr
  hqr := S.hpr
  cornerP := S.cornerQ
  cornerQ := S.cornerP
  hcB := by rw [dist_comm]; exact S.hcB
  haL := S.haR
  haR := S.haL

/-- **Rule W2 at the level of tokens (HAND RULE, geometry NOT formalized).**  `PROOF_W2.md`
(audited, `AUDIT_W2.md`: sound with gaps; the gaps are L3 for the chord `P₂V₂`, "the points `P, G₁, G₂`
are vertices of every incident tile", and `a < b` in two subcases that is harmless): in the band
setting with `e ≥ 2`, `f ≥ 3` and left leg `> 2a`, a base word cannot begin `cBA, cBA, X` with
`X ∈ {bAG, cAB, bGA}`.  Stated here as a `Prop` so that the theorems below are *conditional on it*,
and become unconditional the moment a proof of `W2Rule e f` is supplied. -/
def W2Rule (e f : ℕ) : Prop :=
  ∀ (N : ℕ) (D : CongruentDissection N) (α β γ : ℝ) (p q r : Fin 3),
    BandSetup D e f α β γ p q r → 2 ≤ e → 3 ≤ f →
    2 * (ta e f : ℝ) < dist (D.target.pts p) (D.target.pts r) →
    ∀ (i1 i2 i3 : Fin N), i2 ≠ i1 → i3 ≠ i2 →
    ∀ (P1 P2 P3 G1 G2 Z3 : Plane) (x3 : Side) (l3 r3 : Corner),
      ((x3 = .b ∧ l3 = .A) ∨ (x3 = .c ∧ l3 = .A) ∨ (x3 = .b ∧ l3 = .G ∧ r3 = .A)) →
      BaseTok D p q (angOf α β γ) (lenOf (ta e f) (tb e f) (tc e f)) .c .B .A i1
        (D.target.pts p) P1 G1 →
      G1 ∈ segment ℝ (D.target.pts p) (D.target.pts r) →
      BaseTok D p q (angOf α β γ) (lenOf (ta e f) (tb e f) (tc e f)) .c .B .A i2 P1 P2 G2 →
      BaseTok D p q (angOf α β γ) (lenOf (ta e f) (tb e f) (tc e f)) x3 l3 r3 i3 P2 P3 Z3 →
      False

/-- `W2` does not occur in the word of a chain, given `W2Rule`. -/
theorem chain_noW2 {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ} {p q r : Fin 3}
    (hW : W2Rule e f) (S : BandSetup D e f α β γ p q r) (he2 : 2 ≤ e) (hf3 : 3 ≤ f)
    (hL2 : 2 * (ta e f : ℝ) < dist (D.target.pts p) (D.target.pts r))
    (ch : BaseChain D e f α β γ p q r) : ¬ winW2 ch.word := by
  rintro ⟨Y, hY, s, hs⟩
  obtain ⟨c0, c1, c2, cs', hcs⟩ : ∃ c0 c1 c2 cs', ch.cs = c0 :: c1 :: c2 :: cs' := by
    rcases hc : ch.cs with _ | ⟨c0, _ | ⟨c1, _ | ⟨c2, cs'⟩⟩⟩
    · rw [BaseChain.word, hc] at hs; simp at hs
    · rw [BaseChain.word, hc] at hs; simp at hs
    · rw [BaseChain.word, hc] at hs; simp at hs
    · exact ⟨c0, c1, c2, cs', rfl⟩
  rw [BaseChain.word, hcs] at hs
  simp only [List.map_cons, List.cons_append, List.nil_append, List.cons.injEq] at hs
  obtain ⟨e0, e1, e2, -⟩ := hs
  have hlink := ch.linked
  rw [hcs] at hlink
  obtain ⟨hY01, hne1, hY12, hne2, -⟩ := hlink
  have hX0 : c0.X = D.target.pts p := ch.start c0 (by rw [hcs]; rfl)
  have hZ0 : c0.Z ∈ segment ℝ (D.target.pts p) (D.target.pts r) := ch.topL c0 (by rw [hcs]; rfl)
  have t1 : BaseTok D p q (angOf α β γ) (lenOf (ta e f) (tb e f) (tc e f)) .c .B .A c0.tile
      c0.X c0.Y c0.Z := by
    have := c0.h; rw [← e0] at this; exact this
  rw [hX0] at t1
  have t2 : BaseTok D p q (angOf α β γ) (lenOf (ta e f) (tb e f) (tc e f)) .c .B .A c1.tile
      c1.X c1.Y c1.Z := by
    have := c1.h; rw [← e1] at this; exact this
  rw [← hY01] at t2
  have t3 := c2.h
  rw [← hY12] at t3
  have hlr : (c2.tok.side = .b ∧ c2.tok.left = .A) ∨ (c2.tok.side = .c ∧ c2.tok.left = .A) ∨
      (c2.tok.side = .b ∧ c2.tok.left = .G ∧ c2.tok.right = .A) := by
    rw [← e2]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hY
    rcases hY with rfl | rfl | rfl <;> simp [Tok.left, Tok.side, Tok.right]
  exact hW N D α β γ p q r S he2 hf3 hL2 c0.tile c1.tile c2.tile hne1 hne2 _ _ _ _ _ _ _ _ _ hlr
    t1 hZ0 t2 t3

/-- `W2m` does not occur in the word of a chain, given `W2Rule` (by reflecting the base). -/
theorem chain_noW2m {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ} {p q r : Fin 3}
    (hW : W2Rule e f) (S : BandSetup D e f α β γ p q r) (he2 : 2 ≤ e) (hf3 : 3 ≤ f)
    (hR2 : 2 * (ta e f : ℝ) < dist (D.target.pts q) (D.target.pts r))
    (ch : BaseChain D e f α β γ p q r) : ¬ winW2m ch.word := by
  rintro ⟨Y, hY, s, hs⟩
  obtain ⟨s', c1, c2, c3, hcs⟩ : ∃ s' c1 c2 c3, ch.cs = s' ++ [c1, c2, c3] := by
    rcases hc : ch.cs.reverse with _ | ⟨c3, _ | ⟨c2, _ | ⟨c1, r'⟩⟩⟩
    · have : ch.cs = [] := by simpa using congrArg List.reverse hc
      rw [BaseChain.word, this] at hs; simp at hs
    · have : ch.cs = [c3] := by simpa using congrArg List.reverse hc
      rw [BaseChain.word, this] at hs
      have := congrArg List.length hs; simp at this
    · have : ch.cs = [c2, c3] := by simpa using congrArg List.reverse hc
      rw [BaseChain.word, this] at hs
      have := congrArg List.length hs; simp at this
    · refine ⟨r'.reverse, c1, c2, c3, ?_⟩
      simpa using congrArg List.reverse hc
  rw [BaseChain.word, hcs, List.map_append] at hs
  have hsuf := List.append_inj_right' hs (by simp)
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hsuf
  obtain ⟨e1, e2, e3⟩ := hsuf
  have hlink := ch.linked
  rw [hcs] at hlink
  obtain ⟨⟨hY12, hne12⟩, ⟨hY23, hne23⟩⟩ := Linked.append_three s' c1 c2 c3 hlink
  have hY3 : c3.Y = D.target.pts q := ch.stop c3 (by rw [hcs]; simp)
  have hZ3 : c3.Z ∈ segment ℝ (D.target.pts q) (D.target.pts r) := ch.topR c3 (by rw [hcs]; simp)
  have t1 : BaseTok D p q (angOf α β γ) (lenOf (ta e f) (tb e f) (tc e f)) .c .A .B c3.tile
      c3.X c3.Y c3.Z := by
    have := c3.h; rw [← e3] at this; exact this
  have t2 : BaseTok D p q (angOf α β γ) (lenOf (ta e f) (tb e f) (tc e f)) .c .A .B c2.tile
      c2.X c2.Y c2.Z := by
    have := c2.h; rw [← e2] at this; exact this
  have t1' := t1.reflect
  have t2' := t2.reflect
  have t3' := c1.h.reflect
  rw [hY3] at t1'
  rw [hY23] at t2'
  rw [hY12] at t3'
  have hlr : (c1.tok.side = .b ∧ c1.tok.right = .A) ∨ (c1.tok.side = .c ∧ c1.tok.right = .A) ∨
      (c1.tok.side = .b ∧ c1.tok.right = .G ∧ c1.tok.left = .A) := by
    rw [← e1]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hY
    rcases hY with rfl | rfl | rfl <;> simp [Tok.left, Tok.side, Tok.right]
  exact hW N D α β γ q p r S.swap he2 hf3 hR2 c3.tile c2.tile c1.tile hne23.symm hne12.symm _ _ _ _ _ _ _ _ _
    hlr t1' hZ3 t2' t3'

/-- **Theorem U for real tilings (`d ≤ 1`), no hypothesis on W2.**  Let `ch` be the base chain of a real
dissection of the band target.  If the word has no `a`-token and exactly `K` `c`-tokens (Prop. B1:
`K = 2Me`), its end tokens have the corner angle `β`, it carries a run of `f ≥ 2` equal `c`-tokens
(`thm:siderunall`), and `K ≤ f + 1`, then `False`. -/
theorem U_real {D : CongruentDissection N} {e f K : ℕ} {α β γ : ℝ} {p q r : Fin 3}
    (S : BandSetup D e f α β γ p q r) (ch : BaseChain D e f α β γ p q r)
    (hno : ∀ t ∈ ch.word, t.side ≠ .a)
    (hfirst : ∃ t, ch.word.head? = some t ∧ okFirst t)
    (hlast : ∃ t, ch.word.getLast? = some t ∧ okLast t)
    (hrun : HasRun f ch.word) (hcount : countC ch.word = K) (hf : 2 ≤ f) (hd : K ≤ f + 1) :
    False := by
  rcases U_core f K ch.word hno hfirst hlast hrun hcount hf hd with h | h
  · exact chain_noC0 S ch h
  · exact chain_noC0m S ch h

/-- **Theorem U2 for real tilings (`d ≤ 2`), conditional on the hand rule `W2Rule e f`.** -/
theorem U2_real {D : CongruentDissection N} {e f K : ℕ} {α β γ : ℝ} {p q r : Fin 3}
    (hW : W2Rule e f) (S : BandSetup D e f α β γ p q r) (he2 : 2 ≤ e)
    (hL2 : 2 * (ta e f : ℝ) < dist (D.target.pts p) (D.target.pts r))
    (hR2 : 2 * (ta e f : ℝ) < dist (D.target.pts q) (D.target.pts r))
    (ch : BaseChain D e f α β γ p q r)
    (hno : ∀ t ∈ ch.word, t.side ≠ .a)
    (hfirst : ∃ t, ch.word.head? = some t ∧ okFirst t)
    (hlast : ∃ t, ch.word.getLast? = some t ∧ okLast t)
    (hrun : HasRun f ch.word) (hcount : countC ch.word = K) (hf : 3 ≤ f) (hd : K ≤ f + 2) :
    False := by
  rcases U2_core f K ch.word hno hfirst hlast hrun hcount hf hd with h | h | h | h
  · exact chain_noC0 S ch h
  · exact chain_noC0m S ch h
  · exact chain_noW2 hW S he2 hf hL2 ch h
  · exact chain_noW2m hW S he2 hf hR2 ch h

#print axioms chain_noC0
#print axioms chain_noC0m
#print axioms U_real
#print axioms U2_real

end Erdos634.LaczJunction
