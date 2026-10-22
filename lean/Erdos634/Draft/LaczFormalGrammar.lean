import Erdos634.Draft.LaczFormalJunctionTok

/-!
# The band base-word grammar and the counting theorems U, U2 (purely combinatorial)

Erdős #634, base-`β` band.  Credit: AI assistant (item 3, the band program, the `L*/J/R` decomposition),
Beeson–Roșu (tiles, Lemma 34, the template for runs), Beeson, Laczkovich, Paliy, Zhang, and the authors
of the word enumerator ((private working notes, not included)).  Hand proof: `PROOF_U.md`
((private working notes, not included)).  STATUS: UNAUDITED by a second reader.  Axiom-clean.

## What is modelled
The six tokens `A1 … C2` of `gram.rs` (`TYPE`: `(left angle, side)`), the angle vectors `ANG`
(`α = (1,−2)`, `β = (−1,3)`, `γ = (1,−1)`, `π = (1,0)`, so `3α + 2β = π` and `γ = 2α + β`), the
representability test `rep x ⇔ x ∈ ℕα + ℕβ` and the three local conditions
`okFirst`, `okPair`, `okLast` (`ok_first`, `ok_pair`, `ok_last` for the isosceles target `T`, whose two
base corners are `β`), the total length, the run condition (`f` consecutive equal `c`-tokens, the `nrun`
state of `gram.rs`), and the *forbidden windows*: `S`, `E`, `I`, `Im`, `C0`, `C0m`, `W2`, `W2m`.

## What is NOT modelled (named, honest)
* That the census words `gram.rs` enumerates are exactly the words satisfying these predicates is a
  transcription (the `rep` test and the `nrun` run state are re-expressed, not imported).
* That every base word of a real tiling is a grammar word with the counts `(0, Me, 2Me)` is the Band
  Lemma / Proposition B1 (hand proof, brute-checked) together with `thm:siderunall` (Lean).  Here those
  appear only as the *hypotheses* `(∀ t ∈ w, t.side ≠ a)`, `countC w = 2Me`, `HasRun f w`.
* That a window is forbidden for a tiling is the Lean token theorems (`band_S_tok`, `band_E_tok`,
  `band_I_tok`, `band_Im_tok`, `band_C0_full`, `band_C0m_full`; `W2` is the hand rule, see
  `LaczFormalChain`).  This file only does the counting.

## Results (uniform in all parameters; no per-instance computation)
* `window_free_prefix_suffix`: a no-`a` word with `okFirst`, `okLast`, length `≥ 3` that avoids
  `C0, C0m, W2, W2m` begins `cBA³` and ends `cAB³` (avoiding only `C0, C0m`: `cBA²`, `cAB²`).
* `count_prefix_run`: the counting lemma (a prefix `x^k` and an infix run `y^f`, `x ≠ y` both `c`-tokens,
  force `k + f` `c`-tokens).
* `U2_grammar`: if `2Me ≤ f + 2` (`d ≤ 2`), every such grammar word with `countC = 2Me` contains `C0, C0m, W2`
  or `W2m`; `U_grammar`: if `2Me ≤ f + 1` already `C0` or `C0m`.
* Negative control (`survivor_*`): the d = 3 word `cBA³ bAG⁸ cAB¹³` of `T₂(4,13)` is a grammar word with no
  forbidden window, so the theorem is sharp in `d`; and `example_d1_*`: at `T₁(2,3)` (`d = 1`) a grammar
  word exists (it contains `C0`), so the hypotheses of `U_grammar` are satisfiable.
-/

namespace Erdos634.LaczJunction.Grammar

open Erdos634.LaczJunction

/-- The six tokens of `gram.rs`: `A1 = aBG, A2 = aGB, B1 = bAG, B2 = bGA, C1 = cAB, C2 = cBA`. -/
inductive Tok | aBG | aGB | bAG | bGA | cAB | cBA
  deriving DecidableEq, Repr, Fintype

def Tok.side : Tok → Side
  | .aBG | .aGB => .a
  | .bAG | .bGA => .b
  | .cAB | .cBA => .c

def Tok.left : Tok → Corner
  | .aBG => .B | .aGB => .G | .bAG => .A | .bGA => .G | .cAB => .A | .cBA => .B

def Tok.right : Tok → Corner
  | .aBG => .G | .aGB => .B | .bAG => .G | .bGA => .A | .cAB => .B | .cBA => .A

/-- The token list reads `(left, side)` as `tokType` of `LaczFormalJunctionTok`. -/
theorem tok_matches_tokType :
    ([Tok.aBG, .aGB, .bAG, .bGA, .cAB, .cBA].map fun t => (t.left, t.side)) = tokType := by
  decide

/-- The right angle is `3 − left − side` (`gram.rs`, `right`). -/
theorem right_eq_rightIdx : ∀ t : Tok, t.right.idx = rightIdx t.left t.side := by decide

/-- Angle vectors in the basis of `gram.rs` (`ANG`). -/
def angv : Corner → ℤ × ℤ
  | .A => (1, -2)
  | .B => (-1, 3)
  | .G => (1, -1)

/-- `x ∈ ℕα + ℕβ` (the representability test `rep` of `gram.rs`). -/
def rep (x : ℤ × ℤ) : Prop := 0 ≤ 2 * x.1 + x.2 ∧ 0 ≤ 3 * x.1 + x.2

instance (x : ℤ × ℤ) : Decidable (rep x) := inferInstanceAs (Decidable (_ ∧ _))

/-- `3α + 2β = π = (1,0)` and `γ = 2α + β`: the vectors are the claimed angles. -/
theorem angv_rel : 3 • angv .A + 2 • angv .B = (1, 0) ∧ angv .G = 2 • angv .A + angv .B := by
  decide

/-- `rep` is exactly representability as `pα + qβ`, `p, q ≥ 0`. -/
theorem rep_iff (x : ℤ × ℤ) :
    rep x ↔ ∃ p q : ℕ, x = (p : ℤ) • angv .A + (q : ℤ) • angv .B := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨(3 * x.1 + x.2).toNat, (2 * x.1 + x.2).toNat, ?_⟩
    ext <;> simp [angv] <;> omega
  · rintro ⟨p, q, rfl⟩
    simp only [rep, angv]
    constructor <;> simp <;> omega

/-- `ok_first` for the isosceles target (corner angle `β`). -/
def okFirst (t : Tok) : Prop := rep (angv .B - angv t.left)
/-- `ok_last` for the isosceles target (corner angle `β`). -/
def okLast (t : Tok) : Prop := rep (angv .B - angv t.right)
/-- `ok_pair u v`: what is left at the junction, `π − right u − left v`, is representable. -/
def okPair (u v : Tok) : Prop := rep ((1, 0) - angv u.right - angv v.left)

instance (t : Tok) : Decidable (okFirst t) := inferInstanceAs (Decidable (rep _))
instance (t : Tok) : Decidable (okLast t) := inferInstanceAs (Decidable (rep _))
instance (u v : Tok) : Decidable (okPair u v) := inferInstanceAs (Decidable (rep _))

theorem okFirst_iff (t : Tok) : okFirst t ↔ t.left = .B := by cases t <;> decide
theorem okLast_iff (t : Tok) : okLast t ↔ t.right = .B := by cases t <;> decide


/-- The local tables agree with `gram.rs` (checked against an independent transcription of `ok_pair`,
`ok_first`, `ok_last` for the isosceles target; order `aBG, aGB, bAG, bGA, cAB, cBA`). -/
theorem okPair_table :
    ([Tok.aBG, .aGB, .bAG, .bGA, .cAB, .cBA].map fun u =>
      [Tok.aBG, .aGB, .bAG, .bGA, .cAB, .cBA].map fun v => decide (okPair u v)) =
    [[true, false, true, false, true, true], [true, true, true, true, true, true],
     [true, false, true, false, true, true], [true, true, true, true, true, true],
     [true, true, true, true, true, true], [true, true, true, true, true, true]] := by decide

theorem okFirstLast_table :
    ([Tok.aBG, .aGB, .bAG, .bGA, .cAB, .cBA].map fun t => (decide (okFirst t), decide (okLast t))) =
    [(true, false), (false, true), (false, false), (false, false), (false, true), (true, false)] := by
  decide

/-- The consecutive-pair condition along a word. -/
def pairsOk : List Tok → Prop
  | [] => True
  | [_] => True
  | u :: v :: r => okPair u v ∧ pairsOk (v :: r)

/-- The local grammar of an isosceles-target base word. -/
def okWord (w : List Tok) : Prop :=
  (∃ t, w.head? = some t ∧ okFirst t) ∧ pairsOk w ∧ (∃ t, w.getLast? = some t ∧ okLast t)

/-- Length of a token (`a, b, c = ef, f² − e², f²`). -/
def wt (e f : ℕ) (t : Tok) : ℕ :=
  match t.side with
  | .a => e * f
  | .b => f ^ 2 - e ^ 2
  | .c => f ^ 2

def total (e f : ℕ) (w : List Tok) : ℕ := (w.map (wt e f)).sum

/-- Number of `c`-tokens. -/
def countC (w : List Tok) : ℕ := w.countP (fun t => decide (t.side = .c))

/-- The run condition (`nrun` of `gram.rs`): `f` consecutive equal `c`-tokens (`C1` or `C2`). -/
def HasRun (f : ℕ) (w : List Tok) : Prop :=
  ∃ t, (t = Tok.cAB ∨ t = Tok.cBA) ∧ List.replicate f t <:+: w

/-- A grammar word of the isosceles target `T_M(e,f)`: local conditions, total length
`M e (3f² − e²)`, run of `f` equal `c`-tokens. -/
structure Gram (e f M : ℕ) (w : List Tok) : Prop where
  ok : okWord w
  len : total e f w = M * e * (3 * f ^ 2 - e ^ 2)
  run : HasRun f w

/-! ## The forbidden windows -/

def winS (w : List Tok) : Prop := [Tok.cBA, Tok.bGA] <+: w
def winE (w : List Tok) : Prop := [Tok.bAG, Tok.cAB] <:+ w
def winI (w : List Tok) : Prop :=
  ∃ X, (X.right = .B ∨ X.right = .G) ∧ [X, Tok.cBA, Tok.bGA] <:+: w
def winIm (w : List Tok) : Prop :=
  ∃ Y, (Y.left = .B ∨ Y.left = .G) ∧ [Tok.bAG, Tok.cAB, Y] <:+: w
/-- `C0`: begins `cBA, Y` with `Y ∈ {bAG, cAB, bGA}`. -/
def winC0 (w : List Tok) : Prop := ∃ Y ∈ [Tok.bAG, Tok.cAB, Tok.bGA], [Tok.cBA, Y] <+: w
/-- `C0m`: ends `Y, cAB` with `Y ∈ {bGA, cBA, bAG}`. -/
def winC0m (w : List Tok) : Prop := ∃ Y ∈ [Tok.bGA, Tok.cBA, Tok.bAG], [Y, Tok.cAB] <:+ w
/-- `W2`: begins `cBA, cBA, Y` with `Y ∈ {bAG, cAB, bGA}`. -/
def winW2 (w : List Tok) : Prop :=
  ∃ Y ∈ [Tok.bAG, Tok.cAB, Tok.bGA], [Tok.cBA, Tok.cBA, Y] <+: w
/-- `W2m`: ends `Y, cAB, cAB` with `Y ∈ {bGA, cBA, bAG}`. -/
def winW2m (w : List Tok) : Prop :=
  ∃ Y ∈ [Tok.bGA, Tok.cBA, Tok.bAG], [Y, Tok.cAB, Tok.cAB] <:+ w

/-- The reflection of a token: `x l r ↦ x r l`. -/
def Tok.mirror : Tok → Tok
  | .aBG => .aGB | .aGB => .aBG | .bAG => .bGA | .bGA => .bAG | .cAB => .cBA | .cBA => .cAB

theorem Tok.mirror_cAB : Tok.cAB.mirror = Tok.cBA := rfl
theorem Tok.mirror_cBA : Tok.cBA.mirror = Tok.cAB := rfl
theorem Tok.mirror_mirror (t : Tok) : t.mirror.mirror = t := by cases t <;> rfl
theorem Tok.mirror_left (t : Tok) : t.mirror.left = t.right := by cases t <;> rfl
theorem Tok.mirror_right (t : Tok) : t.mirror.right = t.left := by cases t <;> rfl
theorem Tok.mirror_side (t : Tok) : t.mirror.side = t.side := by cases t <;> rfl

/-- The reflected word (read from the other end of the base). -/
def mirrorWord (w : List Tok) : List Tok := (w.map Tok.mirror).reverse

theorem mirrorWord_mirrorWord (w : List Tok) : mirrorWord (mirrorWord w) = w := by
  simp [mirrorWord, List.map_reverse, List.map_map, Function.comp_def, Tok.mirror_mirror]

theorem map_isSuffix_iff {m : Tok → Tok} (hm : ∀ t, m (m t) = t) {l w : List Tok} :
    l.map m <:+ w.map m ↔ l <:+ w := by
  refine ⟨fun h => ?_, fun h => h.map m⟩
  have := h.map m
  simpa [List.map_map, Function.comp_def, hm] using this

theorem map_isPrefix_iff {m : Tok → Tok} (hm : ∀ t, m (m t) = t) {l w : List Tok} :
    l.map m <+: w.map m ↔ l <+: w := by
  refine ⟨fun h => ?_, fun h => h.map m⟩
  have := h.map m
  simpa [List.map_map, Function.comp_def, hm] using this

/-- `l <:+ w` iff the reversed mirror of `l` is a prefix of the mirror word. -/
theorem suffix_iff_mirror_prefix (l w : List Tok) :
    l <:+ w ↔ (l.map Tok.mirror).reverse <+: mirrorWord w := by
  unfold mirrorWord
  rw [List.reverse_prefix, map_isSuffix_iff Tok.mirror_mirror]

/-- `C0m` is `C0` for the reflected word. -/
theorem winC0m_iff (w : List Tok) : winC0m w ↔ winC0 (mirrorWord w) := by
  unfold winC0m winC0
  constructor
  · rintro ⟨Y, hY, h⟩
    refine ⟨Y.mirror, ?_, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hY ⊢
      rcases hY with rfl | rfl | rfl <;> simp [Tok.mirror]
    · have := (suffix_iff_mirror_prefix _ w).1 h
      simpa [Tok.mirror_cAB, Tok.mirror_cBA] using this
  · rintro ⟨Y, hY, h⟩
    refine ⟨Y.mirror, ?_, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hY ⊢
      rcases hY with rfl | rfl | rfl <;> simp [Tok.mirror]
    · apply (suffix_iff_mirror_prefix _ w).2
      simpa [Tok.mirror_mirror, Tok.mirror_cAB, Tok.mirror_cBA] using h

/-- `W2m` is `W2` for the reflected word. -/
theorem winW2m_iff (w : List Tok) : winW2m w ↔ winW2 (mirrorWord w) := by
  unfold winW2m winW2
  constructor
  · rintro ⟨Y, hY, h⟩
    refine ⟨Y.mirror, ?_, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hY ⊢
      rcases hY with rfl | rfl | rfl <;> simp [Tok.mirror]
    · have := (suffix_iff_mirror_prefix _ w).1 h
      simpa [Tok.mirror_cAB, Tok.mirror_cBA] using this
  · rintro ⟨Y, hY, h⟩
    refine ⟨Y.mirror, ?_, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hY ⊢
      rcases hY with rfl | rfl | rfl <;> simp [Tok.mirror]
    · apply (suffix_iff_mirror_prefix _ w).2
      simpa [Tok.mirror_mirror, Tok.mirror_cAB, Tok.mirror_cBA] using h

/-- `E` is `S` for the reflected word. -/
theorem winE_iff (w : List Tok) : winE w ↔ winS (mirrorWord w) := by
  unfold winE winS
  rw [suffix_iff_mirror_prefix]
  simp [Tok.mirror]

/-! ## Counting -/

theorem countC_append (u v : List Tok) : countC (u ++ v) = countC u + countC v := by
  unfold countC; exact List.countP_append

theorem countC_reverse (u : List Tok) : countC u.reverse = countC u := by
  unfold countC; exact List.countP_reverse

theorem countC_replicate {t : Tok} (h : t.side = .c) (k : ℕ) : countC (List.replicate k t) = k := by
  unfold countC
  rw [List.countP_replicate]; simp [h]

theorem countC_cons (t : Tok) (u : List Tok) :
    countC (t :: u) = (if t.side = .c then 1 else 0) + countC u := by
  unfold countC
  rw [List.countP_cons]; split_ifs <;> simp_all <;> omega

theorem countC_le_length (u : List Tok) : countC u ≤ u.length := by
  unfold countC; exact List.countP_le_length

/-- **Counting lemma.**  A prefix `x^k` and a disjoint-type infix run `y^f` (`x ≠ y`, both `c`-tokens)
force `k + f` `c`-tokens. -/
theorem count_prefix_run {x y : Tok} (hx : x.side = .c) (hy : y.side = .c) (hxy : x ≠ y) :
    ∀ (k f : ℕ) (w s u v : List Tok), 1 ≤ f → w = List.replicate k x ++ s →
      w = u ++ (List.replicate f y ++ v) → k + f ≤ countC w := by
  intro k
  induction k with
  | zero =>
    intro f w s u v hf _ h2
    rw [h2, countC_append, countC_append, countC_replicate hy]
    omega
  | succ k ih =>
    intro f w s u v hf h1 h2
    cases u with
    | nil =>
      obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
      simp only [List.nil_append, List.replicate_succ, List.cons_append] at h2
      rw [List.replicate_succ, List.cons_append] at h1
      rw [h1] at h2
      exact absurd (List.cons.inj h2).1 hxy
    | cons z u' =>
      rw [List.replicate_succ, List.cons_append] at h1
      rw [List.cons_append] at h2
      rw [h1] at h2
      obtain ⟨hz, htl⟩ := List.cons.inj h2
      have := ih f (List.replicate k x ++ s) s u' v hf rfl htl
      rw [h1, countC_cons, if_pos hx]
      omega

/-- Same with a *suffix* `x^k` (apply the lemma to the reversed word). -/
theorem count_suffix_run {x y : Tok} (hx : x.side = .c) (hy : y.side = .c) (hxy : x ≠ y)
    (k f : ℕ) (w s u v : List Tok) (hf : 1 ≤ f) (h1 : w = s ++ List.replicate k x)
    (h2 : w = u ++ (List.replicate f y ++ v)) : k + f ≤ countC w := by
  have h1' : w.reverse = List.replicate k x ++ s.reverse := by
    rw [h1, List.reverse_append, List.reverse_replicate]
  have h2' : w.reverse = v.reverse ++ (List.replicate f y ++ u.reverse) := by
    rw [h2, List.reverse_append, List.reverse_append, List.reverse_replicate, List.append_assoc]
  have := count_prefix_run hx hy hxy k f w.reverse s.reverse v.reverse u.reverse hf h1' h2'
  rwa [countC_reverse] at this

/-! ## Window-free words begin `cBA^k` and end `cAB^k` -/

theorem tok_left_B_noa {t : Tok} (h : t.left = .B) (hno : t.side ≠ .a) : t = .cBA := by
  cases t <;> simp_all [Tok.left, Tok.side]

theorem tok_right_B_noa {t : Tok} (h : t.right = .B) (hno : t.side ≠ .a) : t = .cAB := by
  cases t <;> simp_all [Tok.right, Tok.side]

/-- A no-`a` word with `okFirst` that avoids `C0` begins `cBA, cBA`. -/
theorem prefix2 (w : List Tok) (hno : ∀ t ∈ w, t.side ≠ .a)
    (hf : ∃ t, w.head? = some t ∧ okFirst t) (h2 : 2 ≤ w.length) (h0 : ¬ winC0 w) :
    List.replicate 2 Tok.cBA <+: w := by
  match w, hf, h2 with
  | t0 :: t1 :: r, ⟨t, ht, hok⟩, _ =>
    have e : t = t0 := by simpa using ht.symm
    subst e
    have h0' : t.left = .B := (okFirst_iff t).1 hok
    have ht0 : t = .cBA := tok_left_B_noa h0' (hno t (by simp))
    subst ht0
    have h1a : t1.side ≠ .a := hno t1 (by simp)
    cases t1 with
    | aBG => exact absurd rfl h1a
    | aGB => exact absurd rfl h1a
    | bAG => exact absurd ⟨.bAG, by simp, r, rfl⟩ h0
    | bGA => exact absurd ⟨.bGA, by simp, r, rfl⟩ h0
    | cAB => exact absurd ⟨.cAB, by simp, r, rfl⟩ h0
    | cBA => exact ⟨r, rfl⟩

/-- ... and avoiding `W2` as well, `cBA, cBA, cBA`. -/
theorem prefix3 (w : List Tok) (hno : ∀ t ∈ w, t.side ≠ .a)
    (hf : ∃ t, w.head? = some t ∧ okFirst t) (h3 : 3 ≤ w.length) (h0 : ¬ winC0 w)
    (h2 : ¬ winW2 w) : List.replicate 3 Tok.cBA <+: w := by
  have hp := prefix2 w hno hf (by omega) h0
  match w, hp, h3 with
  | t0 :: t1 :: t2 :: r, ⟨s, hs⟩, _ =>
    simp only [List.replicate_succ, List.replicate_zero, List.cons_append, List.nil_append,
      List.cons.injEq] at hs
    obtain ⟨rfl, rfl, -⟩ := hs
    have h2a : t2.side ≠ .a := hno t2 (by simp)
    cases t2 with
    | aBG => exact absurd rfl h2a
    | aGB => exact absurd rfl h2a
    | bAG => exact absurd ⟨.bAG, by simp, r, rfl⟩ h2
    | bGA => exact absurd ⟨.bGA, by simp, r, rfl⟩ h2
    | cAB => exact absurd ⟨.cAB, by simp, r, rfl⟩ h2
    | cBA => exact ⟨r, rfl⟩

theorem mirrorWord_length (w : List Tok) : (mirrorWord w).length = w.length := by
  simp [mirrorWord]

theorem mirrorWord_noa (w : List Tok) (hno : ∀ t ∈ w, t.side ≠ .a) :
    ∀ t ∈ mirrorWord w, t.side ≠ .a := by
  intro t ht
  simp only [mirrorWord, List.mem_reverse, List.mem_map] at ht
  obtain ⟨u, hu, rfl⟩ := ht
  rw [Tok.mirror_side]; exact hno u hu

theorem mirrorWord_okFirst (w : List Tok) (hl : ∃ t, w.getLast? = some t ∧ okLast t) :
    ∃ t, (mirrorWord w).head? = some t ∧ okFirst t := by
  obtain ⟨t, ht, hok⟩ := hl
  refine ⟨t.mirror, ?_, ?_⟩
  · simp [mirrorWord, List.head?_reverse, ht]
  · rw [okFirst_iff, Tok.mirror_left]; exact (okLast_iff t).1 hok

theorem suffix_of_mirror_prefix {k : ℕ} (w : List Tok)
    (h : List.replicate k Tok.cBA <+: mirrorWord w) : List.replicate k Tok.cAB <:+ w := by
  rw [suffix_iff_mirror_prefix]
  simpa [List.map_replicate, Tok.mirror_cAB] using h

/-- Window-free words end `cAB, cAB, cAB`. -/
theorem suffix3 (w : List Tok) (hno : ∀ t ∈ w, t.side ≠ .a)
    (hl : ∃ t, w.getLast? = some t ∧ okLast t) (h3 : 3 ≤ w.length) (h0 : ¬ winC0m w)
    (h2 : ¬ winW2m w) : List.replicate 3 Tok.cAB <:+ w := by
  apply suffix_of_mirror_prefix
  exact prefix3 (mirrorWord w) (mirrorWord_noa w hno) (mirrorWord_okFirst w hl)
    (by rw [mirrorWord_length]; exact h3) (by rwa [← winC0m_iff]) (by rwa [← winW2m_iff])

theorem suffix2 (w : List Tok) (hno : ∀ t ∈ w, t.side ≠ .a)
    (hl : ∃ t, w.getLast? = some t ∧ okLast t) (h2 : 2 ≤ w.length) (h0 : ¬ winC0m w) :
    List.replicate 2 Tok.cAB <:+ w := by
  apply suffix_of_mirror_prefix
  exact prefix2 (mirrorWord w) (mirrorWord_noa w hno) (mirrorWord_okFirst w hl)
    (by rw [mirrorWord_length]; exact h2) (by rwa [← winC0m_iff])

/-- **The counting step.**  If the word begins `cBA^k`, ends `cAB^k` and carries a run of `f` equal
`c`-tokens, it has at least `f + k` `c`-tokens. -/
theorem count_bound (w : List Tok) (k f : ℕ) (hf : 1 ≤ f)
    (hpre : List.replicate k Tok.cBA <+: w) (hsuf : List.replicate k Tok.cAB <:+ w)
    (hrun : HasRun f w) : f + k ≤ countC w := by
  obtain ⟨t, ht, ⟨u, v, huv⟩⟩ := hrun
  obtain ⟨s, hs⟩ := hpre
  obtain ⟨s', hs'⟩ := hsuf
  have e2 : w = u ++ (List.replicate f t ++ v) := by rw [← huv]; simp
  rcases ht with rfl | rfl
  · have := count_prefix_run (x := Tok.cBA) (y := Tok.cAB) rfl rfl (by decide) k f w s u v hf hs.symm e2
    omega
  · have := count_suffix_run (x := Tok.cAB) (y := Tok.cBA) rfl rfl (by decide) k f w s' u v hf hs'.symm e2
    omega

theorem HasRun.length_le {f : ℕ} {w : List Tok} (h : HasRun f w) : f ≤ w.length := by
  obtain ⟨t, -, hin⟩ := h
  simpa using hin.length_le

/-- **Theorem U, minimal hypotheses.**  A no-`a` word whose first token has left angle `β`, whose last
token has right angle `β`, which carries a run of `f` equal `c`-tokens and has `2Me ≤ f + 1`
`c`-tokens contains `C0` or `C0m`. -/
theorem U_core (f K : ℕ) (w : List Tok) (hno : ∀ t ∈ w, t.side ≠ .a)
    (hfirst : ∃ t, w.head? = some t ∧ okFirst t) (hlast : ∃ t, w.getLast? = some t ∧ okLast t)
    (hrun : HasRun f w) (hcount : countC w = K) (hf : 2 ≤ f) (hd : K ≤ f + 1) :
    winC0 w ∨ winC0m w := by
  by_contra hcon
  simp only [not_or] at hcon
  obtain ⟨h0, h0m⟩ := hcon
  have hlen : f ≤ w.length := hrun.length_le
  have h1 := prefix2 w hno hfirst (by omega) h0
  have h2 := suffix2 w hno hlast (by omega) h0m
  have := count_bound w 2 f (by omega) h1 h2 hrun
  omega

/-- **Theorem U2, minimal hypotheses** (`K ≤ f + 2`; windows `C0, C0m, W2, W2m`). -/
theorem U2_core (f K : ℕ) (w : List Tok) (hno : ∀ t ∈ w, t.side ≠ .a)
    (hfirst : ∃ t, w.head? = some t ∧ okFirst t) (hlast : ∃ t, w.getLast? = some t ∧ okLast t)
    (hrun : HasRun f w) (hcount : countC w = K) (hf : 3 ≤ f) (hd : K ≤ f + 2) :
    winC0 w ∨ winC0m w ∨ winW2 w ∨ winW2m w := by
  by_contra hcon
  simp only [not_or] at hcon
  obtain ⟨h0, h0m, h2, h2m⟩ := hcon
  have hlen : f ≤ w.length := hrun.length_le
  have h1 := prefix3 w hno hfirst (by omega) h0 h2
  have h3 := suffix3 w hno hlast (by omega) h0m h2m
  have := count_bound w 3 f (by omega) h1 h3 hrun
  omega

/-- **Theorem U (grammar form), `d ≤ 1`.**  A grammar word with no `a`-token, `countC = 2Me`
(Prop. B1) and `2Me ≤ f + 1` contains the window `C0` or `C0m`. -/
theorem U_grammar (e f M : ℕ) (w : List Tok) (hG : Gram e f M w) (hno : ∀ t ∈ w, t.side ≠ .a)
    (hcount : countC w = 2 * M * e) (hf : 2 ≤ f) (hd : 2 * M * e ≤ f + 1) :
    winC0 w ∨ winC0m w :=
  U_core f (2 * M * e) w hno hG.ok.1 hG.ok.2.2 hG.run hcount hf hd

/-- **Theorem U2 (grammar form), `d ≤ 2`.**  Same, with the windows `C0, C0m, W2, W2m`. -/
theorem U2_grammar (e f M : ℕ) (w : List Tok) (hG : Gram e f M w) (hno : ∀ t ∈ w, t.side ≠ .a)
    (hcount : countC w = 2 * M * e) (hf : 3 ≤ f) (hd : 2 * M * e ≤ f + 2) :
    winC0 w ∨ winC0m w ∨ winW2 w ∨ winW2m w :=
  U2_core f (2 * M * e) w hno hG.ok.1 hG.ok.2.2 hG.run hcount hf hd

/-! ## Count form of the run hypothesis (no consecutiveness needed) -/

/-- Weak form of the run: at least `f` tokens `cAB`, or at least `f` tokens `cBA`. -/
def RunCount (f : ℕ) (w : List Tok) : Prop := f ≤ w.count Tok.cAB ∨ f ≤ w.count Tok.cBA

theorem HasRun.runCount {f : ℕ} {w : List Tok} (h : HasRun f w) : RunCount f w := by
  obtain ⟨t, ht, hin⟩ := h
  have hsub : (List.replicate f t).Sublist w := hin.sublist
  have := hsub.count_le t
  rw [List.count_replicate_self] at this
  rcases ht with rfl | rfl
  · exact Or.inl this
  · exact Or.inr this

theorem count_add_le_countC (w : List Tok) : w.count Tok.cAB + w.count Tok.cBA ≤ countC w := by
  induction w with
  | nil => simp [countC]
  | cons t r ih =>
    rw [countC_cons]
    rw [List.count_cons, List.count_cons]
    cases t <;> simp [Tok.side] at * <;> omega

theorem count_bound' (w : List Tok) (k f : ℕ)
    (hpre : List.replicate k Tok.cBA <+: w) (hsuf : List.replicate k Tok.cAB <:+ w)
    (hrun : RunCount f w) : f + k ≤ countC w := by
  have h1 : k ≤ w.count Tok.cBA := by
    have := hpre.sublist.count_le Tok.cBA
    rwa [List.count_replicate_self] at this
  have h2 : k ≤ w.count Tok.cAB := by
    have := hsuf.sublist.count_le Tok.cAB
    rwa [List.count_replicate_self] at this
  have := count_add_le_countC w
  rcases hrun with h | h <;> omega

/-- **Theorem U, count form of the run.** -/
theorem U_core' (f K : ℕ) (w : List Tok) (hno : ∀ t ∈ w, t.side ≠ .a)
    (hfirst : ∃ t, w.head? = some t ∧ okFirst t) (hlast : ∃ t, w.getLast? = some t ∧ okLast t)
    (hrun : RunCount f w) (hcount : countC w = K) (hlen : 2 ≤ w.length) (hd : K ≤ f + 1) :
    winC0 w ∨ winC0m w := by
  by_contra hcon
  simp only [not_or] at hcon
  obtain ⟨h0, h0m⟩ := hcon
  have h1 := prefix2 w hno hfirst hlen h0
  have h2 := suffix2 w hno hlast hlen h0m
  have := count_bound' w 2 f h1 h2 hrun
  omega

/-- **Theorem U2, count form of the run.** -/
theorem U2_core' (f K : ℕ) (w : List Tok) (hno : ∀ t ∈ w, t.side ≠ .a)
    (hfirst : ∃ t, w.head? = some t ∧ okFirst t) (hlast : ∃ t, w.getLast? = some t ∧ okLast t)
    (hrun : RunCount f w) (hcount : countC w = K) (hlen : 3 ≤ w.length) (hd : K ≤ f + 2) :
    winC0 w ∨ winC0m w ∨ winW2 w ∨ winW2m w := by
  by_contra hcon
  simp only [not_or] at hcon
  obtain ⟨h0, h0m, h2, h2m⟩ := hcon
  have h1 := prefix3 w hno hfirst hlen h0 h2
  have h3 := suffix3 w hno hlast hlen h0m h2m
  have := count_bound' w 3 f h1 h3 hrun
  omega

/-! ## The windows `M(j)`: `cBA^j X` with `X ≠ cBA`, and the band counting -/

/-- `M(j)`: the word begins `cBA^j, X` with `X ∈ {bAG, cAB, bGA}`. -/
def winM (j : ℕ) (w : List Tok) : Prop :=
  ∃ X ∈ [Tok.bAG, Tok.cAB, Tok.bGA], (List.replicate j Tok.cBA ++ [X]) <+: w

/-- Mirror `M(k)`: the word ends `X, cAB^k` with `X ∈ {bGA, cBA, bAG}`. -/
def winMm (k : ℕ) (w : List Tok) : Prop :=
  ∃ X ∈ [Tok.bGA, Tok.cBA, Tok.bAG], ([X] ++ List.replicate k Tok.cAB) <:+ w

theorem winMm_iff (k : ℕ) (w : List Tok) : winMm k w ↔ winM k (mirrorWord w) := by
  unfold winMm winM
  constructor
  · rintro ⟨X, hX, h⟩
    refine ⟨X.mirror, ?_, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hX ⊢
      rcases hX with rfl | rfl | rfl <;> simp [Tok.mirror]
    · have := (suffix_iff_mirror_prefix _ w).1 h
      simpa [List.map_replicate, Tok.mirror_cAB, Tok.mirror_cBA] using this
  · rintro ⟨X, hX, h⟩
    refine ⟨X.mirror, ?_, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hX ⊢
      rcases hX with rfl | rfl | rfl <;> simp [Tok.mirror]
    · apply (suffix_iff_mirror_prefix _ w).2
      simpa [List.map_replicate, Tok.mirror_cAB, Tok.mirror_cBA, Tok.mirror_mirror] using h

theorem initial_run (w : List Tok) (hno : ∀ t ∈ w, t.side ≠ .a) (hhead : w.head? = some Tok.cBA)
    (hnon : ∃ t ∈ w, t ≠ Tok.cBA) : ∃ i, 1 ≤ i ∧ winM i w ∧ i ≤ w.count Tok.cBA := by
  induction w with
  | nil => simp at hhead
  | cons t0 r ih =>
    have ht0 : t0 = Tok.cBA := by simpa using hhead
    subst ht0
    cases r with
    | nil => obtain ⟨t, ht, hne⟩ := hnon; simp at ht; exact absurd ht hne
    | cons X r' =>
      by_cases hX : X = Tok.cBA
      · subst hX
        obtain ⟨i', hi', hw, hc⟩ := ih (fun t ht => hno t (List.mem_cons_of_mem _ ht)) (by simp)
          (by
            obtain ⟨t, ht, hne⟩ := hnon
            rcases List.mem_cons.mp ht with rfl | ht'
            · exact absurd rfl hne
            · exact ⟨t, ht', hne⟩)
        refine ⟨i' + 1, by omega, ?_, ?_⟩
        · obtain ⟨Y, hY, t, ht⟩ := hw
          refine ⟨Y, hY, t, ?_⟩
          rw [← ht]; simp [List.replicate_succ]
        · rw [List.count_cons_self]; simp at hc ⊢; omega
      · have hXa : X.side ≠ .a := hno X (by simp)
        refine ⟨1, le_rfl, ⟨X, ?_, ?_⟩, by simp [List.count_cons_self]⟩
        · cases X <;> simp_all [Tok.side]
        · exact ⟨r', by simp⟩

theorem band_counting (f d K : ℕ) (w : List Tok) (hno : ∀ t ∈ w, t.side ≠ .a)
    (hfirst : ∃ t, w.head? = some t ∧ okFirst t) (hlast : ∃ t, w.getLast? = some t ∧ okLast t)
    (hrun : RunCount f w) (hK : countC w = K) (hKd : K = f + d) :
    (∃ i, 1 ≤ i ∧ i ≤ d ∧ winM i w) ∨ (∃ k, 1 ≤ k ∧ k ≤ d ∧ winMm k w) := by
  have hsum := count_add_le_countC w
  obtain ⟨t0, ht0, hok0⟩ := hfirst
  obtain ⟨t1, ht1, hok1⟩ := hlast
  have hcBA : t0 = Tok.cBA := tok_left_B_noa ((okFirst_iff t0).1 hok0) (hno t0 (List.mem_of_mem_head? ht0))
  have hcAB : t1 = Tok.cAB := tok_right_B_noa ((okLast_iff t1).1 hok1) (hno t1 (List.mem_of_getLast? ht1))
  subst hcBA; subst hcAB
  rcases hrun with h | h
  · -- many `cAB`: the initial `cBA` run is short
    left
    obtain ⟨i, hi, hw, hc⟩ := initial_run w hno ht0 ⟨Tok.cAB, List.mem_of_getLast? ht1, by decide⟩
    exact ⟨i, hi, by omega, hw⟩
  · right
    have hmw : (mirrorWord w).head? = some Tok.cBA := by
      simp [mirrorWord, List.head?_reverse, ht1, Tok.mirror_cAB]
    have hnon : ∃ t ∈ mirrorWord w, t ≠ Tok.cBA := by
      refine ⟨Tok.cAB, ?_, by decide⟩
      simp only [mirrorWord, List.mem_reverse, List.mem_map]
      exact ⟨Tok.cBA, List.mem_of_mem_head? ht0, Tok.mirror_cBA⟩
    obtain ⟨k, hk, hw, hc⟩ := initial_run (mirrorWord w) (mirrorWord_noa w hno) hmw hnon
    have hcnt : (mirrorWord w).count Tok.cBA = w.count Tok.cAB := by
      have hinj : Function.Injective Tok.mirror := fun a b h => by
        have := congrArg Tok.mirror h
        rwa [Tok.mirror_mirror, Tok.mirror_mirror] at this
      have := List.count_map_of_injective w Tok.mirror hinj Tok.cAB
      rw [Tok.mirror_cAB] at this
      unfold mirrorWord
      rw [List.count_reverse]; exact this
    refine ⟨k, hk, by omega, (winMm_iff k w).2 hw⟩

/-- Any of the eight windows. -/
def Forbidden (w : List Tok) : Prop :=
  winS w ∨ winE w ∨ winI w ∨ winIm w ∨ winC0 w ∨ winC0m w ∨ winW2 w ∨ winW2m w

theorem U2_forbidden (e f M : ℕ) (w : List Tok) (hG : Gram e f M w)
    (hno : ∀ t ∈ w, t.side ≠ .a) (hcount : countC w = 2 * M * e) (hf : 3 ≤ f)
    (hd : 2 * M * e ≤ f + 2) : Forbidden w := by
  rcases U2_grammar e f M w hG hno hcount hf hd with h | h | h | h
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))

#print axioms U_grammar
#print axioms U2_grammar

/-! ## Controls: the grammar is satisfiable, and `d = 3` has a survivor -/

def decPairsOk : (w : List Tok) → Decidable (pairsOk w)
  | [] => isTrue trivial
  | [_] => isTrue trivial
  | u :: v :: r =>
    have := decPairsOk (v :: r)
    inferInstanceAs (Decidable (okPair u v ∧ pairsOk (v :: r)))

instance (w : List Tok) : Decidable (pairsOk w) := decPairsOk w

instance : DecidablePred Forbidden := fun w => by unfold Forbidden winS winE winI winIm winC0 winC0m winW2 winW2m; infer_instance

/-- The `d = 3` word `cBA³ bAG⁸ cAB¹³` of `T₂(4,13)`. -/
def survivor : List Tok :=
  List.replicate 3 Tok.cBA ++ List.replicate 8 Tok.bAG ++ List.replicate 13 Tok.cAB

/-- It is a grammar word of `T₂(4,13)` (`M = 2, e = 4, f = 13`, `d = 2Me − f = 3`). -/
theorem survivor_gram : Gram 4 13 2 survivor := by
  refine ⟨⟨⟨.cBA, by decide, by decide⟩, by decide, ⟨.cAB, by decide, by decide⟩⟩, by decide, ?_⟩
  exact ⟨.cAB, Or.inl rfl, [Tok.cBA, Tok.cBA, Tok.cBA] ++ List.replicate 8 Tok.bAG, [],
    by simp [survivor]⟩

theorem survivor_noa : ∀ t ∈ survivor, t.side ≠ .a := by decide
theorem survivor_countC : countC survivor = 2 * 2 * 4 := by decide

/-- **Negative control**: at `d = 3` the word avoids all eight windows (so `U2_grammar` is sharp). -/
theorem survivor_not_forbidden : ¬ Forbidden survivor := by decide

/-- ... and `d = 2Me − f = 3` exactly, so `U2_grammar` (which needs `d ≤ 2`) does not apply. -/
theorem survivor_d : 2 * 2 * 4 = 13 + 3 := by norm_num

/-- Hypotheses of `U_grammar`/`U2_grammar` are satisfiable: at `T₁(2,3)` (`d = 1`) the word
`cBA bAG bAG cAB cAB cAB` is a grammar word with the `B1` counts, and it contains `C0`. -/
def example_d1 : List Tok := [.cBA, .bAG, .bAG, .cAB, .cAB, .cAB]

theorem example_d1_gram : Gram 2 3 1 example_d1 := by
  refine ⟨⟨⟨.cBA, by decide, by decide⟩, by decide, ⟨.cAB, by decide, by decide⟩⟩, by decide, ?_⟩
  exact ⟨.cAB, Or.inl rfl, [Tok.cBA, Tok.bAG, Tok.bAG], [], by simp [example_d1]⟩

theorem example_d1_noa : ∀ t ∈ example_d1, t.side ≠ .a := by decide
theorem example_d1_countC : countC example_d1 = 2 * 1 * 2 := by decide
theorem example_d1_C0 : winC0 example_d1 :=
  ⟨.bAG, by simp, [.bAG, .cAB, .cAB, .cAB], rfl⟩

theorem example_d1_forbidden : Forbidden example_d1 := by decide

#print axioms survivor_not_forbidden
#print axioms example_d1_gram

end Erdos634.LaczJunction.Grammar
