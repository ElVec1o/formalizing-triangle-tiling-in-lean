-- Draft/LaczFormalRegFan.lean -- VERTEX-LOCAL model of the arguments of Laczkovich, "Tilings of convex polygons with congruent
-- triangles", Discrete Comput. Geom. 48 (2012) 330-372, Lemma 4.2, Lemma 4.3 (local step) and Lemma 8.1(i) (Case IV, gamma = pi/3),
-- as DECIDABLE statements about the cyclic arrangement ("fan") of the tile corners around ONE vertex.
--
-- MODEL.  A tile corner at the vertex V is a code x in {0..5} <-> a permutation (t,u,w) of the three tile-angle types (0 = alpha,
-- 1 = beta, 2 = gamma; sides a, b, c are opposite to them):  t = type of the angle AT V, u = type of the tile vertex on the PREVIOUS
-- (clockwise) ray of the sector, w = type of the tile vertex on the NEXT (counterclockwise) ray.  The side of the tile along the
-- previous ray joins types t,u and is opposite w (length s_w); along the next ray it is opposite u (length s_u).  A fan is the list
-- l of tile corners in counterclockwise order; the ray h_i lies between l[i-1] and l[i] (cyclic indices for a full vertex).
-- Hypothesis "a is not a nonnegative rational combination of b, c" is used only through a != b, a != c: lengths are compared by type.
--  * Gamma_a edge from V along h_i (Laczkovich, Sect. 4): exactly one of the two first sides along h_i is a (u(l[i-1]) = 0 xor w(l[i]) = 0)
--    and V is the START of a maximal segment, i.e. no ray h_j is opposite to h_i (sector sum = pi = n weight units).
--  * Gamma_k edge (Sect. 8.1): both tiles at h_i have gamma at V and beta at the far end of the common side.
-- WHAT THIS IS NOT.  It is NOT linked to a real `CongruentDissection`: turning a geometric vertex of a tiling into such a fan (the
-- star of V, its cyclic order, the identification of "first sides" with the maximal-segment divisions) is the missing "lines of the
-- tiling" layer (room (private working notes, not included) batch 13).  The theorems below are therefore the
-- LOCAL halves only; no global statement (Lemma 8.1 (i)-(iii), Lemma 4.3 on a side of the polygon, Theorem 2.1) follows from them yet.
-- Verified by `decide +kernel` over all 6^k fans (k = 3, 6), every hypothesis exhibited by a witness and with negative controls.
-- UNAUDITED.  Credit: Laczkovich (2012, Lemmas 4.2, 4.3, 8.1; 2020 for the vertex-count conventions), Beeson (graph Gamma_a, 'links';
-- arXiv:1206.2229 Def. 4, Lemma 15), Beeson-Zhang (Gamma_a, Gamma_b, Gamma_c in arXiv:2604.01314).
import Mathlib.Tactic

namespace Erdos634.Draft.LaczFormal.RegFan

/-- Angle type at `V` of the tile corner coded `x`. -/
def tT : ℕ → ℕ | 0 => 0 | 1 => 0 | 2 => 1 | 3 => 1 | 4 => 2 | _ => 2
/-- Type of the tile vertex on the previous ray. -/
def tU : ℕ → ℕ | 0 => 1 | 1 => 2 | 2 => 0 | 3 => 2 | 4 => 0 | _ => 1
/-- Type of the tile vertex on the next ray. -/
def tW : ℕ → ℕ | 0 => 2 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 1 | _ => 0

/-- The six codes are exactly the six permutations of `{0,1,2}`. -/
theorem tile_codes_perm : ∀ x < 6, ({tT x, tU x, tW x} : Finset ℕ) = {0, 1, 2} := by decide

/-- All fans with `k` tile corners (codes `< 6`). -/
def allFans : ℕ → List (List ℕ)
  | 0 => [[]]
  | k + 1 => (allFans k).flatMap (fun l => (List.range 6).map (fun x => x :: l))

theorem mem_allFans : ∀ (k : ℕ) (l : List ℕ), l.length = k → (∀ x ∈ l, x < 6) → l ∈ allFans k := by
  intro k
  induction k with
  | zero => intro l hl _; simp [List.length_eq_zero_iff.mp hl, allFans]
  | succ k ih =>
    intro l hl hlt
    match l, hl, hlt with
    | x :: t, hl, hlt =>
      have ht : t ∈ allFans k := ih t (by simpa using hl) (fun y hy => hlt y (List.mem_cons_of_mem _ hy))
      simp only [allFans, List.mem_flatMap, List.mem_map, List.mem_range]
      exact ⟨t, ht, x, hlt x (List.mem_cons_self ..), rfl⟩

/-- Number of corners of angle type `j`. -/
def cnt (l : List ℕ) (j : ℕ) : ℕ := (l.filter (fun x => tT x == j)).length

/-- Weight (angle in common units) of type `j` for the weight triple `w`. -/
def wv (w : ℕ × ℕ × ℕ) (j : ℕ) : ℕ := if j = 0 then w.1 else if j = 1 then w.2.1 else w.2.2

/-- Corner on the clockwise side of ray `i` (cyclic). -/
def Lc (l : List ℕ) (i : ℕ) : ℕ := l.getD ((i + l.length - 1) % l.length) 0
/-- Corner on the counterclockwise side of ray `i` (cyclic). -/
def Rc (l : List ℕ) (i : ℕ) : ℕ := l.getD (i % l.length) 0

/-- Sum of the weights of the `m` corners starting at `l[i]` (cyclic). -/
def sect (w : ℕ × ℕ × ℕ) (l : List ℕ) (i m : ℕ) : ℕ :=
  ((List.range m).map (fun s => wv w (tT (l.getD ((i + s) % l.length) 0)))).sum

/-- Ray `h_i` has an opposite ray in the fan: some block of consecutive corners starting at ray `i` has total angle `n` (= pi). -/
def col (w : ℕ × ℕ × ℕ) (n : ℕ) (l : List ℕ) (i : ℕ) : Bool :=
  (List.range l.length).any (fun m => sect w l i m == n)

/-- A `Γ_a` edge starts at `V` along ray `i` of a fan whose rays have NO opposite ray (a vertex lying on a tile side, `π`-fan). -/
def gaEdge (l : List ℕ) (i : ℕ) : Bool := (tU (Lc l i) == 0) != (tW (Rc l i) == 0)

/-- A `Γ_k` edge starts along ray `i`: both tiles have `γ` at `V` and `β` at the far end of their common side. -/
def gkEdge (l : List ℕ) (i : ℕ) : Bool :=
  tT (Lc l i) == 2 && tT (Rc l i) == 2 && tW (Lc l i) == 1 && tU (Rc l i) == 1

/-- Incoming `Γ_a` edge at a `π`-fan, travelling along the boundary line from either end: the tile at one end has its `a`-side on the line
and the tile at the other end does not. -/
def incoming (l : List ℕ) : Bool :=
  (tW (l.getD 0 0) == 0 && tU (l.getD (l.length - 1) 0) != 0) ||
  (tU (l.getD (l.length - 1) 0) == 0 && tW (l.getD 0 0) != 0)

theorem impl_of_ok {a b : Bool} (h : (!a || b) = true) (ha : a = true) : b = true := by
  simpa [ha] using h

/-! ## Lemma 4.2 / Lemma 8.1: a `Γ_a` edge ending at a `π`-vertex continues -/

def piNormalHyp (l : List ℕ) : Bool := cnt l 0 == 1 && cnt l 1 == 1 && cnt l 2 == 1 && incoming l
def piNormalConcl (l : List ℕ) : Bool := (List.range 3).any (fun i => 1 ≤ i && gaEdge l i)
def piNormalOK (l : List ℕ) : Bool := !(piNormalHyp l) || piNormalConcl l

theorem pi_normal_check : (allFans 3).all piNormalOK = true := by decide +kernel

/-- **Laczkovich Lemma 4.2, local content** (any tile with `a ≠ b`, `a ≠ c`; any angles).  A normal `π`-vertex (three tiles of types
`α, β, γ`) at which an `a`-edge of the boundary line ends and is followed by a non-`a` side has an outgoing `Γ_a` edge along one of the two
inner rays. -/
theorem pi_fan_normal (l : List ℕ) (hlen : l.length = 3) (hlt : ∀ x ∈ l, x < 6) (h : piNormalHyp l = true) :
    piNormalConcl l = true :=
  impl_of_ok ((List.all_eq_true.mp pi_normal_check) l (mem_allFans 3 l hlen hlt)) h

/-- Non-vacuity: `[0,2,4]` satisfies the hypotheses (and the conclusion holds along ray 2). -/
theorem pi_fan_normal_witness : piNormalHyp [0, 2, 4] = true ∧ gaEdge [0, 2, 4] 2 = true := by decide

/-! ## Lemma 8.1: the vertex `3γ = π` needs `Γ_k` as well as `Γ_a` -/

def pi003Hyp (l : List ℕ) : Bool := cnt l 0 == 0 && cnt l 1 == 0 && cnt l 2 == 3 && incoming l
def pi003Concl (l : List ℕ) : Bool := (List.range 3).any (fun i => 1 ≤ i && (gaEdge l i || gkEdge l i))
def pi003OK (l : List ℕ) : Bool := !(pi003Hyp l) || pi003Concl l

theorem pi003_check : (allFans 3).all pi003OK = true := by decide +kernel

/-- **Laczkovich Lemma 8.1(i), vertex `3γ = π`** ("either an edge of `Γ_a` or an edge of `Γ_k` starts from `X`"). -/
theorem pi_fan_3gamma (l : List ℕ) (hlen : l.length = 3) (hlt : ∀ x ∈ l, x < 6) (h : pi003Hyp l = true) :
    pi003Concl l = true :=
  impl_of_ok ((List.all_eq_true.mp pi003_check) l (mem_allFans 3 l hlen hlt)) h

/-- Witness of the hypotheses together with the NEGATIVE CONTROL: for `[4,5,4]` no `Γ_a` edge starts anywhere (so `Γ_a` alone is not
enough, which is why Laczkovich adds `Γ_k`), but a `Γ_k` edge starts along ray 1. -/
theorem pi_fan_3gamma_witness :
    pi003Hyp [4, 5, 4] = true ∧ gaEdge [4, 5, 4] 1 = false ∧ gaEdge [4, 5, 4] 2 = false ∧ gkEdge [4, 5, 4] 1 = true := by decide

/-! ## Lemma 4.3, local step along a side of the polygon -/

/-- The code of the tile corner `(t,u,w)`. -/
def code (t u w : ℕ) : ℕ := ((List.range 6).find? (fun x => tT x == t && tU x == u && tW x == w)).getD 0

/-- The third tile is the translate of the first one along the line (types `(u₁, w₁, t₁)`). -/
def translate (l : List ℕ) : Bool :=
  l.getD 2 0 == code (tU (l.getD 0 0)) (tW (l.getD 0 0)) (tT (l.getD 0 0))

def stepHyp (l : List ℕ) : Bool :=
  cnt l 0 == 1 && cnt l 1 == 1 && cnt l 2 == 1 && !(gaEdge l 1) && !(gaEdge l 2)
def exceptional4 (l : List ℕ) : Bool :=
  l == [0, 2, 5] || l == [1, 4, 3] || l == [2, 5, 0] || l == [4, 3, 1]

def stepOK (l : List ℕ) : Bool := !(stepHyp l) || translate l || exceptional4 l
def line12 (l : List ℕ) : Bool :=      -- first tile has angles beta, gamma on the line (types t,u in {1,2})
  (tT (l.getD 0 0) == 1 && tU (l.getD 0 0) == 2) || (tT (l.getD 0 0) == 2 && tU (l.getD 0 0) == 1)
def line12' (l : List ℕ) : Bool :=     -- last tile has angles beta, gamma on the line (types t,w in {1,2})
  (tT (l.getD 2 0) == 1 && tW (l.getD 2 0) == 2) || (tT (l.getD 2 0) == 2 && tW (l.getD 2 0) == 1)
def stepOK12 (l : List ℕ) : Bool := !(stepHyp l) || !(line12 l) || translate l
def stepOK12' (l : List ℕ) : Bool := !(stepHyp l) || !(line12' l) || translate l

theorem step_check : (allFans 3).all stepOK = true := by decide +kernel
theorem step12_check : (allFans 3).all stepOK12 = true := by decide +kernel
theorem step12'_check : (allFans 3).all stepOK12' = true := by decide +kernel

/-- **Laczkovich Lemma 4.3, local step (Fig. 3: "either `T_{i+1}` is a translated copy of `T_i`, or one of four cases").**  At a normal
vertex on a side of the polygon (three tiles) with no `Γ_a` edge, the tile after is the translate of the tile before, or the fan is one of
the four listed exceptional configurations (each of which has an `α` among the line angles of both end tiles). -/
theorem boundary_step (l : List ℕ) (hlen : l.length = 3) (hlt : ∀ x ∈ l, x < 6) (h : stepHyp l = true) :
    translate l = true ∨ exceptional4 l = true := by
  have := impl_of_ok (a := stepHyp l) (b := (translate l || exceptional4 l))
    (by simpa [stepOK, Bool.or_assoc] using (List.all_eq_true.mp step_check) l (mem_allFans 3 l hlen hlt)) h
  simpa using this

/-- **Lemma 4.3(ii), local step**: if the tile before has angles `β, γ` on the line, the tile after is its translate. -/
theorem boundary_step_beta_gamma (l : List ℕ) (hlen : l.length = 3) (hlt : ∀ x ∈ l, x < 6) (h : stepHyp l = true)
    (hl : line12 l = true) : translate l = true := by
  have := (List.all_eq_true.mp step12_check) l (mem_allFans 3 l hlen hlt)
  simpa [stepOK12, h, hl] using this

/-- Mirror: if the tile after has angles `β, γ` on the line, it is the translate of the tile before. -/
theorem boundary_step_beta_gamma' (l : List ℕ) (hlen : l.length = 3) (hlt : ∀ x ∈ l, x < 6) (h : stepHyp l = true)
    (hl : line12' l = true) : translate l = true := by
  have := (List.all_eq_true.mp step12'_check) l (mem_allFans 3 l hlen hlt)
  simpa [stepOK12', h, hl] using this

/-- Witnesses: a translate fan `[0,4,3]` and an exceptional (non-translate) fan `[0,2,5]` both satisfy `stepHyp`; so both branches of the
disjunction occur and the statement is not vacuous.  Negative control: `[0,4,3]` is a translate, `[0,2,5]` is not. -/
theorem boundary_step_witness :
    stepHyp [0, 4, 3] = true ∧ translate [0, 4, 3] = true ∧
    stepHyp [0, 2, 5] = true ∧ translate [0, 2, 5] = false ∧ exceptional4 [0, 2, 5] = true := by decide

/-- Every exceptional fan has `α` on the line at both ends (so tiles with `{β,γ}` on the line never branch off). -/
theorem exceptional4_alpha_on_line : ∀ l ∈ [[0, 2, 5], [1, 4, 3], [2, 5, 0], [4, 3, 1]],
    line12 l = false ∧ line12' l = false := by decide

/-! ## Lemma 8.1(i) at full (2π) vertices, for the three equilateral-target tiles
`(π/12, 7π/12, π/3)`, `(π/30, 19π/30, π/3)`, `(7π/30, 13π/30, π/3)` (weights in units of π/n, `n = 12, 30, 30`; types 0,1 = the equal-count
pair, type 2 = π/3).  Here `Γ_a` edges need NO collinear ray (the weights decide collinearity exactly). -/

def fullHyp333 (l : List ℕ) : Bool :=
  cnt l 0 == 3 && cnt l 1 == 3 && cnt l 2 == 0 &&
  (List.range 6).any (fun i => tT (Lc l i) == 1 && tT (Rc l i) == 1 && tW (Lc l i) == 2 && tU (Rc l i) == 2)
def fullHyp222 (l : List ℕ) : Bool :=
  cnt l 0 == 2 && cnt l 1 == 2 && cnt l 2 == 2 &&
  (List.range 6).any (fun i => tT (Lc l i) == 1 && tT (Rc l i) == 1 && tW (Lc l i) == 2 && tU (Rc l i) == 2)
def fullConcl (w : ℕ × ℕ × ℕ) (l : List ℕ) : Bool :=
  (List.range 6).any (fun i => (!(col w (w.1 + w.2.1 + w.2.2) l i) && gaEdge l i) || gkEdge l i)
def fullOK (w : ℕ × ℕ × ℕ) (l : List ℕ) : Bool :=
  !(fullHyp333 l || fullHyp222 l) || fullConcl w l

theorem full_check_12 : (allFans 6).all (fullOK (1, 7, 4)) = true := by decide +kernel
theorem full_check_30a : (allFans 6).all (fullOK (1, 19, 10)) = true := by decide +kernel
theorem full_check_30b : (allFans 6).all (fullOK (7, 13, 10)) = true := by decide +kernel

/-- **Laczkovich Lemma 8.1(i), the `Γ_k`-head vertices** `3α+3β = 2π` and `2α+2β+2γ = 2π` (two tiles with `β` at `X` whose common
side `ZX` has `γ` at `Z`): an edge of `Γ_a ∪ Γ_k` starts from `X`.  Instantiated for the three equilateral-target tiles of
Laczkovich 2012 Thm 3.3 (5). -/
theorem full_fan_gk_head (w : ℕ × ℕ × ℕ) (hw : w = (1, 7, 4) ∨ w = (1, 19, 10) ∨ w = (7, 13, 10))
    (l : List ℕ) (hlen : l.length = 6) (hlt : ∀ x ∈ l, x < 6)
    (h : (fullHyp333 l || fullHyp222 l) = true) : fullConcl w l = true := by
  have hm := mem_allFans 6 l hlen hlt
  rcases hw with rfl | rfl | rfl
  · exact impl_of_ok ((List.all_eq_true.mp full_check_12) l hm) h
  · exact impl_of_ok ((List.all_eq_true.mp full_check_30a) l hm) h
  · exact impl_of_ok ((List.all_eq_true.mp full_check_30b) l hm) h

/-- Witnesses (tile `(1,7,4)`): `[0,0,0,2,2,3]` (type `3α+3β`) and `[0,0,2,3,4,5]` (type `2α+2β+2γ`) satisfy the hypotheses; the latter is a
NEGATIVE CONTROL for `Γ_a` alone: no `Γ_a` edge starts anywhere, only a `Γ_k` edge. -/
theorem full_fan_witness :
    fullHyp333 [0, 0, 0, 2, 2, 3] = true ∧ fullConcl (1, 7, 4) [0, 0, 0, 2, 2, 3] = true ∧
    fullHyp222 [0, 0, 2, 3, 4, 5] = true ∧ fullConcl (1, 7, 4) [0, 0, 2, 3, 4, 5] = true ∧
    ((List.range 6).any (fun i => !(col (1, 7, 4) 12 [0, 0, 2, 3, 4, 5] i) && gaEdge [0, 0, 2, 3, 4, 5] i)) = false := by
  decide

end Erdos634.Draft.LaczFormal.RegFan
