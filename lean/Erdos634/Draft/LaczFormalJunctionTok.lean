import Erdos634.Draft.LaczFormalJunctionWord
import Erdos634.Draft.LaczFormalJunctionRev

/-!
# Band junction rules S, E, I, Im at the level of tokens

Erdős #634, base-`β` band.  Credit: AI assistant (band lemma / item-3 proposal), Beeson–Roșu, Beeson,
Laczkovich, Paliy.

## Token semantics (read from (private working notes, not included))

The census words are lists of tokens `xYZ` read **left to right along the base** of the isosceles
target (`gram.rs`: `ttok`, `TYPE`).  Angle indices `A,B,G = 0,1,2` (`α,β,γ`), side indices
`a,b,c = 0,1,2`.  The six token types are `(left angle, side)`:

    A1 = (B, a) = aBG    A2 = (G, a) = aGB    B1 = (A, b) = bAG
    B2 = (G, b) = bGA    C1 = (A, c) = cAB    C2 = (B, c) = cBA

and the **right** angle is `3 − left − side` (`right(t)` in `gram.rs`; `rightAng` below).  So a token
`xYZ` is a tile with its side `x` on the base, the angle `Y` at the left end of that side, the angle
`Z` at the right end, and (since `3 − Y − Z = x`) the angle `x` at the apex.  The first token must
have left angle `B` (`ok_first`: the left corner of the target has angle `β`), the last token right
angle `B` (`ok_last`), consecutive tokens share the junction point (`ok_pair` is an angle-sum
condition at the junction).  `cBA, bGA` are `C2, B2`; `cAB, bAG` are `C1, B1`.

`BaseTok` is the Lean version of one token: a tile `i` with vertices `X` (left end), `Y` (right end)
and `Z` (apex) — `TileVerts` makes no assumption on the tile's vertex labelling — with `X, Y` on the
base `[pts p, pts q]` (`pts p` the left corner), `X` strictly left of `Y`, `|XY| = ` the side length
`x`, and local angles `Y`-angle at `X` and `Z`-angle at `Y`.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.LaczJunction

open Erdos634.Geometry Erdos634.TilePlacement

variable {N : ℕ}

/-! ## The token table (decidable sanity lemmas) -/

inductive Corner | A | B | G deriving DecidableEq, Repr
inductive Side | a | b | c deriving DecidableEq, Repr

def Corner.idx : Corner → ℕ | .A => 0 | .B => 1 | .G => 2
def Side.idx : Side → ℕ | .a => 0 | .b => 1 | .c => 2

/-- The right angle of a token with left angle `l` and base side `x`: index `3 − l − x`
(`gram.rs`, `right`). -/
def rightIdx (l : Corner) (x : Side) : ℕ := 3 - l.idx - x.idx

/-- `gram.rs` `TYPE`: (left angle, side) for `A1 A2 B1 B2 C1 C2`. -/
def tokType : List (Corner × Side) :=
  [(.B, .a), (.G, .a), (.A, .b), (.G, .b), (.A, .c), (.B, .c)]

/-- The four tokens used by the junction rules, as `(side, left, right)`. -/
theorem tok_cBA : rightIdx .B .c = Corner.A.idx := by decide
theorem tok_bGA : rightIdx .G .b = Corner.A.idx := by decide
theorem tok_cAB : rightIdx .A .c = Corner.B.idx := by decide
theorem tok_bAG : rightIdx .A .b = Corner.G.idx := by decide

/-- In every token the apex angle has the index of the base side (`3 − left − right = side`). -/
theorem apex_index : ∀ t ∈ tokType, rightIdx t.1 t.2 + t.1.idx + t.2.idx = 3 := by decide

/-- The six types are pairwise distinct (so the census alphabet is the stated one). -/
theorem tokType_nodup : tokType.Nodup := by decide

/-! ## Tiles with three given vertices -/

/-- The three vertices of the tile `T` are `X, Y, Z` in some order. -/
def TileVerts (T : Tri) (X Y Z : Plane) : Prop :=
  ∃ j : Fin 3, (T.pts j = X ∧ T.pts (j+1) = Y ∧ T.pts (j+2) = Z) ∨
               (T.pts j = X ∧ T.pts (j+1) = Z ∧ T.pts (j+2) = Y)

theorem TileVerts.swap23 {T : Tri} {X Y Z : Plane} (h : TileVerts T X Y Z) : TileVerts T X Z Y := by
  obtain ⟨j, h | h⟩ := h
  · exact ⟨j, Or.inr h⟩
  · exact ⟨j, Or.inl h⟩

theorem TileVerts.swap12 {T : Tri} {X Y Z : Plane} (h : TileVerts T X Y Z) : TileVerts T Y X Z := by
  obtain ⟨j, h | h⟩ := h
  · refine ⟨j+1, Or.inr ⟨h.2.1, ?_, ?_⟩⟩
    · have : j + 1 + 1 = j + 2 := by fin_cases j <;> rfl
      rw [this]; exact h.2.2
    · have : j + 1 + 2 = j := by fin_cases j <;> rfl
      rw [this]; exact h.1
  · refine ⟨j+2, Or.inl ⟨h.2.2, ?_, ?_⟩⟩
    · have : j + 2 + 1 = j := by fin_cases j <;> rfl
      rw [this]; exact h.1
    · have : j + 2 + 2 = j + 1 := by fin_cases j <;> rfl
      rw [this]; exact h.2.1

theorem TileVerts.rot {T : Tri} {X Y Z : Plane} (h : TileVerts T X Y Z) : TileVerts T Y Z X :=
  h.swap12.swap23

/-- Either the tile itself or its reverse has the vertices `P, G, Q` at `j, j+1, j+2`. -/
theorem TileVerts.oriented {T : Tri} {P G Q : Plane} (h : TileVerts T P G Q) :
    (∃ j, T.pts j = P ∧ T.pts (j+1) = G ∧ T.pts (j+2) = Q) ∨
    (∃ j, T.rev.pts j = P ∧ T.rev.pts (j+1) = G ∧ T.rev.pts (j+2) = Q) := by
  obtain ⟨j, h | h⟩ := h
  · exact Or.inl ⟨j, h⟩
  · right
    refine ⟨-j, ?_, ?_, ?_⟩
    · rw [rev_pts, neg_neg]; exact h.1
    · rw [rev_pts]
      have : -(-j + 1) = j + 2 := by fin_cases j <;> rfl
      rw [this]; exact h.2.2
    · rw [rev_pts]
      have : -(-j + 2) = j + 1 := by fin_cases j <;> rfl
      rw [this]; exact h.2.1

/-! ## Base tokens -/

/-- One token `x l r` of the base word, as a tile `i` with left end `X`, right end `Y`, apex `Z`
on the base `[pts p, pts q]` of the target (`pts p` the left corner).  `ang`/`len` give the values
of the angles and sides. -/
structure BaseTok (D : CongruentDissection N) (p q : Fin 3) (ang : Corner → ℝ)
    (len : Side → ℝ) (x : Side) (l r : Corner) (i : Fin N) (X Y Z : Plane) : Prop where
  left_mem : X ∈ segment ℝ (D.target.pts p) (D.target.pts q)
  right_mem : Y ∈ segment ℝ (D.target.pts p) (D.target.pts q)
  order : dist (D.target.pts p) X < dist (D.target.pts p) Y
  verts : TileVerts (D.tile i) X Y Z
  length : dist X Y = len x
  left_angle : (D.tile i).localAngle X = ang l
  right_angle : (D.tile i).localAngle Y = ang r

/-- **Reflection of a token**: the token read from the other end of the base. -/
theorem BaseTok.reflect {D : CongruentDissection N} {p q : Fin 3} {ang : Corner → ℝ}
    {len : Side → ℝ} {x : Side} {l r : Corner} {i : Fin N} {X Y Z : Plane}
    (h : BaseTok D p q ang len x l r i X Y Z) : BaseTok D q p ang len x r l i Y X Z := by
  have e1 : dist (D.target.pts p) X + dist X (D.target.pts q) =
      dist (D.target.pts p) (D.target.pts q) :=
    dist_add_dist_eq_iff.mpr (mem_segment_iff_wbtw.mp h.left_mem)
  have e2 : dist (D.target.pts p) Y + dist Y (D.target.pts q) =
      dist (D.target.pts p) (D.target.pts q) :=
    dist_add_dist_eq_iff.mpr (mem_segment_iff_wbtw.mp h.right_mem)
  have o := h.order
  refine ⟨?_, ?_, ?_, h.verts.swap12, ?_, h.right_angle, h.left_angle⟩
  · rw [segment_symm]; exact h.right_mem
  · rw [segment_symm]; exact h.left_mem
  · rw [dist_comm X (D.target.pts q)] at e1
    rw [dist_comm Y (D.target.pts q)] at e2
    linarith
  · rw [dist_comm]; exact h.length

end Erdos634.LaczJunction
