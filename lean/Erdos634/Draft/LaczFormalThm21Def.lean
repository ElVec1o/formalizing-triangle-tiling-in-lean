-- Draft/LaczFormalThm21Def.lean -- the STATEMENT of Laczkovich DCG 48 (2012), Theorem 2.1 (regular tilings of convex polygons by
-- congruent triangles), as Lean definitions: convex polygon, polygon tiling, regularity, the nine conclusions (i)-(ix).
-- NOTHING here is proved about Theorem 2.1 itself; `Thm21` is a `Prop`, not a theorem.  Case statements `Thm21_V` etc. are the
-- restrictions to the subcases the proof splits into.  Bridge: a polygon with 4 vertices and v0+v2=v1+v3 has carrier `pgramSet`,
-- giving Lemma 4.1 for polygon tilings (`lemma41_poly`).
-- UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Thm 2.1, Lemma 4.1; Combinatorica 10 (1990); Discrete Math 140 (1995)), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalThm21Area

open MeasureTheory Erdos634.Geometry Erdos634.AreaDet Erdos634.RegionDissection Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.Thm21

/-- A strictly convex polygon with `M ≥ 3` vertices listed counterclockwise: every other vertex lies strictly to the left of each
directed edge `v_i → v_{i+1}`. -/
structure ConvPoly (M : ℕ) [NeZero M] where
  v : Fin M → Plane
  three_le : 3 ≤ M
  left : ∀ i j : Fin M, j ≠ i → j ≠ i + 1 → 0 < cross2 (v (i + 1) - v i) (v j - v i)

namespace ConvPoly
variable {M : ℕ} [NeZero M] (P : ConvPoly M)

/-- The filled polygon: the intersection of the closed left half-planes of the directed edges (for a strictly convex polygon this is
the convex hull of the vertices; the half-plane form is the one the local analysis uses). -/
def carrier : Set Plane := {x | ∀ i : Fin M, 0 ≤ cross2 (P.v (i + 1) - P.v i) (x - P.v i)}
/-- Length of the side `v_i v_{i+1}`. -/
noncomputable def side (i : Fin M) : ℝ := dist (P.v i) (P.v (i + 1))
/-- Interior angle at `v_i`. -/
noncomputable def angle (i : Fin M) : ℝ := cornerAngle (P.v (i - 1)) (P.v i) (P.v (i + 1))
end ConvPoly

/-- Commensurable reals: positive integer multiples agree. -/
def Comm (x y : ℝ) : Prop := ∃ p q : ℕ, 0 < p ∧ 0 < q ∧ (p : ℝ) * x = q * y

/-- A polygon is rational when its sides are pairwise commensurable (Laczkovich, Sect. 2). -/
def RationalPoly {M : ℕ} [NeZero M] (P : ConvPoly M) : Prop := ∀ i j : Fin M, Comm (P.side i) (P.side j)

/-- A dissection of the polygon `P` into `N` congruent triangles (a `CongruentRegionDissection` whose region is the polygon). -/
structure PolyTiling (N M : ℕ) [NeZero M] where
  C : CongruentRegionDissection N
  P : ConvPoly M
  region_eq : C.region = P.carrier

/-- Number of corners of type `l` (model vertex `l`, via the vertex correspondence `idx`) located at `X`. -/
noncomputable def cntR {N : ℕ} (C : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) (X : Plane) (l : Fin 3) : ℕ :=
  open Classical in (Finset.univ.filter (fun p : Fin N × Fin 3 => (C.tile p.1).pts p.2 = X ∧ idx p.1 p.2 = l)).card

/-- **Regular (Laczkovich, Sect. 2), in the normalisation of Theorem 2.1:** with `α, β, γ` the model angles at vertices `0, 1, 2`,
at every point of the plane the number of tile corners carrying `α` equals the number carrying `β`.  `idx` is an
angle-preserving vertex correspondence.  (The paper's definition lists three alternatives `p=q`, `p=r`, `q=r`; Theorem 2.1 fixes
the first by relabelling, which is a choice of the model's vertex order.) -/
def RegularPQ {N : ℕ} (C : CongruentRegionDissection N) : Prop :=
  ∃ idx : Fin N → Equiv.Perm (Fin 3), (∀ i v, angleAt C.model (idx i v) = angleAt (C.tile i) v) ∧
    ∀ X, cntR C idx X 0 = cntR C idx X 1

section Concl
variable {N M : ℕ} [NeZero M]

/-- `sin α, sin β, sin γ` pairwise commensurable. -/
def SinComm (C : CongruentRegionDissection N) : Prop :=
  Comm (Real.sin (angleAt C.model 0)) (Real.sin (angleAt C.model 1)) ∧
  Comm (Real.sin (angleAt C.model 1)) (Real.sin (angleAt C.model 2)) ∧
  Comm (Real.sin (angleAt C.model 0)) (Real.sin (angleAt C.model 2))

/-- (i): `A` is a parallelogram of angles `γ`, `α+β`, and the ratio of its sides is a rational multiple of `sin α / sin β`
(the ratio of the two different sides in either order). -/
def Concl1 (C : CongruentRegionDissection N) (P : ConvPoly M) : Prop :=
  (M = 4 ∧ ∀ i : Fin M, P.v i + P.v (i + 2) = P.v (i + 1) + P.v (i + 3)) ∧
  (∃ i : Fin M, P.angle i = angleAt C.model 2) ∧
  ((∃ q : ℚ, P.side 0 / P.side 1 = q * (Real.sin (angleAt C.model 0) / Real.sin (angleAt C.model 1))) ∨
   (∃ q : ℚ, P.side 1 / P.side 0 = q * (Real.sin (angleAt C.model 0) / Real.sin (angleAt C.model 1))))

/-- (ii): rational polygon, `M-2` angles equal `γ`, the other two are integer multiples of `α+β`, sines pairwise commensurable. -/
def Concl2 (C : CongruentRegionDissection N) (P : ConvPoly M) : Prop :=
  RationalPoly P ∧
  (∃ i j : Fin M, i ≠ j ∧ (∀ k, k ≠ i → k ≠ j → P.angle k = angleAt C.model 2) ∧
    ∃ m n : ℕ, P.angle i = m * (angleAt C.model 0 + angleAt C.model 1) ∧ P.angle j = n * (angleAt C.model 0 + angleAt C.model 1)) ∧
  SinComm C

/-- (iii): rational polygon, `M-2` angles equal `α+β`, the other two are integer multiples of `γ`, sines pairwise commensurable. -/
def Concl3 (C : CongruentRegionDissection N) (P : ConvPoly M) : Prop :=
  RationalPoly P ∧
  (∃ i j : Fin M, i ≠ j ∧ (∀ k, k ≠ i → k ≠ j → P.angle k = angleAt C.model 0 + angleAt C.model 1) ∧
    ∃ m n : ℕ, P.angle i = m * angleAt C.model 2 ∧ P.angle j = n * angleAt C.model 2) ∧
  SinComm C

/-- (iv): regular triangle, `γ = π/3` or `2π/3`, sines pairwise commensurable. -/
def Concl4 (C : CongruentRegionDissection N) (P : ConvPoly M) : Prop :=
  M = 3 ∧ (∀ i, P.side i = P.side 0) ∧ (angleAt C.model 2 = Real.pi / 3 ∨ angleAt C.model 2 = 2 * Real.pi / 3) ∧ SinComm C

/-- (v): centrally symmetric rational `2k`-gon, `k ≥ 4`, all angles `α+β`, sides `a_1..a_k,a_1..a_k` (read from some vertex, in
some direction -- the paper's "in this order"), `a_1..a_{k-1}` geometric with ratio `q = sin α / sin β`, `a_k ≥ q^{k-1} a_1`.
STATEMENT-MATCH NOTE (2026-10-22): the paper's labels `α, β` of the two non-`γ` angles are interchangeable, so `q` is `sin α / sin β` for EITHER order
of the model labels 0, 1 (`q = sin0/sin1 ∨ q = sin1/sin0`).  Until 2026-10-22 this definition fixed `q = sin0/sin1`, which is strictly stronger than the paper
whenever `sin0 > sin1` (see (private working notes, not included) Sect. 3). -/
def Concl5 (C : CongruentRegionDissection N) (P : ConvPoly M) : Prop :=
  ∃ k : ℕ, M = 2 * k ∧ 4 ≤ k ∧ RationalPoly P ∧ (∀ i, P.angle i = angleAt C.model 0 + angleAt C.model 1) ∧
    (∀ i : Fin M, P.side i = P.side (i + Fin.ofNat M k)) ∧
    ∃ q : ℝ, (q = Real.sin (angleAt C.model 0) / Real.sin (angleAt C.model 1) ∨ q = Real.sin (angleAt C.model 1) / Real.sin (angleAt C.model 0)) ∧
    ∃ (s : Fin M) (rev : Bool), ∃ a : ℕ → ℝ, (∀ n, a n = if rev then P.side (s - (Fin.ofNat M n) - 1) else P.side (s + (Fin.ofNat M n))) ∧
      (∀ n, n + 2 < k → a (n + 1) = q * a n) ∧ q ^ (k - 1) * a 0 ≤ a (k - 1)

/-- (vi): centrally symmetric rational hexagon, all angles `2π/3`, `γ = π/3` or `2π/3`, `sin α / sin β` rational. -/
def Concl6 (C : CongruentRegionDissection N) (P : ConvPoly M) : Prop :=
  M = 6 ∧ RationalPoly P ∧ (∀ i : Fin M, P.side i = P.side (i + 3)) ∧ (∀ i, P.angle i = 2 * Real.pi / 3) ∧
  (angleAt C.model 2 = Real.pi / 3 ∨ angleAt C.model 2 = 2 * Real.pi / 3) ∧
  ∃ q : ℚ, Real.sin (angleAt C.model 0) / Real.sin (angleAt C.model 1) = q

/-- (vii): regular `M`-gon, `α = β = π/2 - π/M`, `γ = 2π/M`. -/
def Concl7 (C : CongruentRegionDissection N) (P : ConvPoly M) : Prop :=
  (∀ i, P.side i = P.side 0) ∧ (∀ i, P.angle i = P.angle 0) ∧ angleAt C.model 0 = angleAt C.model 1 ∧
  angleAt C.model 0 = Real.pi / 2 - Real.pi / M ∧ angleAt C.model 2 = 2 * Real.pi / M

/-- (viii): rational `M`-gon, `M ≤ 6`, each angle `π/3` or `2π/3`, `α = β = π/6`, `γ = 2π/3`. -/
def Concl8 (C : CongruentRegionDissection N) (P : ConvPoly M) : Prop :=
  RationalPoly P ∧ M ≤ 6 ∧ (∀ i, P.angle i = Real.pi / 3 ∨ P.angle i = 2 * Real.pi / 3) ∧
  angleAt C.model 0 = Real.pi / 6 ∧ angleAt C.model 1 = Real.pi / 6 ∧ angleAt C.model 2 = 2 * Real.pi / 3

/-- (ix): rational hexagon, all angles `2π/3`, `γ = π/3`, `{α, β} = {π/6, π/2}`. -/
def Concl9 (C : CongruentRegionDissection N) (P : ConvPoly M) : Prop :=
  M = 6 ∧ RationalPoly P ∧ (∀ i, P.angle i = 2 * Real.pi / 3) ∧ angleAt C.model 2 = Real.pi / 3 ∧
  ((angleAt C.model 0 = Real.pi / 6 ∧ angleAt C.model 1 = Real.pi / 2) ∨
   (angleAt C.model 0 = Real.pi / 2 ∧ angleAt C.model 1 = Real.pi / 6))

/-- The conclusion of Theorem 2.1: one of (i)-(ix). -/
def Thm21Concl (C : CongruentRegionDissection N) (P : ConvPoly M) : Prop :=
  Concl1 C P ∨ Concl2 C P ∨ Concl3 C P ∨ Concl4 C P ∨ Concl5 C P ∨ Concl6 C P ∨ Concl7 C P ∨ Concl8 C P ∨ Concl9 C P

end Concl

/-- **Laczkovich, DCG 48 (2012), Theorem 2.1 (statement only; NOT proved here).** -/
def Theorem21 : Prop :=
  ∀ (N M : ℕ) [NeZero M] (T : PolyTiling N M), RegularPQ T.C → Thm21Concl T.C T.P

/-- Case V of the proof: `γ = π/2` (each angle of `A` is then `π/2`, `A` a rectangle; the paper proves (i)). -/
def Thm21_V : Prop :=
  ∀ (N M : ℕ) [NeZero M] (T : PolyTiling N M), RegularPQ T.C → angleAt T.C.model 2 = Real.pi / 2 → Concl1 T.C T.P

/-- Case IV of the proof: `γ = π/3`. -/
def Thm21_IV : Prop :=
  ∀ (N M : ℕ) [NeZero M] (T : PolyTiling N M), RegularPQ T.C → angleAt T.C.model 2 = Real.pi / 3 → Thm21Concl T.C T.P

/-- Case III of the proof: `γ = 2π/3`. -/
def Thm21_III : Prop :=
  ∀ (N M : ℕ) [NeZero M] (T : PolyTiling N M), RegularPQ T.C → angleAt T.C.model 2 = 2 * Real.pi / 3 → Thm21Concl T.C T.P

/-! ## Bridge: a 4-gon with `v0 + v2 = v1 + v3` is the parallelogram `pgramSet`, so Lemma 4.1 applies to polygon tilings. -/

theorem cross2_add_left (a b c : Plane) : cross2 (a + b) c = cross2 a c + cross2 b c := by unfold cross2; simp; ring
theorem cross2_sub_left (a b c : Plane) : cross2 (a - b) c = cross2 a c - cross2 b c := by unfold cross2; simp; ring
theorem cross2_add_right (a b c : Plane) : cross2 a (b + c) = cross2 a b + cross2 a c := by unfold cross2; simp; ring
theorem cross2_sub_right (a b c : Plane) : cross2 a (b - c) = cross2 a b - cross2 a c := by unfold cross2; simp; ring
theorem cross2_smul_left (r : ℝ) (a b : Plane) : cross2 (r • a) b = r * cross2 a b := by unfold cross2; simp; ring
theorem cross2_smul_right (r : ℝ) (a b : Plane) : cross2 a (r • b) = r * cross2 a b := by unfold cross2; simp; ring
theorem cross2_self (a : Plane) : cross2 a a = 0 := by unfold cross2; ring
theorem cross2_anti (a b : Plane) : cross2 b a = - cross2 a b := by unfold cross2; ring

/-- Half-plane description of the parallelogram `O + [0,1]u + [0,1]w` (`cross2 u w > 0`), for `y = x - O`. -/
theorem pgram_halfplanes (u w y : Plane) (hD : 0 < cross2 u w) :
    (0 ≤ cross2 u y ∧ 0 ≤ cross2 y w ∧ cross2 w (y - u) ≥ 0 ∧ cross2 (-u) (y - u - w) ≥ 0) ↔
    ∃ s ∈ Set.Icc (0:ℝ) 1, ∃ t ∈ Set.Icc (0:ℝ) 1, y = s • u + t • w := by
  constructor
  · rintro ⟨k0, k3, k1, k2⟩
    refine ⟨cross2 y w / cross2 u w, ⟨div_nonneg k3 hD.le, ?_⟩, cross2 u y / cross2 u w, ⟨div_nonneg k0 hD.le, ?_⟩, ?_⟩
    · rw [div_le_one hD]; unfold cross2 at *; simp at k1 ⊢; nlinarith [k1]
    · rw [div_le_one hD]; unfold cross2 at *; simp at k2 ⊢; nlinarith [k2]
    · have hDne : cross2 u w ≠ 0 := hD.ne'
      ext j; fin_cases j
      · show y 0 = (cross2 y w / cross2 u w) * u 0 + (cross2 u y / cross2 u w) * w 0
        rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, eq_div_iff hDne]
        unfold cross2; ring
      · show y 1 = (cross2 y w / cross2 u w) * u 1 + (cross2 u y / cross2 u w) * w 1
        rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, eq_div_iff hDne]
        unfold cross2; ring
  · rintro ⟨s, hs, t, ht, rfl⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · unfold cross2 at *; simp; nlinarith [ht.1, hD]
    · unfold cross2 at *; simp; nlinarith [hs.1, hD]
    · unfold cross2 at *; simp; nlinarith [hs.2, hD]
    · unfold cross2 at *; simp; nlinarith [ht.2, hD]

theorem poly4_carrier (P : ConvPoly 4) (hpg : P.v 0 + P.v 2 = P.v 1 + P.v 3) :
    P.carrier = pgramSet (P.v 0) (P.v 1 - P.v 0) (P.v 3 - P.v 0) := by
  have hD : 0 < cross2 (P.v 1 - P.v 0) (P.v 3 - P.v 0) := by
    have := P.left 0 3 (by decide) (by decide)
    simpa using this
  have h2 : P.v 2 = P.v 1 + P.v 3 - P.v 0 := by rw [← hpg]; abel
  ext x
  have key := pgram_halfplanes (P.v 1 - P.v 0) (P.v 3 - P.v 0) (x - P.v 0) hD
  have e01 : (0 : Fin 4) + 1 = 1 := by decide
  have e12 : (1 : Fin 4) + 1 = 2 := by decide
  have e23 : (2 : Fin 4) + 1 = 3 := by decide
  have e30 : (3 : Fin 4) + 1 = 0 := by decide
  have hmem : x ∈ pgramSet (P.v 0) (P.v 1 - P.v 0) (P.v 3 - P.v 0) ↔
      ∃ s ∈ Set.Icc (0:ℝ) 1, ∃ t ∈ Set.Icc (0:ℝ) 1, x - P.v 0 = s • (P.v 1 - P.v 0) + t • (P.v 3 - P.v 0) := by
    constructor
    · rintro ⟨s, hs, t, ht, hx⟩
      exact ⟨s, hs, t, ht, by rw [hx]; abel⟩
    · rintro ⟨s, hs, t, ht, hx⟩
      exact ⟨s, hs, t, ht, by rw [add_assoc, ← hx]; abel⟩
  rw [hmem, ← key]
  constructor
  · intro hx
    have c0 := hx 0; have c1 := hx 1; have c2 := hx 2; have c3 := hx 3
    rw [e01] at c0; rw [e12] at c1; rw [e23] at c2; rw [e30] at c3
    refine ⟨c0, ?_, ?_, ?_⟩
    · have : P.v 0 - P.v 3 = -(P.v 3 - P.v 0) := by abel
      rw [this] at c3
      have e : x - P.v 3 = (x - P.v 0) - (P.v 3 - P.v 0) := by abel
      rw [e] at c3
      unfold cross2 at c3 ⊢; simp at c3 ⊢; nlinarith [c3]
    · have e : P.v 2 - P.v 1 = P.v 3 - P.v 0 := by rw [h2]; abel
      rw [e] at c1
      have e' : x - P.v 1 = (x - P.v 0) - (P.v 1 - P.v 0) := by abel
      rw [e'] at c1; exact c1
    · have e : P.v 3 - P.v 2 = -(P.v 1 - P.v 0) := by rw [h2]; abel
      rw [e] at c2
      have e' : x - P.v 2 = (x - P.v 0) - (P.v 1 - P.v 0) - (P.v 3 - P.v 0) := by rw [h2]; abel
      rw [e'] at c2; exact c2
  · rintro ⟨k0, k3, k1, k2⟩ i
    fin_cases i
    · show 0 ≤ cross2 (P.v (0 + 1) - P.v 0) (x - P.v 0)
      rw [e01]; exact k0
    · show 0 ≤ cross2 (P.v (1 + 1) - P.v 1) (x - P.v 1)
      rw [e12]
      have e : P.v 2 - P.v 1 = P.v 3 - P.v 0 := by rw [h2]; abel
      have e' : x - P.v 1 = (x - P.v 0) - (P.v 1 - P.v 0) := by abel
      rw [e, e']; exact k1
    · show 0 ≤ cross2 (P.v (2 + 1) - P.v 2) (x - P.v 2)
      rw [e23]
      have e : P.v 3 - P.v 2 = -(P.v 1 - P.v 0) := by rw [h2]; abel
      have e' : x - P.v 2 = (x - P.v 0) - (P.v 1 - P.v 0) - (P.v 3 - P.v 0) := by rw [h2]; abel
      rw [e, e']; exact k2
    · show 0 ≤ cross2 (P.v (3 + 1) - P.v 3) (x - P.v 3)
      rw [e30]
      have e : P.v 0 - P.v 3 = -(P.v 3 - P.v 0) := by abel
      have e' : x - P.v 3 = (x - P.v 0) - (P.v 3 - P.v 0) := by abel
      rw [e, e']
      unfold cross2 at k3 ⊢; simp at k3 ⊢; nlinarith [k3]

/-- **Lemma 4.1 for a polygon tiling** (Laczkovich, DCG 48 (2012)): `A` a parallelogram (`v0 + v2 = v1 + v3`) with an angle `γ`
(equivalently `α+β`) at `v0`, tiled by `N` congruent triangles of angles `α, β, γ`; if a side adjacent to `v0` is `k a`
(`k ≥ 1`, `a` the model side opposite `α`) then the ratio (that side)/(the other) is a rational multiple of `sin α / sin β`.
This is the content of `Concl1`'s ratio clause. -/
theorem lemma41_poly {N : ℕ} (T : PolyTiling N 4) (hpg : T.P.v 0 + T.P.v 2 = T.P.v 1 + T.P.v 3)
    (hang : T.P.angle 0 = angleAt T.C.model 2 ∨ T.P.angle 0 = Real.pi - angleAt T.C.model 2)
    (k : ℕ) (hk : 0 < k)
    (hside : T.P.side 0 = k * sideOpp T.C.model 0 ∨ T.P.side 3 = k * sideOpp T.C.model 0) :
    (∃ q : ℚ, T.P.side 0 / T.P.side 3 = q * (Real.sin (angleAt T.C.model 0) / Real.sin (angleAt T.C.model 1))) ∨
    (∃ q : ℚ, T.P.side 3 / T.P.side 0 = q * (Real.sin (angleAt T.C.model 0) / Real.sin (angleAt T.C.model 1))) := by
  have hreg : T.C.region = pgramSet (T.P.v 0) (T.P.v 1 - T.P.v 0) (T.P.v 3 - T.P.v 0) := by
    rw [T.region_eq]; exact poly4_carrier T.P hpg
  have h0 : ‖T.P.v 1 - T.P.v 0‖ = T.P.side 0 := by
    rw [← dist_eq_norm, ConvPoly.side, dist_comm]; rfl
  have h3 : ‖T.P.v 3 - T.P.v 0‖ = T.P.side 3 := by
    rw [← dist_eq_norm, ConvPoly.side]; rfl
  have hA : T.P.angle 0 = InnerProductGeometry.angle (T.P.v 1 - T.P.v 0) (T.P.v 3 - T.P.v 0) := by
    rw [InnerProductGeometry.angle_comm]; rfl
  have hsin : Real.sin (InnerProductGeometry.angle (T.P.v 1 - T.P.v 0) (T.P.v 3 - T.P.v 0)) = Real.sin (angleAt T.C.model 2) := by
    rw [← hA]; rcases hang with h | h
    · rw [h]
    · rw [h, Real.sin_pi_sub]
  rcases hside with h | h
  · left
    have := lemma41 T.C _ _ _ hreg hsin k hk (by rw [h0]; exact h)
    rwa [h0, h3] at this
  · right
    have := lemma41' T.C _ _ _ hreg hsin k hk (by rw [h3]; exact h)
    rwa [h0, h3] at this

end Erdos634.Draft.LaczFormal.Thm21
