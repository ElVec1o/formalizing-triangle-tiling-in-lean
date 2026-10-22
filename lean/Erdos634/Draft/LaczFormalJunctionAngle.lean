import Erdos634.ThickAngleIrrational
import Erdos634.Draft.LaczFormalJunctionArith

/-!
# Band junction rules: wedge arithmetic and the conditional Theorem 1

Erdős #634, base-`β` band.  Formalizes `PROOF_C1.md` (room KILLATTR_2026-10-21, audit `AUDIT_C1.md`).
Credit: AI assistant (band lemma / item-3 proposal, C1/C2/C3 observations), Beeson–Roșu (tiles, band
grammar), Beeson, Laczkovich, Paliy.

## Proved unconditionally here
* `modelAlpha_irrational` — for every `0 < e < f`, `α = modelAlpha e f ∉ ℚπ` (generalizes the
  `(2,3)` instance; Niven via `BaseBetaE1.tile_alpha_irrational`).
* `wedge_beta` (L-a): `π − α − γ = β`.
* `coeff_unique` and `wedge_fill_beta/alpha/threeAlpha/gamma` (L-b): the corner combinations
  `xα + yβ + zγ` that fill a wedge `β` (only one `β`), `α` (only one `α`), `3α` (only three `α`),
  `γ` (one `γ` or `{α,α,β}`).
* chord cover (L-c) in `LaczFormalJunctionArith.cover_unique`.

## Conditional (named geometric hypotheses)
`theorem1_conditional`: no `JunctionGeometry` exists.  `JunctionGeometry` packages exactly the
planar-geometry steps of the hand proof that are NOT machine-checked here (hand proof step L3,
convexity + "no tile has `P` inside an edge" + finite local structure):

* `straight`: the corners at `P` of `cBA` (angle `α`), `bGA` (angle `γ`) and the tiles filling the
  free wedge add up to `π` (the base is a straight line through `P`);
* `chord`: the tiles on the far side of the chord `PG1` have edges along it that start at `P`,
  are consecutive and end exactly at `G1` (so their lengths add to `b`);
* `first_mem`/`first_edge`: the first of those tiles has a corner at `P` lying in the wedge, and
  that corner carries the edge of that tile along `PG1`.

Satisfiability of the individual hypotheses is witnessed below for the real tile `(e,f)=(2,3)`
(`witness_*`).  As for any no-tiling theorem, the conjunction is inconsistent by the theorem.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.LaczJunction

open Erdos634.BaseBetaTargetCoord Erdos634.ThickJunctionCoords

/-! ## Angle relations -/

/-- `α = modelAlpha e f` is an irrational multiple of `π`, for every `0 < e < f`. -/
theorem modelAlpha_irrational (e f : ℕ) (he : 1 ≤ e) (hef : e < f) :
    ¬ ∃ r : ℚ, modelAlpha (e:ℝ) (f:ℝ) = (r : ℝ) * Real.pi := by
  have he0 : (0:ℝ) < e := by exact_mod_cast he
  have hef' : (e:ℝ) < f := by exact_mod_cast hef
  have hf0 : (0:ℝ) < f := by linarith
  refine Erdos634.BaseBetaE1.tile_alpha_irrational e f he hef _ ?_
  have hβ := modelBeta_mem he0 hef'
  have hα0 : 0 < modelAlpha (e:ℝ) f := by simp only [modelAlpha]; linarith [hβ.1, hβ.2, Real.pi_pos]
  have hαπ : modelAlpha (e:ℝ) f < Real.pi := by
    simp only [modelAlpha]; have := Real.pi_pos; nlinarith [hβ.1]
  have hsq : Real.sin (modelAlpha (e:ℝ) f / 2) ^ 2 = ((e:ℝ) / (2 * f)) ^ 2 := by
    rw [Real.sin_sq_eq_half_sub, show 2 * (modelAlpha (e:ℝ) f / 2) = modelAlpha (e:ℝ) f by ring,
      cos_modelAlpha he0 hef']
    field_simp
    ring
  have hnn : 0 ≤ Real.sin (modelAlpha (e:ℝ) f / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  exact (sq_eq_sq₀ hnn (by positivity)).mp hsq

/-- (L-a) The free wedge at the junction vertex has angle exactly `β`. -/
theorem wedge_beta (α β γ : ℝ) (hγ : γ = 2 * α + β) (hrel : 3 * α + 2 * β = Real.pi) :
    Real.pi - α - γ = β := by rw [hγ, ← hrel]; ring

/-- Coefficient uniqueness (L0): `pα + qβ` determines `(p,q)` when `α ∉ ℚπ`. -/
theorem coeff_unique (α β : ℝ) (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (p q p' q' : ℤ)
    (h : (p:ℝ) * α + q * β = p' * α + q' * β) : p = p' ∧ q = q' := by
  have hβ : β = (Real.pi - 3 * α) / 2 := by linarith
  subst hβ
  have hπ := Real.pi_pos
  set k : ℤ := 2 * (p - p') - 3 * (q - q') with hk
  have key : (k:ℝ) * α = -((q - q' : ℤ):ℝ) * Real.pi := by
    simp only [hk]; push_cast; linarith
  by_cases hk0 : k = 0
  · rw [hk0] at key
    simp only [Int.cast_zero, zero_mul] at key
    have : ((q - q' : ℤ):ℝ) = 0 := by
      have : ((q - q' : ℤ):ℝ) * Real.pi = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · exact h
      · exact absurd h hπ.ne'
    have hq : q - q' = 0 := by exact_mod_cast this
    omega
  · exfalso
    apply hirr
    refine ⟨(-(q - q') : ℚ) / k, ?_⟩
    have hkR : (k:ℝ) ≠ 0 := by exact_mod_cast hk0
    push_cast
    field_simp
    push_cast at key
    linarith

section
variable {α β γ : ℝ} (hγ : γ = 2 * α + β) (hrel : 3 * α + 2 * β = Real.pi)
  (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
include hγ hrel hirr

private theorem fill_aux (x y z : ℕ) (p q : ℕ)
    (h : (x:ℝ) * α + y * β + z * γ = p * α + q * β) : x + 2 * z = p ∧ y + z = q := by
  have := coeff_unique α β hrel hirr ((x + 2 * z : ℕ):ℤ) ((y + z : ℕ):ℤ) (p:ℤ) (q:ℤ) (by
    push_cast; rw [hγ] at h; linarith)
  omega

/-- (L-b) A wedge `β` is filled only by a single `β` corner. -/
theorem wedge_fill_beta (x y z : ℕ) (h : (x:ℝ) * α + y * β + z * γ = β) :
    x = 0 ∧ y = 1 ∧ z = 0 := by
  have := fill_aux hγ hrel hirr x y z 0 1 (by simpa using h)
  omega

theorem wedge_fill_alpha (x y z : ℕ) (h : (x:ℝ) * α + y * β + z * γ = α) :
    x = 1 ∧ y = 0 ∧ z = 0 := by
  have := fill_aux hγ hrel hirr x y z 1 0 (by simpa using h)
  omega

theorem wedge_fill_threeAlpha (x y z : ℕ) (h : (x:ℝ) * α + y * β + z * γ = 3 * α) :
    x = 3 ∧ y = 0 ∧ z = 0 := by
  have := fill_aux hγ hrel hirr x y z 3 0 (by simpa using h)
  omega

theorem wedge_fill_gamma (x y z : ℕ) (h : (x:ℝ) * α + y * β + z * γ = γ) :
    (x = 0 ∧ y = 0 ∧ z = 1) ∨ (x = 2 ∧ y = 1 ∧ z = 0) := by
  have := fill_aux hγ hrel hirr x y z 2 1 (by rw [hγ] at h ⊢; push_cast; linarith)
  omega
end

/-! ## The junction data and Theorem 1 (conditional) -/

inductive Ang | A | B | G deriving DecidableEq
inductive Len | a | b | c deriving DecidableEq

/-- Side lengths meeting at the vertex of angle `A` (`α`): `b,c`; at `B`: `a,c`; at `G`: `a,b`. -/
def Ang.hasEdge : Ang → Len → Prop
  | .A, .b => True | .A, .c => True
  | .B, .a => True | .B, .c => True
  | .G, .a => True | .G, .b => True
  | _, _ => False

def Ang.val (α β γ : ℝ) : Ang → ℝ | .A => α | .B => β | .G => γ
def Len.val (a b c : ℕ) : Len → ℕ | .a => a | .b => b | .c => c

theorem sum_val_ang (α β γ : ℝ) (l : List Ang) :
    (l.map (Ang.val α β γ)).sum
      = (l.count .A : ℝ) * α + (l.count .B : ℝ) * β + (l.count .G : ℝ) * γ := by
  induction l with
  | nil => simp
  | cons h t ih =>
    cases h <;> simp [List.count_cons, ih, Ang.val] <;> ring

theorem sum_val_len (a b c : ℕ) (l : List Len) :
    (l.map (Len.val a b c)).sum = l.count .a * a + l.count .b * b + l.count .c * c := by
  induction l with
  | nil => simp
  | cons h t ih =>
    cases h <;> simp [List.count_cons, ih, Len.val] <;> ring

/-- **The geometric hypotheses of the hand proof of Theorem 1** (all still to be discharged from a
`CongruentDissection` of the isosceles band target; the planar step is L3 of `PROOF_C1.md`).

`wedge`: corners at `P` of the tiles filling the free wedge between `cBA` and `bGA`;
`far`: lengths of the far-side edges along the chord `PG1` of `cBA`, from `P` to `G1`;
`first`: the corner at `P` of the tile carrying the first far edge. -/
structure JunctionGeometry (α β γ : ℝ) (a b c : ℕ) where
  wedge : List Ang
  far : List Len
  first : Ang
  straight : α + γ + (wedge.map (Ang.val α β γ)).sum = Real.pi
  chord : (far.map (Len.val a b c)).sum = b
  first_mem : first ∈ wedge
  first_edge : ∃ l ∈ far.head?, first.hasEdge l

/-- **Theorem 1 (band corner pair), CONDITIONAL on `JunctionGeometry`.**  For the family tile
`(a,b,c) = (ef, f²−e², f²)`, `1 ≤ e < f` coprime, with `3α+2β=π`, `γ = 2α+β`, `α ∉ ℚπ`, there is no
`JunctionGeometry`; i.e. a base word beginning `cBA, bGA` cannot exist once the geometric steps
(L3) hold.  Uses L-a (wedge `β`), L-b (single `β` corner), L-c (single `b`-edge) and L-d (the tile
carrying a `b`-edge has apex angle `α` or `γ`, not `β`). -/
theorem theorem1_conditional (e f : ℕ) (he : 1 ≤ e) (hef : e < f) (hcop : Nat.Coprime e f)
    {α β γ : ℝ} (hγ : γ = 2 * α + β) (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (J : JunctionGeometry α β γ (ta e f) (tb e f) (tc e f)) : False := by
  -- (L-a)
  have hw : (J.wedge.map (Ang.val α β γ)).sum = β := by
    have := J.straight; have := wedge_beta α β γ hγ hrel; linarith
  rw [sum_val_ang] at hw
  -- (L-b)
  have hfill := wedge_fill_beta hγ hrel hirr _ _ _ hw
  obtain ⟨hA, hB, hG⟩ := hfill
  have hA0 : J.wedge.count .A = 0 := hA
  have hG0 : J.wedge.count .G = 0 := hG
  -- (L-c)
  have hc := J.chord
  rw [sum_val_len] at hc
  have hcov := cover_unique e f _ _ _ he hef hcop hc
  obtain ⟨hx, hy, hz⟩ := hcov
  -- far has exactly one b edge, nothing else
  obtain ⟨l, hl, hedge⟩ := J.first_edge
  have hmem : l ∈ J.far := List.mem_of_mem_head? hl
  have hlb : l = .b := by
    cases l
    · exact absurd (List.count_pos_iff.mpr hmem) (by omega)
    · rfl
    · exact absurd (List.count_pos_iff.mpr hmem) (by omega)
  subst hlb
  -- (L-d)
  have hpos : 0 < J.wedge.count J.first := List.count_pos_iff.mpr J.first_mem
  cases hf : J.first
  · rw [hf] at hpos; omega
  · rw [hf] at hedge; exact hedge
  · rw [hf] at hpos; omega

/-! ## Non-vacuity: every single hypothesis is satisfiable for a real tile.

Angles from `modelAlpha 2 3`, `modelBeta 2 3` (`(a,b,c) = (6,5,9)`, `α ∉ ℚπ`). -/

theorem model_hyps_23 :
    (modelBeta 2 3 > 0) ∧ (modelAlpha 2 3 > 0) ∧
    3 * modelAlpha 2 3 + 2 * modelBeta 2 3 = Real.pi ∧
    ¬ ∃ r : ℚ, modelAlpha 2 3 = (r : ℝ) * Real.pi :=
  ⟨(modelBeta_mem (by norm_num) (by norm_num)).1, angles_pos_63.1, modelAngle_rel 2 3,
    Erdos634.ThickAngleIrrational.modelAlpha_irrational_23⟩

/-- Drop only `first_edge`: wedge `[β]`, far `[b]`, `first = β` is a consistent geometry. -/
theorem witness_without_first_edge :
    let α := modelAlpha 2 3; let β := modelBeta 2 3; let γ := 2 * α + β
    ∃ (wedge far : List Ang) (cf : List Len) (first : Ang),
      α + γ + (wedge.map (Ang.val α β γ)).sum = Real.pi ∧
      (cf.map (Len.val (ta 2 3) (tb 2 3) (tc 2 3))).sum = tb 2 3 ∧ first ∈ wedge ∧ far = wedge := by
  intro α β γ
  refine ⟨[.B], [.B], [.b], .B, ?_, ?_, by simp, rfl⟩
  · have := modelAngle_rel 2 3
    simp [Ang.val, γ, α, β]; linarith
  · simp [Len.val, tb]

/-- Drop only the wedge sum: wedge `[α]`, far `[b]`, `first = α` (an `α`-corner has a `b`-edge). -/
theorem witness_without_straight :
    ∃ (wedge : List Ang) (cf : List Len) (first : Ang),
      (cf.map (Len.val (ta 2 3) (tb 2 3) (tc 2 3))).sum = tb 2 3 ∧ first ∈ wedge ∧
      ∃ l ∈ cf.head?, first.hasEdge l :=
  ⟨[.A], [.b], .A, by simp [Len.val, tb], by simp, ⟨.b, by simp, trivial⟩⟩

#print axioms modelAlpha_irrational
#print axioms coeff_unique
#print axioms wedge_fill_beta
#print axioms theorem1_conditional

end Erdos634.LaczJunction
