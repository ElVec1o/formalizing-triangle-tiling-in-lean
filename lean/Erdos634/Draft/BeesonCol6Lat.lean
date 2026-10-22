import Mathlib

/-!
# Beeson (arXiv 1206.2229 v4) Definition 7 and Lemma 26 (relation lattice), the elementary clauses

NOTE, UNAUDITED.  Credit: Michael Beeson (arXiv 1206.2229 v4, Definition 7, Lemma 26), Beeson-Rosu (Lemma 28, Definition 10.1).
Formalization debt, not progress on the /goal outcomes.

`relLat a b c` = `{(P,Q,R) ∈ ℤ³ | P a + Q b + R c = 0}` as an `AddSubgroup (Fin 3 → ℤ)`.  Proved: it is a subgroup (by construction),
saturated (`k ν ∈ L`, `k ≠ 0` => `ν ∈ L`), `L = ⊥` iff no nonzero integer relation (so, `a,b,c` independent over ℚ),
and for `a = s c`, `b = (1 - s^2) c` (`3α+2β=π`, `c ≠ 0`): `(P,Q,R) ∈ L ↔ Q s^2 - P s - (Q+R) = 0`.
NOT done: "rank L = 3 - dim_ℚ span{a,b,c}" and "rank 2 iff T rational", "rank 0/1/2 according as the degree of s".
-/

namespace Erdos634.BeesonCol6

/-- The relation lattice `L` of Definition 7. -/
def relLat (a b c : ℝ) : AddSubgroup (Fin 3 → ℤ) where
  carrier := {v | (v 0 : ℝ) * a + (v 1 : ℝ) * b + (v 2 : ℝ) * c = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    simp only [Set.mem_setOf_eq, Pi.add_apply] at *
    push_cast; linarith
  neg_mem' := by
    intro x hx
    simp only [Set.mem_setOf_eq, Pi.neg_apply] at *
    push_cast; linarith

theorem mem_relLat {a b c : ℝ} {v : Fin 3 → ℤ} :
    v ∈ relLat a b c ↔ (v 0 : ℝ) * a + (v 1 : ℝ) * b + (v 2 : ℝ) * c = 0 := Iff.rfl

/-- if `k ν ∈ L` for a nonzero integer `k` then `ν ∈ L`. -/
theorem relLat_saturated {a b c : ℝ} {v : Fin 3 → ℤ} {k : ℤ} (hk : k ≠ 0) (h : k • v ∈ relLat a b c) :
    v ∈ relLat a b c := by
  rw [mem_relLat] at h ⊢
  simp only [Pi.smul_apply, smul_eq_mul] at h
  push_cast at h
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  have : (k : ℝ) * ((v 0 : ℝ) * a + (v 1 : ℝ) * b + (v 2 : ℝ) * c) = 0 := by linarith
  exact (mul_eq_zero.mp this).resolve_left hk'

/-- rank 0: `L` is trivial iff there is no nonzero integer relation. -/
theorem relLat_eq_bot_iff {a b c : ℝ} :
    relLat a b c = ⊥ ↔ ∀ P Q R : ℤ, (P : ℝ) * a + Q * b + R * c = 0 → P = 0 ∧ Q = 0 ∧ R = 0 := by
  constructor
  · intro h P Q R hr
    have hm : ![P, Q, R] ∈ relLat a b c := by rw [mem_relLat]; simpa using hr
    rw [h, AddSubgroup.mem_bot] at hm
    have h0 := congrFun hm 0; have h1 := congrFun hm 1; have h2 := congrFun hm 2
    simp at h0 h1 h2
    exact ⟨h0, h1, h2⟩
  · intro h
    apply (AddSubgroup.eq_bot_iff_forall _).mpr
    intro v hv
    rw [mem_relLat] at hv
    obtain ⟨h0, h1, h2⟩ := h (v 0) (v 1) (v 2) hv
    ext i; fin_cases i <;> simp [h0, h1, h2]

/-- for `a = s c`, `b = (1 - s^2) c`, `c ≠ 0`: `(P,Q,R) ∈ L ↔ Q s^2 - P s - (Q + R) = 0`. -/
theorem relLat_mem_iff_quadratic {s c : ℝ} (hc : c ≠ 0) (v : Fin 3 → ℤ) :
    v ∈ relLat (s * c) ((1 - s ^ 2) * c) c ↔ (v 1 : ℝ) * s ^ 2 - (v 0 : ℝ) * s - ((v 1 : ℝ) + (v 2 : ℝ)) = 0 := by
  rw [mem_relLat]
  have e : (v 0 : ℝ) * (s * c) + (v 1 : ℝ) * ((1 - s ^ 2) * c) + (v 2 : ℝ) * c
      = -((v 1 : ℝ) * s ^ 2 - (v 0 : ℝ) * s - ((v 1 : ℝ) + (v 2 : ℝ))) * c := by ring
  rw [e]
  constructor
  · intro h
    have := (mul_eq_zero.mp h).resolve_right hc
    linarith
  · intro h; rw [h]; ring

/-- non-vacuity: the tile `(2,3,4)` (`s = 1/2`, `c = 4`) has the relation `(P,Q,R) = (-?)`: `2P+3Q+4R = 0` at `(1,2,-2)`; `L ≠ ⊥`. -/
theorem relLat_wit : relLat 2 3 4 ≠ ⊥ := by
  intro h
  have hm : ![(1 : ℤ), 2, -2] ∈ relLat (2 : ℝ) 3 4 := by rw [mem_relLat]; simp <;> norm_num
  rw [h, AddSubgroup.mem_bot] at hm
  have := congrFun hm 0
  simp at this

end Erdos634.BeesonCol6

#print axioms Erdos634.BeesonCol6.relLat_saturated
#print axioms Erdos634.BeesonCol6.relLat_eq_bot_iff
#print axioms Erdos634.BeesonCol6.relLat_mem_iff_quadratic
#print axioms Erdos634.BeesonCol6.relLat_wit
