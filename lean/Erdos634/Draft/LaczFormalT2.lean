-- Draft/LaczFormalT2.lean -- target T2 of the L8-general plan (abstract part): classification of a triangle all of whose
-- angles are rational multiples of pi with cosines in Q(sqrt N) (from `LaczFormalT1.lemmaQ_general`).  Angles in units of pi/60:
-- each angle is n*pi/60 with n in {20,30,40} (pi/3, pi/2, 2pi/3), {15,45} (N = 2k^2), {10,50} (N = 3k^2), {12,24,36,48}
-- (N = 5k^2); the triples with sum 60 are exactly (20,20,20), (15,15,30), (10,20,30), (10,10,40), (12,24,24), (12,12,36)
-- (machine-checked by `omega` below).  UNAUDITED.  Credit: Snover-Waiveris-Williams, Beeson, Beeson-Rosu.
import Erdos634.Draft.LaczFormalT1
import Erdos634.Draft.LaczFormalBase

open scoped Classical
open Real Erdos634.Geometry Erdos634.TilePlacement Erdos634.Draft.TheoremPConditional

namespace Erdos634.Draft.LaczFormal

def TagCore (N n : ℕ) : Prop :=
  (n = 20 ∨ n = 30 ∨ n = 40) ∨ ((n = 15 ∨ n = 45) ∧ ∃ k : ℕ, N = 2 * k ^ 2) ∨
  ((n = 10 ∨ n = 50) ∧ ∃ k : ℕ, N = 3 * k ^ 2) ∨
  ((n = 12 ∨ n = 24 ∨ n = 36 ∨ n = 48) ∧ ∃ k : ℕ, N = 5 * k ^ 2)

def TagOK (N : ℕ) (θ : ℝ) : Prop := ∃ n : ℕ, θ = (n : ℝ) / 60 * π ∧ TagCore N n

theorem tagOK_of_Q {N : ℕ} {θ : ℝ}
    (h : (θ = π / 3 ∨ θ = π / 2 ∨ θ = π * (2 / 3)) ∨
    ((θ = π / 4 ∨ θ = π * (3 / 4)) ∧ ∃ k : ℕ, N = 2 * k ^ 2) ∨
    ((θ = π / 6 ∨ θ = π * (5 / 6)) ∧ ∃ k : ℕ, N = 3 * k ^ 2) ∨
    ((θ = π / 5 ∨ θ = π * (2 / 5) ∨ θ = π * (3 / 5) ∨ θ = π * (4 / 5)) ∧ ∃ k : ℕ, N = 5 * k ^ 2)) :
    TagOK N θ := by
  rcases h with (h | h | h) | ⟨h | h, k⟩ | ⟨h | h, k⟩ | ⟨h | h | h | h, k⟩
  · exact ⟨20, by rw [h]; push_cast; ring, Or.inl (by omega)⟩
  · exact ⟨30, by rw [h]; push_cast; ring, Or.inl (by omega)⟩
  · exact ⟨40, by rw [h]; push_cast; ring, Or.inl (by omega)⟩
  · exact ⟨15, by rw [h]; push_cast; ring, Or.inr (Or.inl ⟨by omega, k⟩)⟩
  · exact ⟨45, by rw [h]; push_cast; ring, Or.inr (Or.inl ⟨by omega, k⟩)⟩
  · exact ⟨10, by rw [h]; push_cast; ring, Or.inr (Or.inr (Or.inl ⟨by omega, k⟩))⟩
  · exact ⟨50, by rw [h]; push_cast; ring, Or.inr (Or.inr (Or.inl ⟨by omega, k⟩))⟩
  · exact ⟨12, by rw [h]; push_cast; ring, Or.inr (Or.inr (Or.inr ⟨by omega, k⟩))⟩
  · exact ⟨24, by rw [h]; push_cast; ring, Or.inr (Or.inr (Or.inr ⟨by omega, k⟩))⟩
  · exact ⟨36, by rw [h]; push_cast; ring, Or.inr (Or.inr (Or.inr ⟨by omega, k⟩))⟩
  · exact ⟨48, by rw [h]; push_cast; ring, Or.inr (Or.inr (Or.inr ⟨by omega, k⟩))⟩

def VAL (n : ℕ) : Prop := n = 20 ∨ n = 30 ∨ n = 40 ∨ n = 15 ∨ n = 45 ∨ n = 10 ∨ n = 50 ∨ n = 12 ∨ n = 24 ∨ n = 36 ∨ n = 48

theorem val_of_tag {N n : ℕ} (t : TagCore N n) : VAL n := by
  unfold TagCore at t
  rcases t with h | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> unfold VAL <;> omega

theorem tag2 {N n : ℕ} (t : TagCore N n) (h : n = 15 ∨ n = 45) : ∃ m : ℕ, N = 2 * m ^ 2 := by
  rcases t with h' | ⟨-, k⟩ | ⟨h', -⟩ | ⟨h', -⟩
  · omega
  · exact k
  · omega
  · omega

theorem tag3 {N n : ℕ} (t : TagCore N n) (h : n = 10 ∨ n = 50) : ∃ m : ℕ, N = 3 * m ^ 2 := by
  rcases t with h' | ⟨h', -⟩ | ⟨-, k⟩ | ⟨h', -⟩
  · omega
  · omega
  · exact k
  · omega

theorem tag5 {N n : ℕ} (t : TagCore N n) (h : n = 12 ∨ n = 24 ∨ n = 36 ∨ n = 48) :
    ∃ m : ℕ, N = 5 * m ^ 2 := by
  rcases t with h' | ⟨h', -⟩ | ⟨h', -⟩ | ⟨-, k⟩
  · omega
  · omega
  · omega
  · exact k

def SLIST : List ℕ := [20, 30, 40, 15, 45, 10, 50, 12, 24, 36, 48]
def ALLOWED : List (ℕ × ℕ × ℕ) := [(20, 20, 20), (20, 30, 10), (20, 10, 30), (30, 20, 10), (30, 15, 15), (30, 10, 20), (40, 10, 10), (15, 30, 15), (15, 15, 30), (10, 20, 30), (10, 30, 20), (10, 40, 10), (10, 10, 40), (12, 12, 36), (12, 24, 24), (12, 36, 12), (24, 12, 24), (24, 24, 12), (36, 12, 12)]

theorem key_class : ∀ a ∈ SLIST, ∀ b ∈ SLIST, ∀ c ∈ SLIST, a + b + c = 60 → (a, b, c) ∈ ALLOWED := by
  decide +kernel

theorem val_mem {n : ℕ} (v : VAL n) : n ∈ SLIST := by
  unfold VAL at v; unfold SLIST; simp; omega

theorem nat_class (n0 n1 n2 : ℕ) (hs : n0 + n1 + n2 = 60) (v0 : VAL n0) (v1 : VAL n1) (v2 : VAL n2) :
  (n0 = 20 ∧ n1 = 20 ∧ n2 = 20) ∨ (n0 = 20 ∧ n1 = 30 ∧ n2 = 10) ∨ (n0 = 20 ∧ n1 = 10 ∧ n2 = 30) ∨ (n0 = 30 ∧ n1 = 20 ∧ n2 = 10) ∨ (n0 = 30 ∧ n1 = 15 ∧ n2 = 15) ∨ (n0 = 30 ∧ n1 = 10 ∧ n2 = 20) ∨ (n0 = 40 ∧ n1 = 10 ∧ n2 = 10) ∨ (n0 = 15 ∧ n1 = 30 ∧ n2 = 15) ∨ (n0 = 15 ∧ n1 = 15 ∧ n2 = 30) ∨ (n0 = 10 ∧ n1 = 20 ∧ n2 = 30) ∨ (n0 = 10 ∧ n1 = 30 ∧ n2 = 20) ∨ (n0 = 10 ∧ n1 = 40 ∧ n2 = 10) ∨ (n0 = 10 ∧ n1 = 10 ∧ n2 = 40) ∨ (n0 = 12 ∧ n1 = 12 ∧ n2 = 36) ∨ (n0 = 12 ∧ n1 = 24 ∧ n2 = 24) ∨ (n0 = 12 ∧ n1 = 36 ∧ n2 = 12) ∨ (n0 = 24 ∧ n1 = 12 ∧ n2 = 24) ∨ (n0 = 24 ∧ n1 = 24 ∧ n2 = 12) ∨ (n0 = 36 ∧ n1 = 12 ∧ n2 = 12) := by
  have := key_class n0 (val_mem v0) n1 (val_mem v1) n2 (val_mem v2) hs
  simpa [ALLOWED] using this

/-- **T2 (abstract part).**  A tile all of whose angles are rational multiples of `π` with cosines in `ℚ(√N)`
is equilateral, or one of the five classes below (each with the matching form of `N`). -/
theorem class_of_rational {N : ℕ} (D : CongruentDissection N)
    (htag : ∀ k, TagOK N (D.model.angleAt k)) :
    (∀ k, D.model.angleAt k = π / 3) ∨
    ((∃ m : ℕ, N = 2 * m ^ 2) ∧ TileAngles D (π / 4) (π / 4) (π / 2)) ∨
    ((∃ m : ℕ, N = 3 * m ^ 2) ∧ TileAngles D (π / 6) (π / 3) (π / 2)) ∨
    ((∃ m : ℕ, N = 3 * m ^ 2) ∧ TileAngles D (π / 6) (π / 6) (2 * π / 3)) ∨
    ((∃ m : ℕ, N = 5 * m ^ 2) ∧ TileAngles D (π / 5) (2 * π / 5) (2 * π / 5)) ∨
    ((∃ m : ℕ, N = 5 * m ^ 2) ∧ TileAngles D (π / 5) (π / 5) (3 * π / 5)) := by
  have hpi := Real.pi_pos
  obtain ⟨n0, hθ0, t0⟩ := htag 0
  obtain ⟨n1, hθ1, t1⟩ := htag 1
  obtain ⟨n2, hθ2, t2⟩ := htag 2
  have hsum := angleAt_sum D.model
  rw [hθ0, hθ1, hθ2] at hsum
  have h60 : (((n0 : ℝ) + n1 + n2 - 60)) * π = 0 := by linear_combination 60 * hsum
  have h60' : ((n0 : ℝ) + n1 + n2 - 60) = 0 := (mul_eq_zero.mp h60).resolve_right hpi.ne'
  have hn : n0 + n1 + n2 = 60 := by
    have : ((n0 + n1 + n2 : ℕ) : ℝ) = 60 := by push_cast; linarith
    exact_mod_cast this
  have base : TileAngles D (D.model.angleAt 0) (D.model.angleAt 1) (D.model.angleAt 2) :=
    ⟨1, rfl, rfl, rfl⟩
  have hc := nat_class n0 n1 n2 hn (val_of_tag t0) (val_of_tag t1) (val_of_tag t2)
  rcases hc with hcase | hcase | hcase | hcase | hcase | hcase | hcase | hcase | hcase | hcase | hcase | hcase | hcase | hcase | hcase | hcase | hcase | hcase | hcase
  · obtain ⟨h0', h1', h2'⟩ := hcase
    subst h0' h1' h2'
    left
    intro k
    rcases (show k = 0 ∨ k = 1 ∨ k = 2 by fin_cases k <;> simp) with rfl | rfl | rfl
    · rw [hθ0]; push_cast; ring
    · rw [hθ1]; push_cast; ring
    · rw [hθ2]; push_cast; ring
  · obtain ⟨h0', h1', h2'⟩ := hcase
    subst h0' h1' h2'
    right; right; left
    refine ⟨tag3 t2 (by omega), (((base).swap23).swap).cast (by simp only [hθ0, hθ1, hθ2]; push_cast; ring) (by simp only [hθ0, hθ1, hθ2]; push_cast; ring) (by simp only [hθ0, hθ1, hθ2]; push_cast; ring)⟩
  · obtain ⟨h0', h1', h2'⟩ := hcase
    subst h0' h1' h2'
    right; right; left
    refine ⟨tag3 t1 (by omega), ((base).swap).cast (by simp only [hθ0, hθ1, hθ2]; push_cast; ring) (by simp only [hθ0, hθ1, hθ2]; push_cast; ring) (by simp only [hθ0, hθ1, hθ2]; push_cast; ring)⟩
  · obtain ⟨h0', h1', h2'⟩ := hcase
    subst h0' h1' h2'
    right; right; left
    refine ⟨tag3 t2 (by omega), ((((base).swap).swap23).swap).cast (by simp only [hθ0, hθ1, hθ2]; push_cast; ring) (by simp only [hθ0, hθ1, hθ2]; push_cast; ring) (by simp only [hθ0, hθ1, hθ2]; push_cast; ring)⟩
  · obtain ⟨h0', h1', h2'⟩ := hcase
    subst h0' h1' h2'
    right; left
    refine ⟨tag2 t1 (by omega), (((base).swap).swap23).cast (by simp only [hθ0, hθ1, hθ2]; push_cast; ring) (by simp only [hθ0, hθ1, hθ2]; push_cast; ring) (by simp only [hθ0, hθ1, hθ2]; push_cast; ring)⟩
  · obtain ⟨h0', h1', h2'⟩ := hcase
    subst h0' h1' h2'
    right; right; left
    refine ⟨tag3 t1 (by omega), (((base).swap).swap23).cast (by simp only [hθ0, hθ1, hθ2]; push_cast; ring) (by simp only [hθ0, hθ1, hθ2]; push_cast; ring) (by simp only [hθ0, hθ1, hθ2]; push_cast; ring)⟩
  · obtain ⟨h0', h1', h2'⟩ := hcase
    subst h0' h1' h2'
    right; right; right; left
    refine ⟨tag3 t1 (by omega), (((base).swap).swap23).cast (by simp only [hθ0, hθ1, hθ2]; push_cast; ring) (by simp only [hθ0, hθ1, hθ2]; push_cast; ring) (by simp only [hθ0, hθ1, hθ2]; push_cast; ring)⟩
  · obtain ⟨h0', h1', h2'⟩ := hcase
    subst h0' h1' h2'
    right; left
    refine ⟨tag2 t0 (by omega), ((base).swap23).cast (by simp only [hθ0, hθ1, hθ2]; push_cast; ring) (by simp only [hθ0, hθ1, hθ2]; push_cast; ring) (by simp only [hθ0, hθ1, hθ2]; push_cast; ring)⟩
  · obtain ⟨h0', h1', h2'⟩ := hcase
    subst h0' h1' h2'
    right; left
    refine ⟨tag2 t0 (by omega), (base).cast (by simp only [hθ0, hθ1, hθ2]; push_cast; ring) (by simp only [hθ0, hθ1, hθ2]; push_cast; ring) (by simp only [hθ0, hθ1, hθ2]; push_cast; ring)⟩
  · obtain ⟨h0', h1', h2'⟩ := hcase
    subst h0' h1' h2'
    right; right; left
    refine ⟨tag3 t0 (by omega), (base).cast (by simp only [hθ0, hθ1, hθ2]; push_cast; ring) (by simp only [hθ0, hθ1, hθ2]; push_cast; ring) (by simp only [hθ0, hθ1, hθ2]; push_cast; ring)⟩
  · obtain ⟨h0', h1', h2'⟩ := hcase
    subst h0' h1' h2'
    right; right; left
    refine ⟨tag3 t0 (by omega), ((base).swap23).cast (by simp only [hθ0, hθ1, hθ2]; push_cast; ring) (by simp only [hθ0, hθ1, hθ2]; push_cast; ring) (by simp only [hθ0, hθ1, hθ2]; push_cast; ring)⟩
  · obtain ⟨h0', h1', h2'⟩ := hcase
    subst h0' h1' h2'
    right; right; right; left
    refine ⟨tag3 t0 (by omega), ((base).swap23).cast (by simp only [hθ0, hθ1, hθ2]; push_cast; ring) (by simp only [hθ0, hθ1, hθ2]; push_cast; ring) (by simp only [hθ0, hθ1, hθ2]; push_cast; ring)⟩
  · obtain ⟨h0', h1', h2'⟩ := hcase
    subst h0' h1' h2'
    right; right; right; left
    refine ⟨tag3 t0 (by omega), (base).cast (by simp only [hθ0, hθ1, hθ2]; push_cast; ring) (by simp only [hθ0, hθ1, hθ2]; push_cast; ring) (by simp only [hθ0, hθ1, hθ2]; push_cast; ring)⟩
  · obtain ⟨h0', h1', h2'⟩ := hcase
    subst h0' h1' h2'
    right; right; right; right; right
    refine ⟨tag5 t0 (by omega), (base).cast (by simp only [hθ0, hθ1, hθ2]; push_cast; ring) (by simp only [hθ0, hθ1, hθ2]; push_cast; ring) (by simp only [hθ0, hθ1, hθ2]; push_cast; ring)⟩
  · obtain ⟨h0', h1', h2'⟩ := hcase
    subst h0' h1' h2'
    right; right; right; right; left
    refine ⟨tag5 t0 (by omega), (base).cast (by simp only [hθ0, hθ1, hθ2]; push_cast; ring) (by simp only [hθ0, hθ1, hθ2]; push_cast; ring) (by simp only [hθ0, hθ1, hθ2]; push_cast; ring)⟩
  · obtain ⟨h0', h1', h2'⟩ := hcase
    subst h0' h1' h2'
    right; right; right; right; right
    refine ⟨tag5 t0 (by omega), ((base).swap23).cast (by simp only [hθ0, hθ1, hθ2]; push_cast; ring) (by simp only [hθ0, hθ1, hθ2]; push_cast; ring) (by simp only [hθ0, hθ1, hθ2]; push_cast; ring)⟩
  · obtain ⟨h0', h1', h2'⟩ := hcase
    subst h0' h1' h2'
    right; right; right; right; left
    refine ⟨tag5 t0 (by omega), ((base).swap).cast (by simp only [hθ0, hθ1, hθ2]; push_cast; ring) (by simp only [hθ0, hθ1, hθ2]; push_cast; ring) (by simp only [hθ0, hθ1, hθ2]; push_cast; ring)⟩
  · obtain ⟨h0', h1', h2'⟩ := hcase
    subst h0' h1' h2'
    right; right; right; right; left
    refine ⟨tag5 t0 (by omega), (((base).swap23).swap).cast (by simp only [hθ0, hθ1, hθ2]; push_cast; ring) (by simp only [hθ0, hθ1, hθ2]; push_cast; ring) (by simp only [hθ0, hθ1, hθ2]; push_cast; ring)⟩
  · obtain ⟨h0', h1', h2'⟩ := hcase
    subst h0' h1' h2'
    right; right; right; right; right
    refine ⟨tag5 t0 (by omega), (((base).swap).swap23).cast (by simp only [hθ0, hθ1, hθ2]; push_cast; ring) (by simp only [hθ0, hθ1, hθ2]; push_cast; ring) (by simp only [hθ0, hθ1, hθ2]; push_cast; ring)⟩

end Erdos634.Draft.LaczFormal

#print axioms Erdos634.Draft.LaczFormal.class_of_rational
