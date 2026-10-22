-- Draft/LaczFormalIIcWN23.lean -- Laczkovich (DCG 48 (2012)), Sect. 6.2/6.3, Lemma 6.2 (`IIcNoKites`), step (c) `u = v + N`:
-- discrete Hopf, part 4: bridge from `Fin n` simple polygons (SimplePoly, injective) to the N-indexed data `HData` of WN22
-- (rotation `phi k = m0 + k`, no antiparallel consecutive edges, disjointness of non-adjacent edges, lexicographic minimum).
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.2/6.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcWN22
import Erdos634.Draft.LaczFormalIIcWN11

open scoped Classical Fin.NatCast
open Complex

namespace Erdos634.Draft.LaczFormal.WN

variable {n : ℕ} [NeZero n]

/-- Consecutive edges of a simple polygon are never antiparallel (they would overlap). -/
theorem turn_ok {p : Fin n → ℂ} (hs : SimplePoly p) (hinj : Function.Injective p) (hn : 3 ≤ n) (i : Fin n) :
    ¬ (((p (i + 1 + 1) - p (i + 1)) / (p (i + 1) - p i)).im = 0 ∧
        ((p (i + 1 + 1) - p (i + 1)) / (p (i + 1) - p i)).re ≤ 0) := by
  rintro ⟨him, hre⟩
  set r : ℂ := (p (i + 1 + 1) - p (i + 1)) / (p (i + 1) - p i) with hr
  have hd : p (i + 1) - p i ≠ 0 := sub_ne_zero.2 (nd hinj hn i)
  have hd' : p (i + 1 + 1) - p (i + 1) ≠ 0 := sub_ne_zero.2 (nd hinj hn (i + 1))
  have hrd : p (i + 1 + 1) - p (i + 1) = r * (p (i + 1) - p i) := by rw [hr]; field_simp
  have hr0 : r ≠ 0 := by
    intro h; rw [h] at hrd; simp at hrd; exact hd' hrd
  have hrre : r.re < 0 := by
    rcases lt_or_eq_of_le hre with h | h
    · exact h
    · exfalso; apply hr0; apply Complex.ext <;> simp [h, him]
  have hrr : r = (r.re : ℂ) := by apply Complex.ext <;> simp [him]
  set s : ℝ := - r.re with hs'
  have hspos : 0 < s := by rw [hs']; linarith
  -- p(i+2) - p(i+1) = s * (p i - p(i+1))
  have hrd2 : p (i + 1 + 1) - p (i + 1) = (s : ℂ) * (p i - p (i + 1)) := by
    rw [hrd, hrr]; rw [hs']; push_cast; ring
  have hav : p i ≠ p (i + 1) := (nd hinj hn i).symm
  have hcv : p (i + 1 + 1) ≠ p (i + 1) := nd hinj hn (i + 1)
  have heq : edir (p i) (p (i + 1)) = edir (p (i + 1 + 1)) (p (i + 1)) := by
    unfold edir
    have hn1 : ‖p (i + 1 + 1) - p (i + 1)‖ = s * ‖p i - p (i + 1)‖ := by
      rw [hrd2, norm_mul]; simp [abs_of_pos hspos]
    rw [hn1, hrd2]
    have : ‖p i - p (i + 1)‖ ≠ 0 := norm_ne_zero_iff.2 (sub_ne_zero.2 hav)
    have hs0 : (s : ℂ) ≠ 0 := by exact_mod_cast hspos.ne'
    push_cast
    exact (mul_div_mul_left _ _ hs0).symm
  exact rays_distinct hs hinj hn i heq

/-- The rotation `phi m0 k = m0 + k`. -/
def phi (m0 : Fin n) (k : ℕ) : Fin n := m0 + (k : Fin n)

theorem phi_succ (m0 : Fin n) (k : ℕ) : phi m0 (k + 1) = phi m0 k + 1 := by
  unfold phi; rw [Nat.cast_succ, add_assoc]

theorem phi_n (m0 : Fin n) : phi m0 n = m0 := by
  unfold phi; simp

theorem phi_zero (m0 : Fin n) : phi m0 0 = m0 := by
  unfold phi; simp

theorem mod_small {a b : ℕ} (ha : a ≤ n) (hb : b ≤ n) (h : a % n = b % n) :
    a = b ∨ (a = 0 ∧ b = n) ∨ (a = n ∧ b = 0) := by
  have hpos : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  rcases lt_or_eq_of_le ha with ha' | ha'
  · rcases lt_or_eq_of_le hb with hb' | hb'
    · left; rwa [Nat.mod_eq_of_lt ha', Nat.mod_eq_of_lt hb'] at h
    · subst hb'; rw [Nat.mod_self, Nat.mod_eq_of_lt ha'] at h
      right; left; exact ⟨h, rfl⟩
  · subst ha'
    rcases lt_or_eq_of_le hb with hb' | hb'
    · rw [Nat.mod_self, Nat.mod_eq_of_lt hb'] at h
      right; right; exact ⟨rfl, h.symm⟩
    · left; exact hb'.symm

theorem phi_inj_small {p : Fin n → ℂ} (hinj : Function.Injective p) (m0 : Fin n) {a b : ℕ} (ha : a ≤ n) (hb : b ≤ n)
    (h : p (phi m0 a) = p (phi m0 b)) : a = b ∨ (a = 0 ∧ b = n) ∨ (a = n ∧ b = 0) := by
  have h1 := hinj h
  unfold phi at h1
  have h2 : ((a : ℕ) : Fin n) = ((b : ℕ) : Fin n) := add_left_cancel h1
  have h3 := congrArg Fin.val h2
  simp only [Fin.val_natCast] at h3
  exact mod_small ha hb h3

/-- Lexicographic minimum: a vertex `m0` such that every other vertex difference lies in `H`. -/
theorem exists_lexmin {p : Fin n → ℂ} (hinj : Function.Injective p) :
    ∃ m0 : Fin n, ∀ k : Fin n, k ≠ m0 → InH (p k - p m0) := by
  obtain ⟨m0, -, hm0⟩ := Finset.exists_min_image (Finset.univ : Finset (Fin n))
    (fun k => toLex ((p k).re, (p k).im)) ⟨0, Finset.mem_univ _⟩
  refine ⟨m0, fun k hk => ?_⟩
  have hle := hm0 k (Finset.mem_univ _)
  have hne : p k ≠ p m0 := fun h => hk (hinj h)
  rw [Prod.Lex.le_iff] at hle
  unfold InH
  simp only [Complex.sub_re, Complex.sub_im]
  simp only [ofLex_toLex] at hle
  rcases hle with h | ⟨h1, h2⟩
  · left; linarith
  · rcases lt_or_eq_of_le h2 with h3 | h3
    · right; exact ⟨by linarith, by linarith⟩
    · exfalso; apply hne; exact Complex.ext (by linarith) (by linarith)

end Erdos634.Draft.LaczFormal.WN
