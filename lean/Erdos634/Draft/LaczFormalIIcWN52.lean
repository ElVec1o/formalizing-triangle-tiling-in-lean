-- Draft/LaczFormalIIcWN52.lean -- Laczkovich (DCG 48 (2012), Sect. 6.3), Lemma 6.2 (`IIcNoKites`), step (h), part 13:
-- `ChordFam` (every concave vertex has an exterior chord to another vertex, chords of distinct concave vertices disjoint), `Inv` (a pocket: an arc with a family
-- chord and orientation opposite to p), `arcPoly_arcPoly`, `sub_arc` (the arc between two interior vertices of a pocket joined by an exterior chord is again a pocket).
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcWN51

open scoped Classical Fin.NatCast
open Complex Filter Topology

namespace Erdos634.Draft.LaczFormal.WN

variable {n : ℕ} [NeZero n]

structure ChordFam (p : Fin n → ℂ) (σ : ℝ) (J : Fin n → Fin n) : Prop where
  chord : ∀ k : Fin n, σ * extAng p k < 0 → ExtChord p (p k) (p (J k))
  disj : ∀ k k' : Fin n, σ * extAng p k < 0 → σ * extAng p k' < 0 → k ≠ k' →
    Disjoint (segment ℝ (p k) (p (J k))) (segment ℝ (p k') (p (J k')))

/-- A pocket: the arc `a, ..., a+d` with a family chord between its ends and orientation opposite to that of `p`. -/
def Inv (p : Fin n → ℂ) (σ : ℝ) (J : Fin n → Fin n) (a : Fin n) (d : ℕ) : Prop :=
  2 ≤ d ∧ d + 2 ≤ n ∧
    ((σ * extAng p a < 0 ∧ J a = phi a d) ∨ (σ * extAng p (phi a d) < 0 ∧ J (phi a d) = a)) ∧
    ∃ σQ : ℝ, OrientOK (arcPoly p a d) σQ ∧ σQ = -σ

theorem inv_data {p : Fin n → ℂ} {σ : ℝ} {J : Fin n → Fin n} (F : ChordFam p σ J) {a : Fin n} {d : ℕ}
    (hI : Inv p σ J a d) :
    ExtChord p (p (phi a d)) (p a) ∧
      ∀ k' : Fin n, σ * extAng p k' < 0 → k' ≠ a → k' ≠ phi a d →
        Disjoint (segment ℝ (p k') (p (J k'))) (segment ℝ (p (phi a d)) (p a)) := by
  obtain ⟨-, -, hc, -⟩ := hI
  rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have := F.chord a h1
    rw [h2] at this
    refine ⟨this.symm, fun k' hk' hna hnd => ?_⟩
    have := F.disj k' a hk' h1 hna
    rw [h2, segment_symm ℝ (p a)] at this
    exact this
  · have := F.chord _ h1
    rw [h2] at this
    refine ⟨this, fun k' hk' hna hnd => ?_⟩
    have := F.disj k' _ hk' h1 hnd
    rw [h2] at this
    exact this

theorem arcPoly_arcPoly (p : Fin n → ℂ) (a : Fin n) {d : ℕ} (u : Fin (d + 1)) {e : ℕ} (h : u.val + e ≤ d) :
    arcPoly (arcPoly p a d) u e = arcPoly p (phi a u.val) e := by
  funext t
  simp only [arcPoly]
  have hm : t.val ≤ e := by have := t.isLt; omega
  have hv : (phi u t.val).val = u.val + t.val := by
    unfold phi
    rw [Fin.val_add, Fin.val_natCast, Nat.mod_eq_of_lt (by omega : t.val < d + 1)]
    exact Nat.mod_eq_of_lt (by omega)
  rw [hv, phi_phi]

end Erdos634.Draft.LaczFormal.WN
