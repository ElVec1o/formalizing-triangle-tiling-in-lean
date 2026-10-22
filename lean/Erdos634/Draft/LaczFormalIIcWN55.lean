-- Draft/LaczFormalIIcWN55.lean -- Laczkovich (DCG 48 (2012), Sect. 6.3), Lemma 6.2 (`IIcNoKites`), step (h) ("C1 is convex"), ASSEMBLY:
-- `no_concave`: a simple polygon (SimplePoly, injective, 3 <= n; orientation sigma) in which every concave vertex (sigma * extAng < 0) has an exterior chord to another
-- vertex (open chord off the polygon, winding 0 along it) and the closed chords of distinct concave vertices are pairwise disjoint, has NO concave vertex.
-- Proof: minimal pocket; the pocket (the piece of orientation -sigma) has a concave vertex by the angle sum; its chord stays in the pocket (winding argument); the sub-pocket is smaller.
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcWN54

open scoped Classical Fin.NatCast
open Complex Filter Topology

namespace Erdos634.Draft.LaczFormal.WN

variable {n : ℕ} [NeZero n]

theorem no_inv {p : Fin n → ℂ} (hs : SimplePoly p) (hinj : Function.Injective p) (hn : 3 ≤ n) {σ : ℝ} (Op : OrientOK p σ)
    {J : Fin n → Fin n} (F : ChordFam p σ J) : ∀ d : ℕ, ∀ a : Fin n, ¬ Inv p σ J a d := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro a hI
    obtain ⟨a', d', hd', hI'⟩ := inv_step hs hinj hn Op F hI
    exact ih d' hd' a' hI'

theorem no_concave {p : Fin n → ℂ} (hs : SimplePoly p) (hinj : Function.Injective p) (hn : 3 ≤ n) {σ : ℝ} (Op : OrientOK p σ)
    {J : Fin n → Fin n} (F : ChordFam p σ J) : ∀ k : Fin n, ¬ σ * extAng p k < 0 := by
  intro k hk
  have hch := F.chord k hk
  obtain ⟨d, hd, hd2, hdn⟩ := chord_arc_param hn hch
  have hch' : ExtChord p (p (phi k d)) (p k) := by rw [hd]; exact hch.symm
  obtain ⟨σ1, σ2, O1, O2⟩ := arc_pair_orient hs hinj k hd2 hdn hch'.1
  have hsg := chord_signs hinj k hd2 hdn hch'.1 O1.1 O2.1 hch'.2
  have hneg := hsg.1 rfl
  have hσ := Op.1.1
  have h1 := O1.1.1
  by_cases hcase : σ1 = -σ
  · exact no_inv hs hinj hn Op F d k ⟨hd2, hdn, Or.inl ⟨hk, hd.symm⟩, σ1, O1, hcase⟩
  · have hσ1 : σ1 = σ := by
      rcases hσ with h | h <;> rcases h1 with h' | h' <;> first | linarith | (exfalso; apply hcase; linarith)
    have hσ2 : σ2 = -σ := by linarith
    refine no_inv hs hinj hn Op F (n - d) (phi k d) ⟨by omega, by omega, Or.inr ⟨?_, ?_⟩, σ2, O2, hσ2⟩
    · rw [phi_phi_last k (by omega)]; exact hk
    · rw [phi_phi_last k (by omega), hd]

#print axioms Erdos634.Draft.LaczFormal.WN.no_concave
#print axioms Erdos634.Draft.LaczFormal.WN.inv_step

end Erdos634.Draft.LaczFormal.WN
