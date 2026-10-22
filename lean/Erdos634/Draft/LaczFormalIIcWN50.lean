-- Draft/LaczFormalIIcWN50.lean -- Laczkovich (DCG 48 (2012), Sect. 6.3), Lemma 6.2 (`IIcNoKites`), step (h), part 11:
-- `arc_pair_orient`: both pieces of a polygon cut along an exterior-type chord (open part off the polygon) are simple injective polygons and carry orientations;
-- `edgeSet_arc_sub`: the piece lies in `edgeSet p` union the chord.
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcWN49

open scoped Classical Fin.NatCast
open Complex Filter Topology

namespace Erdos634.Draft.LaczFormal.WN

variable {n : ℕ} [NeZero n]

theorem chord_closed_sub {p : Fin n → ℂ} {x y : ℂ} (h : ∀ s : ℝ, 0 < s → s < 1 → x + (s : ℂ) * (y - x) ∉ edgeSet p) :
    ∀ z ∈ segment ℝ x y, z ∈ edgeSet p → z = x ∨ z = y := by
  intro z hz hzE
  rw [segment_eq_image'] at hz
  obtain ⟨τ, ⟨h0, h1⟩, rfl⟩ := hz
  rcases h0.lt_or_eq with h0' | h0'
  · rcases h1.lt_or_eq with h1' | h1'
    · exfalso
      apply h τ h0' h1'
      simpa [Complex.real_smul] using hzE
    · right; rw [h1']; simp
  · left; rw [← h0']; simp

theorem edgeSet_arc_sub (p : Fin n → ℂ) (a : Fin n) (d : ℕ) {z : ℂ} (hz : z ∈ edgeSet (arcPoly p a d)) :
    z ∈ edgeSet p ∨ z ∈ segment ℝ (p (phi a d)) (p a) := by
  rcases (mem_edgeSet_arc p a d z).1 hz with ⟨i, -, hi⟩ | hz
  · left
    refine Set.mem_iUnion.2 ⟨phi a i, ?_⟩
    rw [← phi_succ]; exact hi
  · right; exact hz

theorem arc_pair_orient {p : Fin n → ℂ} (hs : SimplePoly p) (hinj : Function.Injective p) (a : Fin n) {d : ℕ} (hd2 : 2 ≤ d) (hdn : d + 2 ≤ n)
    (hopen : ∀ s : ℝ, 0 < s → s < 1 → p (phi a d) + (s : ℂ) * (p a - p (phi a d)) ∉ edgeSet p) :
    ∃ σ1 σ2 : ℝ, OrientOK (arcPoly p a d) σ1 ∧ OrientOK (arcPoly p (phi a d) (n - d)) σ2 := by
  have hn : 3 ≤ n := by omega
  have hc1 := chord_closed_sub hopen
  have hc1' : ∀ z ∈ segment ℝ (p (phi a d)) (p a), z ∈ edgeSet p → z = p a ∨ z = p (phi a d) := fun z hz hE => (hc1 z hz hE).symm
  have S1 := arc_simple hs hinj a hd2 hdn hc1'
  have I1 := arc_inj hinj a (d := d) (by omega)
  -- the second piece
  have hlast : phi (phi a d) (n - d) = a := phi_phi_last a (by omega)
  have hopen2 : ∀ s : ℝ, 0 < s → s < 1 → p (phi (phi a d) (n - d)) + (s : ℂ) * (p (phi a d) - p (phi (phi a d) (n - d))) ∉ edgeSet p := by
    intro s hs0 hs1
    rw [hlast]
    have := hopen (1 - s) (by linarith) (by linarith)
    have e : p a + (s : ℂ) * (p (phi a d) - p a) = p (phi a d) + ((1 - s : ℝ) : ℂ) * (p a - p (phi a d)) := by push_cast; ring
    rw [e]; exact this
  have hc2 := chord_closed_sub hopen2
  have hc2' : ∀ z ∈ segment ℝ (p (phi (phi a d) (n - d))) (p (phi a d)), z ∈ edgeSet p →
      z = p (phi a d) ∨ z = p (phi (phi a d) (n - d)) := fun z hz hE => (hc2 z hz hE).symm
  have S2 := arc_simple hs hinj (phi a d) (d := n - d) (by omega) (by omega) (by
    intro z hz hE
    rw [hlast] at hz ⊢
    have := hc2' z (by rw [hlast]; exact hz) hE
    rw [hlast] at this
    exact this)
  have I2 := arc_inj hinj (phi a d) (d := n - d) (by omega)
  obtain ⟨σ1, h1⟩ := orient_exists S1 I1 (by omega)
  obtain ⟨σ2, h2⟩ := orient_exists S2 I2 (by omega)
  exact ⟨σ1, σ2, h1, h2⟩

end Erdos634.Draft.LaczFormal.WN
