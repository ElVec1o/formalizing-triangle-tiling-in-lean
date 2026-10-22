-- Draft/LaczFormalIIcWN51.lean -- Laczkovich (DCG 48 (2012), Sect. 6.3), Lemma 6.2 (`IIcNoKites`), step (h), part 12:
-- `orient_unique`, `arc_vertex_transfer` (vertex transfer between p and an arc polygon at an interior arc vertex), `arc_chord_near`
-- (winding of the arc polygon along an exterior chord starting at an interior arc vertex, near that vertex), `wind_const_on_chord`.
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcWN50

open scoped Classical Fin.NatCast
open Complex Filter Topology

namespace Erdos634.Draft.LaczFormal.WN

variable {n : ℕ} [NeZero n]

theorem orient_unique {p : Fin n → ℂ} (hs : SimplePoly p) (hinj : Function.Injective p) (hn : 3 ≤ n) {σ σ' : ℝ}
    (h : OrientOK p σ) (h' : OrientOK p σ') : σ = σ' := by
  obtain ⟨ρ, hρ, hsum⟩ := exterior_angle_sum hs hinj hn
  have e1 := h.2.2.1
  have e2 := h'.2.2.1
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hsum] at e1 e2
  have : (σ - σ') * (2 * Real.pi * ρ) = 0 := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at e1 e2
    linarith
  have hne : 2 * Real.pi * ρ ≠ 0 := by
    rcases hρ with rfl | rfl <;> positivity
  have := (mul_eq_zero.1 this).resolve_right hne
  linarith

theorem phi_phi (a : Fin n) (d m : ℕ) : phi (phi a d) m = phi a (d + m) := by
  unfold phi; rw [Nat.cast_add, add_assoc]

theorem arc_vertex_transfer {p : Fin n → ℂ} (hs : SimplePoly p) (hinj : Function.Injective p) (hn : 3 ≤ n) (a : Fin n) {d : ℕ}
    {σ σQ : ℝ} (Op : OrientOK p σ) (OQ : OrientOK (arcPoly p a d) σQ) (k : ℕ) (hk1 : 1 ≤ k) (hk2 : k + 1 ≤ d) :
    ∃ r > 0, ∀ z : ℂ, dist z (p (phi a k)) < r → z ∉ edgeSet p →
      (σQ = σ → wind (arcPoly p a d) z = wind p z) ∧
      (σQ = -σ → (wind p z = 0 → wind (arcPoly p a d) z = σQ) ∧ (wind p z = σ → wind (arcPoly p a d) z = 0)) := by
  set u : Fin (d + 1) := ⟨k, by omega⟩ with hu
  obtain ⟨e0, e1, e2⟩ := arc_nbrs p a u hk1 hk2
  have huv : u.val = k := rfl
  rw [huv] at e0 e1 e2
  have hs0 : phi a (k - 1) + 1 = phi a k := by rw [← phi_succ]; congr 1; omega
  have hs1 : phi a (k - 1) + 1 + 1 = phi a (k + 1) := by rw [hs0, ← phi_succ]
  have := vertex_transfer hs hinj hn Op OQ (i := phi a (k - 1)) (j := u - 1) (by
      rw [e0]) (by rw [sub_add_cancel, hs0, e1]) (by rw [sub_add_cancel, hs0, ← phi_succ, e2])
  rw [hs0] at this
  exact this

theorem arc_chord_near {p : Fin n → ℂ} (hs : SimplePoly p) (hinj : Function.Injective p) (hn : 3 ≤ n) (a : Fin n) {d : ℕ}
    {σ σQ : ℝ} (Op : OrientOK p σ) (OQ : OrientOK (arcPoly p a d) σQ) (k : ℕ) (hk1 : 1 ≤ k) (hk2 : k + 1 ≤ d) {y : ℂ}
    (hy : ExtChord p (p (phi a k)) y) :
    ∃ s0 > 0, ∀ s : ℝ, 0 < s → s < s0 → s < 1 →
      (σQ = σ → wind (arcPoly p a d) (p (phi a k) + (s : ℂ) * (y - p (phi a k))) = 0) ∧
      (σQ = -σ → wind (arcPoly p a d) (p (phi a k) + (s : ℂ) * (y - p (phi a k))) = σQ) := by
  obtain ⟨r, hr, ht⟩ := arc_vertex_transfer hs hinj hn a Op OQ k hk1 hk2
  have hyv : y ≠ p (phi a k) := by
    intro h
    apply hy.1 (1 / 2) (by norm_num) (by norm_num)
    rw [h]; simpa using vertex_mem_edgeSet p (phi a k)
  have hn0 : 0 < ‖y - p (phi a k)‖ := norm_pos_iff.2 (sub_ne_zero.2 hyv)
  refine ⟨min 1 (r / ‖y - p (phi a k)‖), lt_min one_pos (by positivity), fun s hs0 hs1 hs2 => ?_⟩
  have hd : dist (p (phi a k) + (s : ℂ) * (y - p (phi a k))) (p (phi a k)) < r := by
    rw [dist_eq_norm]
    have e : p (phi a k) + (s : ℂ) * (y - p (phi a k)) - p (phi a k) = (s : ℂ) * (y - p (phi a k)) := by ring
    rw [e, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs0]
    have : s < r / ‖y - p (phi a k)‖ := lt_of_lt_of_le hs1 (min_le_right _ _)
    rwa [lt_div_iff₀ hn0] at this
  have hw := hy.wind_zero hs0 hs2
  obtain ⟨h1, h2⟩ := ht _ hd (hy.1 s hs0 hs2)
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [h1 h, hw]
  · exact (h2 h).1 hw

theorem wind_const_on_chord (q : Fin n → ℂ) {x y : ℂ} (h : ∀ s : ℝ, 0 < s → s < 1 → x + (s : ℂ) * (y - x) ∉ edgeSet q)
    {s s' : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hs0' : 0 < s') (hs1' : s' < 1) :
    wind q (x + (s : ℂ) * (y - x)) = wind q (x + (s' : ℂ) * (y - x)) := by
  apply wind_const_segment q
  intro z hz
  rw [segment_eq_image'] at hz
  obtain ⟨θ, ⟨hθ0, hθ1⟩, rfl⟩ := hz
  have e : x + (s : ℂ) * (y - x) + θ • (x + (s' : ℂ) * (y - x) - (x + (s : ℂ) * (y - x))) =
      x + ((s + θ * (s' - s) : ℝ) : ℂ) * (y - x) := by
    simp only [Complex.real_smul]; push_cast; ring
  beta_reduce
  rw [e]
  apply h
  · rcases le_total s s' with hh | hh
    · nlinarith [mul_nonneg hθ0 (sub_nonneg.2 hh)]
    · nlinarith [mul_nonneg (sub_nonneg.2 hθ1) (sub_nonneg.2 hh)]
  · rcases le_total s s' with hh | hh
    · nlinarith [mul_nonneg (sub_nonneg.2 hθ1) (sub_nonneg.2 hh)]
    · nlinarith [mul_nonneg hθ0 (sub_nonneg.2 hh)]

end Erdos634.Draft.LaczFormal.WN
