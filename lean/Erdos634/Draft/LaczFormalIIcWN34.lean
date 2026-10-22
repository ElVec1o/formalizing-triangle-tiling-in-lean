-- Draft/LaczFormalIIcWN34.lean -- Laczkovich (DCG 48 (2012)), Sect. 6.2/6.3, Lemma 6.2 (`IIcNoKites`), step (d1), part 2:
-- `vertex_sectors`: at every vertex of a simple polygon the sector swept counterclockwise from the incoming ray up to the outgoing ray has
-- winding number `k0 = edgeVal 0`, the complementary sector `k0 + 1`.
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.2/6.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcWN33

open scoped Classical Fin.NatCast
open Complex Filter Topology

namespace Erdos634.Draft.LaczFormal.WN

variable {n : ℕ} [NeZero n]

theorem vertex_sectors {p : Fin n → ℂ} (hs : SimplePoly p) (hinj : Function.Injective p) (hn : 3 ≤ n) (i : Fin n) :
    ∃ r > 0, ∃ Δ : ℝ, 0 < Δ ∧ Δ < 2 * Real.pi ∧
      edir (p i) (p (i + 1)) * Complex.exp (Δ * I) = edir (p (i + 1 + 1)) (p (i + 1)) ∧
      (∀ ρ θ : ℝ, 0 < ρ → ρ < r → 0 < θ → θ < Δ →
        wind p (pt (p (i + 1)) (edir (p i) (p (i + 1))) ρ θ) = (edgeVal hs hinj hn 0 : ℝ)) ∧
      (∀ ρ θ : ℝ, 0 < ρ → ρ < r → Δ < θ → θ < 2 * Real.pi →
        wind p (pt (p (i + 1)) (edir (p i) (p (i + 1))) ρ θ) = (edgeVal hs hinj hn 0 : ℝ) + 1) := by
  obtain ⟨r, hr, Δ, hΔ0, hΔ1, hΔ, hR⟩ := tworays_vertex hs hinj hn i
  have hav : p i ≠ p (i + 1) := (nd hinj hn i).symm
  have hcv : p (i + 1 + 1) ≠ p (i + 1) := nd hinj hn (i + 1)
  have hLa : 0 < ‖p i - p (i + 1)‖ := norm_pos_iff.2 (sub_ne_zero.2 hav)
  have hLc : 0 < ‖p (i + 1 + 1) - p (i + 1)‖ := norm_pos_iff.2 (sub_ne_zero.2 hcv)
  set La := ‖p i - p (i + 1)‖ with hLadef
  set Lc := ‖p (i + 1 + 1) - p (i + 1)‖ with hLcdef
  set δa := min (1 / 2 : ℝ) (r / (4 * La)) with hδa
  set δc := min (1 / 2 : ℝ) (r / (4 * Lc)) with hδc
  have hδa0 : 0 < δa := lt_min (by norm_num) (by positivity)
  have hδc0 : 0 < δc := lt_min (by norm_num) (by positivity)
  have hδa1 : δa ≤ 1 / 2 := min_le_left _ _
  have hδc1 : δc ≤ 1 / 2 := min_le_left _ _
  have hδaL : La * δa ≤ r / 4 := by
    have h1 : δa ≤ r / (4 * La) := min_le_right _ _
    have := mul_le_mul_of_nonneg_left h1 hLa.le
    have e : La * (r / (4 * La)) = r / 4 := by field_simp
    linarith
  have hδcL : Lc * δc ≤ r / 4 := by
    have h1 : δc ≤ r / (4 * Lc) := min_le_right _ _
    have := mul_le_mul_of_nonneg_left h1 hLc.le
    have e : Lc * (r / (4 * Lc)) = r / 4 := by field_simp
    linarith
  obtain ⟨k, hk⟩ := good_exists hs hinj hn i (s := 1 - δa) (by linarith) (by linarith)
  obtain ⟨k', hk'⟩ := good_exists hs hinj hn (i + 1) (s := δc) hδc0 (by linarith)
  have key := vertex_abstract2 (p := p) (a := p i) (v := p (i + 1)) (c := p (i + 1 + 1)) (d1 := edir (p i) (p (i + 1)))
    hav hcv hr hΔ0 hΔ1 rfl hΔ hR (s := 1 - δa) (s' := δc) (by linarith) (by simpa using hδaL) hδc0 hδcL hk hk'
  obtain ⟨hkk, hsec1, hsec2⟩ := key
  have hg := good_eq_edgeVal hs hinj hn i (s := 1 - δa) (by linarith) (by linarith) hk
  rw [edgeVal_const hs hinj hn i] at hg
  refine ⟨r, hr, Δ, hΔ0, hΔ1, hΔ, ?_, ?_⟩
  · intro ρ θ h1 h2 h3 h4
    rw [hsec1 ρ θ h1 h2 h3 h4, hg]
  · intro ρ θ h1 h2 h3 h4
    rw [hsec2 ρ θ h1 h2 h3 h4, hg]

end Erdos634.Draft.LaczFormal.WN
