-- Draft/LaczFormalIIcWN38.lean -- Laczkovich (DCG 48 (2012)), Sect. 6.2/6.3, Lemma 6.2 (`IIcNoKites`), step (d1), ASSEMBLY:
-- `polygon_orientation`: for a simple polygon p (SimplePoly, injective, 3 <= n) there is sigma = +-1 such that
--   (1) wind p takes the values {0, sigma} off the polygon;
--   (2) the interior angles pi - sigma * extAng p k lie in (0, 2 pi) and sum to (n-2) pi;
--   (3) at every vertex p(i+1), near the vertex, the counterclockwise sector from the incoming ray to the outgoing ray (angle Delta = pi + ext)
--       has winding number k0 and the other k0 + 1, and the sector of winding number sigma is the INTERIOR sector of angle pi - sigma * ext.
-- (rho = sigma: the identification of the Hopf orientation with the winding sign, via the lexicographically minimal vertex.)
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.2/6.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcWN37

open scoped Classical Fin.NatCast
open Complex Filter Topology

namespace Erdos634.Draft.LaczFormal.WN

variable {n : ℕ} [NeZero n]

theorem polygon_orientation {p : Fin n → ℂ} (hs : SimplePoly p) (hinj : Function.Injective p) (hn : 3 ≤ n) :
    ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ (∀ z : ℂ, z ∉ edgeSet p → wind p z = 0 ∨ wind p z = σ) ∧
      (∀ k : Fin n, 0 < Real.pi - σ * extAng p k ∧ Real.pi - σ * extAng p k < 2 * Real.pi) ∧
      ∑ k : Fin n, (Real.pi - σ * extAng p k) = ((n : ℝ) - 2) * Real.pi ∧
      ∀ i : Fin n, ∃ r > 0, ∃ Δ : ℝ, 0 < Δ ∧ Δ < 2 * Real.pi ∧ Δ = Real.pi + extAng p (i + 1) ∧
        edir (p i) (p (i + 1)) * Complex.exp (Δ * I) = edir (p (i + 1 + 1)) (p (i + 1)) ∧
        ∀ ρ θ : ℝ, 0 < ρ → ρ < r → 0 < θ → θ < 2 * Real.pi → θ ≠ Δ →
          wind p (pt (p (i + 1)) (edir (p i) (p (i + 1))) ρ θ) = if (σ = -1 ↔ θ < Δ) then σ else 0 := by
  obtain ⟨ρ, hρ, hsum, m0, hm0, hsign⟩ := exterior_angle_sum_lex hs hinj hn
  have hk0 : (ρ = 1 ∧ (edgeVal hs hinj hn 0 : ℝ) = 0) ∨ (ρ = -1 ∧ (edgeVal hs hinj hn 0 : ℝ) = -1) := by
    rcases lex_vertex hs hinj hn hm0 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rcases hsign with ⟨-, h3⟩ | ⟨h3, -⟩
      · linarith
      · exact Or.inr ⟨h3, h2⟩
    · rcases hsign with ⟨h3, -⟩ | ⟨-, h3⟩
      · exact Or.inl ⟨h3, h2⟩
      · linarith
  obtain ⟨σ', hσ', hdich⟩ := simple_wind_dichotomy hs hinj hn
  -- two off-polygon points with wind k0 and k0+1 near the minimal vertex (sector values) identify sigma' = rho
  have hboth : ∃ z1 z2 : ℂ, z1 ∉ edgeSet p ∧ z2 ∉ edgeSet p ∧ wind p z1 = (edgeVal hs hinj hn 0 : ℝ) ∧
      wind p z2 = (edgeVal hs hinj hn 0 : ℝ) + 1 := by
    obtain ⟨ε, hε, h⟩ := edgeVal_spec hs hinj hn 0
    obtain ⟨a1, a2, a3, a4⟩ := h (ε / 2) (by positivity) (by linarith)
    exact ⟨_, _, a2, a1, a3, a4⟩
  have hσρ : σ' = ρ := by
    obtain ⟨z1, z2, h1, h2, w1, w2⟩ := hboth
    rcases hk0 with ⟨rfl, hk⟩ | ⟨rfl, hk⟩
    · rcases hdich z2 h2 with h | h
      · rw [w2, hk] at h; norm_num at h
      · rw [w2, hk] at h; linarith
    · rcases hdich z1 h1 with h | h
      · rw [w1, hk] at h; norm_num at h
      · rw [w1, hk] at h; linarith
  subst hσρ
  refine ⟨σ', hρ, hdich, ?_, ?_, ?_⟩
  · intro k
    have hb := extAng_bounds hs hinj hn k
    rcases hρ with rfl | rfl
    · constructor <;> linarith [hb.1, hb.2]
    · constructor <;> linarith [hb.1, hb.2]
  · rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hsum]
    simp
    rcases hρ with rfl | rfl <;> ring
  · intro i
    obtain ⟨r, hr, Δ, hΔ0, hΔ1, hΔ, hs1, hs2⟩ := vertex_sectors hs hinj hn i
    refine ⟨r, hr, Δ, hΔ0, hΔ1, delta_eq hs hinj hn i hΔ0 hΔ1 hΔ, hΔ, ?_⟩
    intro ρ' θ h1 h2 h3 h4 h5
    rcases lt_or_gt_of_ne h5 with h | h
    · rw [hs1 ρ' θ h1 h2 h3 h]
      rcases hk0 with ⟨rfl, hk⟩ | ⟨rfl, hk⟩
      · simp [hk, h]; norm_num
      · simp [hk, h]
    · rw [hs2 ρ' θ h1 h2 h h4]
      rcases hk0 with ⟨rfl, hk⟩ | ⟨rfl, hk⟩
      · simp [hk, not_lt.2 h.le]; norm_num
      · simp [hk, not_lt.2 h.le]

end Erdos634.Draft.LaczFormal.WN

#print axioms Erdos634.Draft.LaczFormal.WN.polygon_orientation
#print axioms Erdos634.Draft.LaczFormal.WN.vertex_sectors
#print axioms Erdos634.Draft.LaczFormal.WN.lex_vertex
