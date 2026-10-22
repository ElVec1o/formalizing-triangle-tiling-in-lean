-- Draft/LaczFormalIIcWN46.lean -- Laczkovich (DCG 48 (2012)), Sect. 6.3, Lemma 6.2 (`IIcNoKites`), step (h), part 7:
-- `OrientOK p sigma` (the content of `polygon_orientation` as a predicate), `orient_exists`, and `vertex_transfer`: two simple polygons sharing a vertex and
-- both neighbours have, near the vertex, winding numbers related by their orientation signs (equal if equal signs; swapped sectors if opposite).
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcWN45

open scoped Classical Fin.NatCast
open Complex Filter Topology

namespace Erdos634.Draft.LaczFormal.WN

variable {n : ℕ} [NeZero n]

/-- Vertex sector formula with sign `σ`. -/
def VertexFormula (p : Fin n → ℂ) (σ : ℝ) : Prop :=
  ∀ i : Fin n, ∃ r > 0, ∃ Δ : ℝ, 0 < Δ ∧ Δ < 2 * Real.pi ∧ Δ = Real.pi + extAng p (i + 1) ∧
    edir (p i) (p (i + 1)) * Complex.exp (Δ * I) = edir (p (i + 1 + 1)) (p (i + 1)) ∧
    ∀ ρ θ : ℝ, 0 < ρ → ρ < r → 0 < θ → θ < 2 * Real.pi → θ ≠ Δ →
      wind p (pt (p (i + 1)) (edir (p i) (p (i + 1))) ρ θ) = if (σ = -1 ↔ θ < Δ) then σ else 0

/-- Everything `polygon_orientation` provides, for a given sign. -/
def OrientOK (p : Fin n → ℂ) (σ : ℝ) : Prop :=
  Dich p σ ∧ (∀ k : Fin n, 0 < Real.pi - σ * extAng p k ∧ Real.pi - σ * extAng p k < 2 * Real.pi) ∧
    ∑ k : Fin n, (Real.pi - σ * extAng p k) = ((n : ℝ) - 2) * Real.pi ∧ VertexFormula p σ

theorem orient_exists {p : Fin n → ℂ} (hs : SimplePoly p) (hinj : Function.Injective p) (hn : 3 ≤ n) : ∃ σ : ℝ, OrientOK p σ := by
  obtain ⟨σ, h1, h2, h3, h4, h5⟩ := polygon_orientation hs hinj hn
  exact ⟨σ, ⟨h1, h2⟩, h3, h4, h5⟩

theorem sign_swap {σp σq : ℝ} (hp : σp = 1 ∨ σp = -1) (hq : σq = 1 ∨ σq = -1) (hne : σq = -σp) (Δ θ : ℝ) :
    ((if (σp = -1 ↔ θ < Δ) then σp else 0) = 0 → (if (σq = -1 ↔ θ < Δ) then σq else 0) = σq) ∧
    ((if (σp = -1 ↔ θ < Δ) then σp else 0) = σp → (if (σq = -1 ↔ θ < Δ) then σq else 0) = 0) := by
  rcases hp with rfl | rfl <;> rcases hq with rfl | rfl <;> norm_num at hne <;> by_cases h : θ < Δ <;> simp [h] <;> norm_num

theorem vertex_transfer {m : ℕ} [NeZero m] {p : Fin n → ℂ} {q : Fin m → ℂ} (hs : SimplePoly p) (hinj : Function.Injective p) (hn : 3 ≤ n)
    {σp σq : ℝ} (Op : OrientOK p σp) (Oq : OrientOK q σq) {i : Fin n} {j : Fin m}
    (h0 : q j = p i) (h1 : q (j + 1) = p (i + 1)) (h2 : q (j + 1 + 1) = p (i + 1 + 1)) :
    ∃ r > 0, ∀ z : ℂ, dist z (p (i + 1)) < r → z ∉ edgeSet p →
      (σq = σp → wind q z = wind p z) ∧ (σq = -σp → (wind p z = 0 → wind q z = σq) ∧ (wind p z = σp → wind q z = 0)) := by
  obtain ⟨r1, hr1, Δ1, hΔ10, hΔ11, hΔ1e, hΔ1, hF1⟩ := Op.2.2.2 i
  obtain ⟨r2, hr2, Δ2, hΔ20, hΔ21, hΔ2e, hΔ2, hF2⟩ := Oq.2.2.2 j
  obtain ⟨r3, hr3, Δ3, hΔ30, hΔ31, hΔ3, hR⟩ := tworays_vertex hs hinj hn i
  have hΔ3e := delta_eq hs hinj hn i hΔ30 hΔ31 hΔ3
  have hext : extAng q (j + 1) = extAng p (i + 1) := by
    unfold extAng
    have : j + 1 - 1 = j := by simp
    have h' : i + 1 - 1 = i := by simp
    rw [this, h', h1, h0, h2]
  have hΔ12 : Δ2 = Δ1 := by rw [hΔ2e, hΔ1e, hext]
  have hΔ13 : Δ3 = Δ1 := by rw [hΔ3e, hΔ1e]
  have hd : edir (q j) (q (j + 1)) = edir (p i) (p (i + 1)) := by rw [h0, h1]
  refine ⟨min r1 (min r2 r3), lt_min hr1 (lt_min hr2 hr3), fun z hz hzE => ?_⟩
  have hzr1 : dist z (p (i + 1)) < r1 := lt_of_lt_of_le hz (min_le_left _ _)
  have hzr2 : dist z (p (i + 1)) < r2 := lt_of_lt_of_le hz ((min_le_right _ _).trans (min_le_left _ _))
  have hzr3 : dist z (p (i + 1)) < r3 := lt_of_lt_of_le hz ((min_le_right _ _).trans (min_le_right _ _))
  have hd1 : ‖edir (p i) (p (i + 1))‖ = 1 := edir_norm (fun h => (nd hinj hn i) h.symm)
  obtain ⟨ρ, θ, hρ, hρr, hθ0, hθ1, hθΔ, hzeq⟩ := pt_cover hR hd1 hr3 hzr3 hzE
  have hρd : ρ = dist z (p (i + 1)) := by
    rw [hzeq, pt_dist hd1 hρ.le]
  rw [hΔ13] at hθΔ
  have hwp : wind p z = if (σp = -1 ↔ θ < Δ1) then σp else 0 := by
    rw [hzeq]; exact hF1 ρ θ hρ (by rw [hρd]; exact hzr1) hθ0 hθ1 hθΔ
  have hwq : wind q z = if (σq = -1 ↔ θ < Δ1) then σq else 0 := by
    rw [hzeq]
    have := hF2 ρ θ hρ (by rw [hρd]; exact hzr2) hθ0 hθ1 (by rw [hΔ12]; exact hθΔ)
    rw [hΔ12] at this
    rw [h1, h0] at this
    exact this
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [hwq, hwp, h]
  · have := sign_swap Op.1.1 Oq.1.1 h Δ1 θ
    rw [hwq, hwp]
    exact this

end Erdos634.Draft.LaczFormal.WN
