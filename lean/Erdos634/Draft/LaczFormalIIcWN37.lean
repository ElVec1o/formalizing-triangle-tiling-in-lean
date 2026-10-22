-- Draft/LaczFormalIIcWN37.lean -- Laczkovich (DCG 48 (2012)), Sect. 6.2/6.3, Lemma 6.2 (`IIcNoKites`), step (d1), part 5:
-- `lex_vertex`: at a lexicographically minimal vertex the convex wedge between the two edges is the sector of winding number sigma (sector values k0 = -1 / 0 vs
-- the sign of the exterior angle).
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.2/6.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcWN36
import Mathlib.Analysis.Complex.Convex

open scoped Classical Fin.NatCast
open Complex Filter Topology

namespace Erdos634.Draft.LaczFormal.WN

variable {n : ℕ} [NeZero n]

theorem edir_eq_exp {a v : ℂ} (h : a ≠ v) : edir a v = Complex.exp ((Complex.arg (a - v) : ℝ) * I) := by
  have hn0 : ((‖a - v‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (norm_pos_iff.2 (sub_ne_zero.2 h)).ne'
  unfold edir
  rw [div_eq_iff hn0, mul_comm]
  exact (Complex.norm_mul_exp_arg_mul_I (a - v)).symm

theorem pt_left {v : ℂ} {φ1 : ℝ} (ρ : ℝ) : pt v (Complex.exp ((φ1 : ℝ) * I)) ρ (Real.pi - φ1) = v - (ρ : ℂ) := by
  unfold pt
  rw [mul_assoc, ← Complex.exp_add]
  have : (φ1 : ℂ) * I + ((Real.pi - φ1 : ℝ) : ℂ) * I = (Real.pi : ℂ) * I := by push_cast; ring
  rw [this, Complex.exp_pi_mul_I]; ring

theorem wind_left_zero {p : Fin n → ℂ} {m0 : Fin n} (hm0 : ∀ k : Fin n, k ≠ m0 → InH (p k - p m0)) {ρ : ℝ} (hρ : 0 < ρ) :
    wind p (p m0 - (ρ : ℂ)) = 0 := by
  obtain ⟨w, hwim, hwre, hw0⟩ := exists_far_left p (p m0).im ((p m0).re - ρ)
  have hv : ∀ k : Fin n, (p m0).re ≤ (p k).re := by
    intro k
    by_cases hk : k = m0
    · rw [hk]
    · have := hm0 k hk
      rcases this with h | ⟨h, -⟩
      · simp at h; linarith
      · simp at h; linarith
  have hedge : ∀ q ∈ edgeSet p, (p m0).re ≤ q.re := by
    intro q hq
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hq
    have hsub : segment ℝ (p i) (p (i + 1)) ⊆ {z : ℂ | (p m0).re ≤ z.re} :=
      (convex_halfSpace_re_ge (p m0).re).segment_subset (hv i) (hv (i + 1))
    exact hsub hi
  have hz : (p m0 - (ρ : ℂ)).re = (p m0).re - ρ := by simp
  have hzim : (p m0 - (ρ : ℂ)).im = (p m0).im := by simp
  have := wind_const_segment p (u := w) (v := p m0 - (ρ : ℂ)) (by
    intro y hy hyE
    have h1 := hedge y hyE
    have hconv : segment ℝ w (p m0 - (ρ : ℂ)) ⊆ {z : ℂ | z.re ≤ (p m0).re - ρ} :=
      (convex_halfSpace_re_le ((p m0).re - ρ)).segment_subset (by simp; linarith) (by simp)
    have := hconv hy
    simp at this
    linarith)
  rw [← this, hw0]

theorem lex_vertex {p : Fin n → ℂ} (hs : SimplePoly p) (hinj : Function.Injective p) (hn : 3 ≤ n) {m0 : Fin n}
    (hm0 : ∀ k : Fin n, k ≠ m0 → InH (p k - p m0)) :
    (extAng p m0 < 0 ∧ (edgeVal hs hinj hn 0 : ℝ) = -1) ∨ (0 < extAng p m0 ∧ (edgeVal hs hinj hn 0 : ℝ) = 0) := by
  obtain ⟨r, hr, Δ, hΔ0, hΔ1, hΔ, hs1, hs2⟩ := vertex_sectors hs hinj hn (m0 - 1)
  have hδ := delta_eq hs hinj hn (m0 - 1) hΔ0 hΔ1 hΔ
  have hi : m0 - 1 + 1 = m0 := sub_add_cancel _ _
  rw [hi] at hΔ hs1 hs2 hδ
  have hne1 : m0 - 1 ≠ m0 := by
    intro h
    have : (1 : Fin n) = 0 := by simpa using h
    exact fin_one_ne hn this
  have hne2 : m0 + 1 ≠ m0 := by
    intro h
    have : (1 : Fin n) = 0 := by simpa using h
    exact fin_one_ne hn this
  have ha := hm0 _ hne1
  have hc := hm0 _ hne2
  have hb1 := ha.arg_bounds
  have hb2 := hc.arg_bounds
  have e1 := edir_eq_exp (a := p (m0 - 1)) (v := p m0) (fun h => hne1 (hinj h))
  have e2 := edir_eq_exp (a := p (m0 + 1)) (v := p m0) (fun h => hne2 (hinj h))
  set φ1 := Complex.arg (p (m0 - 1) - p m0) with hφ1
  set φ2 := Complex.arg (p (m0 + 1) - p m0) with hφ2
  rw [e1, e2] at hΔ
  rw [e1] at hs1 hs2
  have hex : Complex.exp (((φ1 + Δ : ℝ) : ℂ) * I) = Complex.exp ((φ2 : ℂ) * I) := by
    rw [← hΔ, ← Complex.exp_add]; push_cast; ring_nf
  obtain ⟨m, hm⟩ := Complex.exp_eq_exp_iff_exists_int.1 hex
  have hre := congrArg Complex.im hm
  simp at hre
  have hpi := Real.pi_pos
  have hb1a := hb1.1
  have hb1b := hb1.2
  have hb2a := hb2.1
  have hb2b := hb2.2
  have hmm : (m : ℝ) * (2 * Real.pi) = φ1 + Δ - φ2 := by linarith
  have hm1 : (m : ℝ) < 3 / 2 := by by_contra hc'; push Not at hc'; nlinarith
  have hm2 : (-1 / 2 : ℝ) < m := by by_contra hc'; push Not at hc'; nlinarith
  have hm1' : m < 2 := by
    have : (m : ℝ) < 2 := by linarith
    exact_mod_cast this
  have hm2' : -1 < m := by
    have : (-1 : ℝ) < m := by linarith
    exact_mod_cast this
  have hleft := wind_left_zero hm0 (ρ := r / 2) (by positivity)
  have hpt : pt (p m0) (Complex.exp ((φ1 : ℝ) * I)) (r / 2) (Real.pi - φ1) = p m0 - ((r / 2 : ℝ) : ℂ) := pt_left _
  have hm01 : m = 0 ∨ m = 1 := by omega
  rcases hm01 with rfl | rfl
  · simp at hmm
    have hw := hs2 (r / 2) (Real.pi - φ1) (by positivity) (by linarith) (by linarith) (by linarith)
    rw [hpt, hleft] at hw
    left
    exact ⟨by linarith, by linarith⟩
  · simp at hmm
    have hw := hs1 (r / 2) (Real.pi - φ1) (by positivity) (by linarith) (by linarith) (by linarith)
    rw [hpt, hleft] at hw
    right
    exact ⟨by linarith, by linarith⟩

end Erdos634.Draft.LaczFormal.WN
