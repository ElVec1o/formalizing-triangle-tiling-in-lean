-- Draft/LaczFormalIIcWN59.lean -- Laczkovich (DCG 48 (2012), Sect. 6.3), Lemma 6.2 (`IIcNoKites`), step (i), part 3:
-- `wind_zero_of_affine`: if a half-plane { Im((z - z0) mu) < delta } containing z0 misses a closed polygon, the winding number about z0 is 0.
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcWN58

open scoped Classical Fin.NatCast
open Complex Filter Topology

namespace Erdos634.Draft.LaczFormal.WN

theorem aff_comb (z0 μ y1 y2 : ℂ) (θ : ℝ) :
    ((y1 + (θ : ℂ) * (y2 - y1) - z0) * μ).im = (1 - θ) * ((y1 - z0) * μ).im + θ * ((y2 - z0) * μ).im := by
  have : (y1 + (θ : ℂ) * (y2 - y1) - z0) * μ = ((1 - θ : ℝ) : ℂ) * ((y1 - z0) * μ) + (θ : ℂ) * ((y2 - z0) * μ) := by
    push_cast; ring
  rw [this, Complex.add_im, Complex.im_ofReal_mul, Complex.im_ofReal_mul]

theorem wind_zero_of_affine {m : ℕ} [NeZero m] (q : Fin m → ℂ) {z0 μ : ℂ} (hμ : μ ≠ 0) (hq : ∀ i, 0 < ((q i - z0) * μ).im) :
    wind q z0 = 0 := by
  obtain ⟨i0, -, hi0⟩ := Finset.exists_min_image (Finset.univ : Finset (Fin m)) (fun i => ((q i - z0) * μ).im) ⟨0, Finset.mem_univ _⟩
  set δ := ((q i0 - z0) * μ).im with hδ
  have hδpos : 0 < δ := hq i0
  have hedge : ∀ y ∈ edgeSet q, δ ≤ ((y - z0) * μ).im := by
    intro y hy
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hy
    rw [segment_eq_image'] at hi
    obtain ⟨θ, ⟨h0, h1⟩, rfl⟩ := hi
    have e : q i + θ • (q (i + 1) - q i) = q i + (θ : ℂ) * (q (i + 1) - q i) := by simp [Complex.real_smul]
    beta_reduce
    rw [e, aff_comb]
    have a1 := hi0 i (Finset.mem_univ _)
    have a2 := hi0 (i + 1) (Finset.mem_univ _)
    nlinarith [mul_nonneg h0 (sub_nonneg.2 a2), mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 a1)]
  -- a far point in the half plane
  obtain ⟨K, hK, hKs⟩ := Filter.mem_cocompact.1 (wind_eventually_zero q)
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : ℂ)
  have hμn : 0 < ‖μ‖ := norm_pos_iff.2 hμ
  set R' : ℝ := max R 0 with hR'
  have hKR : K ⊆ Metric.closedBall (0 : ℂ) R' := fun x hx => by
    have := hR hx
    rw [Metric.mem_closedBall] at this ⊢
    exact this.trans (le_max_left _ _)
  have hR'0 : 0 ≤ R' := le_max_right _ _
  set lam : ℝ := (R' + ‖z0‖ + 1) / ‖μ‖ with hlam
  have hlampos : 0 ≤ lam := by positivity
  set ζ : ℂ := -(lam : ℂ) * I * (starRingEnd ℂ) μ with hζ
  have hζμ : ζ * μ = ((-(lam * Complex.normSq μ) : ℝ) : ℂ) * I := by
    rw [hζ]
    have : (starRingEnd ℂ) μ * μ = (Complex.normSq μ : ℂ) := (Complex.normSq_eq_conj_mul_self).symm
    calc -(lam : ℂ) * I * (starRingEnd ℂ) μ * μ = -(lam : ℂ) * I * ((starRingEnd ℂ) μ * μ) := by ring
      _ = _ := by rw [this]; push_cast; ring
  have hζn : ‖ζ‖ = R' + ‖z0‖ + 1 := by
    rw [hζ, norm_mul, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlampos, Complex.norm_I,
      mul_one, Complex.norm_conj, hlam]
    field_simp
  have him : ∀ θ : ℝ, 0 ≤ θ → ((z0 + (θ : ℂ) * ζ - z0) * μ).im = -(θ * (lam * Complex.normSq μ)) := by
    intro θ _
    have : (z0 + (θ : ℂ) * ζ - z0) * μ = (θ : ℂ) * (ζ * μ) := by ring
    rw [this, hζμ]
    have : (θ : ℂ) * (((-(lam * Complex.normSq μ) : ℝ) : ℂ) * I) = (((-(θ * (lam * Complex.normSq μ))) : ℝ) : ℂ) * I := by
      push_cast; ring
    rw [this]; simp
  have hns : 0 < Complex.normSq μ := Complex.normSq_pos.2 hμ
  have hfar : wind q (z0 + ζ) = 0 := by
    apply hKs
    intro hmem
    have := hKR hmem
    rw [Metric.mem_closedBall, dist_zero_right] at this
    have h2 : ‖ζ‖ ≤ ‖z0 + ζ‖ + ‖z0‖ := by
      calc ‖ζ‖ = ‖(z0 + ζ) - z0‖ := by ring_nf
        _ ≤ ‖z0 + ζ‖ + ‖z0‖ := norm_sub_le _ _
    rw [hζn] at h2
    linarith
  have hconst := wind_const_segment q (u := z0) (v := z0 + ζ) (by
    intro y hy hyE
    rw [segment_eq_image'] at hy
    obtain ⟨θ, ⟨h0, h1⟩, rfl⟩ := hy
    have e : z0 + θ • (z0 + ζ - z0) = z0 + (θ : ℂ) * ζ := by simp [Complex.real_smul]
    beta_reduce at hyE
    rw [e] at hyE
    have h3 := hedge _ hyE
    rw [him θ h0] at h3
    have : 0 ≤ θ * (lam * Complex.normSq μ) := by positivity
    linarith)
  rw [hconst, hfar]

end Erdos634.Draft.LaczFormal.WN
