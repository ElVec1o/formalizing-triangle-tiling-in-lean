-- Draft/LaczFormalIIcWN16.lean -- Laczkovich (DCG 48 (2012)), Sect. 6.2, step (a): two distinct edges of Gamma_kite meet only at common endpoints.
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.2), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcWN15

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement Erdos634.CertCoord Filter Topology

namespace Erdos634.Draft.LaczFormal.RG

variable {N : ℕ}

theorem toV2_mkPt (a b : ℝ) : toV2 (mkPt a b) = (a, b) := by
  unfold toV2; simp [mkPt_zero, mkPt_one]

/-- A point `z + eps * vec` with `eps > 0` as close to `z` as we like. -/
theorem exists_eps (z vec : Plane) {r : ℝ} (hr : 0 < r) : ∃ ε : ℝ, 0 < ε ∧ dist (z + ε • vec) z < r := by
  have hc' : ContinuousAt (fun ε : ℝ => dist (z + ε • vec) z) 0 := by fun_prop
  have h0 : dist (z + (0 : ℝ) • vec) z < r := by simpa using hr
  have h := hc'.tendsto.eventually (eventually_lt_nhds h0)
  obtain ⟨ε, hε, hεpos⟩ := ((h.filter_mono nhdsWithin_le_nhds : ∀ᶠ ε in 𝓝[>] (0 : ℝ), _).and self_mem_nhdsWithin).exists
  exact ⟨ε, hεpos, hε⟩

theorem crs_shift (d : V2) (z : Plane) (ε : ℝ) (v : V2) :
    crs d (toV2 ((z + ε • mkPt v.1 v.2) - z)) = ε * crs d v := by
  simp only [crs, toV2, add_sub_cancel_left, PiLp.smul_apply, smul_eq_mul, mkPt_zero, mkPt_one]
  ring

theorem exists_dir {d d' : V2} (h : crs d d' ≠ 0) (α β : ℝ) : ∃ v : V2, crs d v = α ∧ crs d' v = β := by
  have h' : d.1 * d'.2 - d.2 * d'.1 ≠ 0 := h
  refine ⟨((α * d'.1 - d.1 * β) / (d.1 * d'.2 - d.2 * d'.1), (d'.2 * α - d.2 * β) / (d.1 * d'.2 - d.2 * d'.1)), ?_, ?_⟩
  · unfold crs; field_simp; ring
  · unfold crs
    have e : d'.1 * ((d'.2 * α - d.2 * β) / (d.1 * d'.2 - d.2 * d'.1)) - d'.2 * ((α * d'.1 - d.1 * β) / (d.1 * d'.2 - d.2 * d'.1))
        = β * (d.1 * d'.2 - d.2 * d'.1) / (d.1 * d'.2 - d.2 * d'.1) := by ring
    rw [e, mul_div_assoc, div_self h', mul_one]

/-- Two nonzero parallel directions are positively or negatively parallel. -/
theorem par_or_neg {d d' : V2} (hd : d ≠ 0) (hd' : d' ≠ 0) (hc : crs d d' = 0) : Par d d' ∨ Par d (neg2 d') := by
  have hdt : dt d d' ≠ 0 := by
    intro h0
    have hsq : (crs d d') ^ 2 + (dt d d') ^ 2 = (d.1 ^ 2 + d.2 ^ 2) * (d'.1 ^ 2 + d'.2 ^ 2) := by
      unfold crs dt; ring
    rw [hc, h0] at hsq
    have h1 : 0 < d.1 ^ 2 + d.2 ^ 2 := by
      by_contra hh
      apply hd
      have a : d.1 = 0 := by nlinarith [sq_nonneg d.1, sq_nonneg d.2]
      have b : d.2 = 0 := by nlinarith [sq_nonneg d.1, sq_nonneg d.2]
      exact Prod.ext a b
    have h2 : 0 < d'.1 ^ 2 + d'.2 ^ 2 := by
      by_contra hh
      apply hd'
      have a : d'.1 = 0 := by nlinarith [sq_nonneg d'.1, sq_nonneg d'.2]
      have b : d'.2 = 0 := by nlinarith [sq_nonneg d'.1, sq_nonneg d'.2]
      exact Prod.ext a b
    nlinarith [mul_pos h1 h2]
  rcases lt_or_gt_of_ne hdt with h | h
  · right
    refine ⟨?_, ?_⟩
    · unfold crs at hc ⊢; simp only [neg2]; linarith
    · unfold dt at h ⊢; simp only [neg2]; linarith
  · exact Or.inl ⟨hc, h⟩

theorem triStep_congr_par' {T : Tri} {d d' : V2} {U U' : Plane} (h : TriStep T d U U') (hp : Par d d') : TriStep T d' U U' := by
  obtain ⟨kk, f, g, hk, hf, hfk, hgk, hgf, hpar, hleft⟩ := h
  refine ⟨kk, f, g, hk, hf, hfk, hgk, hgf, hpar.trans hp, ?_⟩
  obtain ⟨c, hc, hcd⟩ := hp.smul
  have : crs d (toV2 (T.pts g - U)) = c * crs d' (toV2 (T.pts g - U)) := by
    rw [hcd]; unfold crs; ring
  rw [this] at hleft
  exact (mul_pos_iff_of_pos_left hc).mp hleft

end Erdos634.Draft.LaczFormal.RG
