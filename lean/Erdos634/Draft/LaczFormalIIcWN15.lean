-- Draft/LaczFormalIIcWN15.lean -- Laczkovich (DCG 48 (2012)), Sect. 6.2, step (a): no tile vertex lies in the relative interior of a side that has tiles on both sides ("no T-junction on a double edge").
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.2), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcWN14

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement Erdos634.CertCoord Filter Topology

namespace Erdos634.Draft.LaczFormal.RG

variable {N : ℕ}

/-- A vertex of a tile is never a relative interior point of one of its own sides. -/
theorem step_open_not_vertex (T : Tri) {d : V2} {U V : Plane} (hS : TriStep T d U V) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (k0 : Fin 3) : T.pts k0 ≠ U + t • (V - U) := by
  obtain ⟨kk, f, g, hk, hf, hfk, hgk, hgf, -, -⟩ := hS
  intro h
  have hx : U + t • (V - U) = (1 - t) • T.pts kk + t • T.pts f + (0 : ℝ) • T.pts g := by
    rw [← hk, ← hf]
    ext j
    simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
    ring
  obtain ⟨c1, c2, c3⟩ := coord_lbl T hfk hgk hgf (U + t • (V - U)) (1 - t) t 0 (by ring) hx
  have hc : T.basis.coord k0 (U + t • (V - U)) = 1 := by
    rw [← h]
    exact T.basis.coord_apply_eq k0
  rcases fin3_cover5a kk f g k0 hfk hgk hgf with rfl | rfl | rfl
  · rw [c1] at hc; linarith
  · rw [c2] at hc; linarith
  · rw [c3] at hc; linarith

theorem crs_collinear {d u v : V2} (hd : d ≠ 0) (hu : crs d u = 0) (hv : crs d v = 0) : crs u v = 0 := by
  have h1 : d.1 * crs u v = 0 := by unfold crs at *; linear_combination u.1 * hv - v.1 * hu
  have h2 : d.2 * crs u v = 0 := by unfold crs at *; linear_combination u.2 * hv - v.2 * hu
  by_contra hne
  apply hd
  have e1 : d.1 = 0 := by rcases mul_eq_zero.1 h1 with h | h; exact h; exact absurd h hne
  have e2 : d.2 = 0 := by rcases mul_eq_zero.1 h2 with h | h; exact h; exact absurd h hne
  exact Prod.ext e1 e2

/-- **No T-junction on a double edge.**  A vertex of any tile cannot lie in the relative interior of a segment `XY` that is a left step of one tile along `d` and a left step of another tile along `-d`. -/
theorem tjunction (D : RegionDissection N) {k i j : Fin N} {k0 : Fin 3} {d : V2} {X Y : Plane} {t : ℝ}
    (hi : TriStep (D.tile i) d X Y) (hj : TriStep (D.tile j) (neg2 d) Y X) (ht0 : 0 < t) (ht1 : t < 1)
    (hv : (D.tile k).pts k0 = X + t • (Y - X)) : False := by
  have hd0 : d ≠ 0 := by
    obtain ⟨kk, f, g, hk, hf, hfk, hgk, hgf, hpar, -⟩ := hi
    exact hpar.ne_right
  have hz2 : Y + (1 - t) • (X - Y) = X + t • (Y - X) := by
    ext j; simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]; ring
  obtain ⟨r1, hr1, h1⟩ := halfdisc (D.tile i) hi ht0 ht1
  obtain ⟨r2, hr2, h2⟩ := halfdisc (D.tile j) hj (t := 1 - t) (by linarith) (by linarith)
  rw [hz2] at h2
  set z : Plane := X + t • (Y - X) with hzdef
  obtain ⟨f, g, hfk, hgk, hgf⟩ : ∃ f g : Fin 3, f ≠ k0 ∧ g ≠ k0 ∧ g ≠ f := by
    have : ∀ k0 : Fin 3, ∃ f g : Fin 3, f ≠ k0 ∧ g ≠ k0 ∧ g ≠ f := by decide
    exact this k0
  set T' := D.tile k with hT'
  set P := T'.pts k0 with hP
  set Q := T'.pts f with hQ
  set R := T'.pts g with hR
  have hΔ := tri_cross_ne T' hfk hgk hgf
  set aQ := crs d (toV2 (Q - P)) with haQ
  set aR := crs d (toV2 (R - P)) with haR
  have hne : aQ ≠ 0 ∨ aR ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hΔ (crs_collinear hd0 hcon.1 hcon.2)
  obtain ⟨μ, ν, hμ, hν, hσ⟩ : ∃ μ ν : ℝ, 0 < μ ∧ 0 < ν ∧ μ * aQ + ν * aR ≠ 0 := by
    by_cases hs : aQ + aR = 0
    · refine ⟨2, 1, by norm_num, by norm_num, ?_⟩
      have : aQ ≠ 0 := by
        intro h0
        rcases hne with h | h
        · exact h h0
        · exact h (by linarith)
      intro h; apply this; linarith
    · exact ⟨1, 1, by norm_num, by norm_num, by intro h; apply hs; linarith⟩
  set σ := μ * aQ + ν * aR with hσdef
  -- the sector point
  set v : Plane := μ • (Q - P) + ν • (R - P) with hvdef
  set ε : ℝ := min (1 / (μ + ν + 1)) (min r1 r2 / (‖v‖ + 1)) / 2 with hεdef
  have hε0 : 0 < ε := by
    have : 0 < min (1 / (μ + ν + 1)) (min r1 r2 / (‖v‖ + 1)) :=
      lt_min (by positivity) (div_pos (lt_min hr1 hr2) (by positivity))
    positivity
  have hε1 : ε * (μ + ν) < 1 := by
    have h1 : ε ≤ 1 / (μ + ν + 1) / 2 := by
      have := min_le_left (1 / (μ + ν + 1)) (min r1 r2 / (‖v‖ + 1))
      have hεeq : ε = min (1 / (μ + ν + 1)) (min r1 r2 / (‖v‖ + 1)) / 2 := rfl
      linarith
    have h2 : 1 / (μ + ν + 1) / 2 * (μ + ν) < 1 := by
      rw [div_div, div_mul_eq_mul_div, div_lt_one (by positivity)]
      nlinarith
    calc ε * (μ + ν) ≤ 1 / (μ + ν + 1) / 2 * (μ + ν) := by gcongr
      _ < 1 := h2
  set w : Plane := P + (ε * μ) • (Q - P) + (ε * ν) • (R - P) with hwdef
  have hwint : w ∈ interior T'.carrier :=
    sector_interior T' hfk hgk hgf (mul_pos hε0 hμ) (mul_pos hε0 hν) (by nlinarith)
  have hwz : w - z = ε • v := by
    rw [← hv]
    simp only [hwdef, hvdef, hP]
    ext j; simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]; ring
  have hdist : dist w z < min r1 r2 := by
    rw [dist_eq_norm, hwz, norm_smul, Real.norm_of_nonneg hε0.le]
    have h1 : ε ≤ min r1 r2 / (‖v‖ + 1) / 2 := by
      have := min_le_right (1 / (μ + ν + 1)) (min r1 r2 / (‖v‖ + 1))
      have hεeq : ε = min (1 / (μ + ν + 1)) (min r1 r2 / (‖v‖ + 1)) / 2 := rfl
      linarith
    have hm : 0 < min r1 r2 := lt_min hr1 hr2
    have h3 : ε * ‖v‖ ≤ min r1 r2 / (‖v‖ + 1) / 2 * ‖v‖ := by gcongr
    have h4 : min r1 r2 / (‖v‖ + 1) / 2 * ‖v‖ < min r1 r2 := by
      rw [div_div, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith [norm_nonneg v]
    linarith
  have hcrs : crs d (toV2 (w - z)) = ε * σ := by
    rw [hwz]
    simp only [hvdef, hσdef, haQ, haR, crs, toV2, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  rcases lt_or_gt_of_ne hσ with hneg | hpos
  · -- right side: tile j
    have hc2 : 0 < crs (neg2 d) (toV2 (w - z)) := by
      have : crs (neg2 d) (toV2 (w - z)) = -(ε * σ) := by
        rw [← hcrs]; simp only [neg2, crs]; ring
      rw [this]; nlinarith
    have hwj := h2 w (lt_of_lt_of_le hdist (min_le_right _ _)) hc2
    have hkj : k = j := by
      by_contra hkj
      exact Set.disjoint_left.1 (D.interiors_disjoint hkj) hwint hwj
    subst hkj
    exact step_open_not_vertex (D.tile k) hj (t := 1 - t) (by linarith) (by linarith) k0 (by rw [hz2]; exact hv)
  · have hc1 : 0 < crs d (toV2 (w - z)) := by rw [hcrs]; positivity
    have hwi := h1 w (lt_of_lt_of_le hdist (min_le_left _ _)) hc1
    have hki : k = i := by
      by_contra hki
      exact Set.disjoint_left.1 (D.interiors_disjoint hki) hwint hwi
    subst hki
    exact step_open_not_vertex (D.tile k) hi ht0 ht1 k0 hv

end Erdos634.Draft.LaczFormal.RG
