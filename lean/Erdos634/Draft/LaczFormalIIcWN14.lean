-- Draft/LaczFormalIIcWN14.lean -- Laczkovich (DCG 48 (2012)), Sect. 6.2, step (a): tile-level half-disc and sector lemmas (cross-product tests for interior points of a tile).
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.2), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalRG12GKite
import Erdos634.Draft.LaczFormalIVcRatBr5a

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement Erdos634.CertCoord Filter Topology

namespace Erdos634.Draft.LaczFormal.RG

variable {N : ℕ}

/-- Cross-product test for interior points of a labelled tile. -/
theorem interior_of_cross (T : Tri) {kk f g : Fin 3} (hfk : f ≠ kk) (hgk : g ≠ kk) (hgf : g ≠ f) (w : Plane)
    (hΔ : 0 < crs (toV2 (T.pts f - T.pts kk)) (toV2 (T.pts g - T.pts kk)))
    (ha : 0 < crs (toV2 (T.pts f - w)) (toV2 (T.pts g - w)))
    (hb : 0 < crs (toV2 (T.pts g - w)) (toV2 (T.pts kk - w)))
    (hc : 0 < crs (toV2 (T.pts kk - w)) (toV2 (T.pts f - w))) : w ∈ interior T.carrier := by
  set Δ := crs (toV2 (T.pts f - T.pts kk)) (toV2 (T.pts g - T.pts kk)) with hΔdef
  set ca := crs (toV2 (T.pts f - w)) (toV2 (T.pts g - w)) with hca
  set cb := crs (toV2 (T.pts g - w)) (toV2 (T.pts kk - w)) with hcb
  set cc := crs (toV2 (T.pts kk - w)) (toV2 (T.pts f - w)) with hcc
  have hsum : ca + cb + cc = Δ := by
    simp only [hca, hcb, hcc, hΔdef, crs, toV2, PiLp.sub_apply]; ring
  refine interior_lbl T hfk hgk hgf w (ca / Δ) (cb / Δ) (cc / Δ) (div_pos ha hΔ) (div_pos hb hΔ) (div_pos hc hΔ) ?_ ?_
  · field_simp; linarith
  · ext j
    fin_cases j
    · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, Fin.zero_eta]
      field_simp
      simp only [hca, hcb, hcc, hΔdef, crs, toV2, PiLp.sub_apply]
      ring
    · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, Fin.mk_one]
      field_simp
      simp only [hca, hcb, hcc, hΔdef, crs, toV2, PiLp.sub_apply]
      ring

/-- Points `P + s (Q - P) + s' (R - P)` with `s, s' > 0`, `s + s' < 1` are interior to the tile. -/
theorem sector_interior (T : Tri) {kk f g : Fin 3} (hfk : f ≠ kk) (hgk : g ≠ kk) (hgf : g ≠ f) {s s' : ℝ}
    (hs : 0 < s) (hs' : 0 < s') (hss : s + s' < 1) :
    T.pts kk + s • (T.pts f - T.pts kk) + s' • (T.pts g - T.pts kk) ∈ interior T.carrier := by
  refine interior_lbl T hfk hgk hgf _ (1 - s - s') s s' (by linarith) hs hs' (by ring) ?_
  ext j
  simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
  ring


theorem tri_cross_ne (T : Tri) {kk f g : Fin 3} (hfk : f ≠ kk) (hgk : g ≠ kk) (hgf : g ≠ f) :
    crs (toV2 (T.pts f - T.pts kk)) (toV2 (T.pts g - T.pts kk)) ≠ 0 := by
  intro h
  apply T.det_ne_zero
  unfold Tri.det
  simp only [crs, toV2, PiLp.sub_apply] at h ⊢
  revert hfk hgk hgf h
  fin_cases kk <;> fin_cases f <;> fin_cases g <;> intro hfk hgk hgf h <;> simp at hfk hgk hgf <;>
    (try simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue] at h ⊢) <;>
    first | linear_combination h | linear_combination -h

/-- **Half-disc lemma.**  Near a relative interior point `z` of a left step `U -> V` along `d`, every point on the left of the line is interior to the tile. -/
theorem halfdisc (T : Tri) {d : V2} {U V : Plane} (hS : TriStep T d U V) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    ∃ r > 0, ∀ w : Plane, dist w (U + t • (V - U)) < r → 0 < crs d (toV2 (w - (U + t • (V - U)))) →
      w ∈ interior T.carrier := by
  obtain ⟨kk, f, g, hk, hf, hfk, hgk, hgf, hpar, hleft⟩ := hS
  obtain ⟨c0, hc0, hcv⟩ := hpar.smul
  set G := T.pts g with hG
  set z : Plane := U + t • (V - U) with hz
  have hw0 : Continuous (fun w : Plane => w 0) := (EuclideanSpace.proj (0 : Fin 2) : Plane →L[ℝ] ℝ).continuous
  have hw1 : Continuous (fun w : Plane => w 1) := (EuclideanSpace.proj (1 : Fin 2) : Plane →L[ℝ] ℝ).continuous
  have hΔ : 0 < crs (toV2 (T.pts f - T.pts kk)) (toV2 (T.pts g - T.pts kk)) := by
    rw [hk, hf, toV2_sub V U] at *
    rw [hcv]
    unfold crs at hleft ⊢
    rw [toV2_sub] at hleft ⊢
    simp only at hleft ⊢
    nlinarith
  -- continuity of the two cross products
  have hca : Continuous (fun w : Plane => crs (toV2 (T.pts f - w)) (toV2 (T.pts g - w))) := by
    unfold crs toV2
    simp only [PiLp.sub_apply]
    exact ((continuous_const.sub hw0).mul (continuous_const.sub hw1)).sub ((continuous_const.sub hw1).mul (continuous_const.sub hw0))
  have hcb : Continuous (fun w : Plane => crs (toV2 (T.pts g - w)) (toV2 (T.pts kk - w))) := by
    unfold crs toV2
    simp only [PiLp.sub_apply]
    exact ((continuous_const.sub hw0).mul (continuous_const.sub hw1)).sub ((continuous_const.sub hw1).mul (continuous_const.sub hw0))
  have hopen : IsOpen {w : Plane | 0 < crs (toV2 (T.pts f - w)) (toV2 (T.pts g - w)) ∧
      0 < crs (toV2 (T.pts g - w)) (toV2 (T.pts kk - w))} :=
    (isOpen_lt continuous_const hca).inter (isOpen_lt continuous_const hcb)
  have hzmem : z ∈ {w : Plane | 0 < crs (toV2 (T.pts f - w)) (toV2 (T.pts g - w)) ∧
      0 < crs (toV2 (T.pts g - w)) (toV2 (T.pts kk - w))} := by
    refine ⟨?_, ?_⟩
    · have : crs (toV2 (T.pts f - z)) (toV2 (T.pts g - z)) = (1 - t) * crs (toV2 (T.pts f - T.pts kk)) (toV2 (T.pts g - T.pts kk)) := by
        rw [hz, hk, hf]
        simp only [crs, toV2, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
        ring
      show 0 < _
      rw [this]; exact mul_pos (by linarith) hΔ
    · have : crs (toV2 (T.pts g - z)) (toV2 (T.pts kk - z)) = t * crs (toV2 (T.pts f - T.pts kk)) (toV2 (T.pts g - T.pts kk)) := by
        rw [hz, hk, hf]
        simp only [crs, toV2, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
        ring
      show 0 < _
      rw [this]; exact mul_pos ht0 hΔ
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hopen z hzmem
  refine ⟨r, hr, fun w hw hleftw => ?_⟩
  obtain ⟨ha, hb⟩ := hball (Metric.mem_ball.2 hw)
  refine interior_of_cross T hfk hgk hgf w hΔ ha hb ?_
  have : crs (toV2 (T.pts kk - w)) (toV2 (T.pts f - w)) = c0 * crs d (toV2 (w - z)) := by
    rw [hk, hf] at *
    rw [toV2_sub V U] at hcv
    obtain ⟨hv0, hv1⟩ := Prod.mk.inj hcv
    simp only [PiLp.sub_apply] at hv0 hv1
    have hV0 : V 0 = U 0 + c0 * d.1 := by linarith
    have hV1 : V 1 = U 1 + c0 * d.2 := by linarith
    simp only [hz, crs, toV2, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    rw [hV0, hV1]
    ring
  rw [this]; exact mul_pos hc0 hleftw

end Erdos634.Draft.LaczFormal.RG
