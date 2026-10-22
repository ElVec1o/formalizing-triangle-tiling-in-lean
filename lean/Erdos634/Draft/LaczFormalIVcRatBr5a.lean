-- Draft/LaczFormalIVcRatBr5a.lean -- Laczkovich DCG 48 (2012), Sect. 8.3 (Subcase IVc, rational branch): BRIDGE item (1), stage Br5a (tile-level plane lemmas).
--   Goal of items Br5a-d: the hypothesis `hint` of `BrHyp` (every c-edge of a tile has an open-segment point interior to the region) from "no tile edge on bd A has length c".
--   Br5a: `step_near_interior` (near the relative interior of a left step, the points on the LEFT of the line are interior to the tile),
--   `tri_edges_par_eq` (a tile has only one left step along a given direction), `overlap_eq` (two tiles with left steps along the same direction whose open
--   segments overlap are the same tile).  No polygon, no fans.
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 4, 8.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalRGWalk
import Erdos634.CellCoord
import Erdos634.CertCoord

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.CertCoord Erdos634.Subdivision Filter Topology

namespace Erdos634.Draft.LaczFormal.RG

variable {N : ℕ}

theorem fin3_cover5a : ∀ kk f g i : Fin 3, f ≠ kk → g ≠ kk → g ≠ f → i = kk ∨ i = f ∨ i = g := by decide

/-- Barycentric coordinates of a point written with weights on three DISTINCT labelled vertices. -/
theorem coord_lbl (T : Tri) {kk f g : Fin 3} (hfk : f ≠ kk) (hgk : g ≠ kk) (hgf : g ≠ f) (x : Plane) (a b c : ℝ)
    (hsum : a + b + c = 1) (hx : x = a • T.pts kk + b • T.pts f + c • T.pts g) :
    T.basis.coord kk x = a ∧ T.basis.coord f x = b ∧ T.basis.coord g x = c := by
  set w : Fin 3 → ℝ := fun i => if i = kk then a else if i = f then b else c with hw
  have e1 : w 0 + w 1 + w 2 = a + b + c := by
    revert hfk hgk hgf
    fin_cases kk <;> fin_cases f <;> fin_cases g <;> simp [hw] <;> ring
  have e2 : w 0 • T.pts 0 + w 1 • T.pts 1 + w 2 • T.pts 2 = a • T.pts kk + b • T.pts f + c • T.pts g := by
    revert hfk hgk hgf
    fin_cases kk <;> fin_cases f <;> fin_cases g <;> simp [hw] <;> abel
  have key : ∀ i, T.basis.coord i x = w i :=
    Tri.coord_eq_of_combo T x w (by rw [e1]; exact hsum) (by rw [e2]; exact hx)
  refine ⟨?_, ?_, ?_⟩
  · rw [key]; simp [hw]
  · rw [key]; simp [hw, hfk]
  · rw [key]; simp [hw, hgk, hgf]

theorem interior_lbl (T : Tri) {kk f g : Fin 3} (hfk : f ≠ kk) (hgk : g ≠ kk) (hgf : g ≠ f) (x : Plane) (a b c : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hsum : a + b + c = 1) (hx : x = a • T.pts kk + b • T.pts f + c • T.pts g) :
    x ∈ interior T.carrier := by
  have hint : interior T.carrier = {x | ∀ i, 0 < T.basis.coord i x} := by
    have : T.carrier = convexHull ℝ (Set.range (T.basis : Fin 3 → Plane)) := rfl
    rw [this]
    exact AffineBasis.interior_convexHull T.basis
  rw [hint]
  obtain ⟨h1, h2, h3⟩ := coord_lbl T hfk hgk hgf x a b c hsum hx
  intro i
  rcases fin3_cover5a kk f g i hfk hgk hgf with rfl | rfl | rfl
  · rw [h1]; exact ha
  · rw [h2]; exact hb
  · rw [h3]; exact hc

/-- Near the relative interior of a left step `U -> V` along `d`, the points on the left of the line (`+ eps * rot d`) are interior points of the tile. -/
theorem step_near_interior (T : Tri) {d : V2} {U V : Plane} (hS : TriStep T d U V) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), (U + t • (V - U)) + ε • mkPt (-d.2) d.1 ∈ interior T.carrier := by
  obtain ⟨kk, f, g, hk, hf, hfk, hgk, hgf, hpar, hleft⟩ := hS
  obtain ⟨c0, hc0, hcv⟩ := hpar.smul
  rw [toV2_sub] at hcv
  obtain ⟨hv0, hv1⟩ := Prod.mk.inj hcv
  have hV0 : V 0 = U 0 + c0 * d.1 := by simp only [PiLp.sub_apply] at hv0; linarith
  have hV1 : V 1 = U 1 + c0 * d.2 := by simp only [PiLp.sub_apply] at hv1; linarith
  unfold crs at hleft
  rw [toV2_sub] at hleft
  simp only at hleft
  set G := T.pts g with hG
  set q0 := G 0 - U 0 with hq0
  set q1 := G 1 - U 1 with hq1
  set Dd := d.1 * q1 - d.2 * q0 with hDd
  have hDd0 : 0 < Dd := hleft
  have hd0 : 0 < d.1 ^ 2 + d.2 ^ 2 := by
    by_contra h
    have h1 : d.1 = 0 := by nlinarith [sq_nonneg d.1, sq_nonneg d.2]
    have h2 : d.2 = 0 := by nlinarith [sq_nonneg d.1, sq_nonneg d.2]
    rw [hDd, h1, h2] at hDd0; simp at hDd0
  set κ := (d.1 ^ 2 + d.2 ^ 2) / Dd with hκ
  set η := -(d.1 * q0 + d.2 * q1) / (c0 * Dd) with hη
  have hκ0 : 0 < κ := by positivity
  have ha' : ∀ᶠ ε in 𝓝 (0 : ℝ), 0 < 1 - t - ε * (η + κ) :=
    ((continuous_const.sub (continuous_id.mul continuous_const)).tendsto (0 : ℝ)).eventually (lt_mem_nhds (by simp; linarith))
  have hb' : ∀ᶠ ε in 𝓝 (0 : ℝ), 0 < t + ε * η :=
    ((continuous_const.add (continuous_id.mul continuous_const)).tendsto (0 : ℝ)).eventually (lt_mem_nhds (by simp; linarith))
  filter_upwards [nhdsWithin_le_nhds ha', nhdsWithin_le_nhds hb', self_mem_nhdsWithin] with ε ha hb hε
  have hε0 : 0 < ε := hε
  refine interior_lbl T hfk hgk hgf _ (1 - t - ε * (η + κ)) (t + ε * η) (ε * κ) ha hb (by positivity) (by ring) ?_
  rw [hk, hf]
  ext j
  fin_cases j
  · simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, mkPt_zero, Fin.zero_eta]
    rw [hV0]
    have hq0' : G 0 = U 0 + q0 := by rw [hq0]; ring
    rw [hq0']
    rw [hη, hκ]
    field_simp
    ring
  · simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, mkPt_one, Fin.mk_one]
    rw [hV1]
    have hq1' : G 1 = U 1 + q1 := by rw [hq1]; ring
    rw [hq1']
    rw [hη, hκ]
    field_simp
    ring

/-- A tile has only one left step along a given direction. -/
theorem tri_edges_par_eq (T : Tri) {d : V2} {U V A B : Plane} (h1 : TriStep T d U V) (h2 : TriStep T d A B) : U = A ∧ V = B := by
  obtain ⟨kk, f, g, hk, hf, hfk, hgk, hgf, hpar, hleft⟩ := h1
  obtain ⟨kk', f', g', hk', hf', hfk', hgk', hgf', hpar', hleft'⟩ := h2
  have hdet := T.det_ne_zero
  have hp := hpar.trans hpar'.symm
  have hc := hp.1
  have hd := hp.2
  subst hk hf hk' hf'
  unfold crs at hc
  unfold dt at hd
  simp only [toV2_sub, PiLp.sub_apply] at hc hd
  unfold Tri.det at hdet
  simp only [PiLp.sub_apply] at hdet
  revert hfk hfk' hc hd
  fin_cases kk <;> fin_cases f <;> fin_cases kk' <;> fin_cases f' <;> intro hfk hfk' hc hd <;> simp at hfk hfk' <;>
  (try simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue] at hc hd) <;>
  first
  | exact ⟨rfl, rfl⟩
  | (exfalso; first
      | exact hdet (by linear_combination hc)
      | exact hdet (by linear_combination -hc)
      | nlinarith [sq_nonneg (T.pts 1 0 - T.pts 0 0), sq_nonneg (T.pts 1 1 - T.pts 0 1), sq_nonneg (T.pts 2 0 - T.pts 0 0),
          sq_nonneg (T.pts 2 1 - T.pts 0 1), sq_nonneg (T.pts 2 0 - T.pts 1 0), sq_nonneg (T.pts 2 1 - T.pts 1 1)])

/-- Two tiles with left steps along the same direction whose open segments overlap are the same tile.
Coordinates: `B - A = c1 d`, `V - U = c2 d`, `U - A = r d`, `0 <= r < c1` (so `U` is in `[A, B)` and the open segments `(A,B)`, `(U,V)` meet). -/
theorem overlap_eq (D : RegionDissection N) {i j : Fin N} {d : V2} {A B U V : Plane}
    (hi : TriStep (D.tile i) d U V) (hj : TriStep (D.tile j) d A B) {c1 c2 r : ℝ} (hc1 : 0 < c1) (hc2 : 0 < c2) (hr0 : 0 ≤ r) (hr1 : r < c1)
    (hAB : toV2 (B - A) = (c1 * d.1, c1 * d.2)) (hUV : toV2 (V - U) = (c2 * d.1, c2 * d.2)) (hAU : toV2 (U - A) = (r * d.1, r * d.2)) :
    i = j := by
  set t2 : ℝ := min (1 / 2) ((c1 - r) / (2 * c2)) with ht2
  have hcr : 0 < c1 - r := by linarith
  have ht2p : 0 < t2 := lt_min (by norm_num) (by positivity)
  have ht2l : t2 < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have ht2c : t2 * c2 ≤ (c1 - r) / 2 := by
    calc t2 * c2 ≤ ((c1 - r) / (2 * c2)) * c2 := by gcongr; exact min_le_right _ _
      _ = (c1 - r) / 2 := by field_simp
  set t1 : ℝ := (r + t2 * c2) / c1 with ht1
  have ht1c : t1 * c1 = r + t2 * c2 := by rw [ht1]; field_simp
  have ht1p : 0 < t1 := by
    have : 0 < t2 * c2 := by positivity
    rw [ht1]; positivity
  have ht1l : t1 < 1 := by
    rw [ht1, div_lt_one hc1]; linarith
  rw [toV2_sub] at hAB hUV hAU
  obtain ⟨hab0, hab1⟩ := Prod.mk.inj hAB
  obtain ⟨huv0, huv1⟩ := Prod.mk.inj hUV
  obtain ⟨hau0, hau1⟩ := Prod.mk.inj hAU
  simp only [PiLp.sub_apply] at hab0 hab1 huv0 huv1 hau0 hau1
  have hm : U + t2 • (V - U) = A + t1 • (B - A) := by
    ext k
    fin_cases k
    · simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, Fin.zero_eta]
      rw [huv0, hab0]
      have : U 0 = A 0 + r * d.1 := by linarith
      rw [this]
      linear_combination (-(d.1)) * ht1c
    · simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, Fin.mk_one]
      rw [huv1, hab1]
      have : U 1 = A 1 + r * d.2 := by linarith
      rw [this]
      linear_combination (-(d.2)) * ht1c
  have h1 := step_near_interior (D.tile i) hi ht2p ht2l
  have h2 := step_near_interior (D.tile j) hj ht1p ht1l
  rw [← hm] at h2
  obtain ⟨ε, he1, he2⟩ := (h1.and h2).exists
  by_contra hij
  exact Set.disjoint_left.1 (D.interiors_disjoint hij) he1 he2

end Erdos634.Draft.LaczFormal.RG
