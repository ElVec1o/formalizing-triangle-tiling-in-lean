-- Draft/LaczFormalRG4GkFan.lean -- Case IV (gamma = pi/3): for a dissection of a convex polygon, the corner angles at a tiling vertex that is not an interior point of the polygon add up to at most `pi`;
-- hence the head `X` of an edge of `Gamma_k` (two `beta` corners, regular counts) is an interior point whose fan is complete with six corner tiles, of type `(3,3,0)` or `(2,2,2)`.
-- UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), proof of Lemma 8.1), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalRG4Gk
import Erdos634.Draft.LaczFormalRG4Pos

open scoped Classical
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ} [NeZero M]

/-- At a tiling vertex that is not an interior point of the polygon the corner angles add up to at most `π`. -/
theorem boundary_sum_le (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v)
    {X : Plane} (hvert : ∃ j k, (D.tile j).pts k = X) (hX : X ∉ interior D.region) :
    ∑ l, (cnt D idx X l : ℝ) * D.model.angleAt l ≤ Real.pi := by
  classical
  have hpi := Real.pi_pos
  rcases point_cases D.toRegionDissection P hreg hvert with h | ⟨i, t, ht0, ht1, hXt⟩ | ⟨k, hXk⟩
  · exact absurd h hX
  · subst hXt
    obtain ⟨pT, F, hpd, hpe, hqe, hTgt⟩ := fan_open_edge D.toRegionDissection P hreg i ht0 ht1 hvert
    have hpT : pT ≠ 0 := hpd.ne_left
    have hang := head_angle_sum_gen D idx hidxA F
    have hvirt : ∑ j : Unit, wd (F.pe j) (F.qe j) = Real.pi := by
      rw [Fintype.sum_unique]
      show wd (F.pe ()) (F.qe ()) = Real.pi
      rw [hpe, hqe, wd_ext hpT]
    rw [hvirt] at hang
    have : 0 ≤ Real.pi * ((Strn D.toRegionDissection ((1 - t) • P.v i + t • P.v (i + 1))).card : ℝ) := by positivity
    linarith
  · subst hXk
    obtain ⟨pT, qT, F, hpd, hqd, hcr, h1, h2, h3, h4, h5⟩ := fan_vertex_poly D.toRegionDissection P hreg k hvert
    have hqT : qT ≠ 0 := by intro h; rw [h] at hcr; unfold crs at hcr; simp at hcr
    have hang := head_angle_sum_gen D idx hidxA F
    have hvirt : ∑ j : Bool, wd (F.pe j) (F.qe j) = Real.pi + (Real.pi - wd pT qT) := by
      rw [Fintype.sum_bool, h1, h2, h3, h4, wd_straight hqT, wd_neg_left hcr]; ring
    rw [hvirt] at hang
    have hwlt := wd_lt_pi_of_crs_pos hcr
    have : 0 ≤ Real.pi * ((Strn D.toRegionDissection (P.v (k + 1))).card : ℝ) := by positivity
    linarith

/-- **The head of a `Γ_k` edge has a complete fan of six corner tiles** with types `(3,3,0)` or `(2,2,2)` (`γ = π/3`, regular counts). -/
theorem gk_fan_full' (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3))
    (hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v) (hγ : D.model.angleAt 2 = Real.pi / 3)
    (hαβ : D.model.angleAt 0 + D.model.angleAt 1 = 2 * Real.pi / 3)
    {Z X : Plane} (hE : GkEdge D.toRegionDissection idx Z X) (hreg' : cnt D idx X 0 = cnt D idx X 1) :
    ∃ (F : ExtFan D.toRegionDissection X Empty),
      (∀ x : AtV D.toRegionDissection X, 0 < crs (F.p x) (F.q x)) ∧ Fintype.card (AtV D.toRegionDissection X) = 6 ∧
      ((cnt D idx X 0 = 3 ∧ cnt D idx X 1 = 3 ∧ cnt D idx X 2 = 0) ∨ (cnt D idx X 0 = 2 ∧ cnt D idx X 1 = 2 ∧ cnt D idx X 2 = 2)) := by
  classical
  have hpi := Real.pi_pos
  have hX : ∃ i k, (D.tile i).pts k = X := by
    obtain ⟨i, j, k1, k2, k1', k2', -, -, a2, -⟩ := hE
    exact ⟨i, k2, a2⟩
  have hb := gk_two_beta D idx hE
  have hA0 := model_angle_pos' D 0
  have hA1 := model_angle_pos' D 1
  have hA2 := model_angle_pos' D 2
  set c0 := cnt D idx X 0 with hc0
  set c1 := cnt D idx X 1 with hc1
  set c2 := cnt D idx X 2 with hc2
  have hc0' : (2 : ℝ) ≤ c0 := by exact_mod_cast (hreg' ▸ hb : 2 ≤ c0)
  have hc1' : (2 : ℝ) ≤ c1 := by exact_mod_cast hb
  have hc01 : (c0 : ℝ) = c1 := by exact_mod_cast hreg'
  have hSge : 4 * Real.pi / 3 ≤ ∑ l, (cnt D idx X l : ℝ) * D.model.angleAt l := by
    rw [Fin.sum_univ_three]
    have t0 : (c0 : ℝ) * D.model.angleAt 0 ≥ 2 * D.model.angleAt 0 := by nlinarith
    have t1 : (c1 : ℝ) * D.model.angleAt 1 ≥ 2 * D.model.angleAt 1 := by nlinarith
    have t2 : (c2 : ℝ) * D.model.angleAt 2 ≥ 0 := mul_nonneg (Nat.cast_nonneg c2) hA2.le
    linarith
  have hint : X ∈ interior D.region := by
    by_contra hnot
    have := boundary_sum_le D P hreg idx hidxA hX hnot
    linarith
  obtain ⟨F⟩ := extFan_interior D.toRegionDissection X hX hint
  have hang := head_angle_sum D idx hidxA F inferInstance
  have hStr : (Strn D.toRegionDissection X).card = 0 := by
    by_contra hne
    have : (1 : ℝ) ≤ (Strn D.toRegionDissection X).card := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hne
    nlinarith
  rw [hStr] at hang
  have hS2 : ∑ l, (cnt D idx X l : ℝ) * D.model.angleAt l = 2 * Real.pi := by simpa using hang
  rw [Fin.sum_univ_three] at hS2
  have hS2' : (c0 : ℝ) * D.model.angleAt 0 + (c1 : ℝ) * D.model.angleAt 1 + (c2 : ℝ) * D.model.angleAt 2 = 2 * Real.pi := hS2
  have hnat : 2 * c0 + c2 = 6 := by
    rw [hγ, ← hc01] at hS2'
    have e1 : (c0 : ℝ) * (D.model.angleAt 0 + D.model.angleAt 1) + c2 * (Real.pi / 3) = 2 * Real.pi := by
      linarith
    rw [hαβ] at e1
    have e2 : ((2 * c0 + c2 : ℕ) : ℝ) = 6 := by
      push_cast
      have : ((2 : ℝ) * c0 + c2) * (Real.pi / 3) = 6 * (Real.pi / 3) := by nlinarith [e1]
      exact mul_right_cancel₀ (by positivity) this
    exact_mod_cast e2
  have hcorner : ∀ x : AtV D.toRegionDissection X, 0 < crs (F.p x) (F.q x) := by
    intro x
    rcases F.hspec x with ⟨k, hk, -⟩ | ⟨hnv, -⟩
    · exact crs_pos_of_corner (F.hok x) (F.hspec x) ⟨k, hk⟩
    · exfalso
      have : x.1 ∈ Strn D.toRegionDissection X := by
        simp only [Strn, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨x.2, hnv⟩
      have := Finset.card_pos.mpr ⟨x.1, this⟩
      omega
  have hcard : Fintype.card (AtV D.toRegionDissection X) = 6 := by
    rw [card_atV, card_corn D idx X, hStr, Fin.sum_univ_three]
    omega
  refine ⟨F, hcorner, hcard, ?_⟩
  have hc0le : c0 ≤ 3 := by omega
  have : c0 = 2 ∨ c0 = 3 := by omega
  rcases this with h | h
  · right; refine ⟨h, by omega, by omega⟩
  · left; refine ⟨h, by omega, by omega⟩

end Erdos634.Draft.LaczFormal.RG
