-- Draft/LaczFormalBZ1.lean -- Beeson-Zhang (arXiv 2604.01314v1) Sect. 2.2 / Table 2 for polygon targets: the TOTAL CORNER ANGLE `A_X = sum_l cnt_l angle_l` at every tiling vertex `X`
-- of a congruent dissection of a convex polygon is `2 pi` (interior point), `pi` (interior point with a straight tile, or interior point of a side) or the polygon angle (a vertex of the polygon).
-- (Weight-free: no hypothesis on the tile.)  UNAUDITED.  Credit: Beeson-Zhang (Table 2), Laczkovich (DCG 48 (2012), Sect. 4-7).
import Erdos634.Draft.LaczFormalRG5GammaC
import Erdos634.Draft.LaczFormalRG3Comm

open scoped Classical
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ} [NeZero M]

/-- The total corner angle at `X`. -/
noncomputable def Asum (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) (X : Plane) : ℝ :=
  ∑ l, (cnt D idx X l : ℝ) * D.model.angleAt l

theorem Asum_pos (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) {X : Plane}
    (hvert : ∃ j k, (D.tile j).pts k = X) : 0 < Asum D idx X := by
  obtain ⟨j, k, hk⟩ := hvert
  have hc : 1 ≤ cnt D idx X (idx j k) := by
    unfold cnt
    exact Finset.card_pos.mpr ⟨(j, k), by simp [hk]⟩
  unfold Asum
  refine Finset.sum_pos' (fun l _ => mul_nonneg (Nat.cast_nonneg _) (model_angle_pos' D l).le) ⟨idx j k, Finset.mem_univ _, ?_⟩
  exact mul_pos (by exact_mod_cast hc) (model_angle_pos' D _)

/-- **The corner angle sum at a vertex of the polygon is the polygon angle.** -/
theorem corner_A (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v) (k : Fin M)
    (hvert : ∃ j k', (D.tile j).pts k' = P.v (k + 1)) : Asum D idx (P.v (k + 1)) = P.angle (k + 1) := by
  classical
  have hpi := Real.pi_pos
  set V := P.v (k + 1) with hVdef
  obtain ⟨pT, qT, F, hpd, hqd, hcr, h1, h2, h3, h4, h5⟩ := fan_vertex_poly D.toRegionDissection P hreg k hvert
  have hqT : qT ≠ 0 := by intro h; rw [h] at hcr; unfold crs at hcr; simp at hcr
  obtain ⟨i0, k0, hk0⟩ := hvert
  have hmem0 : V ∈ (D.tile i0).carrier := hk0 ▸ subset_convexHull ℝ _ ⟨k0, rfl⟩
  have hsumT := corner_tile_sum D.toRegionDissection F hcr h1 h2 h3 h4
  have hwlt := wd_lt_pi_of_crs_pos hcr
  have hwpos := wd_pos (Or.inl hcr : SecOK pT qT)
  have hnostr : ∀ x : AtV D.toRegionDissection V, ∃ k, (D.tile x.1).pts k = V := by
    intro x
    rcases F.hspec x with ⟨k, hk, -⟩ | ⟨hnv, m', -, -, hq, -⟩
    · exact ⟨k, hk⟩
    · exfalso
      have hw : wd (F.p x) (F.q x) = Real.pi := by rw [hq]; exact wd_straight (F.hok x).ne_p
      have hle : wd (F.p x) (F.q x) ≤ ∑ y : AtV D.toRegionDissection V, wd (F.p y) (F.q y) :=
        Finset.single_le_sum (f := fun y => wd (F.p y) (F.q y)) (fun y _ => (wd_pos (F.hok y)).le) (Finset.mem_univ x)
      linarith
  have hStrn : Strn D.toRegionDissection V = ∅ := by
    ext j
    simp only [Strn, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false, not_and, not_forall, not_not]
    intro hj
    exact hnostr ⟨j, hj⟩
  have hang := head_angle_sum_gen D idx hidxA F
  have hvirt : ∑ j : Bool, wd (F.pe j) (F.qe j) = Real.pi + (Real.pi - wd pT qT) := by
    rw [Fintype.sum_bool, h1, h2, h3, h4, wd_straight hqT, wd_neg_left hcr]; ring
  rw [hStrn, hvirt] at hang
  simp only [Finset.card_empty, Nat.cast_zero, mul_zero, add_zero] at hang
  have hAsum : Asum D idx V = wd pT qT := by unfold Asum; linarith
  have hθ : P.angle (k + 1) = wd pT qT := by
    obtain ⟨ρ, hρ, hiff⟩ := P.vertex_local_T P.three_le k
    have hN : 0 < N := Fin.pos i0
    have hT1 : (P.locTri P.three_le k).pts 1 = V := rfl
    have hiffD : ∀ y, dist y ((P.locTri P.three_le k).pts 1) < ρ → (y ∈ D.region ↔ y ∈ (P.locTri P.three_le k).carrier) := by
      intro y hy; rw [hreg]; exact hiff y hy
    have hs := sum_localAngle_tri D.toRegionDissection hN (P.locTri P.three_le k) hρ hiffD
    have hwdt := tiles_angle_sum D.toRegionDissection V F.p F.q F.hwd
    have hwdT : wd pT qT = (P.locTri P.three_le k).localAngle V := by
      rw [← hsumT, hwdt]; exact hs
    have hloc : (P.locTri P.three_le k).localAngle V = P.angle (k + 1) := by
      have := Tri.localAngle_vertex (P.locTri P.three_le k) 1
      rw [hT1] at this
      rw [this]
      unfold ConvPoly.angle cornerAngle
      have e1 : k + 1 - 1 = k := by simp
      have e2 : k + 1 + 1 = k + 2 := (ConvPoly.fin_facts P.three_le k).2.2.2.2.2
      rw [e1, e2, EuclideanGeometry.angle_comm (P.v k)]
      rfl
    rw [← hloc, hwdT]
  rw [hAsum, hθ]

/-- **The total corner angle at a tiling vertex** of a dissection of a convex polygon. -/
theorem vertex_A (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v) {X : Plane}
    (hvert : ∃ j k, (D.tile j).pts k = X) :
    (X ∈ interior D.region ∧ (Asum D idx X = 2 * Real.pi ∨ Asum D idx X = Real.pi)) ∨
    ((X ∉ interior D.region) ∧ (Asum D idx X = Real.pi ∨ ∃ k : Fin M, X = P.v (k + 1) ∧ Asum D idx X = P.angle (k + 1))) := by
  classical
  have hpi := Real.pi_pos
  have hA := Asum_pos D idx hvert
  by_cases hint : X ∈ interior D.region
  · left
    refine ⟨hint, ?_⟩
    obtain ⟨F⟩ := extFan_interior D.toRegionDissection X hvert hint
    have hang := head_angle_sum D idx hidxA F inferInstance
    have hAe : Asum D idx X + Real.pi * ((Strn D.toRegionDissection X).card : ℝ) = 2 * Real.pi := hang
    rcases Nat.lt_or_ge (Strn D.toRegionDissection X).card 2 with hlt | hge
    · interval_cases hc : (Strn D.toRegionDissection X).card
      · left; simpa using hAe
      · right; simp at hAe; linarith
    · exfalso
      have : (2 : ℝ) ≤ (Strn D.toRegionDissection X).card := by exact_mod_cast hge
      nlinarith
  · right
    refine ⟨hint, ?_⟩
    rcases point_cases D.toRegionDissection P hreg hvert with h | ⟨i, t, ht0, ht1, hXt⟩ | ⟨k, hXk⟩
    · exact absurd h hint
    · left
      subst hXt
      obtain ⟨pT, F, hpd, hpe, hqe, hTgt⟩ := fan_open_edge D.toRegionDissection P hreg i ht0 ht1 hvert
      have hpT : pT ≠ 0 := hpd.ne_left
      have hang := head_angle_sum_gen D idx hidxA F
      have hvirt : ∑ j : Unit, wd (F.pe j) (F.qe j) = Real.pi := by
        rw [Fintype.sum_unique]
        show wd (F.pe ()) (F.qe ()) = Real.pi
        rw [hpe, hqe, wd_ext hpT]
      rw [hvirt] at hang
      have hAe : Asum D idx ((1 - t) • P.v i + t • P.v (i + 1)) +
          Real.pi * ((Strn D.toRegionDissection ((1 - t) • P.v i + t • P.v (i + 1))).card : ℝ) = Real.pi := by
        unfold Asum; linarith
      rcases Nat.eq_zero_or_pos (Strn D.toRegionDissection ((1 - t) • P.v i + t • P.v (i + 1))).card with h0 | h0
      · rw [h0] at hAe; simpa using hAe
      · exfalso
        have : (1 : ℝ) ≤ (Strn D.toRegionDissection ((1 - t) • P.v i + t • P.v (i + 1))).card := by exact_mod_cast h0
        nlinarith
    · right
      refine ⟨k, hXk, ?_⟩
      subst hXk
      exact corner_A D P hreg idx hidxA k hvert

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.vertex_A
