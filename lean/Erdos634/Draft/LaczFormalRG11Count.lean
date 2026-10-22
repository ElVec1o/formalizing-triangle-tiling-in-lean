-- Draft/LaczFormalRG11Count.lean -- Laczkovich DCG 48 (2012), Sect. 6 (Case II, `gamma < pi/2`, `gamma != pi/3`): the counting of corner types, the mirror of `RG9Count` (roles of `p = #alpha = #beta` and `r = #gamma` exchanged).
-- At a polygon vertex the angle is `p(pi-gamma) + r gamma < pi`, hence the vertex is one pair `alpha,beta` (`p = 1, r = 0`) or `p = 0, r >= 1`; at every other vertex of the tiling `p <= r`
-- (the equation `(p-r)(pi-gamma) = (v-r) pi` with `v = 1,2` forces `gamma = pi/3`).  The deficit `d = r - p` of a non-polygon vertex is `0` or satisfies `d gamma >= pi`.
-- `sum d = P - R` and `(P - R) gamma = (P - M + 2) pi` give `#exceptional <= P - M + 2`.  NOTE, UNAUDITED.
-- Credit: Laczkovich (DCG 48 (2012), Sect. 6), Beeson, Beeson-Zhang (Table 2 technique).
import Erdos634.Draft.LaczFormalRG9Count

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ} [NeZero M]

/-- Arithmetic of Case II: `γ ∈ (0, π/2)`, `γ ≠ π/3`; the equation `p(π-γ) + rγ = vπ` with `v ∈ {1,2}` forces `p ≤ r`. -/
theorem caseII_arith {γ : ℝ} (h0 : 0 < γ) (h1 : γ < Real.pi / 2) (h3 : γ ≠ Real.pi / 3) (p r v : ℕ) (hv : v = 1 ∨ v = 2)
    (h : (p : ℝ) * (Real.pi - γ) + r * γ = v * Real.pi) : p ≤ r := by
  by_contra hr
  push Not at hr
  have hpi := Real.pi_pos
  have hA : ((p : ℝ) - r) * (Real.pi - γ) = ((v : ℝ) - r) * Real.pi := by linarith
  have hpos : (0 : ℝ) < (p : ℝ) - r := by
    have : (r : ℝ) < p := by exact_mod_cast hr
    linarith
  have hlt : (v : ℝ) < p := by
    have : ((p : ℝ) - r) * (Real.pi - γ) < ((p : ℝ) - r) * Real.pi := mul_lt_mul_of_pos_left (by linarith) hpos
    nlinarith
  have hgt : (p : ℝ) - r < 2 * ((v : ℝ) - r) := by
    have : ((p : ℝ) - r) * (Real.pi / 2) < ((p : ℝ) - r) * (Real.pi - γ) := mul_lt_mul_of_pos_left (by linarith) hpos
    nlinarith
  have hlt' : v < p := by exact_mod_cast hlt
  have hgt' : (p : ℤ) - r < 2 * ((v : ℤ) - r) := by
    have : ((p : ℝ) - r) < 2 * ((v : ℝ) - r) := hgt
    exact_mod_cast this
  have hr0 : r = 0 ∧ p = 3 ∧ v = 2 := by omega
  obtain ⟨rfl, rfl, rfl⟩ := hr0
  apply h3
  push_cast at h
  linarith

/-- **Polygon vertices** (Case II): the corner at `v_{k+1}` is one pair `α, β` (angle `π - γ`), or consists of `r ≥ 1` angles `γ` and no `α, β` (angle `rγ`). -/
theorem caseII_polyvertex (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v) (hregc : ∀ X, cnt D idx X 0 = cnt D idx X 1)
    (h1 : D.model.angleAt 2 < Real.pi / 2) (k : Fin M) :
    (cnt D idx (P.v (k + 1)) 0 = 1 ∧ cnt D idx (P.v (k + 1)) 2 = 0 ∧ P.angle (k + 1) = Real.pi - D.model.angleAt 2) ∨
    (cnt D idx (P.v (k + 1)) 0 = 0 ∧ 1 ≤ cnt D idx (P.v (k + 1)) 2 ∧ P.angle (k + 1) = (cnt D idx (P.v (k + 1)) 2 : ℝ) * D.model.angleAt 2) := by
  have hpi := Real.pi_pos
  have hvert : ∃ j k', (D.tile j).pts k' = P.v (k + 1) := poly_vertex_is_tile_vertex D.toRegionDissection P hreg (k + 1)
  have hcA := corner_A D P hreg idx hidxA k hvert
  rw [Asum_eq D idx hregc] at hcA
  have hlt := (polyAngle_bounds P (k + 1)).2
  have hpos := Asum_pos D idx hvert
  rw [Asum_eq D idx hregc] at hpos
  have hγ := model_gamma_lt_pi D
  have hγ0 := model_angle_pos' D 2
  set p := cnt D idx (P.v (k + 1)) 0 with hp
  set r := cnt D idx (P.v (k + 1)) 2 with hr
  have hp1 : p ≤ 1 := by
    by_contra hge
    push Not at hge
    have : (2 : ℝ) ≤ p := by exact_mod_cast hge
    have : (r : ℝ) * D.model.angleAt 2 ≥ 0 := mul_nonneg (Nat.cast_nonneg _) hγ0.le
    nlinarith
  interval_cases hpv : p
  · right
    refine ⟨rfl, ?_, ?_⟩
    · by_contra hr0
      have : r = 0 := by omega
      rw [this] at hpos
      simp at hpos
    · rw [← hcA]; simp
  · left
    have hr0 : r = 0 := by
      by_contra hne
      have h1r : (1 : ℝ) ≤ r := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hne
      have := mul_le_mul_of_nonneg_right h1r hγ0.le
      simp only [Nat.cast_one] at hcA
      linarith
    refine ⟨rfl, hr0, ?_⟩
    rw [← hcA, hr0]; simp

/-- **Non-polygon vertices** (Case II). `Asum = vπ`, `v ∈ {1,2}` (`v = 2` only at interior points); `p ≤ r`; the deficit `d = r - p` is `0` (then `p = v` on the boundary) or satisfies `d γ ≥ π`. -/
theorem caseII_nonpoly (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v) (hregc : ∀ X, cnt D idx X 0 = cnt D idx X 1)
    (h1 : D.model.angleAt 2 < Real.pi / 2) (h3 : D.model.angleAt 2 ≠ Real.pi / 3) {X : Plane}
    (hvert : ∃ j k, (D.tile j).pts k = X) (hnc : ∀ k : Fin M, X ≠ P.v (k + 1)) :
    cnt D idx X 0 ≤ cnt D idx X 2 ∧
    (cnt D idx X 0 < cnt D idx X 2 → Real.pi ≤ ((cnt D idx X 2 - cnt D idx X 0 : ℕ) : ℝ) * D.model.angleAt 2) ∧
    (cnt D idx X 2 = cnt D idx X 0 → X ∉ interior D.region → cnt D idx X 0 = 1) := by
  have hpi := Real.pi_pos
  have hγ := model_gamma_lt_pi D
  have hγ0 := model_angle_pos' D 2
  have hv : ∃ v : ℕ, (v = 1 ∨ (v = 2 ∧ X ∈ interior D.region)) ∧ Asum D idx X = v * Real.pi := by
    rcases vertex_A D P hreg idx hidxA hvert with ⟨hi, h2 | h1'⟩ | ⟨hni, h1' | ⟨k, hXk, -⟩⟩
    · exact ⟨2, Or.inr ⟨rfl, hi⟩, by rw [h2]; push_cast; ring⟩
    · exact ⟨1, Or.inl rfl, by rw [h1']; push_cast; ring⟩
    · exact ⟨1, Or.inl rfl, by rw [h1']; push_cast; ring⟩
    · exact absurd hXk (hnc k)
  obtain ⟨v, hv12, hAv⟩ := hv
  rw [Asum_eq D idx hregc] at hAv
  have hle : cnt D idx X 0 ≤ cnt D idx X 2 := by
    apply caseII_arith hγ0 h1 h3 (cnt D idx X 0) (cnt D idx X 2) v (by rcases hv12 with h | ⟨h, -⟩ <;> simp [h]) hAv
  refine ⟨hle, ?_, ?_⟩
  · intro hlt
    have hcast : ((cnt D idx X 2 - cnt D idx X 0 : ℕ) : ℝ) = (cnt D idx X 2 : ℝ) - cnt D idx X 0 := by
      rw [Nat.cast_sub hle]
    rw [hcast]
    have hA : ((cnt D idx X 2 : ℝ) - cnt D idx X 0) * D.model.angleAt 2 = ((v : ℝ) - cnt D idx X 0) * Real.pi := by linarith
    have hd : (0 : ℝ) < (cnt D idx X 2 : ℝ) - cnt D idx X 0 := by
      have : (cnt D idx X 0 : ℝ) < cnt D idx X 2 := by exact_mod_cast hlt
      linarith
    have hvr : (0 : ℝ) < (v : ℝ) - cnt D idx X 0 := by
      have h0 : 0 < ((cnt D idx X 2 : ℝ) - cnt D idx X 0) * D.model.angleAt 2 := mul_pos hd hγ0
      rw [hA] at h0
      exact (mul_pos_iff_of_pos_right hpi).mp h0
    have hvr' : 1 ≤ (v : ℤ) - cnt D idx X 0 := by
      have h5 : (cnt D idx X 0 : ℝ) < v := by linarith
      have h6 : (cnt D idx X 0 : ℤ) < v := by exact_mod_cast h5
      omega
    have : (1 : ℝ) ≤ (v : ℝ) - cnt D idx X 0 := by exact_mod_cast hvr'
    rw [hA]
    nlinarith
  · intro heq hni
    have hAv' := hAv
    rw [heq] at hAv'
    have hv1 : v = 1 := by
      rcases hv12 with h | ⟨h, hint⟩
      · exact h
      · exact absurd hint hni
    subst hv1
    push_cast at hAv'
    have : (cnt D idx X 0 : ℝ) * Real.pi = 1 * Real.pi := by linarith
    have := mul_right_cancel₀ hpi.ne' this
    exact_mod_cast (by simpa using this : (cnt D idx X 0 : ℝ) = 1)

/-- The exceptional vertices of Case II: non-polygon vertices of the tiling with `p < r`. -/
noncomputable def excVerts2 (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) (P : ConvPoly M) : Finset Plane :=
  (vtxSet D.toRegionDissection \ polyVerts P).filter (fun X => cnt D idx X 0 < cnt D idx X 2)

/-- **Exceptional vertices of Case II**: `P ≥ R`, `P ≥ M - 2`, and the number of exceptional vertices is at most `P - M + 2` (`P = cntP0`, `R = cntR2`). -/
theorem caseII_exc_count (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v) (hregc : ∀ X, cnt D idx X 0 = cnt D idx X 1)
    (h1 : D.model.angleAt 2 < Real.pi / 2) (h3 : D.model.angleAt 2 ≠ Real.pi / 3) :
    cntR2 D idx P ≤ cntP0 D idx P ∧ (M : ℤ) - 2 ≤ cntP0 D idx P ∧ ((excVerts2 D idx P).card : ℤ) ≤ (cntP0 D idx P : ℤ) - M + 2 ∧
    ((cntP0 D idx P : ℝ) - cntR2 D idx P) * D.model.angleAt 2 = ((cntP0 D idx P : ℝ) - M + 2) * Real.pi := by
  have hpi := Real.pi_pos
  have hγ := model_gamma_lt_pi D
  have hγ0 := model_angle_pos' D 2
  have hang0 := caseI_angle_sum D P hreg idx hidxA hregc
  have hang : ((cntP0 D idx P : ℝ) - cntR2 D idx P) * D.model.angleAt 2 = ((cntP0 D idx P : ℝ) - M + 2) * Real.pi := by linarith
  have hdef0 := caseI_deficit_sum D P hreg idx
  have hdef : ∑ X ∈ vtxSet D.toRegionDissection \ polyVerts P, ((cnt D idx X 2 : ℤ) - cnt D idx X 0) = (cntP0 D idx P : ℤ) - cntR2 D idx P := by
    have : ∑ X ∈ vtxSet D.toRegionDissection \ polyVerts P, ((cnt D idx X 2 : ℤ) - cnt D idx X 0) =
        -∑ X ∈ vtxSet D.toRegionDissection \ polyVerts P, ((cnt D idx X 0 : ℤ) - cnt D idx X 2) := by
      rw [← Finset.sum_neg_distrib]; apply Finset.sum_congr rfl; intro X _; ring
    rw [this, hdef0]; ring
  have hnp : ∀ X ∈ vtxSet D.toRegionDissection \ polyVerts P,
      cnt D idx X 0 ≤ cnt D idx X 2 ∧ (cnt D idx X 0 < cnt D idx X 2 → Real.pi ≤ ((cnt D idx X 2 - cnt D idx X 0 : ℕ) : ℝ) * D.model.angleAt 2) := by
    intro X hX
    rw [Finset.mem_sdiff] at hX
    have hnc : ∀ k : Fin M, X ≠ P.v (k + 1) := fun k hk => hX.2 (mem_polyVerts.mpr ⟨k, hk⟩)
    obtain ⟨a, b, -⟩ := caseII_nonpoly D P hreg idx hidxA hregc h1 h3 (mem_vtxSet.mp hX.1) hnc
    exact ⟨a, b⟩
  have hsplit : ∑ X ∈ vtxSet D.toRegionDissection \ polyVerts P, ((cnt D idx X 2 : ℤ) - cnt D idx X 0) =
      ∑ X ∈ excVerts2 D idx P, ((cnt D idx X 2 : ℤ) - cnt D idx X 0) := by
    unfold excVerts2
    rw [← Finset.sum_filter_add_sum_filter_not (vtxSet D.toRegionDissection \ polyVerts P) (fun X => cnt D idx X 0 < cnt D idx X 2)]
    have : ∑ X ∈ (vtxSet D.toRegionDissection \ polyVerts P).filter (fun X => ¬ cnt D idx X 0 < cnt D idx X 2), ((cnt D idx X 2 : ℤ) - cnt D idx X 0) = 0 := by
      apply Finset.sum_eq_zero
      intro X hX
      simp only [Finset.mem_filter] at hX
      have := (hnp X hX.1).1
      have : cnt D idx X 2 = cnt D idx X 0 := by omega
      omega
    rw [this, add_zero]
  have hexc_ge : ∀ X ∈ excVerts2 D idx P, Real.pi ≤ (((cnt D idx X 2 : ℤ) - cnt D idx X 0 : ℤ) : ℝ) * D.model.angleAt 2 := by
    intro X hX
    unfold excVerts2 at hX
    simp only [Finset.mem_filter] at hX
    have := (hnp X hX.1).2 hX.2
    have hc : (((cnt D idx X 2 : ℤ) - cnt D idx X 0 : ℤ) : ℝ) = ((cnt D idx X 2 - cnt D idx X 0 : ℕ) : ℝ) := by
      have hle := (hnp X hX.1).1
      rw [Nat.cast_sub hle]; push_cast; ring
    rw [hc]; exact this
  have hsumR : (((cntP0 D idx P : ℤ) - cntR2 D idx P : ℤ) : ℝ) * D.model.angleAt 2 =
      ∑ X ∈ excVerts2 D idx P, (((cnt D idx X 2 : ℤ) - cnt D idx X 0 : ℤ) : ℝ) * D.model.angleAt 2 := by
    rw [← Finset.sum_mul, ← hdef, hsplit]
    push_cast
    rfl
  have hge : ((excVerts2 D idx P).card : ℝ) * Real.pi ≤ (((cntP0 D idx P : ℤ) - cntR2 D idx P : ℤ) : ℝ) * D.model.angleAt 2 := by
    rw [hsumR]
    calc ((excVerts2 D idx P).card : ℝ) * Real.pi = ∑ _X ∈ excVerts2 D idx P, Real.pi := by simp
      _ ≤ _ := Finset.sum_le_sum hexc_ge
  have hRP : (((cntP0 D idx P : ℤ) - cntR2 D idx P : ℤ) : ℝ) = (cntP0 D idx P : ℝ) - cntR2 D idx P := by push_cast; ring
  rw [hRP, hang] at hge
  have hRP0 : 0 ≤ (cntP0 D idx P : ℤ) - cntR2 D idx P := by
    rw [← hdef]
    apply Finset.sum_nonneg
    intro X hX
    have := (hnp X hX).1
    omega
  have hRP0' : (0 : ℝ) ≤ (cntP0 D idx P : ℝ) - cntR2 D idx P := by
    have : (0 : ℝ) ≤ (((cntP0 D idx P : ℤ) - cntR2 D idx P : ℤ) : ℝ) := by exact_mod_cast hRP0
    rw [hRP] at this; exact this
  refine ⟨by omega, ?_, ?_, hang⟩
  · have : 0 ≤ ((cntP0 D idx P : ℝ) - M + 2) * Real.pi := by rw [← hang]; exact mul_nonneg hRP0' hγ0.le
    have h4 : (0 : ℝ) ≤ (cntP0 D idx P : ℝ) - M + 2 := by
      by_contra hneg
      push Not at hneg
      nlinarith
    have h5 : (M : ℝ) - 2 ≤ cntP0 D idx P := by linarith
    exact_mod_cast h5
  · have h4 : ((excVerts2 D idx P).card : ℝ) ≤ (cntP0 D idx P : ℝ) - M + 2 := by
      by_contra hneg
      push Not at hneg
      nlinarith
    have h5 : ((excVerts2 D idx P).card : ℝ) ≤ (((cntP0 D idx P : ℤ) - M + 2 : ℤ) : ℝ) := by push_cast; exact h4
    exact_mod_cast h5

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.caseII_exc_count
#print axioms Erdos634.Draft.LaczFormal.RG.caseII_polyvertex
