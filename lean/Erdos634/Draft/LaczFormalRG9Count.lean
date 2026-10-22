-- Draft/LaczFormalRG9Count.lean -- Laczkovich DCG 48 (2012), Sect. 5 (Case I, `gamma > pi/2`, `gamma != 2pi/3`): the counting of corner types.  At a polygon vertex the angle is `p(alpha+beta) + r gamma < pi`, hence the vertex
-- is a single `gamma` (`p = 0, r = 1`) or has `r = 0, p >= 1`; at every other vertex of the tiling `r <= p` (the equation `(r-p) gamma = (v-p) pi` forces `gamma = 2 pi/3`).
-- The deficit `d = p - r` of a non-polygon vertex is `0` (a normal vertex) or satisfies `d (pi - gamma) >= pi`; `sum d = R - P` and `P (pi-gamma) + R gamma = (M-2) pi` give `(R-P)(pi-gamma) = (R-M+2) pi`.
-- UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 5), Beeson, Beeson-Zhang (Table 2 technique).
import Erdos634.Draft.LaczFormalRG9Geo
import Erdos634.Draft.LaczFormalBZ4b

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ} [NeZero M]

/-- Arithmetic of Case I: `γ ∈ (π/2, π)`, `γ ≠ 2π/3`; the equation `p(π-γ) + rγ = vπ` with `v ∈ {1,2}` forces `r ≤ p`. -/
theorem caseI_arith {γ : ℝ} (h1 : Real.pi / 2 < γ) (h2 : γ < Real.pi) (h3 : γ ≠ 2 * Real.pi / 3) (p r v : ℕ) (hv : v = 1 ∨ v = 2)
    (h : (p : ℝ) * (Real.pi - γ) + r * γ = v * Real.pi) : r ≤ p := by
  by_contra hr
  push Not at hr
  have hpi := Real.pi_pos
  have hA : ((r : ℝ) - p) * γ = ((v : ℝ) - p) * Real.pi := by linarith
  have hpos : (0 : ℝ) < (r : ℝ) - p := by
    have : (p : ℝ) < r := by exact_mod_cast hr
    linarith
  have hlt : (v : ℝ) - p < (r : ℝ) - p := by
    have : ((r : ℝ) - p) * γ < ((r : ℝ) - p) * Real.pi := mul_lt_mul_of_pos_left h2 hpos
    nlinarith
  have hgt : (r : ℝ) - p < 2 * ((v : ℝ) - p) := by
    have : ((r : ℝ) - p) * (Real.pi / 2) < ((r : ℝ) - p) * γ := mul_lt_mul_of_pos_left h1 hpos
    nlinarith
  have hlt' : (v : ℤ) < r := by
    have : (v : ℝ) < r := by linarith
    exact_mod_cast this
  have hgt' : (r : ℤ) - p < 2 * ((v : ℤ) - p) := by
    have : ((r : ℝ) - p) < 2 * ((v : ℝ) - p) := hgt
    exact_mod_cast this
  have hr3 : r = p + 3 ∧ v = p + 2 := by omega
  have hp0 : p = 0 := by omega
  subst hp0
  have hv2 : v = 2 := by omega
  have hr3' : r = 3 := by omega
  subst hv2 hr3'
  apply h3
  push_cast at h
  linarith

/-- The model angle `γ` of a congruent dissection is `< π`. -/
theorem model_gamma_lt_pi (D : CongruentRegionDissection N) : D.model.angleAt 2 < Real.pi := by
  have := Erdos634.Draft.LaczFormal.angleAt_sum D.model
  have h0 := model_angle_pos' D 0
  have h1 := model_angle_pos' D 1
  linarith

/-- The total corner angle at a vertex in terms of `p = #α = #β` and `r = #γ`. -/
theorem Asum_eq (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) (hregc : ∀ X, cnt D idx X 0 = cnt D idx X 1) (X : Plane) :
    Asum D idx X = (cnt D idx X 0 : ℝ) * (Real.pi - D.model.angleAt 2) + (cnt D idx X 2 : ℝ) * D.model.angleAt 2 := by
  unfold Asum
  rw [Fin.sum_univ_three]
  have hr : ((cnt D idx X 0 : ℕ) : ℝ) = (cnt D idx X 1 : ℕ) := by exact_mod_cast hregc X
  have hs := Erdos634.Draft.LaczFormal.angleAt_sum D.model
  rw [← hr]
  nlinarith [hs]

/-- **Polygon vertices** (Case I): the corner at `v_{k+1}` is a single `γ`, or consists of `p ≥ 1` pairs `α, β` and no `γ`; its angle is `γ` resp. `p(π-γ)`. -/
theorem caseI_polyvertex (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v) (hregc : ∀ X, cnt D idx X 0 = cnt D idx X 1)
    (h1 : Real.pi / 2 < D.model.angleAt 2) (k : Fin M) :
    (cnt D idx (P.v (k + 1)) 0 = 0 ∧ cnt D idx (P.v (k + 1)) 2 = 1 ∧ P.angle (k + 1) = D.model.angleAt 2) ∨
    (cnt D idx (P.v (k + 1)) 2 = 0 ∧ 1 ≤ cnt D idx (P.v (k + 1)) 0 ∧ P.angle (k + 1) = (cnt D idx (P.v (k + 1)) 0 : ℝ) * (Real.pi - D.model.angleAt 2)) := by
  have hpi := Real.pi_pos
  have hvert : ∃ j k', (D.tile j).pts k' = P.v (k + 1) := poly_vertex_is_tile_vertex D.toRegionDissection P hreg (k + 1)
  have hcA := corner_A D P hreg idx hidxA k hvert
  rw [Asum_eq D idx hregc] at hcA
  have hlt := (polyAngle_bounds P (k + 1)).2
  have hpos := Asum_pos D idx hvert
  rw [Asum_eq D idx hregc] at hpos
  have hγ := model_gamma_lt_pi D
  set p := cnt D idx (P.v (k + 1)) 0 with hp
  set r := cnt D idx (P.v (k + 1)) 2 with hr
  have hr1 : r ≤ 1 := by
    by_contra hge
    push Not at hge
    have : (2 : ℝ) ≤ r := by exact_mod_cast hge
    have : (p : ℝ) * (Real.pi - D.model.angleAt 2) ≥ 0 := mul_nonneg (Nat.cast_nonneg _) (by linarith)
    nlinarith
  interval_cases hrv : r
  · right
    refine ⟨rfl, ?_, ?_⟩
    · by_contra hp0
      have : p = 0 := by omega
      rw [this] at hpos
      simp at hpos
    · rw [← hcA]; simp
  · left
    have hp0 : p = 0 := by
      by_contra hne
      have h1p : (1 : ℝ) ≤ p := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hne
      have hw : 0 < Real.pi - D.model.angleAt 2 := by linarith
      have := mul_le_mul_of_nonneg_right h1p hw.le
      simp only [Nat.cast_one] at hcA
      linarith
    refine ⟨hp0, rfl, ?_⟩
    rw [← hcA, hp0]; simp

/-- **Non-polygon vertices** (Case I). `Asum = vπ`, `v ∈ {1,2}` (`v = 2` only at interior points); `r ≤ p`; the deficit `d = p - r` is `0` (then `p = v`) or satisfies `d (π - γ) ≥ π`. -/
theorem caseI_nonpoly (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v) (hregc : ∀ X, cnt D idx X 0 = cnt D idx X 1)
    (h1 : Real.pi / 2 < D.model.angleAt 2) (h3 : D.model.angleAt 2 ≠ 2 * Real.pi / 3) {X : Plane}
    (hvert : ∃ j k, (D.tile j).pts k = X) (hnc : ∀ k : Fin M, X ≠ P.v (k + 1)) :
    cnt D idx X 2 ≤ cnt D idx X 0 ∧
    (cnt D idx X 2 < cnt D idx X 0 → Real.pi ≤ ((cnt D idx X 0 - cnt D idx X 2 : ℕ) : ℝ) * (Real.pi - D.model.angleAt 2)) ∧
    (cnt D idx X 2 = cnt D idx X 0 → X ∉ interior D.region → cnt D idx X 0 = 1) := by
  have hpi := Real.pi_pos
  have hγ := model_gamma_lt_pi D
  have hv : ∃ v : ℕ, (v = 1 ∨ (v = 2 ∧ X ∈ interior D.region)) ∧ Asum D idx X = v * Real.pi := by
    rcases vertex_A D P hreg idx hidxA hvert with ⟨hi, h2 | h1'⟩ | ⟨hni, h1' | ⟨k, hXk, -⟩⟩
    · exact ⟨2, Or.inr ⟨rfl, hi⟩, by rw [h2]; push_cast; ring⟩
    · exact ⟨1, Or.inl rfl, by rw [h1']; push_cast; ring⟩
    · exact ⟨1, Or.inl rfl, by rw [h1']; push_cast; ring⟩
    · exact absurd hXk (hnc k)
  obtain ⟨v, hv12, hAv⟩ := hv
  rw [Asum_eq D idx hregc] at hAv
  have hle : cnt D idx X 2 ≤ cnt D idx X 0 := by
    apply caseI_arith h1 hγ h3 (cnt D idx X 0) (cnt D idx X 2) v (by rcases hv12 with h | ⟨h, -⟩ <;> simp [h]) hAv
  refine ⟨hle, ?_, ?_⟩
  · intro hlt
    -- `(p - r)(π - γ) = (v - r) π` and `p - r > 0`
    have hcast : ((cnt D idx X 0 - cnt D idx X 2 : ℕ) : ℝ) = (cnt D idx X 0 : ℝ) - cnt D idx X 2 := by
      rw [Nat.cast_sub hle]
    rw [hcast]
    have hA : ((cnt D idx X 0 : ℝ) - cnt D idx X 2) * (Real.pi - D.model.angleAt 2) = ((v : ℝ) - cnt D idx X 2) * Real.pi := by linarith
    have hd : (0 : ℝ) < (cnt D idx X 0 : ℝ) - cnt D idx X 2 := by
      have : (cnt D idx X 2 : ℝ) < cnt D idx X 0 := by exact_mod_cast hlt
      linarith
    have hw : 0 < Real.pi - D.model.angleAt 2 := by linarith
    have hvr : (0 : ℝ) < (v : ℝ) - cnt D idx X 2 := by
      have h0 : 0 < ((cnt D idx X 0 : ℝ) - cnt D idx X 2) * (Real.pi - D.model.angleAt 2) := mul_pos hd hw
      rw [hA] at h0
      exact (mul_pos_iff_of_pos_right hpi).mp h0
    have hvr' : 1 ≤ (v : ℤ) - cnt D idx X 2 := by
      have h5 : (cnt D idx X 2 : ℝ) < v := by linarith
      have h6 : (cnt D idx X 2 : ℤ) < v := by exact_mod_cast h5
      omega
    have : (1 : ℝ) ≤ (v : ℝ) - cnt D idx X 2 := by exact_mod_cast hvr'
    rw [hA]
    nlinarith
  · intro heq hni
    rw [heq] at hAv
    have hv1 : v = 1 := by
      rcases hv12 with h | ⟨h, hint⟩
      · exact h
      · exact absurd hint hni
    subst hv1
    push_cast at hAv
    have : (cnt D idx X 0 : ℝ) * Real.pi = 1 * Real.pi := by linarith
    have := mul_right_cancel₀ hpi.ne' this
    exact_mod_cast (by simpa using this : (cnt D idx X 0 : ℝ) = 1)

/-- The set of vertices of the polygon. -/
noncomputable def polyVerts (P : ConvPoly M) : Finset Plane := Finset.univ.image (fun k : Fin M => P.v (k + 1))

theorem mem_polyVerts {P : ConvPoly M} {X : Plane} : X ∈ polyVerts P ↔ ∃ k : Fin M, X = P.v (k + 1) := by
  unfold polyVerts
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨k, rfl⟩; exact ⟨k, rfl⟩
  · rintro ⟨k, rfl⟩; exact ⟨k, rfl⟩

theorem sum_polyVerts (P : ConvPoly M) {α : Type*} [AddCommMonoid α] (f : Plane → α) : ∑ X ∈ polyVerts P, f X = ∑ k : Fin M, f (P.v (k + 1)) := by
  unfold polyVerts
  rw [Finset.sum_image]
  intro a _ b _ hab
  have := polyV_injective P hab
  exact add_right_cancel this

/-- Number of corners `γ` at the polygon vertices (`R`) and number of pairs `α, β` (`P`). -/
noncomputable def cntR2 (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) (P : ConvPoly M) : ℕ := ∑ k : Fin M, cnt D idx (P.v (k + 1)) 2
noncomputable def cntP0 (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) (P : ConvPoly M) : ℕ := ∑ k : Fin M, cnt D idx (P.v (k + 1)) 0

/-- **The angle sum**: `(R - P)(π - γ) = (R - M + 2) π`. -/
theorem caseI_angle_sum (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v) (hregc : ∀ X, cnt D idx X 0 = cnt D idx X 1) :
    ((cntR2 D idx P : ℝ) - cntP0 D idx P) * (Real.pi - D.model.angleAt 2) = ((cntR2 D idx P : ℝ) - M + 2) * Real.pi := by
  have hsum := poly_angle_sum P
  have hshift : ∑ k : Fin M, P.angle (k + 1) = ∑ i : Fin M, P.angle i :=
    Fintype.sum_equiv (Equiv.addRight 1) _ _ (fun k => rfl)
  have hk : ∀ k : Fin M, P.angle (k + 1) = (cnt D idx (P.v (k + 1)) 0 : ℝ) * (Real.pi - D.model.angleAt 2) + (cnt D idx (P.v (k + 1)) 2 : ℝ) * D.model.angleAt 2 := by
    intro k
    have hvert : ∃ j k', (D.tile j).pts k' = P.v (k + 1) := poly_vertex_is_tile_vertex D.toRegionDissection P hreg (k + 1)
    rw [← corner_A D P hreg idx hidxA k hvert, Asum_eq D idx hregc]
  have h2 : ∑ k : Fin M, P.angle (k + 1) = (cntP0 D idx P : ℝ) * (Real.pi - D.model.angleAt 2) + (cntR2 D idx P : ℝ) * D.model.angleAt 2 := by
    rw [Finset.sum_congr rfl (fun k _ => hk k), Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul]
    unfold cntP0 cntR2
    push_cast
    rfl
  rw [hshift, hsum] at h2
  have hM : ((M - 2 : ℕ) : ℝ) = (M : ℝ) - 2 := by
    have := (ConvPoly.three_le P)
    rw [Nat.cast_sub (by omega)]; norm_num
  rw [hM] at h2
  linarith

/-- **Balance of the corner counts**: `∑ over non-polygon vertices of (p - r) = R - P` (as integers). -/
theorem caseI_deficit_sum (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) :
    ∑ X ∈ vtxSet D.toRegionDissection \ polyVerts P, ((cnt D idx X 0 : ℤ) - cnt D idx X 2) = (cntR2 D idx P : ℤ) - cntP0 D idx P := by
  have hsub : polyVerts P ⊆ vtxSet D.toRegionDissection := by
    intro X hX
    obtain ⟨k, rfl⟩ := mem_polyVerts.mp hX
    exact mem_vtxSet.mpr (poly_vertex_is_tile_vertex D.toRegionDissection P hreg (k + 1))
  have h0 : ∑ X ∈ vtxSet D.toRegionDissection, ((cnt D idx X 0 : ℤ) - cnt D idx X 2) = 0 := by
    rw [Finset.sum_sub_distrib]
    have a := sum_cnt_vtx D idx 0
    have b := sum_cnt_vtx D idx 2
    have a' : ∑ X ∈ vtxSet D.toRegionDissection, (cnt D idx X 0 : ℤ) = N := by exact_mod_cast a
    have b' : ∑ X ∈ vtxSet D.toRegionDissection, (cnt D idx X 2 : ℤ) = N := by exact_mod_cast b
    rw [a', b']; ring
  have h1 := Finset.sum_sdiff (f := fun X => ((cnt D idx X 0 : ℤ) - cnt D idx X 2)) hsub
  rw [h0, sum_polyVerts] at h1
  have h2 : ∑ k : Fin M, (((cnt D idx (P.v (k + 1)) 0 : ℤ) - cnt D idx (P.v (k + 1)) 2)) = (cntP0 D idx P : ℤ) - cntR2 D idx P := by
    rw [Finset.sum_sub_distrib]
    unfold cntP0 cntR2
    push_cast
    rfl
  rw [h2] at h1
  linarith

/-- The exceptional vertices: non-polygon vertices of the tiling with `r < p`. -/
noncomputable def excVerts (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) (P : ConvPoly M) : Finset Plane :=
  (vtxSet D.toRegionDissection \ polyVerts P).filter (fun X => cnt D idx X 2 < cnt D idx X 0)

/-- **Exceptional vertices of Case I**: `R ≥ M - 2`, `P ≤ R`, and the number of exceptional vertices is at most `R - M + 2`. -/
theorem caseI_exc_count (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v) (hregc : ∀ X, cnt D idx X 0 = cnt D idx X 1)
    (h1 : Real.pi / 2 < D.model.angleAt 2) (h3 : D.model.angleAt 2 ≠ 2 * Real.pi / 3) :
    cntP0 D idx P ≤ cntR2 D idx P ∧ (M : ℤ) - 2 ≤ cntR2 D idx P ∧ ((excVerts D idx P).card : ℤ) ≤ (cntR2 D idx P : ℤ) - M + 2 := by
  have hpi := Real.pi_pos
  have hγ := model_gamma_lt_pi D
  have hw : 0 < Real.pi - D.model.angleAt 2 := by linarith
  have hang := caseI_angle_sum D P hreg idx hidxA hregc
  have hdef := caseI_deficit_sum D P hreg idx
  have hnp : ∀ X ∈ vtxSet D.toRegionDissection \ polyVerts P,
      cnt D idx X 2 ≤ cnt D idx X 0 ∧ (cnt D idx X 2 < cnt D idx X 0 → Real.pi ≤ ((cnt D idx X 0 - cnt D idx X 2 : ℕ) : ℝ) * (Real.pi - D.model.angleAt 2)) := by
    intro X hX
    rw [Finset.mem_sdiff] at hX
    have hnc : ∀ k : Fin M, X ≠ P.v (k + 1) := fun k hk => hX.2 (mem_polyVerts.mpr ⟨k, hk⟩)
    obtain ⟨a, b, -⟩ := caseI_nonpoly D P hreg idx hidxA hregc h1 h3 (mem_vtxSet.mp hX.1) hnc
    exact ⟨a, b⟩
  -- the sum of the deficits equals the sum over the exceptional vertices
  have hsplit : ∑ X ∈ vtxSet D.toRegionDissection \ polyVerts P, ((cnt D idx X 0 : ℤ) - cnt D idx X 2) =
      ∑ X ∈ excVerts D idx P, ((cnt D idx X 0 : ℤ) - cnt D idx X 2) := by
    unfold excVerts
    rw [← Finset.sum_filter_add_sum_filter_not (vtxSet D.toRegionDissection \ polyVerts P) (fun X => cnt D idx X 2 < cnt D idx X 0)]
    have : ∑ X ∈ (vtxSet D.toRegionDissection \ polyVerts P).filter (fun X => ¬ cnt D idx X 2 < cnt D idx X 0), ((cnt D idx X 0 : ℤ) - cnt D idx X 2) = 0 := by
      apply Finset.sum_eq_zero
      intro X hX
      simp only [Finset.mem_filter] at hX
      have := (hnp X hX.1).1
      have : cnt D idx X 2 = cnt D idx X 0 := by omega
      omega
    rw [this, add_zero]
  have hexc_ge : ∀ X ∈ excVerts D idx P, Real.pi ≤ (((cnt D idx X 0 : ℤ) - cnt D idx X 2 : ℤ) : ℝ) * (Real.pi - D.model.angleAt 2) := by
    intro X hX
    unfold excVerts at hX
    simp only [Finset.mem_filter] at hX
    have := (hnp X hX.1).2 hX.2
    have hc : (((cnt D idx X 0 : ℤ) - cnt D idx X 2 : ℤ) : ℝ) = ((cnt D idx X 0 - cnt D idx X 2 : ℕ) : ℝ) := by
      have hle := (hnp X hX.1).1
      rw [Nat.cast_sub hle]; push_cast; ring
    rw [hc]; exact this
  -- (R - P) w = sum over exceptional vertices of d w
  have hsumR : (((cntR2 D idx P : ℤ) - cntP0 D idx P : ℤ) : ℝ) * (Real.pi - D.model.angleAt 2) =
      ∑ X ∈ excVerts D idx P, (((cnt D idx X 0 : ℤ) - cnt D idx X 2 : ℤ) : ℝ) * (Real.pi - D.model.angleAt 2) := by
    rw [← Finset.sum_mul, ← hdef, hsplit]
    push_cast
    rfl
  have hge : ((excVerts D idx P).card : ℝ) * Real.pi ≤ (((cntR2 D idx P : ℤ) - cntP0 D idx P : ℤ) : ℝ) * (Real.pi - D.model.angleAt 2) := by
    rw [hsumR]
    calc ((excVerts D idx P).card : ℝ) * Real.pi = ∑ _X ∈ excVerts D idx P, Real.pi := by simp
      _ ≤ _ := Finset.sum_le_sum hexc_ge
  have hRP : (((cntR2 D idx P : ℤ) - cntP0 D idx P : ℤ) : ℝ) = (cntR2 D idx P : ℝ) - cntP0 D idx P := by push_cast; ring
  rw [hRP, hang] at hge
  have hRP0 : 0 ≤ (cntR2 D idx P : ℤ) - cntP0 D idx P := by
    rw [← hdef]
    apply Finset.sum_nonneg
    intro X hX
    have := (hnp X hX).1
    omega
  have hRP0' : (0 : ℝ) ≤ (cntR2 D idx P : ℝ) - cntP0 D idx P := by
    have : (0 : ℝ) ≤ (((cntR2 D idx P : ℤ) - cntP0 D idx P : ℤ) : ℝ) := by exact_mod_cast hRP0
    rw [hRP] at this; exact this
  refine ⟨by omega, ?_, ?_⟩
  · have : 0 ≤ ((cntR2 D idx P : ℝ) - M + 2) * Real.pi := by rw [← hang]; exact mul_nonneg hRP0' hw.le
    have h4 : (0 : ℝ) ≤ (cntR2 D idx P : ℝ) - M + 2 := by
      by_contra hneg
      push Not at hneg
      nlinarith
    have : (M : ℤ) - 2 ≤ (cntR2 D idx P : ℤ) := by
      have h5 : (M : ℝ) - 2 ≤ cntR2 D idx P := by linarith
      exact_mod_cast h5
    exact this
  · have h4 : ((excVerts D idx P).card : ℝ) ≤ (cntR2 D idx P : ℝ) - M + 2 := by
      by_contra hneg
      push Not at hneg
      nlinarith
    have h5 : ((excVerts D idx P).card : ℝ) ≤ (((cntR2 D idx P : ℤ) - M + 2 : ℤ) : ℝ) := by push_cast; exact h4
    exact_mod_cast h5

end Erdos634.Draft.LaczFormal.RG
