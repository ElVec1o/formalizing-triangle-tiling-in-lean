-- Draft/LaczFormalRG4Bal.lean -- Case IV (gamma = pi/3), Laczkovich Lemma 8.1 (i), (ii) for a congruent dissection of a CONVEX POLYGON, arbitrary tile angles with `alpha + beta = 2 pi/3`,
-- `gamma = pi/3`, `a` not a nonnegative rational combination of `b, c`, regular corner counts:
--  (i) at every vertex the out-degree of `Gamma_a u Gamma_k` equals the in-degree;  (ii) no edge of `Gamma_a u Gamma_k` starts at a vertex that is not an interior point of the polygon.
-- UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Lemma 8.1), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalRG4GkHead

open scoped Classical
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ} [NeZero M]

/-- The half-plane arithmetic of Case IV: `n₀ α + n₁ β + n₂ γ = π` with `n₀ = n₁` forces `(0,0,3)` or `(1,1,1)`. -/
theorem CaseIV.harith {D : CongruentRegionDissection N} {idx : Fin N → Equiv.Perm (Fin 3)} (h : CaseIV D idx) : HalfPlaneArith D := by
  intro n0 n1 n2 hs hn
  subst hn
  have hp := Real.pi_pos
  have hγ := h.hγ
  have hαβ := h.hαβ
  rw [hγ] at hs
  have e1 : (n0 : ℝ) * (2 * Real.pi / 3) + n2 * (Real.pi / 3) = Real.pi := by nlinarith [hs, hαβ]
  have e2 : ((2 * n0 + n2 : ℕ) : ℝ) = 3 := by
    push_cast
    have : ((2 : ℝ) * n0 + n2) * (Real.pi / 3) = 3 * (Real.pi / 3) := by nlinarith [e1]
    exact mul_right_cancel₀ (by positivity) this
  have e3 : 2 * n0 + n2 = 3 := by exact_mod_cast e2
  omega

theorem cnt_zero_of_not_vertex' (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) {P : Plane}
    (hP : ¬ ∃ i k, (D.tile i).pts k = P) (l : Fin 3) : cnt D idx P l = 0 := by
  unfold cnt
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro ⟨i, k⟩ _ ⟨h, -⟩
  exact hP ⟨i, k, h⟩

/-- At every tiling vertex the corner angles add up to at most `2π`. -/
theorem corner_sum_le_two_pi (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (idx : Fin N → Equiv.Perm (Fin 3))
    (hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v) (X : Plane) :
    ∑ l, (cnt D idx X l : ℝ) * D.model.angleAt l ≤ 2 * Real.pi := by
  classical
  by_cases hX : ∃ i k, (D.tile i).pts k = X
  · obtain ⟨κ, _, ⟨F⟩⟩ := HasFansC.fans (D := D.toRegionDissection) X hX
    have h := head_angle_sum_gen D idx hidxA F
    have h1 : 0 ≤ ∑ j, wd (F.pe j) (F.qe j) := Finset.sum_nonneg (fun j _ => (wd_pos (F.hokE j)).le)
    have h2 : 0 ≤ Real.pi * ((Strn D.toRegionDissection X).card : ℝ) := by positivity
    linarith
  · have : ∀ l, cnt D idx X l = 0 := fun l => cnt_zero_of_not_vertex' D idx hX l
    simp [this]
    positivity


/-- At most three `β` corners at any point (regular counts, `α + β = 2π/3`). -/
theorem beta_le_three' (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (idx : Fin N → Equiv.Perm (Fin 3))
    (h : CaseIV D idx) (X : Plane) : cnt D idx X 1 ≤ 3 := by
  have hs := corner_sum_le_two_pi D idx h.hidxA X
  rw [Fin.sum_univ_three] at hs
  have hA2 := model_angle_pos' D 2
  have hr : ((cnt D idx X 0 : ℕ) : ℝ) = (cnt D idx X 1 : ℕ) := by exact_mod_cast h.hregc X
  rw [hr] at hs
  have hnn : (0 : ℝ) ≤ (cnt D idx X 2 : ℕ) * D.model.angleAt 2 := mul_nonneg (Nat.cast_nonneg _) hA2.le
  have h1 : (cnt D idx X 1 : ℝ) * (2 * Real.pi / 3) ≤ 2 * Real.pi := by
    have : (cnt D idx X 1 : ℝ) * (D.model.angleAt 0 + D.model.angleAt 1) ≤ 2 * Real.pi := by nlinarith
    rwa [h.hαβ] at this
  have hp := Real.pi_pos
  have h2 : (cnt D idx X 1 : ℝ) ≤ 3 := by nlinarith
  exact_mod_cast h2

/-- The head of a `Γ_k` edge is an interior point of the polygon. -/
theorem gk_head_interior' (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (h : CaseIV D idx) {Z X : Plane} (hE : GkEdge D.toRegionDissection idx Z X) :
    X ∈ interior D.region := by
  classical
  have hpi := Real.pi_pos
  have hX : ∃ i k, (D.tile i).pts k = X := by
    obtain ⟨i, j, k1, k2, k1', k2', -, -, a2, -⟩ := hE
    exact ⟨i, k2, a2⟩
  have hb := gk_two_beta D idx hE
  have hA0 := model_angle_pos' D 0
  have hA1 := model_angle_pos' D 1
  have hA2 := model_angle_pos' D 2
  have hreg' := h.hregc X
  have hc0' : (2 : ℝ) ≤ cnt D idx X 0 := by exact_mod_cast (hreg' ▸ hb : 2 ≤ cnt D idx X 0)
  have hc1' : (2 : ℝ) ≤ cnt D idx X 1 := by exact_mod_cast hb
  have hSge : 4 * Real.pi / 3 ≤ ∑ l, (cnt D idx X l : ℝ) * D.model.angleAt l := by
    rw [Fin.sum_univ_three]
    have t0 : (cnt D idx X 0 : ℝ) * D.model.angleAt 0 ≥ 2 * D.model.angleAt 0 := by nlinarith
    have t1 : (cnt D idx X 1 : ℝ) * D.model.angleAt 1 ≥ 2 * D.model.angleAt 1 := by nlinarith
    have t2 : (cnt D idx X 2 : ℝ) * D.model.angleAt 2 ≥ 0 := mul_nonneg (Nat.cast_nonneg _) hA2.le
    linarith [h.hαβ]
  by_contra hnot
  have := boundary_sum_le D P hreg idx h.hidxA hX hnot
  linarith

/-- The edge set of `Γ_a ∪ Γ_k` on the finite vertex set. -/
noncomputable def GEset (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) :
    Finset (↥(vtxSet D.toRegionDissection) × ↥(vtxSet D.toRegionDissection)) :=
  Finset.univ.filter (fun e => GE D idx e.1.1 e.2.1)

theorem GE_endpoints' (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) {X H : Plane} (h : GE D idx X H) :
    (∃ i k, (D.tile i).pts k = X) ∧ (∃ i k, (D.tile i).pts k = H) := by
  rcases h with h | ⟨i, j, k1, k2, k1', k2', -, a1, a2, -⟩
  · exact ga_edge_endpoints _ _ h
  · exact ⟨⟨i, k1, a1⟩, ⟨i, k2, a2⟩⟩

/-- **Lemma 8.1 (i)** (polygon, any tile with `γ = π/3`): at every vertex the out-degree of `Γ_a ∪ Γ_k` equals its in-degree. -/
theorem lemma81_i' (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (h : CaseIV D idx) :
    ∀ v : ↥(vtxSet D.toRegionDissection), ((GEset D idx).filter fun e => e.1 = v).card = ((GEset D idx).filter fun e => e.2 = v).card := by
  classical
  have harith := h.harith
  apply digraph_balance
  · intro v
    rw [Finset.card_le_one]
    intro a ha b hb
    simp only [GEset, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    have hb1 : GE D idx b.1.1 a.2.1 := by rw [show a.2 = b.2 from ha.2.trans hb.2.symm]; exact hb.1
    have := GE_indegree D idx h.hidx h.hidxA h.hnc harith h.hregc (beta_le_three' D idx h) ha.1 hb1
    exact Prod.ext (Subtype.ext this) (ha.2.trans hb.2.symm)
  · intro v hv
    obtain ⟨e, he⟩ := Finset.card_pos.mp hv
    simp only [GEset, Finset.mem_filter, Finset.mem_univ, true_and] at he
    obtain ⟨hE, hev⟩ := he
    have hvv : v.1 = e.2.1 := by rw [hev]
    have hout : (∃ H', GaEdge D.toRegionDissection (slen D 0) v.1 H') ∨ ∃ Z', GkEdge D.toRegionDissection idx v.1 Z' := by
      rcases hE with hE | hE
      · rw [hvv]
        exact ga_head_out D idx h.hidx h.hidxA h.hnc h.hab h.hac harith hE (h.hregc _)
      · rw [hvv]
        exact gk_head_out' D P hreg idx h.hidx h.hidxA h.hnc h.hab h.hac h.hγ h.hαβ hE (h.hregc _)
    apply Finset.card_pos.mpr
    rcases hout with ⟨H', hH'⟩ | ⟨Z', hZ'⟩
    · have hv' : H' ∈ vtxSet D.toRegionDissection := mem_vtxSet.mpr (ga_edge_endpoints _ _ hH').2
      exact ⟨(v, ⟨H', hv'⟩), by simp [GEset, GE, hH']⟩
    · have hv' : Z' ∈ vtxSet D.toRegionDissection := mem_vtxSet.mpr (GE_endpoints' D idx (Or.inr hZ')).2
      exact ⟨(v, ⟨Z', hv'⟩), by simp [GEset, GE, hZ']⟩

/-- **Lemma 8.1 (ii)**: no edge of `Γ_a ∪ Γ_k` starts at a vertex that is not an interior point of the polygon. -/
theorem lemma81_ii' (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (h : CaseIV D idx) {X H : Plane} (hX : X ∉ interior D.region) : ¬ GE D idx X H := by
  classical
  intro hGE
  have hXv : X ∈ vtxSet D.toRegionDissection := mem_vtxSet.mpr (GE_endpoints' D idx hGE).1
  have hHv : H ∈ vtxSet D.toRegionDissection := mem_vtxSet.mpr (GE_endpoints' D idx hGE).2
  have hbal := lemma81_i' D P hreg idx h ⟨X, hXv⟩
  have hout : 0 < ((GEset D idx).filter fun e => e.1 = (⟨X, hXv⟩ : ↥(vtxSet D.toRegionDissection))).card :=
    Finset.card_pos.mpr ⟨(⟨X, hXv⟩, ⟨H, hHv⟩), by simp [GEset, hGE]⟩
  rw [hbal] at hout
  obtain ⟨e, he⟩ := Finset.card_pos.mp hout
  simp only [GEset, Finset.mem_filter, Finset.mem_univ, true_and] at he
  obtain ⟨hE, hev⟩ := he
  have hvv : e.2.1 = X := by rw [hev]
  apply hX
  rw [← hvv]
  rcases hE with hE | hE
  · exact ga_head_interior D idx h.hidx h.hnc hE
  · exact gk_head_interior' D P hreg idx h hE

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.lemma81_i'
#print axioms Erdos634.Draft.LaczFormal.RG.lemma81_ii'
