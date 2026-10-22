import Erdos634.Draft.BeesonIso5e
import Erdos634.Draft.BeesonIso4e

/-!
# Beeson, "Tilings of an isosceles triangle" (arXiv 1206.1974 v7), Lemma 11.10 for the isosceles triangle: at least FOUR tiles are supported by the base

NOTE, UNAUDITED.  Credit: Michael Beeson (arXiv 1206.1974 v7, Lemma 11.10, 11.5, Thm 10.7; arXiv 1206.2229), Laczkovich (DCG 48 (2012), Sect. 4), Beeson-Zhang, Herdt, Zhang.
Formalization debt, not progress on the /goal outcomes.

`beeson_l11_10`: isosceles `ABC` (base angles `alpha` at corners 0, 1), `N`-tiled (`CongruentDissection`) by the tile `(alpha, beta, 2 alpha)` (`TwoAlphaData`), H1.  In the counterclockwise polygon form `P` of the target,
every walk of tiles along the side `j` joining the corners `0` and `1` (the base `AC`) has at least four steps.
PRINTED GAP (recorded in `BeesonIso4e`): the print dismisses the leg case `X = a + c` by a statement about `AC`; here it is excluded on BOTH legs at `B` (`four_base`).
Witness: `wit_1125_hyps` (BeesonIso4e): the 1125-tiling satisfies every hypothesis.
-/

open scoped Classical
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N : ℕ}

theorem param_distinct {a b c t : ℝ} (ht : 0 < t) {kt mt : ℕ} (hcop : Nat.Coprime kt mt) (hlt : kt < mt) (hm2 : mt < 2 * kt)
    (ha : a = t * (kt : ℝ) ^ 2) (hb : b = t * ((mt : ℝ) ^ 2 - (kt : ℝ) ^ 2)) (hc : c = t * ((kt : ℝ) * mt)) :
    a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  have hk2 : 2 ≤ kt := by omega
  have hcop2 : Nat.Coprime kt (mt ^ 2) := Nat.Coprime.pow_right 2 hcop
  have hkd : kt ∣ mt ^ 2 → False := by
    intro h; have := Nat.Coprime.eq_one_of_dvd hcop2 h; omega
  refine ⟨?_, ?_, ?_⟩
  · intro h
    rw [ha, hb] at h
    have h2 : (kt : ℝ) ^ 2 = (mt : ℝ) ^ 2 - (kt : ℝ) ^ 2 := mul_left_cancel₀ ht.ne' h
    have h3 : mt ^ 2 = kt * (2 * kt) := by
      have : ((mt ^ 2 : ℕ) : ℝ) = ((kt * (2 * kt) : ℕ) : ℝ) := by push_cast; nlinarith [h2]
      exact_mod_cast this
    exact hkd ⟨2 * kt, h3⟩
  · intro h
    rw [ha, hc] at h
    have h2 : (kt : ℝ) ^ 2 = (kt : ℝ) * mt := mul_left_cancel₀ ht.ne' h
    have h3 : (kt : ℝ) = mt := by
      have hk : (0 : ℝ) < kt := by exact_mod_cast (by omega : 0 < kt)
      nlinarith
    have : kt = mt := by exact_mod_cast h3
    omega
  · intro h
    rw [hb, hc] at h
    have h2 : (mt : ℝ) ^ 2 - (kt : ℝ) ^ 2 = (kt : ℝ) * mt := mul_left_cancel₀ ht.ne' h
    have h3 : mt ^ 2 = kt * (kt + mt) := by
      have : ((mt ^ 2 : ℕ) : ℝ) = ((kt * (kt + mt) : ℕ) : ℝ) := by push_cast; nlinarith [h2]
      exact_mod_cast this
    exact hkd ⟨kt + mt, h3⟩

theorem beeson_l11_10 (D : CongruentDissection N) {α a b c : ℝ} (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (h : D.model.TwoAlphaData α a b c) (hA : D.target.angleAt 0 = α) (hB : D.target.angleAt 1 = α) :
    ∃ (P : ConvPoly 3) (j : Fin 3), P.carrier = D.target.carrier ∧
      (P.v j = D.target.pts 0 ∧ P.v (j + 1) = D.target.pts 1 ∨ P.v j = D.target.pts 1 ∧ P.v (j + 1) = D.target.pts 0) ∧
      ∀ L : List (Fin N × Plane × Plane), WalkT D.toRegion.toRegionDissection (toV2 (P.e j)) (P.v j) (P.v (j + 1)) L → 4 ≤ L.length := by
  have hrel0 := (Erdos634.Draft.BeesonIsoL11Geo.l11_1_4 D hα h hA hB).1
  obtain ⟨κ, -, -, -, -, hc2, -, hY2, hX1e⟩ := Row4.sides D h hA hB
  have h' := h
  obtain ⟨σ, h0, o0, h1, o1, h2, o2⟩ := h
  set C := relabel D.toRegion σ with hC
  have hAC : C.model.angleAt 0 = α := (relabel_angleAt D.toRegion σ 0).trans h0
  have hβ : C.model.angleAt 1 = Real.pi - 3 * C.model.angleAt 0 := by
    rw [hAC]; exact (relabel_angleAt D.toRegion σ 1).trans h1
  have hγ : C.model.angleAt 2 = 2 * C.model.angleAt 0 := by
    rw [hAC]; exact (relabel_angleAt D.toRegion σ 2).trans h2
  have hirr : ¬ ∃ r : ℚ, C.model.angleAt 0 = (r : ℝ) * Real.pi := by rw [hAC]; exact hα
  obtain ⟨P, hPc, τ, hPa, hPv⟩ := exists_convpoly_of_tri' D.target
  have hreg : C.region = P.carrier := hPc.symm
  haveI : HasFansC C.toRegionDissection := hasFansC_poly _ P hreg
  obtain ⟨idx, hidx, hidxA⟩ := exists_idx_both C
  have ea : slen C 0 = a := (relabel_slen D.toRegion σ 0).trans o0
  have eb : slen C 1 = b := (relabel_slen D.toRegion σ 1).trans o1
  have ec : slen C 2 = c := (relabel_slen D.toRegion σ 2).trans o2
  have hrel : slen C 2 ^ 2 = slen C 0 ^ 2 + slen C 0 * slen C 1 := by rw [ea, eb, ec]; exact hrel0
  have htri : slen C 1 < slen C 0 + slen C 2 := by
    have := Tri.oppLen_lt_sum C.model 1
    have e0 : C.model.oppLen 0 = slen C 0 := rfl
    have e1 : C.model.oppLen 1 = slen C 1 := rfl
    have e2 : C.model.oppLen 2 = slen C 2 := rfl
    simp only [show (1 : Fin 3) + 1 = 2 from rfl, show (1 : Fin 3) + 2 = 0 from rfl] at this
    rw [e0, e1, e2] at this
    linarith
  have hsum := Erdos634.Draft.LaczFormal.angleAt_sum D.target
  have t2 : D.target.angleAt 2 = Real.pi - 2 * α := by linarith
  have hang : ∀ j : Fin 3, D.target.angleAt j = α ∨ D.target.angleAt j = Real.pi - 2 * α := by
    intro j; fin_cases j
    · exact Or.inl hA
    · exact Or.inl hB
    · exact Or.inr t2
  obtain ⟨k0, hk0⟩ := τ.surjective 2
  obtain ⟨kA, hkA⟩ := τ.surjective 0
  obtain ⟨r, s, hr, hs⟩ := beeson_thm107_proved C P hreg hβ hγ hirr
    (fun k => by rw [hPa, hAC]; exact hang _) (k0 - 1) (by simp only [sub_add_cancel]; rw [hPa, hk0, hAC]; exact t2)
    (kA - 1) (by simp only [sub_add_cancel]; rw [hPa, hkA, hAC]; exact hA)
  have ha0 : 0 < a := ea ▸ slen_pos C 0
  have hb0 : 0 < b := eb ▸ slen_pos C 1
  have hc0 : 0 < c := ec ▸ slen_pos C 2
  have hrat1 : a = (r : ℝ) * b := by rw [← ea, ← eb]; exact hr
  have hrat2 : c = (s : ℝ) * a := by rw [← ea, ← ec]; exact hs
  have htri' : b < a + c := by rw [← ea, ← eb, ← ec]; exact htri
  obtain ⟨t, ht, kt, mt, hcop, hlt, hm2, pa, pb, pc⟩ := Erdos634.Draft.BeesonIso3a.tile_param ha0 hb0 hc0 hrel0 htri' hrat1 hrat2
  have ea' : slen C 0 = t * (kt : ℝ) ^ 2 := by rw [ea]; exact pa
  have eb' : slen C 1 = t * ((mt : ℝ) ^ 2 - (kt : ℝ) ^ 2) := by rw [eb]; exact pb
  have ec' : slen C 2 = t * ((kt : ℝ) * mt) := by rw [ec]; exact pc
  obtain ⟨hab, hac, hbc⟩ := param_distinct ht hcop hlt hm2 ea' eb' ec'
  have hPang : ∀ k : Fin 3, P.angle (k + 1) = C.model.angleAt 0 ∨ P.angle (k + 1) = Real.pi - 2 * C.model.angleAt 0 :=
    fun k => by rw [hPa, hAC]; exact hang _
  -- distances in the triangle
  have dBase : dist (D.target.pts 0) (D.target.pts 1) = D.target.oppLen 2 := rfl
  have dLeg1 : dist (D.target.pts 1) (D.target.pts 2) = D.target.oppLen 0 := rfl
  have dLeg2 : dist (D.target.pts 2) (D.target.pts 0) = D.target.oppLen 1 := rfl
  have hca : slen C 2 * D.target.oppLen 0 = slen C 0 * D.target.oppLen 2 := by
    rw [ea, ec, hY2, hc2]; ring
  -- the position of the base
  have hPu : P.v (τ.symm 0) = D.target.pts 0 := by rw [hPv]; simp
  have hPw : P.v (τ.symm 1) = D.target.pts 1 := by rw [hPv]; simp
  have hPb : P.v (τ.symm 2) = D.target.pts 2 := by rw [hPv]; simp
  have hAu : P.angle (τ.symm 0) = α := by rw [hPa]; simp; exact hA
  have hAw : P.angle (τ.symm 1) = α := by rw [hPa]; simp; exact hB
  have hAb : P.angle (τ.symm 2) = Real.pi - 2 * α := by rw [hPa]; simp; exact t2
  have hu : τ.symm 0 ≠ τ.symm 1 := fun e => by have := τ.symm.injective e; simp at this
  have h3 : ∀ x y : Fin 3, x ≠ y → y = x + 1 ∨ x = y + 1 := by
    intro x y; fin_cases x <;> fin_cases y <;> simp
  have hz1 : τ.symm 2 ≠ τ.symm 0 := fun e => by have := τ.symm.injective e; simp at this
  have hz2 : τ.symm 2 ≠ τ.symm 1 := fun e => by have := τ.symm.injective e; simp at this
  have h4 : ∀ k z : Fin 3, z ≠ k + 1 → z ≠ k + 1 + 1 → z = k + 1 + 1 + 1 := by
    intro k z; fin_cases k <;> fin_cases z <;> simp
  have core : ∀ k : Fin 3, ((τ.symm 0 = k + 1 ∧ τ.symm 1 = k + 1 + 1) ∨ (τ.symm 1 = k + 1 ∧ τ.symm 0 = k + 1 + 1)) → τ.symm 2 = k + 1 + 1 + 1 →
      ∀ L : List (Fin N × Plane × Plane), WalkT D.toRegion.toRegionDissection (toV2 (P.e (k + 1))) (P.v (k + 1)) (P.v (k + 1 + 1)) L → 4 ≤ L.length := by
    intro k hk hk2 L W
    have vk3 : P.v (k + 1 + 1 + 1) = D.target.pts 2 := by rw [← hk2]; exact hPb
    have vk4 : P.v (k + 1 + 1 + 1 + 1) = P.v (k + 1) := by rw [fin3_add4]
    have hangB' : P.angle (k + 1 + 1 + 1) = Real.pi - 2 * C.model.angleAt 0 := by
      rw [hAC, ← hk2]; exact hAb
    rcases hk with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · have vk1 : P.v (k + 1) = D.target.pts 0 := by rw [← e1]; exact hPu
      have vk2 : P.v (k + 1 + 1) = D.target.pts 1 := by rw [← e2]; exact hPw
      have hang0 : P.angle (k + 1) = C.model.angleAt 0 := by rw [hAC, ← e1]; exact hAu
      have hang1 : P.angle (k + 1 + 1) = C.model.angleAt 0 := by rw [hAC, ← e2]; exact hAw
      have hX1 : slen C 2 * dist (P.v (k + 1 + 1)) (P.v (k + 1 + 1 + 1)) = slen C 0 * dist (P.v (k + 1)) (P.v (k + 1 + 1)) := by
        rw [vk2, vk3, vk1, dLeg1, dBase]; exact hca
      have hX2 : slen C 2 * dist (P.v (k + 1 + 1 + 1)) (P.v (k + 1 + 1 + 1 + 1)) = slen C 0 * dist (P.v (k + 1)) (P.v (k + 1 + 1)) := by
        rw [vk4, vk3, vk1, vk2, dLeg2, dBase, hX1e]; exact hca
      exact four_base C P hreg idx hidx hidxA hβ hγ hirr hPang hab hac hbc ht hcop hlt hm2 ea' eb' ec' k hang0 hang1 hangB' hX1 hX2 W
    · have vk1 : P.v (k + 1) = D.target.pts 1 := by rw [← e1]; exact hPw
      have vk2 : P.v (k + 1 + 1) = D.target.pts 0 := by rw [← e2]; exact hPu
      have hang0 : P.angle (k + 1) = C.model.angleAt 0 := by rw [hAC, ← e1]; exact hAw
      have hang1 : P.angle (k + 1 + 1) = C.model.angleAt 0 := by rw [hAC, ← e2]; exact hAu
      have hX1 : slen C 2 * dist (P.v (k + 1 + 1)) (P.v (k + 1 + 1 + 1)) = slen C 0 * dist (P.v (k + 1)) (P.v (k + 1 + 1)) := by
        rw [vk2, vk3, vk1, dist_comm (D.target.pts 0) (D.target.pts 2), dLeg2, dist_comm (D.target.pts 1) (D.target.pts 0), dBase, hX1e]
        exact hca
      have hX2 : slen C 2 * dist (P.v (k + 1 + 1 + 1)) (P.v (k + 1 + 1 + 1 + 1)) = slen C 0 * dist (P.v (k + 1)) (P.v (k + 1 + 1)) := by
        rw [vk4, vk3, vk1, vk2, dist_comm (D.target.pts 2) (D.target.pts 1), dLeg1, dist_comm (D.target.pts 1) (D.target.pts 0), dBase]
        exact hca
      exact four_base C P hreg idx hidx hidxA hβ hγ hirr hPang hab hac hbc ht hcop hlt hm2 ea' eb' ec' k hang0 hang1 hangB' hX1 hX2 W
  rcases h3 _ _ hu with hc | hc
  · obtain ⟨k, hk⟩ : ∃ k, k + 1 = τ.symm 0 := ⟨τ.symm 0 - 1, sub_add_cancel _ _⟩
    have e1 : τ.symm 0 = k + 1 := hk.symm
    have e2 : τ.symm 1 = k + 1 + 1 := by rw [hc, e1]
    have e3 : τ.symm 2 = k + 1 + 1 + 1 := h4 k _ (by rw [← e1]; exact hz1) (by rw [← e2]; exact hz2)
    refine ⟨P, k + 1, hPc, Or.inl ⟨by rw [← e1]; exact hPu, by rw [← e2]; exact hPw⟩, ?_⟩
    exact core k (Or.inl ⟨e1, e2⟩) e3
  · obtain ⟨k, hk⟩ : ∃ k, k + 1 = τ.symm 1 := ⟨τ.symm 1 - 1, sub_add_cancel _ _⟩
    have e1 : τ.symm 1 = k + 1 := hk.symm
    have e2 : τ.symm 0 = k + 1 + 1 := by rw [hc, e1]
    have e3 : τ.symm 2 = k + 1 + 1 + 1 := h4 k _ (by rw [← e1]; exact hz2) (by rw [← e2]; exact hz1)
    refine ⟨P, k + 1, hPc, Or.inr ⟨by rw [← e1]; exact hPw, by rw [← e2]; exact hPu⟩, ?_⟩
    exact core k (Or.inr ⟨e1, e2⟩) e3

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.beeson_l11_10
