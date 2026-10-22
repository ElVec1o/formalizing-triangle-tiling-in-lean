-- Draft/LaczFormalIVcData.lean -- Laczkovich DCG 48 (2012), Sect. 8.3 (Subcase IVc, alpha/pi irrational), tile data and flux sign.
--   `Tri.IVcData T alpha a b c` : T has angles (alpha, 2pi/3 - alpha, pi/3) with opposite sides (a, b, c) under some vertex order.
--   `Tri.flux_cedge_ivc`        : flux of such a tile in weight fAlphaAt(theta0) = weight(leftUnit of the c-edge) * (c - a - b)   (the sign computation of IIIc redone for gamma = pi/3:
--                                 the exterior angle at gamma is 2pi/3 (chi = +1), at beta it is pi/3 + alpha (chi = -1), at alpha it is 3 pi/3 - alpha (chi = -1)).
--   `ivc_pair_flux_zero`        : the Lemma 4.8 pair (common c-side) has total flux 0.
-- NOTE, UNAUDITED.  The printed text says only 'repeating the argument of IIIc'; the sign lemma does change (c + a - b becomes c - a - b), as flagged in CENSUS_THM21_2026-10-22.md.
-- Non-vacuity of IVcData: NAMED (alpha = pi/6 parallel with sigma = id is the 30-60-90 triangle; for irrational alpha any triangle with these angles).
-- Credit: Laczkovich (DCG 48 (2012), Sect. 8.3, 7.3, Lemma 4.8), Beeson, Beeson-Zhang (Lemma 5.1 sign computation).
import Erdos634.Draft.LaczFormalIIIcPair

open scoped Classical

namespace Erdos634.Geometry

/-- A placement of the tile `(alpha, 2pi/3 - alpha, pi/3)` with opposite sides `(a, b, c)`. -/
def Tri.IVcData (T : Tri) (α a b c : ℝ) : Prop :=
  ∃ σ : Equiv.Perm (Fin 3),
    T.angleAt (σ 0) = α ∧ T.oppLen (σ 0) = a ∧
    T.angleAt (σ 1) = 2 * Real.pi / 3 - α ∧ T.oppLen (σ 1) = b ∧
    T.angleAt (σ 2) = Real.pi / 3 ∧ T.oppLen (σ 2) = c

theorem Tri.IVcData.cases {T : Tri} {α a b c : ℝ} (h : T.IVcData α a b c) (k : Fin 3) :
    (T.angleAt k = Real.pi / 3 ∧ T.oppLen k = c) ∨ (T.angleAt k = α ∧ T.oppLen k = a) ∨
      (T.angleAt k = 2 * Real.pi / 3 - α ∧ T.oppLen k = b) := by
  obtain ⟨σ, h0, o0, h1, o1, h2, o2⟩ := h
  obtain ⟨j, rfl⟩ := σ.surjective k
  fin_cases j
  · exact Or.inr (Or.inl ⟨h0, o0⟩)
  · exact Or.inr (Or.inr ⟨h1, o1⟩)
  · exact Or.inl ⟨h2, o2⟩

theorem Tri.IVcData.of_congruent {T U : Tri} (hc : T.Congruent U) {α a b c : ℝ} (h : U.IVcData α a b c) :
    T.IVcData α a b c := by
  obtain ⟨σ, hσ⟩ := hc.exists_perm
  obtain ⟨τ, h0, o0, h1, o1, h2, o2⟩ := h
  refine ⟨τ.trans σ.symm, ?_⟩
  simp only [Equiv.trans_apply]
  have e : ∀ j, T.angleAt (σ.symm (τ j)) = U.angleAt (τ j) ∧ T.oppLen (σ.symm (τ j)) = U.oppLen (τ j) := by
    intro j
    have := hσ (σ.symm (τ j))
    rw [Equiv.apply_symm_apply] at this
    exact this
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [(e 0).1, h0]
  · rw [(e 0).2, o0]
  · rw [(e 1).1, h1]
  · rw [(e 1).2, o1]
  · rw [(e 2).1, h2]
  · rw [(e 2).2, o2]

theorem ivc_alpha_ne_pi3 {α : ℝ} (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) : α ≠ Real.pi / 3 := by
  intro h; apply hα; exact ⟨1 / 3, by rw [h]; push_cast; ring⟩

/-- Exactly one vertex has angle `pi/3` (needs `alpha/pi` irrational). -/
theorem Tri.IVcData.gamma_unique {T : Tri} {α a b c : ℝ} (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (h : T.IVcData α a b c) :
    ∃ kg : Fin 3, T.angleAt kg = Real.pi / 3 ∧ ∀ k, T.angleAt k = Real.pi / 3 → k = kg := by
  have hne := ivc_alpha_ne_pi3 hα
  obtain ⟨σ, h0, o0, h1, o1, h2, o2⟩ := h
  refine ⟨σ 2, h2, fun k hk => ?_⟩
  obtain ⟨j, rfl⟩ := σ.surjective k
  have hj : j = 0 ∨ j = 1 ∨ j = 2 := by fin_cases j <;> simp
  rcases hj with rfl | rfl | rfl
  · exfalso; rw [h0] at hk; exact hne hk
  · exfalso; rw [h1] at hk; apply hne; linarith
  · rfl

theorem Tri.IVcData.data_angles_mem_at {T : Tri} {α a b c : ℝ} (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (h : T.IVcData α a b c) (b' : ZMod 2) (θ₀ : Real.Angle) :
    ∀ j, ((T.angleAt j : ℝ) : Real.Angle)
      ∈ (GridChar.rankn 3 (by norm_num) (by decide) α hα b' θ₀).L := by
  obtain ⟨σ, h0, -, h1, -, h2, -⟩ := h
  intro j
  obtain ⟨k, rfl⟩ := σ.surjective j
  have hk : k = 0 ∨ k = 1 ∨ k = 2 := by fin_cases k <;> simp
  rcases hk with rfl | rfl | rfl
  · rw [h0, show ((α : ℝ) : Real.Angle)
        = ((((0 : ℤ) : ℝ) * (Real.pi / ((3 : ℕ) : ℝ)) + ((1 : ℤ) : ℝ) * α : ℝ) : Real.Angle) by
          congr 1; push_cast; ring]
    exact GridChar.rankn_mem _ _ _ _ _ _ _ _ _
  · rw [h1, show ((2 * Real.pi / 3 - α : ℝ) : Real.Angle)
        = ((((2 : ℤ) : ℝ) * (Real.pi / ((3 : ℕ) : ℝ)) + ((-1 : ℤ) : ℝ) * α : ℝ) : Real.Angle) by
          congr 1; push_cast; ring]
    exact GridChar.rankn_mem _ _ _ _ _ _ _ _ _
  · rw [h2, show ((Real.pi / 3 : ℝ) : Real.Angle)
        = ((((1 : ℤ) : ℝ) * (Real.pi / ((3 : ℕ) : ℝ)) + ((0 : ℤ) : ℝ) * α : ℝ) : Real.Angle) by
          congr 1; push_cast; ring]
    exact GridChar.rankn_mem _ _ _ _ _ _ _ _ _

/-- Exterior angles on the grid: `pi - alpha = 3 pi/3 - alpha`, `pi - (2pi/3 - alpha) = pi/3 + alpha`, `pi - pi/3 = 2 pi/3`. -/
theorem ivc_tileValue_at (T : Tri) {α a b c : ℝ} (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (h : T.IVcData α a b c) (b' : ZMod 2) (θ₀ : Real.Angle) :
    (GridChar.rankn 3 (by norm_num) (by decide) α hα b' θ₀).tileValue T
      = (if ((3 : ℤ) : ZMod 2) + b' * ((-1 : ℤ) : ZMod 2) = 0 then 1 else -1) * a
        + (if ((1 : ℤ) : ZMod 2) + b' * ((1 : ℤ) : ZMod 2) = 0 then 1 else -1) * b
        + (if ((2 : ℤ) : ZMod 2) + b' * ((0 : ℤ) : ZMod 2) = 0 then 1 else -1) * c := by
  obtain ⟨σ, h0, o0, h1, o1, h2, o2⟩ := h
  unfold GridChar.tileValue
  rw [← Equiv.sum_comp σ (fun j => (GridChar.rankn 3 (by norm_num) (by decide) α hα b' θ₀).chi
    ((Real.pi - T.angleAt j : ℝ) : Real.Angle) * T.oppLen j), Fin.sum_univ_three]
  rw [h0, o0, h1, o1, h2, o2,
    show Real.pi - α = ((3 : ℤ) : ℝ) * (Real.pi / ((3 : ℕ) : ℝ)) + ((-1 : ℤ) : ℝ) * α by
      push_cast; ring,
    show Real.pi - (2 * Real.pi / 3 - α) = ((1 : ℤ) : ℝ) * (Real.pi / ((3 : ℕ) : ℝ)) + ((1 : ℤ) : ℝ) * α by
      push_cast; ring,
    show Real.pi - Real.pi / 3 = ((2 : ℤ) : ℝ) * (Real.pi / ((3 : ℕ) : ℝ)) + ((0 : ℤ) : ℝ) * α by
      push_cast; ring,
    GridChar.rankn_chi, GridChar.rankn_chi, GridChar.rankn_chi]

theorem ivc_tileValue_alpha_at (T : Tri) {α a b c : ℝ} (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (h : T.IVcData α a b c) (θ₀ : Real.Angle) :
    (fAlphaAt α hα θ₀).tileValue T = c - a - b := by
  unfold fAlphaAt
  rw [ivc_tileValue_at T hα h 0 θ₀, if_neg (by decide), if_neg (by decide), if_pos (by decide)]
  ring

/-- **Anchored sign lemma for `gamma = pi/3`**: flux in `fAlphaAt theta0` is `weight(c-edge) * (c - a - b)`. -/
theorem Tri.flux_cedge_ivc (T : Tri) {α a b c : ℝ} (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (h : T.IVcData α a b c) (θ₀ : Real.Angle) (kg : Fin 3) (hkg : T.angleAt kg = Real.pi / 3) :
    T.flux (fAlphaAt α hα θ₀).weight = (fAlphaAt α hα θ₀).weight (T.leftUnit (kg + 1)) * (c - a - b) := by
  obtain ⟨s, hw, hf⟩ := T.weight_form (fAlphaAt α hα θ₀) (GridChar.rankn_sq _ _ _ _ _ _ _) (h.data_angles_mem_at hα 0 θ₀)
  have hk : kg + 1 + 2 = kg := by fin_cases kg <;> rfl
  have hchi : (fAlphaAt α hα θ₀).chi ((Real.pi - Real.pi / 3 : ℝ) : Real.Angle) = 1 := by
    unfold fAlphaAt
    rw [show Real.pi - Real.pi / 3 = ((2 : ℤ) : ℝ) * (Real.pi / ((3 : ℕ) : ℝ)) + ((0 : ℤ) : ℝ) * α by
      push_cast; ring, GridChar.rankn_chi, if_pos (by decide)]
  have h1 := hw (kg + 1)
  rw [hk, hkg, hchi] at h1
  rw [h1, hf, ivc_tileValue_alpha_at T hα h θ₀]
  ring

end Erdos634.Geometry

namespace Erdos634.Draft.LaczFormal.IIIc

open Erdos634.Geometry Erdos634.Draft.LaczFormal.Graph

/-- The edge `k` of a placement with `dist = c` (`c` different from `a`, `b`) is the `c`-edge `kg + 1`. -/
theorem ivc_cedge_index {T : Tri} {α a b c : ℝ} (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (h : T.IVcData α a b c) (hca : c ≠ a) (hcb : c ≠ b)
    (kg : Fin 3) (hkg : T.angleAt kg = Real.pi / 3) (k : Fin 3) (hk : dist (T.pts k) (T.pts (k + 1)) = c) : k = kg + 1 := by
  have hu : ∀ j, T.angleAt j = Real.pi / 3 → j = kg := by
    obtain ⟨kg', h1, h2⟩ := h.gamma_unique hα
    intro j hj
    rw [h2 j hj, h2 kg hkg]
  have ho : T.oppLen (k + 2) = c := by
    unfold Tri.oppLen
    have e1 : k + 2 + 1 = k := by fin_cases k <;> rfl
    have e2 : k + 2 + 2 = k + 1 := by fin_cases k <;> rfl
    rw [e1, e2]; exact hk
  rcases h.cases (k + 2) with ⟨h1, _⟩ | ⟨_, h2⟩ | ⟨_, h3⟩
  · have := hu _ h1
    have e3 : k = k + 2 + 1 := by fin_cases k <;> rfl
    rw [e3, this]
  · exact absurd (ho.symm.trans h2) hca
  · exact absurd (ho.symm.trans h3) hcb

/-- The vertex `kg` (angle `pi/3`) is opposite the `c`-edge `kg + 1`. -/
theorem ivc_cedge_dist {T : Tri} {α a b c : ℝ} (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (h : T.IVcData α a b c) (kg : Fin 3)
    (hkg : T.angleAt kg = Real.pi / 3) : dist (T.pts (kg + 1)) (T.pts (kg + 1 + 1)) = c := by
  have hne := ivc_alpha_ne_pi3 hα
  have ho : T.oppLen kg = c := by
    rcases h.cases kg with ⟨-, h1⟩ | ⟨h1, -⟩ | ⟨h1, -⟩
    · exact h1
    · exfalso; rw [hkg] at h1; exact hne h1.symm
    · exfalso; rw [hkg] at h1; apply hne; linarith
  have e : kg + 1 + 1 = kg + 2 := by fin_cases kg <;> rfl
  rw [e]; exact ho

/-- A `TriStep` of length `c` of a placement is its canonical `c`-edge. -/
theorem ivc_triStep_cedge {T : Tri} {α a b c : ℝ} (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (h : T.IVcData α a b c) (hca : c ≠ a) (hcb : c ≠ b)
    (kg : Fin 3) (hkg : T.angleAt kg = Real.pi / 3) {d : V2} {U V : Plane} (hS : TriStep T d U V) (hc : dist U V = c) :
    U = eU T (kg + 1) ∧ V = eV T (kg + 1) := by
  obtain ⟨k, hl, hp⟩ := triStep_leftDir hS
  have hdk : dist (T.pts k) (T.pts (k + 1)) = c := by
    rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]; exact hc
    · rw [h1, h2, dist_comm]; exact hc
  have e := ivc_cedge_index hα h hca hcb kg hkg k hdk
  subst e
  have hv := eV_sub_eU T (kg + 1)
  rw [hl] at hv
  have hsucc : ∀ j : Fin 3, j ≠ j + 1 := by decide
  have hne : T.pts (kg + 1) ≠ T.pts (kg + 1 + 1) := fun h => hsucc _ (T.indep.injective h)
  by_cases hd : 0 < T.det
  · rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨by simp [eU, hd, h1], by simp [eV, hd, h2]⟩
    · exfalso
      apply hne
      have h4 : eV T (kg + 1) - eU T (kg + 1) = T.pts (kg + 1 + 1) - T.pts (kg + 1) := by simp [eV, eU, hd]
      have h3 : T.pts (kg + 1 + 1) - T.pts (kg + 1) = T.pts (kg + 1) - T.pts (kg + 1 + 1) :=
        h4.symm.trans (hv.trans (by rw [← h1, ← h2]))
      ext i
      have := congrArg (fun z : Plane => z i) h3
      simp at this
      linarith
  · rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exfalso
      apply hne
      have h4 : eV T (kg + 1) - eU T (kg + 1) = T.pts (kg + 1) - T.pts (kg + 1 + 1) := by simp [eV, eU, hd]
      have h3 : T.pts (kg + 1) - T.pts (kg + 1 + 1) = T.pts (kg + 1 + 1) - T.pts (kg + 1) :=
        h4.symm.trans (hv.trans (by rw [← h1, ← h2]))
      ext i
      have := congrArg (fun z : Plane => z i) h3
      simp at this
      linarith
    · exact ⟨by simp [eU, hd, h2], by simp [eV, hd, h1]⟩

/-- **Lemma 4.8 pairs have flux 0** (IVc). -/
theorem ivc_pair_flux_zero {T T' : Tri} {α a b c : ℝ} (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (hT : T.IVcData α a b c) (hT' : T'.IVcData α a b c) (hca : c ≠ a) (hcb : c ≠ b) (θ₀ : Real.Angle)
    {d : V2} {U V : Plane} (hS : TriStep T d U V) (hS' : TriStep T' (neg2 d) V U) (hc : dist U V = c) :
    T.flux (fAlphaAt α hα θ₀).weight + T'.flux (fAlphaAt α hα θ₀).weight = 0 := by
  obtain ⟨kg, hkg, -⟩ := hT.gamma_unique hα
  obtain ⟨kg', hkg', -⟩ := hT'.gamma_unique hα
  obtain ⟨k, hk, hkp⟩ := triStep_leftDir hS
  obtain ⟨k', hk', hkp'⟩ := triStep_leftDir hS'
  have hdk : dist (T.pts k) (T.pts (k + 1)) = c := by
    rcases hkp with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]; exact hc
    · rw [h1, h2, dist_comm]; exact hc
  have hdk' : dist (T'.pts k') (T'.pts (k' + 1)) = c := by
    rcases hkp' with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2, dist_comm]; exact hc
    · rw [h1, h2]; exact hc
  have e := ivc_cedge_index hα hT hca hcb kg hkg k hdk
  have e' := ivc_cedge_index hα hT' hca hcb kg' hkg' k' hdk'
  have hneg : T'.leftDir k' = -(T.leftDir k) := by rw [hk, hk']; abel
  have hu : T'.leftUnit k' = Dir.neg (T.leftUnit k) := by
    apply Subtype.ext
    show ‖T'.leftDir k'‖⁻¹ • T'.leftDir k' = -(‖T.leftDir k‖⁻¹ • T.leftDir k)
    rw [hneg, norm_neg, smul_neg]
  rw [T.flux_cedge_ivc hα hT θ₀ kg hkg, T'.flux_cedge_ivc hα hT' θ₀ kg' hkg', ← e, ← e', hu,
    (fAlphaAt α hα θ₀).weight_odd]
  ring

end Erdos634.Draft.LaczFormal.IIIc

#print axioms Erdos634.Geometry.Tri.IVcData.gamma_unique
#print axioms Erdos634.Geometry.Tri.flux_cedge_ivc
#print axioms Erdos634.Draft.LaczFormal.IIIc.ivc_triStep_cedge
#print axioms Erdos634.Draft.LaczFormal.IIIc.ivc_pair_flux_zero
