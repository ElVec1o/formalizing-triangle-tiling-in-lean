-- Draft/LaczFormalIIIcFlux.lean -- Laczkovich DCG 48 (2012), Sect. 7.3 (Subcase IIIc, N = 6 / the Phi bookkeeping), items (b) and (c):
--   `Tri.flux_cedge_at`        : anchored sign lemma: flux of the tile (alpha, pi/3-alpha, 2pi/3) in weight fAlphaAt(theta0) = weight(leftUnit of the c-edge) * (c + a - b)
--                                (the same as Tri.flux_cedge, for every anchor theta0, e.g. the direction of side 0 of the polygon A, as Phi_additive uses);
--   `triStep_leftDir`   : a left step U -> V of a tile is one of its edges, and its leftDir is V - U;
--   `pair_flux_zero`           : two tiles sharing the c-side UV from opposite sides (the pair of Lemma 4.8) have total flux 0 in EVERY odd weight.
-- NOTE on item (b): the printed Sect. 7.3 puts every tile direction in G only so that chi is defined on tile sides.  Here weight is `GridChar.weight` (0 off the coset), odd on all directions,
-- so interior c-pairs cancel without (b); (b) is used only for a boundary c-tile, whose c-side lies ON a side of A (its direction is then that side's direction, nonzero weight).  Not formalized here.
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 7.3, Lemma 4.8), Beeson, Beeson-Zhang (Lemma 5.1 sign computation).
import Erdos634.Draft.LaczFormalFluxPolyPhi3
import Erdos634.Draft.LaczFormalBZPhi1
import Erdos634.Draft.LaczFormalGraphWalk
import Erdos634.Draft.LaczFormalGraphEnds
import Erdos634.Draft.FluxPaperCorIntAnchored

open scoped Classical

namespace Erdos634.Geometry

/-- **Anchored sign lemma** (Beeson-Zhang Lemma 5.1 computation, anchor `theta0`). -/
theorem Tri.flux_cedge_at (T : Tri) {α a b c : ℝ} (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (h : T.TwoPiThreeData α a b c) (θ₀ : Real.Angle) (kg : Fin 3) (hkg : T.angleAt kg = 2 * Real.pi / 3) :
    T.flux (fAlphaAt α hα θ₀).weight = (fAlphaAt α hα θ₀).weight (T.leftUnit (kg + 1)) * (c + a - b) := by
  obtain ⟨s, hw, hf⟩ := T.weight_form (fAlphaAt α hα θ₀) (GridChar.rankn_sq _ _ _ _ _ _ _) (T.data_angles_mem_at hα h 0 θ₀)
  have hk : kg + 1 + 2 = kg := by fin_cases kg <;> rfl
  have hchi : (fAlphaAt α hα θ₀).chi ((Real.pi - 2 * Real.pi / 3 : ℝ) : Real.Angle) = -1 := by
    unfold fAlphaAt
    rw [show Real.pi - 2 * Real.pi / 3 = ((1 : ℤ) : ℝ) * (Real.pi / ((3 : ℕ) : ℝ)) + ((0 : ℤ) : ℝ) * α by
      push_cast; ring, GridChar.rankn_chi]
    simp
  have h1 := hw (kg + 1)
  rw [hk, hkg, hchi] at h1
  rw [h1, hf, data_tileValue_alpha_at T hα h θ₀]
  ring

end Erdos634.Geometry

namespace Erdos634.Draft.LaczFormal.IIIc

open Erdos634.Geometry Erdos634.Draft.LaczFormal.Graph

theorem leftDir_pos (T : Tri) (hd : 0 < T.det) (k : Fin 3) : T.leftDir k = T.pts (k + 1) - T.pts k := by
  unfold Tri.leftDir; rw [if_pos hd]

theorem leftDir_neg (T : Tri) (hd : T.det < 0) (k : Fin 3) : T.leftDir k = T.pts k - T.pts (k + 1) := by
  unfold Tri.leftDir; rw [if_neg (by linarith)]

/-- **A left step is a tile edge with `leftDir = V - U`.** -/
theorem triStep_leftDir {T : Tri} {d : V2} {U V : Plane} (hS : TriStep T d U V) :
    ∃ k : Fin 3, T.leftDir k = V - U ∧ ((T.pts k = U ∧ T.pts (k + 1) = V) ∨ (T.pts k = V ∧ T.pts (k + 1) = U)) := by
  obtain ⟨kk, f, g, hk, hf, hfk, hgk, hgf, hpar, hleft⟩ := hS
  obtain ⟨c, hc, hcq⟩ := hpar.smul
  have e0 : (V - U) 0 = c * d.1 := congrArg Prod.fst hcq
  have e1 : (V - U) 1 = c * d.2 := congrArg Prod.snd hcq
  have hl : 0 < d.1 * (T.pts g - U) 1 - d.2 * (T.pts g - U) 0 := hleft
  have hcr : 0 < (V - U) 0 * (T.pts g - U) 1 - (V - U) 1 * (T.pts g - U) 0 := by
    rw [e0, e1]
    have : c * d.1 * (T.pts g - U) 1 - c * d.2 * (T.pts g - U) 0 = c * (d.1 * (T.pts g - U) 1 - d.2 * (T.pts g - U) 0) := by ring
    rw [this]; exact mul_pos hc hl
  have hcases := (by decide : ∀ kk f g : Fin 3, f ≠ kk → g ≠ kk → g ≠ f →
    (kk = 0 ∧ f = 1 ∧ g = 2) ∨ (kk = 1 ∧ f = 2 ∧ g = 0) ∨ (kk = 2 ∧ f = 0 ∧ g = 1) ∨
    (kk = 0 ∧ f = 2 ∧ g = 1) ∨ (kk = 2 ∧ f = 1 ∧ g = 0) ∨ (kk = 1 ∧ f = 0 ∧ g = 2)) kk f g hfk hgk hgf
  subst hk hf
  have hdet : T.det = (T.pts 1 - T.pts 0) 0 * (T.pts 2 - T.pts 0) 1 - (T.pts 1 - T.pts 0) 1 * (T.pts 2 - T.pts 0) 0 := rfl
  simp only [PiLp.sub_apply] at hcr hdet
  rcases hcases with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · have hd : 0 < T.det := by rw [hdet]; nlinarith
    exact ⟨0, by rw [leftDir_pos T hd]; rfl, Or.inl ⟨rfl, rfl⟩⟩
  · have hd : 0 < T.det := by rw [hdet]; nlinarith
    exact ⟨1, by rw [leftDir_pos T hd]; rfl, Or.inl ⟨rfl, rfl⟩⟩
  · have hd : 0 < T.det := by rw [hdet]; nlinarith
    exact ⟨2, by rw [leftDir_pos T hd]; rfl, Or.inl ⟨rfl, rfl⟩⟩
  · have hd : T.det < 0 := by rw [hdet]; nlinarith
    exact ⟨2, by rw [leftDir_neg T hd]; rfl, Or.inr ⟨rfl, rfl⟩⟩
  · have hd : T.det < 0 := by rw [hdet]; nlinarith
    exact ⟨1, by rw [leftDir_neg T hd]; rfl, Or.inr ⟨rfl, rfl⟩⟩
  · have hd : T.det < 0 := by rw [hdet]; nlinarith
    exact ⟨0, by rw [leftDir_neg T hd]; rfl, Or.inr ⟨rfl, rfl⟩⟩

/-- The edge `k` of a placement of the `2pi/3` tile with `dist = c` (`c` different from `a`, `b`) is the `c`-edge `kg + 1`. -/
theorem cedge_index {T : Tri} {α a b c : ℝ} (h : T.TwoPiThreeData α a b c) (hca : c ≠ a) (hcb : c ≠ b)
    (kg : Fin 3) (hkg : T.angleAt kg = 2 * Real.pi / 3) (k : Fin 3) (hk : dist (T.pts k) (T.pts (k + 1)) = c) : k = kg + 1 := by
  have hu : ∀ j, T.angleAt j = 2 * Real.pi / 3 → j = kg := by
    obtain ⟨kg', h1, h2⟩ := h.gamma_unique
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

/-- **(c) Lemma 4.8 pairs have flux 0**: two placements of the tile with a common `c`-side `UV` traversed oppositely (tile `T` left of `d`, `T'` left of `-d`) have total flux `0` in
`fAlphaAt theta0`.  Nothing about the shape (kite / parallelogram) or about G-membership of directions is used: `weight` is odd on all directions. -/
theorem pair_flux_zero {T T' : Tri} {α a b c : ℝ} (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (hT : T.TwoPiThreeData α a b c) (hT' : T'.TwoPiThreeData α a b c) (hca : c ≠ a) (hcb : c ≠ b) (θ₀ : Real.Angle)
    {d : V2} {U V : Plane} (hS : TriStep T d U V) (hS' : TriStep T' (neg2 d) V U) (hc : dist U V = c) :
    T.flux (fAlphaAt α hα θ₀).weight + T'.flux (fAlphaAt α hα θ₀).weight = 0 := by
  obtain ⟨kg, hkg, -⟩ := hT.gamma_unique
  obtain ⟨kg', hkg', -⟩ := hT'.gamma_unique
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
  have e := cedge_index hT hca hcb kg hkg k hdk
  have e' := cedge_index hT' hca hcb kg' hkg' k' hdk'
  have hneg : T'.leftDir k' = -(T.leftDir k) := by rw [hk, hk']; abel
  have hu : T'.leftUnit k' = Dir.neg (T.leftUnit k) := by
    apply Subtype.ext
    show ‖T'.leftDir k'‖⁻¹ • T'.leftDir k' = -(‖T.leftDir k‖⁻¹ • T.leftDir k)
    rw [hneg, norm_neg, smul_neg]
  rw [T.flux_cedge_at hα hT θ₀ kg hkg, T'.flux_cedge_at hα hT' θ₀ kg' hkg', ← e, ← e', hu,
    (fAlphaAt α hα θ₀).weight_odd]
  ring

end Erdos634.Draft.LaczFormal.IIIc

#print axioms Erdos634.Geometry.Tri.flux_cedge_at
#print axioms Erdos634.Draft.LaczFormal.IIIc.triStep_leftDir
#print axioms Erdos634.Draft.LaczFormal.IIIc.pair_flux_zero
