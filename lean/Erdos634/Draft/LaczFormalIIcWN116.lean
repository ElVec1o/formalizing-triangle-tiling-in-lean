-- Draft/LaczFormalIIcWN116.lean -- Laczkovich (DCG 48 (2012), Sect. 6.3, p. 360-361, Fig. 8), R4 PROVED: the quadrilaterals `R_i = V_{i-1} V_i W_i W_{i-1}` of the ring have the shapes of Fig. 8.
-- `r4_fig8`: for the chords of R3 (ends `W_i = q (w i)` convex vertices of the corner polygon, `w` monotone) there are `d, L, mm : ZMod M -> R` with `RingQuadA/B alpha beta gamma (L i) (d i) (mm i) (d (i-1))` for all `i`
-- (or the same with `alpha`, `beta` swapped, if the spokes make the angle beta with the OUTGOING side of every corner of `A`).
-- Route: R4 sketch of (private working notes, not included): unsigned angles at the corners of `A` (`spokes_angle`), oriented rotations (`v_rot_of_angles` WN114), the turns at the ends (`vertex_turn_pred/succ`, WN115), and the closure of
-- the quadrilateral (`ringA_of_rot`, `ringB_of_rot`, WN111); the two combinations (sigma, direction of `w`) with right turns at `W` are excluded by the closure (`quad_turns_contra`: total turning `2 gamma`).
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.3, Fig. 8), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcWN115
import Erdos634.Draft.LaczFormalIIcWN111
import Erdos634.Draft.LaczFormalRG12Ring

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG
open Erdos634.Draft.LaczFormal.WN (edgeSet wind extAng OrientOK RotPos IsCornerOfD)

local notation "tc" => Erdos634.Draft.LaczFormal.WN.toC

variable {N M : ℕ}

theorem quad_of_tau2 {A0 B0 γ : ℝ} (hs : A0 + B0 + γ = Real.pi) {P0 P1 P2 P3 : ℂ} (hne : P1 ≠ P0)
    (h1 : RotPos (P1 - P0) (P2 - P1) (Real.pi - B0)) (h4 : RotPos (P1 - P0) (P0 - P3) (A0 + Real.pi))
    {τ2 : ℝ} (hτ : RotPos (P2 - P1) (P3 - P2) τ2) (hτA : τ2 = A0 ∨ τ2 = B0) :
    RingQuadA A0 B0 γ ‖P1 - P0‖ ‖P2 - P1‖ ‖P3 - P2‖ ‖P0 - P3‖ ∨ RingQuadB A0 B0 γ ‖P1 - P0‖ ‖P2 - P1‖ ‖P3 - P2‖ ‖P0 - P3‖ := by
  rcases hτA with h | h
  · left; exact Erdos634.Draft.LaczFormal.WN.ringA_of_rot hs hne h1 (hτ.congr_angle h) h4
  · right; exact Erdos634.Draft.LaczFormal.WN.ringB_of_rot hs hne h1 (hτ.congr_angle h) h4

set_option maxHeartbeats 12800000 in
theorem r4_fig8 [NeZero N] [NeZero M] (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hC : CaseC D idx) (hab : Comm (slen D 0) (slen D 1)) (hac : ¬ Comm (slen D 0) (slen D 2))
    (h1 : D.model.angleAt 2 < Real.pi / 2) (h3 : D.model.angleAt 2 ≠ Real.pi / 3) (G : AngGen (fun l => D.model.angleAt l))
    (hcor : ∀ j : Fin M, cnt D idx (P.v j) 0 = 1 ∧ cnt D idx (P.v j) 1 = 1 ∧ cnt D idx (P.v j) 2 = 0)
    {m : ℕ} [NeZero m] (C : Fin m → Plane) (hCy : ∀ k : Fin m, GKite D idx (C k) (C (k + 1))) (hinj : Function.Injective C)
    (q : Fin M → ℂ) (hq : IsCornerOfD (cyc C) q) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (hturn : ∀ k, σ * extAng q k = D.model.angleAt 2)
    (w : Fin M → Fin M) (hGE : ∀ i, GExc D idx (P.v i) (Erdos634.Draft.LaczFormal.WN.toC.symm (q (w i))))
    (hmono : (∀ i, w (i + 1) = w i + 1) ∨ (∀ i, w (i + 1) = w i - 1)) :
    (∃ d L mm : ZMod M → ℝ, ∀ i, RingQuadA (D.model.angleAt 0) (D.model.angleAt 1) (D.model.angleAt 2) (L i) (d i) (mm i) (d (i - 1)) ∨
        RingQuadB (D.model.angleAt 0) (D.model.angleAt 1) (D.model.angleAt 2) (L i) (d i) (mm i) (d (i - 1))) ∨
    (∃ d L mm : ZMod M → ℝ, ∀ i, RingQuadA (D.model.angleAt 1) (D.model.angleAt 0) (D.model.angleAt 2) (L i) (d i) (mm i) (d (i - 1)) ∨
        RingQuadB (D.model.angleAt 1) (D.model.angleAt 0) (D.model.angleAt 2) (L i) (d i) (mm i) (d (i - 1))) := by
  classical
  have hα := G.pos 0
  have hβ := G.pos 1
  have hγ := G.pos 2
  have hsum := G.sum
  have hint : ∀ a : Fin m, C a ∈ interior P.carrier := by
    intro a
    have hXY : GKite D idx (C (a - 1)) (C a) := by simpa using hCy (a - 1)
    have := (gkite_vertex_type D P hreg idx hC.hidxA hC.hregc h1 h3 hXY).1.1
    rw [hreg] at this; exact this
  set Wp : Fin M → Plane := fun i => Erdos634.Draft.LaczFormal.WN.toC.symm (q (w i)) with hWp
  have hWtc : ∀ i, tc (Wp i) = q (w i) := fun i => by simp [hWp]
  have hWint : ∀ i, Wp i ∈ interior P.carrier := by
    intro i
    obtain ⟨k, hk, -⟩ := hq.2 (w i)
    have : Wp i = C k := by
      simp only [hWp]; rw [hk]; exact Erdos634.Draft.LaczFormal.WN.toC.symm_apply_apply _
    rw [this]; exact hint k
  have hint2 : ∀ E ∈ excVerts2 D idx P, E ∈ interior D.region := fun E hE =>
    (gexc_exc_interior_exact D P hreg idx hC hab hac h1 h3 G hcor E hE).1
  obtain ⟨a, b, hab_, hsp⟩ := spokes_angle D P hreg idx hC h1 h3 hcor hint2 Wp hGE
  have hin : ∀ j : Fin M, EuclideanGeometry.angle (P.v j) (P.v (j + 1)) (Wp (j + 1)) = D.model.angleAt b := fun j => (hsp j).2
  have hout : ∀ j : Fin M, EuclideanGeometry.angle (P.v (j + 1)) (P.v j) (Wp j) = D.model.angleAt a := by
    intro j
    have := (hsp (j - 1)).1
    rwa [sub_add_cancel] at this
  -- the per-quadrilateral statement
  have hAB : (D.model.angleAt a = D.model.angleAt 0 ∧ D.model.angleAt b = D.model.angleAt 1) ∨
      (D.model.angleAt a = D.model.angleAt 1 ∧ D.model.angleAt b = D.model.angleAt 0) := by
    rcases hab_ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · left; exact ⟨rfl, rfl⟩
    · right; exact ⟨rfl, rfl⟩
  have hsAB : D.model.angleAt a + D.model.angleAt b + D.model.angleAt 2 = Real.pi := by
    rcases hAB with ⟨h1', h2'⟩ | ⟨h1', h2'⟩ <;> linarith
  have key : ∀ j : Fin M,
      RingQuadA (D.model.angleAt a) (D.model.angleAt b) (D.model.angleAt 2) ‖tc (P.v (j + 1)) - tc (P.v j)‖ ‖q (w (j + 1)) - tc (P.v (j + 1))‖
        ‖q (w j) - q (w (j + 1))‖ ‖tc (P.v j) - q (w j)‖ ∨
      RingQuadB (D.model.angleAt a) (D.model.angleAt b) (D.model.angleAt 2) ‖tc (P.v (j + 1)) - tc (P.v j)‖ ‖q (w (j + 1)) - tc (P.v (j + 1))‖
        ‖q (w j) - q (w (j + 1))‖ ‖tc (P.v j) - q (w j)‖ := by
    intro j
    have hne : tc (P.v (j + 1)) ≠ tc (P.v j) := by
      intro e
      exact Erdos634.Draft.LaczFormal.WN.convPoly_e_ne P j (Erdos634.Draft.LaczFormal.WN.toC.injective e)
    obtain ⟨hr1, hr4⟩ := v_rot_of_angles P Wp hWint (D.model.angleAt a) (D.model.angleAt b) hin hout j
    simp only [hWtc] at hr1 hr4
    have hr4' : RotPos (tc (P.v (j + 1)) - tc (P.v j)) (tc (P.v j) - q (w j)) (D.model.angleAt a + Real.pi) := hr4
    have hAB' : D.model.angleAt a + D.model.angleAt b = D.model.angleAt 0 + D.model.angleAt 1 := by
      rcases hAB with ⟨h1', h2'⟩ | ⟨h1', h2'⟩ <;> linarith
    have tau_mem : ∀ τ : ℝ, (τ = D.model.angleAt 0 ∨ τ = D.model.angleAt 1) → (τ = D.model.angleAt a ∨ τ = D.model.angleAt b) := by
      intro τ hτ
      rcases hAB with ⟨h1', h2'⟩ | ⟨h1', h2'⟩
      · rcases hτ with h | h
        · left; rw [h1']; exact h
        · right; rw [h2']; exact h
      · rcases hτ with h | h
        · right; rw [h2']; exact h
        · left; rw [h1']; exact h
    rcases hmono with hinc | hdec
    · -- w increasing: P3 = q (w j) is the predecessor of P2 = q (w (j+1)), and P2 the successor of P3
      have hw := hinc j
      have hpred := vertex_turn_pred D P hreg idx hC h1 h3 G C hCy hinj q hq hσ (w (j + 1)) (hturn _) (hGE (j + 1))
      have hsucc := vertex_turn_succ D P hreg idx hC h1 h3 G C hCy hinj q hq hσ (w j) (hturn _) (hGE j)
      have e1 : w (j + 1) - 1 = w j := by rw [hw]; exact add_sub_cancel_right _ _
      have e2 : w j + 1 = w (j + 1) := hw.symm
      rw [e1] at hpred
      rw [e2] at hsucc
      rcases hσ with rfl | rfl
      · obtain ⟨-, ht2, -⟩ : (1 : ℝ) = 1 ∧ _ ∧ _ := by
          rcases hpred with ⟨_, h2, h3'⟩ | ⟨h, _⟩
          · exact ⟨rfl, h2, h3'⟩
          · norm_num at h
        exact quad_of_tau2 hsAB hne hr1 hr4' ht2 (tau_mem _ (Or.inl rfl))
      · exfalso
        have ht2 : RotPos (q (w (j + 1)) - tc (P.v (j + 1))) (q (w j) - q (w (j + 1))) (-D.model.angleAt 0) := by
          rcases hpred with ⟨h, _⟩ | ⟨_, h2, _⟩
          · norm_num at h
          · exact h2
        have ht3 : RotPos (q (w j) - q (w (j + 1))) (tc (P.v j) - q (w j)) (-D.model.angleAt 1) := by
          rcases hsucc with ⟨h, _⟩ | ⟨_, _, h3'⟩
          · norm_num at h
          · exact h3'
        exact Erdos634.Draft.LaczFormal.WN.quad_turns_contra hsAB hγ (G.pos a) (G.pos b) hne (τ2 := -D.model.angleAt 0) (τ3 := -D.model.angleAt 1)
          (by linarith) hr1 ht2 ht3 hr4'
    · -- w decreasing
      have hw := hdec j
      have hsucc := vertex_turn_succ D P hreg idx hC h1 h3 G C hCy hinj q hq hσ (w (j + 1)) (hturn _) (hGE (j + 1))
      have hpred := vertex_turn_pred D P hreg idx hC h1 h3 G C hCy hinj q hq hσ (w j) (hturn _) (hGE j)
      have e1 : w (j + 1) + 1 = w j := by rw [hw]; exact sub_add_cancel _ _
      have e2 : w j - 1 = w (j + 1) := hw.symm
      rw [e1] at hsucc
      rw [e2] at hpred
      rcases hσ with rfl | rfl
      · exfalso
        have ht2 : RotPos (q (w (j + 1)) - tc (P.v (j + 1))) (q (w j) - q (w (j + 1))) (-D.model.angleAt 1) := by
          rcases hsucc with ⟨_, h2, _⟩ | ⟨h, _⟩
          · exact h2
          · norm_num at h
        have ht3 : RotPos (q (w j) - q (w (j + 1))) (tc (P.v j) - q (w j)) (-D.model.angleAt 0) := by
          rcases hpred with ⟨_, _, h3'⟩ | ⟨h, _⟩
          · exact h3'
          · norm_num at h
        exact Erdos634.Draft.LaczFormal.WN.quad_turns_contra hsAB hγ (G.pos a) (G.pos b) hne (τ2 := -D.model.angleAt 1) (τ3 := -D.model.angleAt 0)
          (by linarith) hr1 ht2 ht3 hr4'
      · have ht2 : RotPos (q (w (j + 1)) - tc (P.v (j + 1))) (q (w j) - q (w (j + 1))) (D.model.angleAt 1) := by
          rcases hsucc with ⟨h, _⟩ | ⟨_, h2, _⟩
          · norm_num at h
          · exact h2
        exact quad_of_tau2 hsAB hne hr1 hr4' ht2 (tau_mem _ (Or.inr rfl))
  -- reindex and convert to `ZMod M`
  set dd : Fin M → ℝ := fun j => ‖q (w j) - tc (P.v j)‖ with hdd
  set LL : Fin M → ℝ := fun j => ‖tc (P.v j) - tc (P.v (j - 1))‖ with hLL
  set mm : Fin M → ℝ := fun j => ‖q (w (j - 1)) - q (w j)‖ with hmm
  have key' : ∀ i : Fin M,
      RingQuadA (D.model.angleAt a) (D.model.angleAt b) (D.model.angleAt 2) (LL i) (dd i) (mm i) (dd (i - 1)) ∨
      RingQuadB (D.model.angleAt a) (D.model.angleAt b) (D.model.angleAt 2) (LL i) (dd i) (mm i) (dd (i - 1)) := by
    intro i
    have h := key (i - 1)
    rw [sub_add_cancel] at h
    have e : ‖tc (P.v (i - 1)) - q (w (i - 1))‖ = ‖q (w (i - 1)) - tc (P.v (i - 1))‖ := norm_sub_rev _ _
    rw [e] at h
    exact h
  have conv : ∀ (A0 B0 : ℝ), (∀ i : Fin M, RingQuadA A0 B0 (D.model.angleAt 2) (LL i) (dd i) (mm i) (dd (i - 1)) ∨
        RingQuadB A0 B0 (D.model.angleAt 2) (LL i) (dd i) (mm i) (dd (i - 1))) →
      ∃ d L mm' : ZMod M → ℝ, ∀ i, RingQuadA A0 B0 (D.model.angleAt 2) (L i) (d i) (mm' i) (d (i - 1)) ∨
        RingQuadB A0 B0 (D.model.angleAt 2) (L i) (d i) (mm' i) (d (i - 1)) := by
    intro A0 B0 hk
    refine ⟨fun z => dd ((ZMod.finEquiv M).symm z), fun z => LL ((ZMod.finEquiv M).symm z), fun z => mm ((ZMod.finEquiv M).symm z), fun z => ?_⟩
    have hs : (ZMod.finEquiv M).symm (z - 1) = (ZMod.finEquiv M).symm z - 1 := by rw [map_sub, map_one]
    simp only [hs]
    exact hk _
  rcases hAB with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · left
    rw [ha, hb] at key'
    exact conv _ _ key'
  · right
    rw [ha, hb] at key'
    exact conv _ _ key'

#print axioms r4_fig8


end Erdos634.Draft.LaczFormal.RG
