-- Draft/LaczFormalIIcWN95.lean -- Laczkovich (DCG 48 (2012), Sect. 6.3, p. 359), Lemma 6.2, R2: WHERE THE CHORD OF A CONCAVE VERTEX ENDS.
-- Inputs: the chord `C k -> W` of `r2_chord_core` (WN94: open chord off the polygon, winding number 0 on it), `ExcInside` (all exceptional points are strictly inside the cycle: the printed "C1deg contains all exceptional
-- points", NAMED RESIDUE, not proved here) and the outermost property R1 (`r1_outermost_cycle`, WN84: every Gamma_kite vertex is a vertex of `C` or lies strictly inside).
-- Conclusion (`r2_chord_end`): `W = C k'` is a vertex of the cycle, it is NOT straight and NOT concave (so convex, `0 < sigma * extAng k'`).
-- Route: the end is a vertex of `kiteB` or an exceptional point (`gexc_end_cls`); a point of nonzero winding number cannot be the end of a chord of winding number 0 (`wind_const_segment`); so `W` is a vertex of `C`;
-- if it were concave, the arrival direction (`gexc_arrive_dir` WN92) points into the interior wedge (`chord_arrival_wind_ne` WN93), where the winding number is `sigma <> 0`, but the chord has winding number 0.
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcWN94
import Erdos634.Draft.LaczFormalRG12GExcMatch
import Erdos634.Draft.LaczFormalIIcL8x
import Erdos634.Draft.LaczFormalIIcL8k

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG
open Erdos634.Draft.LaczFormal.WN (edgeSet wind extAng OrientOK)

local notation "tc" => Erdos634.Draft.LaczFormal.WN.toC

variable {N M : ℕ}

theorem rot_neg2' (θ : ℝ) (v : V2) : Graph.rot θ (neg2 v) = neg2 (Graph.rot θ v) := by
  unfold Graph.rot neg2
  ext <;> simp <;> ring

/-- The winding number at the end of a chord of winding number 0 is 0, unless the end lies on the polygon. -/
theorem wind_end_zero {m : ℕ} [NeZero m] (C : Fin m → Plane) (Y W : Plane)
    (hchord : ∀ s : ℝ, 0 < s → s < 1 → tc (Y + s • (W - Y)) ∉ edgeSet (cyc C) ∧ wind (cyc C) (tc (Y + s • (W - Y))) = 0)
    (hW : tc W ∉ edgeSet (cyc C)) : wind (cyc C) (tc W) = 0 := by
  have hmid := (hchord (1 / 2) (by norm_num) (by norm_num)).2
  rw [← hmid]
  symm
  apply Erdos634.Draft.LaczFormal.WN.wind_const_segment
  intro z hz
  rw [segment_eq_image'] at hz
  obtain ⟨t, ⟨ht0, ht1⟩, rfl⟩ := hz
  beta_reduce
  rw [Complex.real_smul]
  have hpt : tc (Y + (1 / 2 : ℝ) • (W - Y)) + (t : ℂ) * (tc W - tc (Y + (1 / 2 : ℝ) • (W - Y))) =
      tc (Y + ((1 + t) / 2) • (W - Y)) := by
    rw [tc_chord_pt, tc_chord_pt]; push_cast; ring
  rw [hpt]
  rcases ht1.lt_or_eq with h | h
  · exact (hchord ((1 + t) / 2) (by linarith) (by linarith)).1
  · subst h
    have : Y + ((1 + 1) / 2 : ℝ) • (W - Y) = W := by
      have : ((1 + 1) / 2 : ℝ) = 1 := by norm_num
      rw [this]; module
    rw [this]; exact hW

set_option maxHeartbeats 6400000 in
/-- **R2, the end of the chord.** -/
theorem r2_chord_end [NeZero N] [NeZero M] (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hC : CaseC D idx) (hab : Comm (slen D 0) (slen D 1)) (hac : ¬ Comm (slen D 0) (slen D 2))
    (h1 : D.model.angleAt 2 < Real.pi / 2) (h3 : D.model.angleAt 2 ≠ Real.pi / 3) (G : AngGen (fun l => D.model.angleAt l))
    (hcor : ∀ j : Fin M, cnt D idx (P.v j) 0 = 1 ∧ cnt D idx (P.v j) 1 = 1 ∧ cnt D idx (P.v j) 2 = 0)
    {m : ℕ} [NeZero m] (C : Fin m → Plane) (hCy : ∀ k : Fin m, GKite D idx (C k) (C (k + 1))) {σ : ℝ} (hO : OrientOK (cyc C) σ)
    (hExc : ∀ E ∈ excVerts2 D idx P, tc E ∉ edgeSet (cyc C) ∧ wind (cyc C) (tc E) ≠ 0)
    (hOut : ∀ v Y, GKite D idx v Y → v ∈ Set.range C ∨ (tc v ∉ edgeSet (cyc C) ∧ wind (cyc C) (tc v) ≠ 0))
    (k : Fin m) {W : Plane} (hW : GExc D idx (C k) W)
    (hchord : ∀ s : ℝ, 0 < s → s < 1 → tc (C k + s • (W - C k)) ∉ edgeSet (cyc C) ∧ wind (cyc C) (tc (C k + s • (W - C k))) = 0) :
    ∃ k' : Fin m, W = C k' ∧ 0 < σ * extAng (cyc C) k' := by
  have hσ : σ = 1 ∨ σ = -1 := hO.1.1
  have hnz : ¬ (tc W ∉ edgeSet (cyc C) ∧ wind (cyc C) (tc W) ≠ 0) := fun h => h.2 (wind_end_zero C (C k) W hchord h.1)
  -- classification of the end
  have hcls := gexc_end_cls D P hreg idx hC hab hac h1 h3 G hcor hW
  have hkB : W ∈ kiteB D idx := by
    rcases hcls with h | h
    · exact h
    · exact absurd (hExc W h) hnz
  have hkB' := hkB
  simp only [kiteB, Finset.mem_filter] at hkB'
  obtain ⟨-, ⟨Z', hWZ⟩, hWstr⟩ := hkB'
  obtain ⟨k', hk'⟩ : W ∈ Set.range C := by
    rcases hOut W Z' hWZ with h | h
    · exact h
    · exact absurd h hnz
  subst hk'
  refine ⟨k', rfl, ?_⟩
  -- not straight, so extAng <> 0
  have hne0 : extAng (cyc C) k' ≠ 0 := by
    intro h0
    exact hWstr ((gkite_cycle_straight_iff D P hreg idx hC h1 h3 G C hCy k').2 h0)
  -- not concave
  have hnc : ¬ σ * extAng (cyc C) k' < 0 := by
    intro hconc
    have hX'Y' : GKite D idx (C (k' - 1)) (C k') := by simpa using hCy (k' - 1)
    have hY'Z' := hCy k'
    have hα := G.pos 0
    have hβ := G.pos 1
    have hγ := G.pos 2
    have hsum := G.sum
    have hne1 : tc (C (k' - 1)) ≠ tc (C k') := fun e => gkite_ne D idx hX'Y' (Erdos634.Draft.LaczFormal.WN.toC.injective e)
    have hne2 : tc (C (k' + 1)) ≠ tc (C k') := fun e => gkite_ne D idx hY'Z' (Erdos634.Draft.LaczFormal.WN.toC.injective e).symm
    have hUW : tc (C k) - tc (C k') ≠ 0 := by
      intro e
      exact gexc_ne D idx hW (Erdos634.Draft.LaczFormal.WN.toC.injective (sub_eq_zero.1 e)).symm
    have hadir := gexc_arrive_dir D P hreg idx hC h1 h3 G hX'Y' hY'Z' hW
    have hnw : 0 < ‖tc (C k) - tc (C k')‖ := norm_pos_iff.2 hUW
    -- the arrival direction, in complex form
    have hnear : ∃ r > 0, ∀ ρ : ℝ, 0 < ρ → ρ < r →
        wind (cyc C) (tc (C k') + (ρ : ℂ) * ((tc (C k) - tc (C k')) / (‖tc (C k) - tc (C k')‖ : ℂ))) = σ := by
      rcases hadir with ⟨hA, hP⟩ | ⟨hB, hP⟩
      · have hP' : Graph.Par (toV2 (C k - C k')) (Graph.rot (D.model.angleAt 0) (toV2 (C k' - C (k' - 1)))) := by
          have e : toV2 (C k' - C (k' - 1)) = neg2 (toV2 (C (k' - 1) - C k')) := toV2_neg_sub _ _
          rw [e, rot_neg2']; exact hP
        obtain ⟨c, hc, hcw⟩ := toC_par_rot hP'
        have hZ := toC_rot hA
        rw [toC_sub, toC_sub] at hZ hcw
        refine Erdos634.Draft.LaczFormal.WN.chord_arrival_wind_ne hO k' hconc hα hβ (by linarith) hne1 hne2 hUW (Or.inl ⟨?_, c, hc, ?_⟩)
        · simpa using hZ
        · rw [hcw]; ring
      · have hP' : Graph.Par (toV2 (C k - C k')) (Graph.rot (D.model.angleAt 1) (toV2 (C k' - C (k' + 1)))) := by
          have e : toV2 (C k' - C (k' + 1)) = neg2 (toV2 (C (k' + 1) - C k')) := toV2_neg_sub _ _
          rw [e, rot_neg2']; exact hP
        obtain ⟨c, hc, hcw⟩ := toC_par_rot hP'
        have hX := toC_rot hB
        rw [toC_sub, toC_sub] at hX hcw
        refine Erdos634.Draft.LaczFormal.WN.chord_arrival_wind_ne hO k' hconc hα hβ (by linarith) hne1 hne2 hUW (Or.inr ⟨?_, c, hc, ?_⟩)
        · simpa using hX
        · rw [hcw]; ring
    obtain ⟨r, hr, hnr⟩ := hnear
    set ρ0 : ℝ := min r ‖tc (C k) - tc (C k')‖ / 2 with hρ0
    have hρ0pos : 0 < ρ0 := by have := lt_min hr hnw; positivity
    have hρ0r : ρ0 < r := by have := min_le_left r ‖tc (C k) - tc (C k')‖; linarith [lt_min hr hnw]
    have hρ0n : ρ0 < ‖tc (C k) - tc (C k')‖ := by have := min_le_right r ‖tc (C k) - tc (C k')‖; linarith [lt_min hr hnw]
    have hs0 : 0 < 1 - ρ0 / ‖tc (C k) - tc (C k')‖ := by
      have := (div_lt_one hnw).2 hρ0n; linarith
    have hs1 : 1 - ρ0 / ‖tc (C k) - tc (C k')‖ < 1 := by
      have : 0 < ρ0 / ‖tc (C k) - tc (C k')‖ := div_pos hρ0pos hnw
      linarith
    have hch := (hchord _ hs0 hs1).2
    have hpt : tc (C k + (1 - ρ0 / ‖tc (C k) - tc (C k')‖) • (C k' - C k)) =
        tc (C k') + (ρ0 : ℂ) * ((tc (C k) - tc (C k')) / (‖tc (C k) - tc (C k')‖ : ℂ)) := by
      rw [tc_chord_pt]
      have : (‖tc (C k) - tc (C k')‖ : ℂ) ≠ 0 := by exact_mod_cast hnw.ne'
      push_cast
      field_simp
      ring
    rw [hpt] at hch
    have := hnr ρ0 hρ0pos hρ0r
    rw [hch] at this
    rcases hσ with h | h <;> rw [h] at this <;> norm_num at this
  rcases hσ with h | h
  · rw [h] at hnc ⊢; rcases lt_or_gt_of_ne hne0 with h' | h'
    · exact absurd (by linarith) hnc
    · linarith
  · rw [h] at hnc ⊢; rcases lt_or_gt_of_ne hne0 with h' | h'
    · linarith
    · exact absurd (by linarith) hnc

#print axioms r2_chord_end

end Erdos634.Draft.LaczFormal.RG
