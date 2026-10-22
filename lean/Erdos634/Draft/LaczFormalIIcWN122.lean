-- Draft/LaczFormalIIcWN122.lean -- Laczkovich (DCG 48 (2012), Sect. 6.3, p. 358-359), Lemma 6.2, `ExcInsideAll` step (ii): the Gamma_except edge at a CONVEX vertex of a cycle runs through the interior and ends at a CONCAVE vertex of the cycle or at an exceptional point.
-- `r2c_chord_core`: for a convex vertex `k` (`0 < sigma * extAng`) there is an edge `C k -> W` of Gamma_except whose open segment misses the polygon and has winding number `sigma` (mirror of WN94).
-- `r2c_chord_end`: if no Gamma_kite vertex lies strictly inside the cycle (printed: "we may assume that C-degree does not contain any vertex of Gamma_kite"), the end `W` is a CONCAVE vertex of `C` or an exceptional point (mirror of WN95; printed (i)-(iii) p. 358).
-- NOTE, UNAUDITED.  Hypotheses: the Case IIc block + AngGen.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcWN121
import Erdos634.Draft.LaczFormalIIcWN95
import Erdos634.Draft.LaczFormalIIcWN94

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG
open Erdos634.Draft.LaczFormal.WN (edgeSet wind extAng OrientOK)

local notation "tc" => Erdos634.Draft.LaczFormal.WN.toC

variable {N M : ℕ}

set_option maxHeartbeats 6400000 in
/-- **ExcInsideAll (b), the chord at one CONVEX vertex: it runs through the interior (winding number `sigma`).** -/
theorem r2c_chord_core [NeZero N] [NeZero M] (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hC : CaseC D idx) (hab : Comm (slen D 0) (slen D 1)) (hac : ¬ Comm (slen D 0) (slen D 2))
    (h1 : D.model.angleAt 2 < Real.pi / 2) (h3 : D.model.angleAt 2 ≠ Real.pi / 3) (G : AngGen (fun l => D.model.angleAt l))
    {m : ℕ} [NeZero m] (C : Fin m → Plane) (hCy : ∀ k : Fin m, GKite D idx (C k) (C (k + 1))) {σ : ℝ} (hO : OrientOK (cyc C) σ)
    (k : Fin m) (hconv : 0 < σ * extAng (cyc C) k) :
    ∃ W : Plane, GExc D idx (C k) W ∧ ∀ s : ℝ, 0 < s → s < 1 →
      tc (C k + s • (W - C k)) ∉ edgeSet (cyc C) ∧ wind (cyc C) (tc (C k + s • (W - C k))) = σ := by
  have hXY : GKite D idx (C (k - 1)) (C k) := by simpa using hCy (k - 1)
  have hYZ := hCy k
  have hstr : ¬ StraightAt D (C k) := by
    rw [gkite_cycle_straight_iff D P hreg idx hC h1 h3 G C hCy k]
    intro h; rw [h] at hconv; simp at hconv
  obtain ⟨W, hW, hcase⟩ := gexc_start_dir D P hreg idx hC h1 h3 G hXY hYZ hstr
  refine ⟨W, hW, ?_⟩
  -- the chord misses the polygon
  have hmiss : ∀ s : ℝ, 0 < s → s < 1 → tc (C k + s • (W - C k)) ∉ edgeSet (cyc C) := by
    intro s hs0 hs1 hmem
    obtain ⟨i, hi⟩ := (mem_edgeSet_cyc C _).1 hmem
    exact gexc_open_miss_gkite D P hreg idx hC hab hac h1 h3 G hW (openseg_pt (C k) W hs0 hs1) (hCy i) hi
  -- the local exterior statement near the vertex
  have hα := G.pos 0
  have hβ := G.pos 1
  have hγ := G.pos 2
  have hsum := G.sum
  have hne1 : tc (C (k - 1)) ≠ tc (C k) := fun e => gkite_ne D idx hXY (Erdos634.Draft.LaczFormal.WN.toC.injective e)
  have hne2 : tc (C (k + 1)) ≠ tc (C k) := fun e => gkite_ne D idx hYZ (Erdos634.Draft.LaczFormal.WN.toC.injective e).symm
  have hWY : tc W - tc (C k) ≠ 0 := by
    have hP0 : toV2 (W - C k) ≠ 0 := by
      rcases hcase with ⟨-, hP⟩ | ⟨-, hP⟩
      · exact hP.ne_left
      · exact hP.ne_left
    intro e
    apply hP0
    have : W = C k := Erdos634.Draft.LaczFormal.WN.toC.injective (sub_eq_zero.1 e)
    rw [this, sub_self]; unfold toV2; ext <;> simp
  have hnear : ∃ r > 0, ∀ ρ : ℝ, 0 < ρ → ρ < r → wind (cyc C) (tc (C k) + (ρ : ℂ) * ((tc W - tc (C k)) / (‖tc W - tc (C k)‖ : ℂ))) = σ := by
    rcases hcase with ⟨hA, hP⟩ | ⟨hB, hP⟩
    · -- case A
      obtain ⟨c, hc, hcw⟩ := toC_par_rot hP
      have hZ := toC_rot hA
      rw [toC_sub, toC_sub] at hZ hcw
      refine Erdos634.Draft.LaczFormal.WN.chord_wind_ne_near hO k hconv hα hβ (by linarith) hne1 hne2 hWY (Or.inl ⟨?_, c, hc, ?_⟩)
      · simpa using hZ
      · simpa using hcw
    · obtain ⟨c, hc, hcw⟩ := toC_par_rot hP
      have hX := toC_rot hB
      rw [toC_sub, toC_sub] at hX hcw
      refine Erdos634.Draft.LaczFormal.WN.chord_wind_ne_near hO k hconv hα hβ (by linarith) hne1 hne2 hWY (Or.inr ⟨?_, c, hc, ?_⟩)
      · simpa using hX
      · simpa using hcw
  obtain ⟨r, hr, hnr⟩ := hnear
  have hnW : 0 < ‖tc W - tc (C k)‖ := norm_pos_iff.2 hWY
  -- a point of the chord near the vertex with winding number 0
  set ρ0 : ℝ := min r (‖tc W - tc (C k)‖) / 2 with hρ0
  have hρ0pos : 0 < ρ0 := by positivity
  have hρ0r : ρ0 < r := by have := min_le_left r ‖tc W - tc (C k)‖; linarith [lt_min hr hnW]
  have hρ0n : ρ0 < ‖tc W - tc (C k)‖ := by have := min_le_right r ‖tc W - tc (C k)‖; linarith [lt_min hr hnW]
  set s0 : ℝ := ρ0 / ‖tc W - tc (C k)‖ with hs0
  have hs0pos : 0 < s0 := div_pos hρ0pos hnW
  have hs01 : s0 < 1 := (div_lt_one hnW).2 hρ0n
  have hw0 : wind (cyc C) (tc (C k + s0 • (W - C k))) = σ := by
    rw [tc_chord_pt]
    have := hnr ρ0 hρ0pos hρ0r
    convert this using 2
    rw [hs0]
    have : (‖tc W - tc (C k)‖ : ℂ) ≠ 0 := by exact_mod_cast hnW.ne'
    push_cast
    field_simp
  intro s hs hs1
  refine ⟨hmiss s hs hs1, ?_⟩
  rw [← hw0]
  symm
  apply Erdos634.Draft.LaczFormal.WN.wind_const_segment
  intro z hz
  rw [segment_eq_image'] at hz
  obtain ⟨t, ⟨ht0, ht1⟩, rfl⟩ := hz
  -- the point lies on the chord strictly between the two parameters
  have hpt : tc (C k + s0 • (W - C k)) + (t : ℂ) * (tc (C k + s • (W - C k)) - tc (C k + s0 • (W - C k))) =
      tc (C k + ((1 - t) * s0 + t * s) • (W - C k)) := by
    rw [tc_chord_pt, tc_chord_pt, tc_chord_pt]; push_cast; ring
  beta_reduce
  rw [Complex.real_smul]
  rw [hpt]
  apply hmiss
  · have h1' : (1 - t) * min s0 s ≤ (1 - t) * s0 := mul_le_mul_of_nonneg_left (min_le_left _ _) (by linarith)
    have h2' : t * min s0 s ≤ t * s := mul_le_mul_of_nonneg_left (min_le_right _ _) ht0
    have : 0 < min s0 s := lt_min hs0pos hs
    nlinarith
  · have h1' : (1 - t) * s0 ≤ (1 - t) * max s0 s := mul_le_mul_of_nonneg_left (le_max_left _ _) (by linarith)
    have h2' : t * s ≤ t * max s0 s := mul_le_mul_of_nonneg_left (le_max_right _ _) ht0
    have : max s0 s < 1 := max_lt hs01 hs1
    nlinarith

/-- The winding number at the end of a chord of constant winding number `c` is `c`, unless the end lies on the polygon. -/
theorem wind_end_eq {m : ℕ} [NeZero m] (C : Fin m → Plane) (Y W : Plane) (c : ℝ)
    (hchord : ∀ s : ℝ, 0 < s → s < 1 → tc (Y + s • (W - Y)) ∉ edgeSet (cyc C) ∧ wind (cyc C) (tc (Y + s • (W - Y))) = c)
    (hW : tc W ∉ edgeSet (cyc C)) : wind (cyc C) (tc W) = c := by
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
/-- **ExcInsideAll (b), the end of the chord of a convex vertex.** -/
theorem r2c_chord_end [NeZero N] [NeZero M] (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hC : CaseC D idx) (hab : Comm (slen D 0) (slen D 1)) (hac : ¬ Comm (slen D 0) (slen D 2))
    (h1 : D.model.angleAt 2 < Real.pi / 2) (h3 : D.model.angleAt 2 ≠ Real.pi / 3) (G : AngGen (fun l => D.model.angleAt l))
    (hcor : ∀ j : Fin M, cnt D idx (P.v j) 0 = 1 ∧ cnt D idx (P.v j) 1 = 1 ∧ cnt D idx (P.v j) 2 = 0)
    {m : ℕ} [NeZero m] (C : Fin m → Plane) (hCy : ∀ k : Fin m, GKite D idx (C k) (C (k + 1))) {σ : ℝ} (hO : OrientOK (cyc C) σ)
    (hK : ∀ v Y, GKite D idx v Y → tc v ∈ edgeSet (cyc C) ∨ wind (cyc C) (tc v) = 0)
    (k : Fin m) {W : Plane} (hW : GExc D idx (C k) W)
    (hchord : ∀ s : ℝ, 0 < s → s < 1 → tc (C k + s • (W - C k)) ∉ edgeSet (cyc C) ∧ wind (cyc C) (tc (C k + s • (W - C k))) = σ) :
    (∃ k' : Fin m, W = C k' ∧ σ * extAng (cyc C) k' < 0) ∨ W ∈ excVerts2 D idx P := by
  have hσ : σ = 1 ∨ σ = -1 := hO.1.1
  have hσ0 : σ ≠ 0 := by rcases hσ with h | h <;> rw [h] <;> norm_num
  have hcls := gexc_end_cls D P hreg idx hC hab hac h1 h3 G hcor hW
  rcases hcls with hkB | hexc
  swap
  · right; exact hexc
  left
  have hkB' := hkB
  simp only [kiteB, Finset.mem_filter] at hkB'
  obtain ⟨-, ⟨Z', hWZ⟩, hWstr⟩ := hkB'
  obtain ⟨k', hk'⟩ : W ∈ Set.range C := by
    by_contra hnr
    obtain ⟨m', hm', C', hC'0, hC'inj, hC'y⟩ := gkite_cycle_exists D P hreg idx hC hab hac h1 h3 hWZ
    have hsh : ∀ j k, C' j ≠ C k := by
      intro j k hjk
      apply hnr
      have := chain_mem_of_share D P hreg idx hC h1 h3 C C' hCy hC'y hjk
      rwa [hC'0] at this
    have hd := gkite_cycles_edge_disjoint D idx C C' hCy hC'y hsh
    have hv : tc W ∈ edgeSet (cyc C') := by
      have := Erdos634.Draft.LaczFormal.WN.vertex_mem_edgeSet (cyc C') 0
      simpa [cyc, hC'0] using this
    have hWoff : tc W ∉ edgeSet (cyc C) := Set.disjoint_right.1 hd hv
    have hwσ := wind_end_eq C (C k) W σ hchord hWoff
    rcases hK W Z' hWZ with h | h
    · exact hWoff h
    · exact hσ0 (hwσ.symm.trans h)
  subst hk'
  refine ⟨k', rfl, ?_⟩
  have hne0 : extAng (cyc C) k' ≠ 0 := by
    intro h0
    exact hWstr ((gkite_cycle_straight_iff D P hreg idx hC h1 h3 G C hCy k').2 h0)
  -- not convex
  have hnc : ¬ 0 < σ * extAng (cyc C) k' := by
    intro hconv
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
        wind (cyc C) (tc (C k') + (ρ : ℂ) * ((tc (C k) - tc (C k')) / (‖tc (C k) - tc (C k')‖ : ℂ))) = 0 := by
      rcases hadir with ⟨hA, hP⟩ | ⟨hB, hP⟩
      · have hP' : Graph.Par (toV2 (C k - C k')) (Graph.rot (D.model.angleAt 0) (toV2 (C k' - C (k' - 1)))) := by
          have e : toV2 (C k' - C (k' - 1)) = neg2 (toV2 (C (k' - 1) - C k')) := toV2_neg_sub _ _
          rw [e, rot_neg2']; exact hP
        obtain ⟨c, hc, hcw⟩ := toC_par_rot hP'
        have hZ := toC_rot hA
        rw [toC_sub, toC_sub] at hZ hcw
        refine Erdos634.Draft.LaczFormal.WN.chord_arrival_wind_zero hO k' hconv hα hβ (by linarith) hne1 hne2 hUW (Or.inl ⟨?_, c, hc, ?_⟩)
        · simpa using hZ
        · rw [hcw]; ring
      · have hP' : Graph.Par (toV2 (C k - C k')) (Graph.rot (D.model.angleAt 1) (toV2 (C k' - C (k' + 1)))) := by
          have e : toV2 (C k' - C (k' + 1)) = neg2 (toV2 (C (k' + 1) - C k')) := toV2_neg_sub _ _
          rw [e, rot_neg2']; exact hP
        obtain ⟨c, hc, hcw⟩ := toC_par_rot hP'
        have hX := toC_rot hB
        rw [toC_sub, toC_sub] at hX hcw
        refine Erdos634.Draft.LaczFormal.WN.chord_arrival_wind_zero hO k' hconv hα hβ (by linarith) hne1 hne2 hUW (Or.inr ⟨?_, c, hc, ?_⟩)
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
  have hne' : σ * extAng (cyc C) k' ≠ 0 := by
    intro h0
    rcases hσ with h | h <;> rw [h] at h0 <;> simp at h0 <;> exact hne0 h0
  exact lt_of_le_of_ne (not_lt.1 hnc) hne'


#print axioms r2c_chord_core
#print axioms r2c_chord_end

end Erdos634.Draft.LaczFormal.RG
