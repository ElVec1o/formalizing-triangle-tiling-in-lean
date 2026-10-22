-- Draft/LaczFormalIIcWN94.lean -- Laczkovich (DCG 48 (2012), Sect. 6.3, p. 359), Lemma 6.2, R2 (chord family of the concave vertices): the chord at ONE concave vertex.
-- For a closed injective Gamma_kite chain `C` (polygon `cyc C = toC o C`), a sign `sigma` with `OrientOK (cyc C) sigma`, and a concave vertex `k` (`sigma * extAng < 0`), there is an edge `C k -> W` of Gamma_except
-- (fan lemma WN87: a concave vertex is not straight; `gexc_start_dir` WN88) whose OPEN segment misses the polygon (`gexc_open_miss_gkite` WN91) and carries winding number 0 at every point (the local exterior statement
-- `chord_wind_zero_near` WN89, then `wind_const_segment` along the chord).
-- NOTE, UNAUDITED.  Hypotheses: the Case IIc block + AngGen.  No `hExc`/`hOut` needed here.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcWN93
import Erdos634.Draft.LaczFormalIIcWN92
import Erdos634.Draft.LaczFormalIIcWN91
import Erdos634.Draft.LaczFormalIIcWN84

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG
open Erdos634.Draft.LaczFormal.WN (edgeSet wind extAng OrientOK)

local notation "tc" => Erdos634.Draft.LaczFormal.WN.toC

/-- The polygon of a chain. -/
noncomputable abbrev cyc {m : ℕ} (C : Fin m → Plane) : Fin m → ℂ := fun k => tc (C k)

variable {N M : ℕ}

theorem toC_par_rot {u w : Plane} {θ : ℝ} (h : Graph.Par (toV2 u) (Graph.rot θ (toV2 w))) :
    ∃ c : ℝ, 0 < c ∧ tc u = (c : ℂ) * (Complex.exp ((θ : ℂ) * Complex.I) * tc w) := by
  obtain ⟨c, hc, he⟩ := h.smul
  refine ⟨c, hc, ?_⟩
  have h0 : u 0 = c * (Real.cos θ * w 0 - Real.sin θ * w 1) := by
    have := congrArg Prod.fst he; simpa [toV2, Graph.rot] using this
  have h1 : u 1 = c * (Real.sin θ * w 0 + Real.cos θ * w 1) := by
    have := congrArg Prod.snd he; simpa [toV2, Graph.rot] using this
  rw [toC_apply, toC_apply, Complex.exp_mul_I, h0, h1]
  push_cast
  rw [← Complex.ofReal_cos, ← Complex.ofReal_sin]
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

theorem tc_chord_pt (Y W : Plane) (s : ℝ) : tc (Y + s • (W - Y)) = tc Y + (s : ℂ) * (tc W - tc Y) := by
  rw [map_add, map_smul, map_sub, Complex.real_smul]

theorem mem_edgeSet_cyc {m : ℕ} [NeZero m] (C : Fin m → Plane) (V : Plane) :
    tc V ∈ edgeSet (cyc C) ↔ ∃ i : Fin m, V ∈ segment ℝ (C i) (C (i + 1)) := by
  unfold edgeSet
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨i, hi⟩; exact ⟨i, (Erdos634.Draft.LaczFormal.WN.mem_segment_toC _ _ _).2 hi⟩
  · rintro ⟨i, hi⟩; exact ⟨i, (Erdos634.Draft.LaczFormal.WN.mem_segment_toC _ _ _).1 hi⟩

theorem openseg_pt (Y W : Plane) {s : ℝ} (h0 : 0 < s) (h1 : s < 1) : Y + s • (W - Y) ∈ openSegment ℝ Y W :=
  ⟨1 - s, s, by linarith, h0, by ring, by module⟩

set_option maxHeartbeats 6400000 in
/-- **R2, the chord at one concave vertex.** -/
theorem r2_chord_core [NeZero N] [NeZero M] (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hC : CaseC D idx) (hab : Comm (slen D 0) (slen D 1)) (hac : ¬ Comm (slen D 0) (slen D 2))
    (h1 : D.model.angleAt 2 < Real.pi / 2) (h3 : D.model.angleAt 2 ≠ Real.pi / 3) (G : AngGen (fun l => D.model.angleAt l))
    {m : ℕ} [NeZero m] (C : Fin m → Plane) (hCy : ∀ k : Fin m, GKite D idx (C k) (C (k + 1))) {σ : ℝ} (hO : OrientOK (cyc C) σ)
    (k : Fin m) (hconc : σ * extAng (cyc C) k < 0) :
    ∃ W : Plane, GExc D idx (C k) W ∧ ∀ s : ℝ, 0 < s → s < 1 →
      tc (C k + s • (W - C k)) ∉ edgeSet (cyc C) ∧ wind (cyc C) (tc (C k + s • (W - C k))) = 0 := by
  have hXY : GKite D idx (C (k - 1)) (C k) := by simpa using hCy (k - 1)
  have hYZ := hCy k
  have hstr : ¬ StraightAt D (C k) := by
    rw [gkite_cycle_straight_iff D P hreg idx hC h1 h3 G C hCy k]
    intro h; rw [h] at hconc; simp at hconc
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
  have hnear : ∃ r > 0, ∀ ρ : ℝ, 0 < ρ → ρ < r → wind (cyc C) (tc (C k) + (ρ : ℂ) * ((tc W - tc (C k)) / (‖tc W - tc (C k)‖ : ℂ))) = 0 := by
    rcases hcase with ⟨hA, hP⟩ | ⟨hB, hP⟩
    · -- case A
      obtain ⟨c, hc, hcw⟩ := toC_par_rot hP
      have hZ := toC_rot hA
      rw [toC_sub, toC_sub] at hZ hcw
      refine Erdos634.Draft.LaczFormal.WN.chord_wind_zero_near hO k hconc hα hβ (by linarith) hne1 hne2 hWY (Or.inl ⟨?_, c, hc, ?_⟩)
      · simpa using hZ
      · simpa using hcw
    · obtain ⟨c, hc, hcw⟩ := toC_par_rot hP
      have hX := toC_rot hB
      rw [toC_sub, toC_sub] at hX hcw
      refine Erdos634.Draft.LaczFormal.WN.chord_wind_zero_near hO k hconc hα hβ (by linarith) hne1 hne2 hWY (Or.inr ⟨?_, c, hc, ?_⟩)
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
  have hw0 : wind (cyc C) (tc (C k + s0 • (W - C k))) = 0 := by
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

#print axioms r2_chord_core

end Erdos634.Draft.LaczFormal.RG
