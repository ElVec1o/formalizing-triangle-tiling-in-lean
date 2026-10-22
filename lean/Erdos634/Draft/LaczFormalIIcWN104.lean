-- Draft/LaczFormalIIcWN104.lean -- Laczkovich (DCG 48 (2012), Sect. 6.3, p. 359-360), Lemma 6.2, R3: the Gamma_except chord from a CORNER of the polygon `A` to the outermost cycle `C`.
-- `chord_end_vertex`: the end of a chord of winding number 0 (open part off the polygon) is a non-straight vertex of `C` (kite vertex outside is excluded by R1 `hOut`, exceptional by `ExcInside`).
-- `r3_chord_core`: for every corner `P.v i` there is such a chord (`gexc_start_of_corner`, L4); its open part misses the cycle (`gexc_open_miss_gkite`, WN91) and has winding number 0 (the corner is on the far side of
-- the A-edge line which has all of `C` strictly on its other side: `wind_zero_of_halfplane`, WN101).
-- NOTE, UNAUDITED.  Hypotheses: the Case IIc block + AngGen + hcor.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcWN95
import Erdos634.Draft.LaczFormalIIcWN102
import Erdos634.Draft.LaczFormalIIcWN78
import Erdos634.Draft.LaczFormalRG12GExcCorner

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.WN

variable {n : ℕ} [NeZero n]

theorem edgeSet_sideFn_pos (p : Fin n → ℂ) (a e : ℂ) (hp : ∀ i, 0 < sideFn a e (p i)) : ∀ w ∈ edgeSet p, 0 < sideFn a e w := by
  intro w hw
  unfold edgeSet at hw
  obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hw
  rw [segment_eq_image'] at hi
  obtain ⟨s, ⟨hs0, hs1⟩, rfl⟩ := hi
  beta_reduce
  rw [Complex.real_smul, sideFn_lin]
  have hA := hp i
  have hB := hp (i + 1)
  rcases hs0.eq_or_lt with h0 | h0
  · rw [← h0]; simpa using hA
  · nlinarith [mul_pos h0 hB, mul_nonneg (sub_nonneg.2 hs1) hA.le]

/-- Along a chord whose open part misses the polygon, the winding number is that of the start, for all parameters in `[0, 1)`. -/
theorem wind_const_along_chord (p : Fin n → ℂ) (x y : ℂ) (hx : x ∉ edgeSet p) (hmiss : ∀ s : ℝ, 0 < s → s < 1 → x + (s : ℂ) * (y - x) ∉ edgeSet p) :
    ∀ s : ℝ, 0 ≤ s → s < 1 → wind p (x + (s : ℂ) * (y - x)) = wind p x := by
  intro s0 hs0 hs1
  symm
  apply wind_const_segment
  intro w hw
  rw [segment_eq_image'] at hw
  obtain ⟨u, ⟨hu0, hu1⟩, rfl⟩ := hw
  beta_reduce
  rw [Complex.real_smul]
  have e : x + (u : ℂ) * (x + (s0 : ℂ) * (y - x) - x) = x + ((u * s0 : ℝ) : ℂ) * (y - x) := by push_cast; ring
  rw [e]
  rcases (mul_nonneg hu0 hs0).eq_or_lt with h0 | h0
  · rw [← h0]; simpa using hx
  · exact hmiss _ h0 (by nlinarith)

end Erdos634.Draft.LaczFormal.WN

namespace Erdos634.Draft.LaczFormal.RG
open Erdos634.Draft.LaczFormal.WN (edgeSet wind extAng OrientOK sideFn)

local notation "tc" => Erdos634.Draft.LaczFormal.WN.toC

variable {N M : ℕ}

set_option maxHeartbeats 6400000 in
/-- The end of a chord of winding number 0 is a non-straight vertex of the cycle. -/
theorem chord_end_vertex [NeZero N] [NeZero M] (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hC : CaseC D idx) (hab : Comm (slen D 0) (slen D 1)) (hac : ¬ Comm (slen D 0) (slen D 2))
    (h1 : D.model.angleAt 2 < Real.pi / 2) (h3 : D.model.angleAt 2 ≠ Real.pi / 3) (G : AngGen (fun l => D.model.angleAt l))
    (hcor : ∀ j : Fin M, cnt D idx (P.v j) 0 = 1 ∧ cnt D idx (P.v j) 1 = 1 ∧ cnt D idx (P.v j) 2 = 0)
    {m : ℕ} [NeZero m] (C : Fin m → Plane)
    (hExc : ∀ E ∈ excVerts2 D idx P, tc E ∉ edgeSet (cyc C) ∧ wind (cyc C) (tc E) ≠ 0)
    (hOut : ∀ v Y, GKite D idx v Y → v ∈ Set.range C ∨ (tc v ∉ edgeSet (cyc C) ∧ wind (cyc C) (tc v) ≠ 0))
    {X W : Plane} (hW : GExc D idx X W)
    (hchord : ∀ s : ℝ, 0 < s → s < 1 → tc (X + s • (W - X)) ∉ edgeSet (cyc C) ∧ wind (cyc C) (tc (X + s • (W - X))) = 0) :
    ∃ k' : Fin m, W = C k' ∧ ¬ StraightAt D (C k') := by
  have hnz : ¬ (tc W ∉ edgeSet (cyc C) ∧ wind (cyc C) (tc W) ≠ 0) := fun h => h.2 (wind_end_zero C X W hchord h.1)
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
  exact ⟨k', rfl, hWstr⟩

set_option maxHeartbeats 6400000 in
/-- **R3, the chord from one corner of `A`.** -/
theorem r3_chord_core [NeZero N] [NeZero M] (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hC : CaseC D idx) (hab : Comm (slen D 0) (slen D 1)) (hac : ¬ Comm (slen D 0) (slen D 2))
    (h1 : D.model.angleAt 2 < Real.pi / 2) (h3 : D.model.angleAt 2 ≠ Real.pi / 3) (G : AngGen (fun l => D.model.angleAt l))
    (hcor : ∀ j : Fin M, cnt D idx (P.v j) 0 = 1 ∧ cnt D idx (P.v j) 1 = 1 ∧ cnt D idx (P.v j) 2 = 0)
    {m : ℕ} [NeZero m] (C : Fin m → Plane) (hCy : ∀ k : Fin m, GKite D idx (C k) (C (k + 1)))
    (hExc : ∀ E ∈ excVerts2 D idx P, tc E ∉ edgeSet (cyc C) ∧ wind (cyc C) (tc E) ≠ 0)
    (hOut : ∀ v Y, GKite D idx v Y → v ∈ Set.range C ∨ (tc v ∉ edgeSet (cyc C) ∧ wind (cyc C) (tc v) ≠ 0))
    (hin : ∀ (j : Fin M) (k : Fin m), 0 < sideFn (tc (P.v j)) (tc (P.v (j + 1)) - tc (P.v j)) (tc (C k))) (i : Fin M) :
    ∃ (W : Plane) (k' : Fin m), GExc D idx (P.v i) W ∧ W = C k' ∧ ¬ StraightAt D (C k') ∧
      (∀ s : ℝ, 0 < s → s < 1 → tc (P.v i + s • (W - P.v i)) ∉ edgeSet (cyc C) ∧ wind (cyc C) (tc (P.v i + s • (W - P.v i))) = 0) := by
  obtain ⟨W, hW⟩ := gexc_start_of_corner D P hreg idx hC h1 h3 hcor i
  have he : tc (P.v (i + 1)) - tc (P.v i) ≠ 0 := by
    intro e
    exact Erdos634.Draft.LaczFormal.WN.convPoly_e_ne P i (Erdos634.Draft.LaczFormal.WN.toC.injective (sub_eq_zero.1 e))
  have hp : ∀ k, 0 < sideFn (tc (P.v i)) (tc (P.v (i + 1)) - tc (P.v i)) (cyc C k) := fun k => hin i k
  have hA0 : wind (cyc C) (tc (P.v i)) = 0 :=
    Erdos634.Draft.LaczFormal.WN.wind_zero_of_halfplane (cyc C) _ _ he hp _ (by rw [Erdos634.Draft.LaczFormal.WN.sideFn_base])
  have hAnot : tc (P.v i) ∉ edgeSet (cyc C) := by
    intro hmem
    have := Erdos634.Draft.LaczFormal.WN.edgeSet_sideFn_pos (cyc C) _ _ hp _ hmem
    rw [Erdos634.Draft.LaczFormal.WN.sideFn_base] at this
    exact lt_irrefl _ this
  have hmiss : ∀ s : ℝ, 0 < s → s < 1 → tc (P.v i + s • (W - P.v i)) ∉ edgeSet (cyc C) := by
    intro s hs0 hs1 hmem
    obtain ⟨j, hj⟩ := (mem_edgeSet_cyc C _).1 hmem
    exact gexc_open_miss_gkite D P hreg idx hC hab hac h1 h3 G hW (openseg_pt (P.v i) W hs0 hs1) (hCy j) hj
  have hmiss' : ∀ s : ℝ, 0 < s → s < 1 → tc (P.v i) + (s : ℂ) * (tc W - tc (P.v i)) ∉ edgeSet (cyc C) := by
    intro s hs0 hs1
    rw [← tc_chord_pt]; exact hmiss s hs0 hs1
  have hconst := Erdos634.Draft.LaczFormal.WN.wind_const_along_chord (cyc C) _ _ hAnot hmiss'
  have hchord : ∀ s : ℝ, 0 < s → s < 1 → tc (P.v i + s • (W - P.v i)) ∉ edgeSet (cyc C) ∧ wind (cyc C) (tc (P.v i + s • (W - P.v i))) = 0 := by
    intro s hs0 hs1
    refine ⟨hmiss s hs0 hs1, ?_⟩
    rw [tc_chord_pt, hconst s hs0.le hs1, hA0]
  obtain ⟨k', hk', hstr⟩ := chord_end_vertex D P hreg idx hC hab hac h1 h3 G hcor C hExc hOut hW hchord
  exact ⟨W, k', hW, hk', hstr, hchord⟩

#print axioms chord_end_vertex
#print axioms r3_chord_core

end Erdos634.Draft.LaczFormal.RG
