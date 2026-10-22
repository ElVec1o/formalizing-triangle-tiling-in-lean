-- Draft/LaczFormalIIcWN98.lean -- Laczkovich (DCG 48 (2012), Sect. 6.3, p. 359), Lemma 6.2, R2 ASSEMBLED: the chord family of the concave vertices of an outermost Gamma_kite cycle.
-- `r2_chordfam`: for a closed injective Gamma_kite chain `C` with `OrientOK (cyc C) sigma`, `ExcInside` (NAMED RESIDUE: every exceptional point is off the polygon and has nonzero winding number about it) and the outermost
-- property R1 (WN84), there is `J` with `ChordFam (cyc C) sigma J`: every concave vertex has an exterior chord to a convex vertex, and the closed chords of distinct concave vertices are disjoint.
-- This is exactly the hypothesis of `no_concave` (WN55), so (with R1, R2 and ExcInside) the cycle has no concave vertex.
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcWN97
import Erdos634.Draft.LaczFormalIIcWN55

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG
open Erdos634.Draft.LaczFormal.WN (edgeSet wind extAng OrientOK ChordFam ExtChord)

local notation "tc" => Erdos634.Draft.LaczFormal.WN.toC

variable {N M : ℕ}

set_option maxHeartbeats 6400000 in
theorem r2_chordfam [NeZero N] [NeZero M] (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hC : CaseC D idx) (hab : Comm (slen D 0) (slen D 1)) (hac : ¬ Comm (slen D 0) (slen D 2))
    (h1 : D.model.angleAt 2 < Real.pi / 2) (h3 : D.model.angleAt 2 ≠ Real.pi / 3) (G : AngGen (fun l => D.model.angleAt l))
    (hcor : ∀ j : Fin M, cnt D idx (P.v j) 0 = 1 ∧ cnt D idx (P.v j) 1 = 1 ∧ cnt D idx (P.v j) 2 = 0)
    {m : ℕ} [NeZero m] (C : Fin m → Plane) (hCy : ∀ k : Fin m, GKite D idx (C k) (C (k + 1))) (hinj : Function.Injective C)
    {σ : ℝ} (hO : OrientOK (cyc C) σ)
    (hExc : ∀ E ∈ excVerts2 D idx P, tc E ∉ edgeSet (cyc C) ∧ wind (cyc C) (tc E) ≠ 0)
    (hOut : ∀ v Y, GKite D idx v Y → v ∈ Set.range C ∨ (tc v ∉ edgeSet (cyc C) ∧ wind (cyc C) (tc v) ≠ 0)) :
    ∃ J : Fin m → Fin m, ChordFam (cyc C) σ J := by
  classical
  have key : ∀ k : Fin m, ∃ j : Fin m, σ * extAng (cyc C) k < 0 → (GExc D idx (C k) (C j) ∧
      (∀ s : ℝ, 0 < s → s < 1 → tc (C k + s • (C j - C k)) ∉ edgeSet (cyc C) ∧ wind (cyc C) (tc (C k + s • (C j - C k))) = 0) ∧
      0 < σ * extAng (cyc C) j) := by
    intro k
    by_cases hk : σ * extAng (cyc C) k < 0
    · obtain ⟨W, hW, hchord⟩ := r2_chord_core D P hreg idx hC hab hac h1 h3 G C hCy hO k hk
      obtain ⟨j, hWj, hconv⟩ := r2_chord_end D P hreg idx hC hab hac h1 h3 G hcor C hCy hO hExc hOut k hW hchord
      subst hWj
      exact ⟨j, fun _ => ⟨hW, hchord, hconv⟩⟩
    · exact ⟨k, fun h => absurd h hk⟩
  choose J hJ using key
  refine ⟨J, ?_, ?_⟩
  · intro k hk
    obtain ⟨hW, hchord, -⟩ := hJ k hk
    refine ⟨fun s hs0 hs1 => ?_, ?_⟩
    · have := (hchord s hs0 hs1).1
      rwa [tc_chord_pt] at this
    · have := (hchord (1 / 2) (by norm_num) (by norm_num)).2
      rwa [tc_chord_pt] at this
  · intro k k' hk hk' hkk'
    obtain ⟨hW, hchord, hconv⟩ := hJ k hk
    obtain ⟨hW', hchord', hconv'⟩ := hJ k' hk'
    rw [Set.disjoint_left]
    intro z hz1 hz2
    obtain ⟨V, hV1⟩ : ∃ V : Plane, tc V = z := ⟨Erdos634.Draft.LaczFormal.WN.toC.symm z, by simp⟩
    subst hV1
    have e1 := (Erdos634.Draft.LaczFormal.WN.mem_segment_toC _ _ _).2 hz1
    have e2 := (Erdos634.Draft.LaczFormal.WN.mem_segment_toC _ _ _).2 hz2
    exact chords_disjoint D P hreg idx hC hab hac h1 h3 G C hCy hinj hExc hkk' hk hk' hconv hconv' hW hW'
      (fun s hs0 hs1 => (hchord s hs0 hs1).2) V e1 e2

#print axioms r2_chordfam

end Erdos634.Draft.LaczFormal.RG
