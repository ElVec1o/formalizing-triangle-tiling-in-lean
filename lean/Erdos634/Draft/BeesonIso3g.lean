import Erdos634.Draft.BeesonIso3f

/-!
# Beeson, "Tilings of an isosceles triangle" (arXiv 1206.1974 v7), Lemma 11.8: the north walk of a chord

NOTE, UNAUDITED.  Credit: Michael Beeson (arXiv 1206.1974 v7, Lemma 11.8; arXiv 1206.2229), Laczkovich (DCG 48 (2012), Sect. 4: maximal segments, `ends_coincide`),
Beeson-Zhang, Herdt, Zhang.  Formalization debt, not progress on the /goal outcomes.

* `chain_at`: the chain of tiles at a tile vertex `E` in the interior of the side `i` (the fan with one virtual straight sector), with `pT` parallel to the side.
* `both_sides_at_E`: a tile having the chord `E -> F` as an edge on one side gives a tile starting at `E` along the chord on the other side (the ray `d` is an end ray of one
  chain sector, hence the start ray of the next; it is strictly inside the half-plane, so not the last).
* `chord_walk`: a right walk `E -> F` along `d` (the tiles on the `B`-side of the chord) exists and is non-empty; with `ends_coincide` and `exit_F`.
-/

open scoped Classical
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ} [NeZero M]

/-- The chain of tiles at a tile vertex in the interior of a side. -/
theorem chain_at (D : RegionDissection N) (P : ConvPoly M) (hreg : D.region = P.carrier) (i : Fin M) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    {E : Plane} (hE : E = (1 - t) • P.v i + t • P.v (i + 1)) (hvE : ∃ j k, (D.tile j).pts k = E) :
    ∃ pT : V2, Par pT (toV2 (P.e i)) ∧ Nonempty (OpenChain D E pT) := by
  subst hE
  obtain ⟨pT, F, hpd, hpe, hqe, -⟩ := fan_open_edge D P hreg i ht0 ht1 hvE
  exact ⟨pT, hpd, open_chain D F hpd.ne_left hpe hqe hvE⟩

/-- Both sides of the chord at `E`. -/
theorem both_sides_at_E (D : RegionDissection N) (P : ConvPoly M) (hreg : D.region = P.carrier) (i : Fin M) {t t' : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (ht0' : 0 < t') {E F : Plane} (hE : E = (1 - t) • P.v i + t • P.v (i + 1)) (hF : F = (1 - t') • P.v (i + 1) + t' • P.v (i + 1 + 1))
    (hvE : ∃ j k, (D.tile j).pts k = E) {i0 : Fin N} {kE kF : Fin 3} (hkE : (D.tile i0).pts kE = E) (hkF : (D.tile i0).pts kF = F)
    (hEF : E ≠ F) :
    (∃ iL U1, TriStep (D.tile iL) (toV2 (F - E)) E U1) ∧ (∃ iR U2, TriStep (D.tile iR) (neg2 (toV2 (F - E))) U2 E) := by
  obtain ⟨hg1, -, -⟩ := chord_geo P i ht1 ht0' hE hF
  obtain ⟨pT, hpd, ⟨C⟩⟩ := chain_at D P hreg i ht0 ht1 hE hvE
  have hpT : pT ≠ 0 := hpd.ne_left
  have hd : 0 < crs pT (toV2 (F - E)) := crs_pos_par_left hpd.symm hg1
  rcases tile_step D hEF hkE hkF with hS | hS
  · -- the tile i0 is a left step E -> F
    refine ⟨⟨i0, F, hS⟩, ?_⟩
    obtain ⟨s, hs1, hsp, hsc, -⟩ := step_start_sector C.F hS
    obtain ⟨m, hm2, hmL, hmx, hmq⟩ := C.split_p hpT hd hsp
    have hcr := C.hcrs (m - 1) (by omega) (by omega)
    obtain ⟨kc, hkc⟩ := corner_of_crs_pos C.F (C.c (m - 1)) hcr
    obtain ⟨kk, fl, hk, hp', hq'⟩ := spec_corner_data (C.F.hspec (C.c (m - 1))) ⟨kc, hkc⟩
    exact ⟨(C.c (m - 1)).1, _, triStep_of_end kk fl hk hp' hq' hcr hmq⟩
  · -- the tile i0 is a right step F -> E
    refine ⟨?_, ⟨i0, F, hS⟩⟩
    obtain ⟨s, hs1, hsq, hsc, -⟩ := step_end_sector C.F hS
    rw [neg2_neg2] at hsq
    obtain ⟨m, hm1, hmL, hmx, hmp⟩ := C.split_q hpT hd hsq
    have hcr := C.hcrs (m + 1) (by omega) hmL
    obtain ⟨kc, hkc⟩ := corner_of_crs_pos C.F (C.c (m + 1)) hcr
    obtain ⟨kk, fl, hk, hp', hq'⟩ := spec_corner_data (C.F.hspec (C.c (m + 1))) ⟨kc, hkc⟩
    exact ⟨(C.c (m + 1)).1, _, triStep_of_start kk fl hk hp' hq' hcr hmp⟩

/-- **The north walk of a chord.**  A tile with the two vertices `E`, `F` on adjacent open sides gives a non-empty right walk `E -> F` along `d = F - E`. -/
theorem chord_walk (D : RegionDissection N) [HasFansC D] (P : ConvPoly M) (hreg : D.region = P.carrier) (i : Fin M) {t t' : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (ht0' : 0 < t') {E F : Plane} (hE : E = (1 - t) • P.v i + t • P.v (i + 1)) (hF : F = (1 - t') • P.v (i + 1) + t' • P.v (i + 1 + 1))
    {i0 : Fin N} {kE kF : Fin 3} (hkE : (D.tile i0).pts kE = E) (hkF : (D.tile i0).pts kF = F) (hEF : E ≠ F) :
    ∃ LR, WalkR D (toV2 (F - E)) E F LR ∧ LR ≠ [] := by
  have hvE : ∃ j k, (D.tile j).pts k = E := ⟨i0, kE, hkE⟩
  have hd0 : toV2 (F - E) ≠ 0 := toV2_ne_zero (sub_ne_zero.mpr (Ne.symm hEF))
  obtain ⟨⟨iL, U1, hL⟩, ⟨iR, U2, hR⟩⟩ := both_sides_at_E D P hreg i ht0 ht1 ht0' hE hF hvE hkE hkF hEF
  obtain ⟨hexL, hexR⟩ := exit_F D P hreg i ht1 ht0' hE hF
  obtain ⟨Y1, L1, W1, hno1⟩ := exists_maxwalkT D hd0 hvE
  obtain ⟨Y2, L2, W2, hno2⟩ := exists_maxwalkR D hd0 hvE
  have hL1 : L1 ≠ [] := by
    rintro rfl
    cases W1
    exact hno1 iL U1 hL
  have hL2 : L2 ≠ [] := by
    rintro rfl
    cases W2
    exact hno2 iR U2 hR
  have hY : Y1 = Y2 := ends_coincide D hd0 hL1 hL2 W1 W2 hno1 hno2
  subst hY
  rcases tile_step D hEF hkE hkF with hS | hS
  · -- the left walk begins with the tile i0, then stops at F
    obtain ⟨i1, X0, X1, Lt, rfl⟩ : ∃ i1 X0 X1 Lt, L1 = (i1, X0, X1) :: Lt := by
      cases L1 with
      | nil => exact absurd rfl hL1
      | cons e Lt => exact ⟨e.1, e.2.1, e.2.2, Lt, rfl⟩
    cases W1 with
    | cons hS1 W1' =>
      obtain ⟨-, hX1⟩ := left_step_unique D hS1 hS
      subst hX1
      have hLt : Lt = [] := by
        cases Lt with
        | nil => rfl
        | cons e Lt' =>
          exfalso
          cases W1' with
          | cons hS2 _ => exact hexL _ _ hS2
      subst hLt
      cases W1'
      exact ⟨L2, W2, hL2⟩
  · obtain ⟨i1, X0, X1, Lt, rfl⟩ : ∃ i1 X0 X1 Lt, L2 = (i1, X0, X1) :: Lt := by
      cases L2 with
      | nil => exact absurd rfl hL2
      | cons e Lt => exact ⟨e.1, e.2.1, e.2.2, Lt, rfl⟩
    cases W2 with
    | cons hS1 W2' =>
      obtain ⟨-, hX1⟩ := right_step_unique D hS1 hS
      subst hX1
      have hLt : Lt = [] := by
        cases Lt with
        | nil => rfl
        | cons e Lt' =>
          exfalso
          cases W2' with
          | cons hS2 _ => exact hexR _ _ hS2
      subst hLt
      cases W2'
      exact ⟨_, WalkR.cons hS1 (WalkR.nil _), by simp⟩

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.chord_walk
