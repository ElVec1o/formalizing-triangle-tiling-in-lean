-- Draft/LaczFormalRG12GExcEnd.lean -- Laczkovich (DCG 48 (2012)), Sect. 6.2, Gamma_except, lemma L7: **statement (ii)**.  For an edge `XY` of Gamma_except, `Y` is a vertex of Gamma_kite (it is the tail of an edge of Gamma_kite) or `Y` is an
-- exceptional point (`excVerts2`: a non-polygon vertex with `p < r`).
-- Route (paper l. 1353-1370, with the repairs of the blueprint): `gexc_end_split` gives the local data at `Y` on both sides of the line; if `p < r` at `Y`, `Y` is exceptional (`caseII_nonpoly`, `Y` is not a polygon corner because it carries a `gamma`
-- corner and polygon corners have `cnt = (1,1,0)`).  Otherwise `p = r`: (a) `Y` is the head of a left and of a right tile (two `gamma` corners): `Y` is an interior (2,2,2) vertex (`caseII_nonpoly`, angle sum) and `sc1_core` gives a kite vertex;
-- (b) `Y` is an inner point of a side of a tile on the other side: `sc2_left` / `sc2_right` (contradiction).
-- Hypotheses: `CaseC`, `HasFansC`, `D.region = P.carrier`, `a,b` commensurable, `a,c` not, gamma < pi/2, != pi/3, `AngGen`, and `hcor` (every polygon vertex has counts `(1,1,0)`, the branch `P = N` of `lemma61_core`, as in `gexc_start_of_corner`).
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.2), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalRG12GExcEndT
import Erdos634.Draft.LaczFormalRG12GExcCRay

namespace Erdos634.Draft.LaczFormal.RG

set_option synthInstance.maxSize 4000 in
theorem fin3_cases4 : ∀ a b c e : Fin 3, a ≠ b → a ≠ c → b ≠ c → e ≠ a → e = b ∨ e = c := by decide
set_option synthInstance.maxSize 4000 in
theorem fin3_cases5 : ∀ a b c e : Fin 3, a ≠ b → a ≠ c → b ≠ c → e ≠ a → e ≠ b → e = c := by decide

end Erdos634.Draft.LaczFormal.RG

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ}

/-- A tile cannot have a side ending at `Y` along `d` and a side starting at `Y` along `-d`. -/
theorem triStep_lr_false {T : Tri} {d : V2} {A Y A' : Plane} (h1 : TriStep T d A Y) (h2 : TriStep T (neg2 d) Y A') : False := by
  obtain ⟨kk, f, g, hk, hf, hfk, hgk, hgf, hpar, hleft⟩ := id h1
  obtain ⟨kk', f', g', hk', hf', hfk', hgk', hgf', hpar', hleft'⟩ := id h2
  have e1 : kk' = f := T.indep.injective (hk'.trans hf.symm)
  subst e1
  have hf'ne : f' ≠ kk' := hfk'
  rcases fin3_cases4 kk' kk g f' hfk hgf.symm hgk.symm hf'ne with h | h
  · -- f' = kk: the two sides coincide
    have hA : A' = A := by rw [← hf', h, hk]
    rw [hA] at h2
    exact triStep_not_both h1 h2
  · -- f' = g: then g' = kk, which lies on the line
    have hg' : g' = kk := fin3_cases5 kk' g kk g' hgf.symm hfk hgk hgk' (by rw [← h]; exact hgf')
    have h0 := hpar.1
    rw [hg', hk] at hleft'
    unfold crs at hleft' h0
    simp only [toV2_sub, neg2] at hleft' h0
    nlinarith

theorem cnt_pos_of_corner {D : CongruentRegionDissection N} {idx : Fin N → Equiv.Perm (Fin 3)} {Y : Plane} {i : Fin N} {k : Fin 3} {l : Fin 3}
    (h1 : (D.tile i).pts k = Y) (h2 : idx i k = l) : 0 < cnt D idx Y l := by
  unfold cnt
  exact Finset.card_pos.mpr ⟨(i, k), by simp [h1, h2]⟩

set_option maxHeartbeats 6400000 in
/-- **The case of two `gamma` heads**: `Y` interior (2,2,2) and `sc1_core`. -/
theorem sc1_wrap [NeZero M] (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hC : CaseC D idx) (hab : Comm (slen D 0) (slen D 1)) (hac : ¬ Comm (slen D 0) (slen D 2))
    (h1 : D.model.angleAt 2 < Real.pi / 2) (h3 : D.model.angleAt 2 ≠ Real.pi / 3) (G : AngGen (fun l => D.model.angleAt l))
    {Y : Plane} {d : V2} (hvert : ∃ j k, (D.tile j).pts k = Y) (hnc : ∀ k : Fin M, Y ≠ P.v (k + 1)) (hnorm : cnt D idx Y 0 = cnt D idx Y 2)
    {iL iR : Fin N} {A A' : Plane} (hL : TriStep (D.tile iL) d A Y) (hLg : ∃ k, (D.tile iL).pts k = Y ∧ idx iL k = 2)
    (hR : TriStep (D.tile iR) (neg2 d) Y A') (hRg : ∃ k, (D.tile iR).pts k = Y ∧ idx iR k = 2)
    (hcont : (∀ i U', TriStep (D.tile i) d Y U' → ¬ ∃ k, (D.tile i).pts k = U' ∧ idx i k = 2) ∨
      (∀ i U', TriStep (D.tile i) (neg2 d) U' Y → ¬ ∃ k, (D.tile i).pts k = U' ∧ idx i k = 2)) :
    ∃ Z, GKite D idx Y Z := by
  classical
  have hij : iL ≠ iR := fun h => by subst h; exact triStep_lr_false hL hR
  obtain ⟨kL, hkL, hkL2⟩ := hLg
  obtain ⟨kR, hkR, hkR2⟩ := hRg
  have h2c : 2 ≤ cnt D idx Y 2 := two_le_cnt hij hkL hkL2 hkR hkR2
  obtain ⟨-, -, hn⟩ := caseII_nonpoly D P hreg idx hC.hidxA hC.hregc h1 h3 hvert hnc
  have hint : Y ∈ interior D.region := by
    by_contra hni
    have := hn hnorm.symm hni
    omega
  obtain ⟨F⟩ := extFan_interior D.toRegionDissection Y hvert hint
  have hang := head_angle_sum D idx hC.hidxA F inferInstance
  rw [Fin.sum_univ_three, hnorm, ← hC.hregc Y, hnorm] at hang
  have hs := G.sum
  have hp := Real.pi_pos
  simp only at hs
  have h2R : (2 : ℝ) ≤ (cnt D idx Y 2 : ℝ) := by exact_mod_cast h2c
  have hk0 : (0 : ℝ) ≤ ((Strn D.toRegionDissection Y).card : ℝ) := Nat.cast_nonneg _
  have hle : (cnt D idx Y 2 : ℝ) ≤ 2 := by nlinarith
  have hc2 : cnt D idx Y 2 = 2 := by
    have : cnt D idx Y 2 ≤ 2 := by exact_mod_cast hle
    omega
  have c0 : cnt D idx Y 0 = 2 := by rw [hnorm]; exact hc2
  have c1 : cnt D idx Y 1 = 2 := by rw [← hC.hregc Y]; exact c0
  exact sc1_core D P hreg idx hC hab hac h1 h3 G hint c0 c1 hc2 hL ⟨kL, hkL, hkL2⟩ hR ⟨kR, hkR, hkR2⟩ hcont

/-- **L7: statement (ii) of Lemma 6.2 for `Gamma_except`.** -/
theorem gexc_end_kite_or_exc [NeZero M] (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hC : CaseC D idx) (hab : Comm (slen D 0) (slen D 1)) (hac : ¬ Comm (slen D 0) (slen D 2))
    (h1 : D.model.angleAt 2 < Real.pi / 2) (h3 : D.model.angleAt 2 ≠ Real.pi / 3) (G : AngGen (fun l => D.model.angleAt l))
    (hcor : ∀ j : Fin M, cnt D idx (P.v j) 0 = 1 ∧ cnt D idx (P.v j) 1 = 1 ∧ cnt D idx (P.v j) 2 = 0) {X Y : Plane} (hE : GExc D idx X Y) :
    (∃ Z, GKite D idx Y Z) ∨ Y ∈ excVerts2 D idx P := by
  classical
  obtain ⟨d, hd, EL, ER, hrun⟩ := gexc_end_split D idx hE
  -- a gamma corner at Y
  obtain ⟨i0, k0, hk0, hk02⟩ : ∃ i k, (D.tile i).pts k = Y ∧ idx i k = 2 := by
    rcases hrun with ⟨⟨iL, A, hL, hLg⟩, -⟩ | ⟨⟨iR, A, hR, hRg⟩, -⟩
    · exact ⟨iL, hLg.choose, hLg.choose_spec⟩
    · exact ⟨iR, hRg.choose, hRg.choose_spec⟩
  have hvert : ∃ j k, (D.tile j).pts k = Y := ⟨i0, k0, hk0⟩
  have hcnt2 : 0 < cnt D idx Y 2 := cnt_pos_of_corner hk0 hk02
  have hnc : ∀ k : Fin M, Y ≠ P.v (k + 1) := by
    intro k hk
    have := (hcor (k + 1)).2.2
    rw [← hk] at this
    omega
  obtain ⟨hle, -, -⟩ := caseII_nonpoly D P hreg idx hC.hidxA hC.hregc h1 h3 hvert hnc
  by_cases hlt : cnt D idx Y 0 < cnt D idx Y 2
  · right
    unfold excVerts2
    simp only [Finset.mem_filter, Finset.mem_sdiff]
    exact ⟨⟨mem_vtxSet.mpr hvert, fun hp => by obtain ⟨k, hk⟩ := mem_polyVerts.mp hp; exact hnc k hk⟩, hlt⟩
  · left
    have hnorm : cnt D idx Y 0 = cnt D idx Y 2 := by omega
    rcases hrun with ⟨⟨iL0, A0, hL0, hLg0⟩, hcL⟩ | ⟨⟨iR0, A0, hR0, hRg0⟩, hcR⟩
    · obtain ⟨iR, A', B', hR, hcase⟩ := ER
      rcases hcase with ⟨hYB, hRg⟩ | hin
      · rw [← hYB] at hR
        exact sc1_wrap D P hreg idx hC hab hac h1 h3 G hvert hnc hnorm hL0 hLg0 hR hRg (Or.inl hcL)
      · exact (sc2_left D P hreg idx hC hab hac G hnorm hL0 hLg0 hR hin hcL).elim
    · obtain ⟨iL, A', B', hL, hcase⟩ := EL
      rcases hcase with ⟨hYB, hLg⟩ | hin
      · rw [← hYB] at hL
        exact sc1_wrap D P hreg idx hC hab hac h1 h3 G hvert hnc hnorm hL hLg hR0 hRg0 (Or.inr hcR)
      · exact (sc2_right D P hreg idx hC hab hac G hnorm hR0 hRg0 hL hin hcR).elim

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.gexc_end_kite_or_exc
