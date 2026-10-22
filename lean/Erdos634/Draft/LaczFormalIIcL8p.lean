-- Draft/LaczFormalIIcL8p.lean -- Laczkovich (DCG 48 (2012)), Sect. 6.3, L8 `gexc_disjoint`, step 9: the THROUGH-edge at an exceptional point.
--  `arrData_or_lineD_of_split`: the proof of `arrData_or_lineD` from the local data (direction, NoBack, a walk to `E`, EndLeftG, EndRightG) alone.
--  `thru_arr_or_lineD`: for an edge `X -> Y` and an inner point `E` of it at which `cnt alpha < cnt gamma` the through edge `X` has the same data at `E` as an arrival: `ArrData` (two `gamma` sectors flanking the back ray) or `LineD`.
--  (If both divisions have `E` inside a tile side, two tiles of `Strn E` are produced, contradicting `strn_card_le_one`.)
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcL8o
import Erdos634.Draft.LaczFormalIIcSharp3

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ}

theorem arrData_or_lineD_of_split (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (idx : Fin N → Equiv.Perm (Fin 3)) {E : Plane} {κ : Type} [Fintype κ]
    (F : ExtFan D.toRegionDissection E κ) {X : Plane} {d : V2} (hd : d ≠ 0) (hnb : NoBack D.toRegionDissection d X)
    (hw : ∃ (bl : Bool) (P : List (Fin N × Plane × Plane)), WalkU D.toRegionDissection bl d X E P ∧ P ≠ [])
    (hL : EndLeftG D idx d E) (hR : EndRightG D idx d E) :
    (∃ aL aR : AtV D.toRegionDissection E, ArrData D idx F X aL aR) ∨ LineD D idx X E := by
  obtain ⟨bl, P, hw, hP⟩ := hw
  obtain ⟨iL, A, B, hL, hcL⟩ := hL
  obtain ⟨iR, A', B', hR, hcR⟩ := hR
  rcases hcL with ⟨hYB, hLg⟩ | ⟨hin, kγ, hkγ, hkγ2⟩
  swap
  · right
    obtain ⟨kk, f, g, hk, hf, hfk, hgk, hgf, hpar, -⟩ := id hL
    have hkf : kγ = f := (D.tile iL).indep.injective (hkγ.trans hf.symm)
    subst hkf
    exact ⟨d, bl, P, iL, A, B, kk, kγ, hd, hnb, hw, hP, strn_of_inner hL hin, hin, hpar, hk, hf, fun e => hfk e.symm, hkγ2⟩
  rcases hcR with ⟨hYB', hRg⟩ | ⟨hin', kγ', hkγ', hkγ2'⟩
  swap
  · right
    obtain ⟨kk, f, g, hk, hf, hfk, hgk, hgf, hpar, -⟩ := id hR
    have hkf : kγ' = kk := (D.tile iR).indep.injective (hkγ'.trans hk.symm)
    subst hkf
    have hin2 : E ∈ openSegment ℝ B' A' := by rw [openSegment_symm]; exact hin'
    have hpar2 : Par (toV2 (B' - A')) d := by
      have := par_neg hpar
      have e1 : ((-(toV2 (A' - B')).1, -(toV2 (A' - B')).2) : V2) = toV2 (B' - A') := by simp [toV2]
      have e2 : ((-(neg2 d).1, -(neg2 d).2) : V2) = d := by simp [neg2]
      rwa [e1, e2] at this
    exact ⟨d, bl, P, iR, A', B', f, kγ', hd, hnb, hw, hP, strn_of_inner hR hin2, hin', hpar2, hf, hk, hfk, hkγ2'⟩
  left
  rw [← hYB] at hL
  rw [← hYB'] at hR
  obtain ⟨x, hxi, hxq⟩ := sec_end F hL
  obtain ⟨x2, hx2i, hx2p⟩ := sec_start F hR
  obtain ⟨kL, hkL, hkL2⟩ := hLg
  obtain ⟨kR, hkR, hkR2⟩ := hRg
  exact ⟨x, x2, d, hd, hnb, ⟨bl, P, hw, hP⟩, hxq, hx2p, ⟨kL, by rw [hxi]; exact hkL, by rw [hxi]; exact hkL2⟩, ⟨kR, by rw [hx2i]; exact hkR, by rw [hx2i]; exact hkR2⟩⟩

/-- a tile cannot have `E` in the open side of a side traversed along `d` (tile on the left) and in the open side of a side traversed along `-d` (tile on the left of `-d`). -/
theorem not_both_inner (T : Tri) {d : V2} (hd : d ≠ 0) {A B A' B' E : Plane} (h1 : TriStep T d A B) (h2 : TriStep T (neg2 d) B' A')
    (hE1 : E ∈ openSegment ℝ A B) (hE2 : E ∈ openSegment ℝ A' B') : False := by
  obtain ⟨kk, f, g, hk, hf, hfk, hgk, hgf, hpar, hleft⟩ := h1
  obtain ⟨kk', f', g', hk', hf', hfk', hgk', hgf', hpar', hleft'⟩ := h2
  rcases tri_inner_side_unique T (a := kk) (b := f) (a' := f') (b' := kk') (fun h => hfk h.symm) (fun h => hfk' h) hk hf hf' hk' hE1 hE2 with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · -- the same side traversed in the two directions: kk = f', f = kk'
    subst e1; subst e2
    subst hk; subst hf; subst hf'; subst hk'
    have hg : g = g' := by
      revert hgk hgf hgk' hgf' hfk; fin_cases kk <;> fin_cases f <;> fin_cases g <;> fin_cases g' <;> decide
    subst hg
    obtain ⟨c, hc, hcw⟩ := hpar.smul
    have : crs (neg2 d) (toV2 (T.pts g - T.pts f)) = - crs d (toV2 (T.pts g - T.pts kk)) := by
      have e : toV2 (T.pts g - T.pts f) = toV2 (T.pts g - T.pts kk) - toV2 (T.pts f - T.pts kk) := by unfold toV2; ext <;> simp
      rw [e, hcw]; unfold crs neg2; simp only [Prod.fst_sub, Prod.snd_sub]; ring
    rw [this] at hleft'
    linarith
  · -- same direction on the same side: contradicts Par with -d
    subst e1; subst e2
    subst hk; subst hf; subst hf'; subst hk'
    have h3 := hpar.symm.trans hpar'
    have h2 := h3.2
    unfold dt neg2 at h2; simp only at h2
    have := nsq_pos hd; unfold nsq at this; nlinarith

end Erdos634.Draft.LaczFormal.RG
