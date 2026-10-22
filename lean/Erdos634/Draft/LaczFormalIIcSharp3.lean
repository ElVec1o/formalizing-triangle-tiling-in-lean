-- Draft/LaczFormalIIcSharp3.lean -- Laczkovich (DCG 48 (2012)), Sect. 6.2-6.3, repair of the hStrn gap (AI assistant plan IIC_STRN.md, S3): at most one edge of Gamma_except arrives at `E` "along a tile side".
-- `arrData_or_lineD`: an arrival has either two `gamma` corner sectors (`ArrData`) or `LineD` data: an element of one of the two divisions has `E` in its OPEN side `[A,B]`, the tile is in `Strn E`, and `gamma` is at the head `B` (S1).
-- `strn_card_le_one`: at an exceptional point `|Strn E| <= 1` (angle count: a straight tile gives `pi`, `r >= 1`).
-- `lineD_unique`: two `LineD` arrivals coincide (S2 gives the same side; `gamma` at both heads forces the same orientation; `align_same`).
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.2-6.3, Lemmas 4.4-4.8), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcSharp1
import Erdos634.Draft.LaczFormalIIcSharp2
import Erdos634.Draft.LaczFormalRG12GExcCapT3

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ}

/-- An arrival along a tile side: the walk, a tile of `Strn E` with `E` in the open side `[A,B]` (vertices `a`, `b'`), direction `d` along `B - A`, and `gamma` at the head `B`. -/
def LineD (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) (X E : Plane) : Prop :=
  ∃ (d : V2) (bl : Bool) (P : List (Fin N × Plane × Plane)) (i : Fin N) (A B : Plane) (a b' : Fin 3),
    d ≠ 0 ∧ NoBack D.toRegionDissection d X ∧ WalkU D.toRegionDissection bl d X E P ∧ P ≠ [] ∧ i ∈ Strn D.toRegionDissection E ∧
    E ∈ openSegment ℝ A B ∧ Par (toV2 (B - A)) d ∧ (D.tile i).pts a = A ∧ (D.tile i).pts b' = B ∧ a ≠ b' ∧ idx i b' = 2

theorem arrData_or_lineD (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (idx : Fin N → Equiv.Perm (Fin 3)) {E : Plane} {κ : Type} [Fintype κ]
    (F : ExtFan D.toRegionDissection E κ) {X : Plane} (h : GExc D idx X E) :
    (∃ aL aR : AtV D.toRegionDissection E, ArrData D idx F X aL aR) ∨ LineD D idx X E := by
  obtain ⟨d, hd, hnb, ⟨bl, P, hw, hP⟩, ⟨iL, A, B, hL, hcL⟩, ⟨iR, A', B', hR, hcR⟩, -⟩ := gexc_end_split_fullG D idx h
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

/-- **At an exceptional point at most one tile has `E` inside a side.** -/
theorem strn_card_le_one (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3))
    (hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v) (hregc : ∀ X, cnt D idx X 0 = cnt D idx X 1)
    (h1 : D.model.angleAt 2 < Real.pi / 2) {E : Plane} {κ : Type} [Fintype κ] (F : ExtFan D.toRegionDissection E κ)
    (hlt : cnt D idx E 0 < cnt D idx E 2) : (Strn D.toRegionDissection E).card ≤ 1 := by
  by_contra hc
  have hc2 : (2 : ℝ) ≤ ((Strn D.toRegionDissection E).card : ℝ) := by exact_mod_cast (by omega : 2 ≤ (Strn D.toRegionDissection E).card)
  have hang := head_angle_sum_gen D idx hidxA F
  have hext : 0 ≤ ∑ j, wd (F.pe j) (F.qe j) := Finset.sum_nonneg (fun j _ => (wd_pos (F.hokE j)).le)
  have hpi := Real.pi_pos
  have hAs : ∑ l, (cnt D idx E l : ℝ) * D.model.angleAt l = (cnt D idx E 0 : ℝ) * (Real.pi - D.model.angleAt 2) + (cnt D idx E 2 : ℝ) * D.model.angleAt 2 :=
    Asum_eq D idx hregc E
  have hγ := model_angle_pos' D 2
  have hlt' : (cnt D idx E 0 : ℝ) + 1 ≤ cnt D idx E 2 := by exact_mod_cast hlt
  have a1 : 0 ≤ (cnt D idx E 0 : ℝ) * (Real.pi - D.model.angleAt 2) := mul_nonneg (Nat.cast_nonneg _) (by linarith)
  have a2 : D.model.angleAt 2 ≤ (cnt D idx E 2 : ℝ) * D.model.angleAt 2 := by
    have : (1 : ℝ) ≤ cnt D idx E 2 := by have := Nat.cast_nonneg (α := ℝ) (cnt D idx E 0); linarith
    nlinarith
  nlinarith

/-- **S3.** Two `LineD` arrivals at `E` coincide, when at most one tile has `E` inside a side. -/
theorem lineD_unique (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (idx : Fin N → Equiv.Perm (Fin 3)) {E X X' : Plane}
    (hcard : (Strn D.toRegionDissection E).card ≤ 1) (h : LineD D idx X E) (h' : LineD D idx X' E) : X' = X := by
  obtain ⟨d, bl, P, i, A, B, a, b', hd, hnb, hw, hP, hi, hE, hpar, ha, hb, hab, hg⟩ := h
  obtain ⟨d', bl', P', i', A', B', a', b'', hd', hnb', hw', hP', hi', hE', hpar', ha', hb', hab', hg'⟩ := h'
  have hii : i = i' := Finset.card_le_one.mp hcard i hi i' hi'
  subst hii
  rcases tri_inner_side_unique (D.tile i) hab hab' ha hb ha' hb' hE hE' with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · subst e1; subst e2
    have hA : A = A' := by rw [← ha, ← ha']
    have hB : B = B' := by rw [← hb, ← hb']
    subst hA; subst hB
    exact align_same D.toRegionDissection hd (hpar'.symm.trans hpar) hw hP hw' hP' hnb hnb'
  · subst e1; subst e2
    have : a = b' := (Equiv.injective (idx i)) (by rw [hg, hg'])
    exact absurd this hab

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.arrData_or_lineD
#print axioms Erdos634.Draft.LaczFormal.RG.strn_card_le_one
#print axioms Erdos634.Draft.LaczFormal.RG.lineD_unique
