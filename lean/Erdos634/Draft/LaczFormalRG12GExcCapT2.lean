-- Draft/LaczFormalRG12GExcCapT2.lean -- Laczkovich (DCG 48 (2012)), Sect. 6.2, lemma L9 for exceptional points WITH a straight tile (an exceptional point inside a tile side, the PRINT GAP of `LaczFormalRG12GExcCap`):
--     (#edges of Gamma_except arriving at E) + cnt alpha <= cnt gamma + 2 * |Strn E|,
-- (and `Strn E = empty` gives the sharp L9).  Route: the right sector of an arrival is a gamma corner sector (as in L9) OR a straight sector (the right end is an inner point of a side, `sec_inner`);
-- the first kind injects into the gamma sectors, the second into (straight sector, which of its two rays) (`align_same`); a straight tile forces `Asum <= pi` (`head_angle_sum_gen`), hence `cnt alpha = 0`.
-- NOT SHARP: the true count is `r + 1` (rays touching a gamma sector); the factor 2 loses one.  NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.2), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalRG12GExcCapT1

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ}

/-- Right-sector data of an arrival at `E`: a `gamma` corner sector with start ray `-d`, or a straight sector with a ray `-d`. -/
def ArrR (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) {E : Plane} {κ : Type} [Fintype κ] (F : ExtFan D.toRegionDissection E κ)
    (X : Plane) (aR : AtV D.toRegionDissection E) (d : V2) : Prop :=
  d ≠ 0 ∧ NoBack D.toRegionDissection d X ∧ (∃ (b : Bool) (P : List (Fin N × Plane × Plane)), WalkU D.toRegionDissection b d X E P ∧ P ≠ []) ∧
    ((Par (F.p aR) (neg2 d) ∧ IsGam D idx aR) ∨
     (aR.1 ∈ Strn D.toRegionDissection E ∧ (Par (F.p aR) (neg2 d) ∨ Par (F.q aR) (neg2 d))))

theorem arrR_exists (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (idx : Fin N → Equiv.Perm (Fin 3)) {E : Plane} {κ : Type} [Fintype κ]
    (F : ExtFan D.toRegionDissection E κ) {X : Plane} (h : GExc D idx X E) :
    ∃ (aR : AtV D.toRegionDissection E) (d : V2), ArrR D idx F X aR d := by
  obtain ⟨d, hd, hnb, hw, -, ⟨iR, A', B', hR, hcR⟩, -⟩ := gexc_end_split_full D idx h
  rcases hcR with ⟨hYB', hRg⟩ | hin'
  · rw [← hYB'] at hR
    obtain ⟨x2, hx2i, hx2p⟩ := sec_start F hR
    obtain ⟨kR, hkR, hkR2⟩ := hRg
    exact ⟨x2, d, hd, hnb, hw, Or.inl ⟨hx2p, kR, by rw [hx2i]; exact hkR, by rw [hx2i]; exact hkR2⟩⟩
  · have hin'' : E ∈ openSegment ℝ B' A' := by rw [openSegment_symm]; exact hin'
    obtain ⟨x2, hx2i, hx2⟩ := sec_inner F hR hin''
    have := strn_of_inner hR hin''
    exact ⟨x2, d, hd, hnb, hw, Or.inr ⟨by rw [hx2i]; exact this, hx2⟩⟩

theorem arrR_unique (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) {E : Plane} {κ : Type} [Fintype κ]
    (F : ExtFan D.toRegionDissection E κ) {X X' : Plane} {aR : AtV D.toRegionDissection E} {d d' : V2} {r : V2}
    (h : ArrR D idx F X aR d) (h' : ArrR D idx F X' aR d') (hr : Par r (neg2 d)) (hr' : Par r (neg2 d')) : X' = X := by
  obtain ⟨hd, hnb, ⟨b, P, w, hP⟩, -⟩ := h
  obtain ⟨hd', hnb', ⟨b', P', w', hP'⟩, -⟩ := h'
  have hdd : Par (neg2 d') (neg2 d) := hr'.symm.trans hr
  exact align_same D.toRegionDissection hd (par_neg2 hdd) w hP w' hP' hnb hnb'

/-- A tile with a vertex... a straight tile at `E` forces `cnt alpha = 0` at an exceptional point. -/
theorem exc_p_zero_of_strn (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3))
    (hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v) (hregc : ∀ X, cnt D idx X 0 = cnt D idx X 1)
    {E : Plane} {κ : Type} [Fintype κ] (F : ExtFan D.toRegionDissection E κ) (hS : (Strn D.toRegionDissection E).Nonempty)
    (hlt : cnt D idx E 0 < cnt D idx E 2) : cnt D idx E 0 = 0 := by
  have hang := head_angle_sum_gen D idx hidxA F
  have hext : 0 ≤ ∑ j, wd (F.pe j) (F.qe j) := Finset.sum_nonneg (fun j _ => (wd_pos (F.hokE j)).le)
  have hk : (1 : ℝ) ≤ ((Strn D.toRegionDissection E).card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hS
  have hpi := Real.pi_pos
  have hAs : ∑ l, (cnt D idx E l : ℝ) * D.model.angleAt l = (cnt D idx E 0 : ℝ) * (Real.pi - D.model.angleAt 2) + (cnt D idx E 2 : ℝ) * D.model.angleAt 2 :=
    Asum_eq D idx hregc E
  have hγ := model_angle_pos' D 2
  have hlt' : (cnt D idx E 0 : ℝ) + 1 ≤ cnt D idx E 2 := by exact_mod_cast hlt
  by_contra hne
  have h1 : (1 : ℝ) ≤ cnt D idx E 0 := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hne
  nlinarith

end Erdos634.Draft.LaczFormal.RG
