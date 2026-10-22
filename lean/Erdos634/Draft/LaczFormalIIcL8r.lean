-- Draft/LaczFormalIIcL8r.lean -- Laczkovich (DCG 48 (2012)), Sect. 6.3, L8 `gexc_disjoint`, step 11 (A): `exc_not_inner`.
-- An exceptional vertex `E` is never an inner point of an edge `X -> Y` of Gamma_except.  The through edge supplies one more arrival-type start at `E` (`thru_arr_or_lineD`), distinct from the arrivals (`gexc_det`),
-- so  (#arrivals + 1) + cnt alpha <= cnt gamma  (`exc_capacity_gen`), against the exact count  #arrivals = cnt gamma - cnt alpha  (S7, `gexc_exc_interior_exact`).
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcL8q
import Erdos634.Draft.LaczFormalIIcSharp7

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ}

theorem par_of_openSegment {X Y E : Plane} (hE : E ∈ openSegment ℝ X Y) (hne : toV2 (Y - X) ≠ 0) : Par (toV2 (Y - X)) (toV2 (E - X)) := by
  obtain ⟨σ, hσ0, hσ1, hEσ⟩ := openSegment_param hE
  have e : toV2 (E - X) = (σ * (toV2 (Y - X)).1, σ * (toV2 (Y - X)).2) := by
    rw [hEσ]; unfold toV2; ext <;> simp
  rw [e]
  refine ⟨by unfold crs; ring, ?_⟩
  have := nsq_pos hne
  unfold dt; unfold nsq at this; nlinarith

set_option maxHeartbeats 6400000 in
/-- **(A)** an exceptional vertex is never an inner point of an edge of Gamma_except. -/
theorem exc_not_inner [NeZero M] (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hC : CaseC D idx) (hab : Comm (slen D 0) (slen D 1)) (hac : ¬ Comm (slen D 0) (slen D 2))
    (h1 : D.model.angleAt 2 < Real.pi / 2) (h3 : D.model.angleAt 2 ≠ Real.pi / 3) (G : AngGen (fun l => D.model.angleAt l))
    (hcor : ∀ j : Fin M, cnt D idx (P.v j) 0 = 1 ∧ cnt D idx (P.v j) 1 = 1 ∧ cnt D idx (P.v j) 2 = 0)
    {E X Y : Plane} (hE : E ∈ excVerts2 D idx P) (h : GExc D idx X Y) (hin : E ∈ openSegment ℝ X Y) : False := by
  classical
  have hE' := hE
  unfold excVerts2 at hE'
  simp only [Finset.mem_filter, Finset.mem_sdiff] at hE'
  obtain ⟨⟨hEv, hEp⟩, hlt⟩ := hE'
  have hvert := mem_vtxSet.mp hEv
  obtain ⟨κ, _, ⟨F⟩⟩ := HasFansC.fans (D := D.toRegionDissection) E hvert
  set Aset := (vtxSet D.toRegionDissection).filter (fun X' => GExc D idx X' E) with hAset
  obtain ⟨d, hd, nb, par, -⟩ := gexc_inner_split D idx h hin
  have hXY : toV2 (Y - X) ≠ 0 := par.ne_left
  have hXn : X ∉ Aset := by
    intro hX
    have hX' := (Finset.mem_filter.mp hX).2
    have hY := gexc_det D idx h hX' (par_of_openSegment hin hXY)
    subst hY
    obtain ⟨σ, hσ0, hσ1, hEσ⟩ := openSegment_param hin
    have c0 : Y 0 = X 0 + σ * (Y 0 - X 0) := by have := congrArg (fun z : Plane => z 0) hEσ; simpa using this
    have c1 : Y 1 = X 1 + σ * (Y 1 - X 1) := by have := congrArg (fun z : Plane => z 1) hEσ; simpa using this
    have h0 : (1 - σ) * (Y 0 - X 0) = 0 := by linarith
    have h1' : (1 - σ) * (Y 1 - X 1) = 0 := by linarith
    have e0 := (mul_eq_zero.mp h0).resolve_left (by linarith)
    have e1 := (mul_eq_zero.mp h1').resolve_left (by linarith)
    apply hXY
    unfold toV2; ext <;> simp [e0, e1]
  have hS : ∀ X' ∈ insert X Aset, (∃ aL aR : AtV D.toRegionDissection E, ArrData D idx F X' aL aR) ∨ LineD D idx X' E := by
    intro X' hX'
    rcases Finset.mem_insert.mp hX' with rfl | hmem
    · exact thru_arr_or_lineD D idx hC.hidxA hC.hregc h1 F hlt h hin
    · exact arrData_or_lineD D idx F (Finset.mem_filter.mp hmem).2
  have hcap := exc_capacity_gen D P hreg idx hC h1 h3 hE F (insert X Aset) hS
  rw [Finset.card_insert_of_notMem hXn] at hcap
  have hex : Aset.card = cnt D idx E 2 - cnt D idx E 0 := (gexc_exc_interior_exact D P hreg idx hC hab hac h1 h3 G hcor E hE).2
  omega

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.exc_not_inner
