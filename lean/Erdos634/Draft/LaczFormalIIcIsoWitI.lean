-- Draft/LaczFormalIIcIsoWitI.lean -- NON-VACUITY witness for `IIcIsoCore`, step I: the half-line outside lemma, `NoBack`, and the two "no tile side continues past the far vertex" clauses of `GExc` at every vertex of the octagon.
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012)), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcIsoWitH

open Erdos634.Geometry Erdos634.CertCoord Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Thm21 Erdos634.Draft.LaczFormal.RG Erdos634.Draft.LaczFormal.Graph

namespace Erdos634.Draft.LaczFormal.IsoWit

theorem oct_v0 (j : Fin 8) : (oct.v j) 0 = cx j := mkPt_zero _ _
theorem oct_v1 (j : Fin 8) : (oct.v j) 1 = cy j := mkPt_one _ _

theorem pt_mem (i : Fin 8) (m : Fin 3) : (tile i).pts m ∈ oct.carrier :=
  tile_sub i (subset_convexHull ℝ _ ⟨m, rfl⟩)

/-- a point beyond a vertex on its radial half-line lies outside the octagon -/
theorem out_lemma (k : Fin 8) (t : ℝ) (ht : 0 < t) (p : Plane) (hp : p ∈ oct.carrier)
    (h0 : p 0 = (1 + t) * cx k) (h1 : p 1 = (1 + t) * cy k) : False := by
  have h := (mem_oct p).mp hp k
  rw [h0, h1] at h
  have hc := cr_1 k
  unfold cr at hc
  nlinarith [mul_pos ht hh_pos]

/-- the direction of the spoke from vertex `j` through the centre -/
noncomputable def dvec (j : Fin 8) : V2 := (-cx j, -cy j)

theorem dvec_ne (j : Fin 8) : dvec j ≠ 0 := by
  intro h
  have h1 : -cx j = 0 := congrArg Prod.fst h
  have h2 : -cy j = 0 := congrArg Prod.snd h
  have := cxy_sq j
  have e1 : cx j = 0 := by linarith
  have e2 : cy j = 0 := by linarith
  rw [e1, e2] at this; norm_num at this

/-- a tile vertex on the radial half-line beyond `V k` (as `V k + c * V k`) cannot exist -/
theorem no_ray (k : Fin 8) (c : ℝ) (hc : 0 < c) (p : Plane) (hp : p ∈ oct.carrier)
    (h0 : p 0 = (1 + c) * cx k) (h1 : p 1 = (1 + c) * cy k) : False := out_lemma k c hc p hp h0 h1

theorem noBack (j : Fin 8) : NoBack octDiss.toRegionDissection (dvec j) (oct.v j) := by
  constructor
  · intro i A B σ hS hσ hσ1 hX
    obtain ⟨kk, f, g, hk, hf, -, -, -, hpar, -⟩ := hS
    obtain ⟨c, hc, hcq⟩ := hpar.smul
    have e0 : B 0 - A 0 = c * (-cx j) := congrArg Prod.fst hcq
    have e1 : B 1 - A 1 = c * (-cy j) := congrArg Prod.snd hcq
    have x0 := congrArg (fun p : Plane => p 0) hX
    have x1 := congrArg (fun p : Plane => p 1) hX
    simp only [oct_v0, oct_v1, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul] at x0 x1
    refine no_ray j (σ * c) (mul_pos hσ hc) A (hk ▸ pt_mem i kk) ?_ ?_
    · nlinarith
    · nlinarith
  · intro i A B σ hS hσ hσ1 hX
    obtain ⟨kk, f, g, hk, hf, -, -, -, hpar, -⟩ := hS
    obtain ⟨c, hc, hcq⟩ := hpar.smul
    have e0 : B 0 - A 0 = c * (cx j) := by have := congrArg Prod.fst hcq; simpa [neg2, dvec] using this
    have e1 : B 1 - A 1 = c * (cy j) := by have := congrArg Prod.snd hcq; simpa [neg2, dvec] using this
    have x0 := congrArg (fun p : Plane => p 0) hX
    have x1 := congrArg (fun p : Plane => p 1) hX
    simp only [oct_v0, oct_v1, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul] at x0 x1
    refine no_ray j (σ * c) (mul_pos hσ hc) B (hf ▸ pt_mem i f) ?_ ?_
    · nlinarith
    · nlinarith

theorem noStepFwd (j : Fin 8) : ∀ i U', ¬ TriStep (octDiss.tile i) (dvec j) (oct.v (j + 4)) U' := by
  intro i U' hS
  obtain ⟨kk, f, g, hk, hf, -, -, -, hpar, -⟩ := hS
  obtain ⟨c, hc, hcq⟩ := hpar.smul
  have e0 : U' 0 - (oct.v (j + 4)) 0 = c * (-cx j) := congrArg Prod.fst hcq
  have e1 : U' 1 - (oct.v (j + 4)) 1 = c * (-cy j) := congrArg Prod.snd hcq
  rw [oct_v0, cx_add4] at e0
  rw [oct_v1, cy_add4] at e1
  refine no_ray (j + 4) c hc U' (hf ▸ pt_mem i f) ?_ ?_
  · rw [cx_add4]; nlinarith
  · rw [cy_add4]; nlinarith

theorem noStepBwd (j : Fin 8) : ∀ i U', ¬ TriStep (octDiss.tile i) (neg2 (dvec j)) U' (oct.v (j + 4)) := by
  intro i U' hS
  obtain ⟨kk, f, g, hk, hf, -, -, -, hpar, -⟩ := hS
  obtain ⟨c, hc, hcq⟩ := hpar.smul
  have e0 : (oct.v (j + 4)) 0 - U' 0 = c * (cx j) := by have := congrArg Prod.fst hcq; simpa [neg2, dvec] using this
  have e1 : (oct.v (j + 4)) 1 - U' 1 = c * (cy j) := by have := congrArg Prod.snd hcq; simpa [neg2, dvec] using this
  rw [oct_v0, cx_add4] at e0
  rw [oct_v1, cy_add4] at e1
  refine no_ray (j + 4) c hc U' (hk ▸ pt_mem i kk) ?_ ?_
  · rw [cx_add4]; nlinarith
  · rw [cy_add4]; nlinarith

end Erdos634.Draft.LaczFormal.IsoWit
