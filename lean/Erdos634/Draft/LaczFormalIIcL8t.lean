-- Draft/LaczFormalIIcL8t.lean -- Laczkovich (DCG 48 (2012)), Sect. 6.3, L8 `gexc_disjoint`: `spokes_disjoint`.
-- For two edges `P.v i -> E`, `P.v l -> F` of Gamma_except from distinct corners of the polygon to distinct exceptional vertices, the closed segments are disjoint.
-- Route (IIC_STRN Sect. 4 step 4): a common point `X` is an endpoint of one of them or an inner point of both.  Endpoint `E` or `F` inside the other edge: `exc_not_inner` (A); polygon corners are not interior points
-- and the open spokes are interior (convexity).  Inner point of both on non-parallel lines: `X` is exceptional (`cross_exc`, B) and an inner point of an edge: `exc_not_inner`.  Parallel (collinear) case: `E, F` lie in the open chord
-- between the two corners (`chord_in_segment`) and the ordering `col_E_in` puts one of them inside the other edge.
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcL8n
import Erdos634.Draft.LaczFormalIIcL8r
import Erdos634.Draft.LaczFormalIIcL8s

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ}

set_option maxHeartbeats 6400000 in
/-- **L8 `gexc_disjoint`**: spokes from distinct corners to distinct exceptional vertices are disjoint. -/
theorem spokes_disjoint [NeZero M] (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hC : CaseC D idx) (hab : Comm (slen D 0) (slen D 1)) (hac : ¬ Comm (slen D 0) (slen D 2))
    (h1 : D.model.angleAt 2 < Real.pi / 2) (h3 : D.model.angleAt 2 ≠ Real.pi / 3) (G : AngGen (fun l => D.model.angleAt l))
    (hcor : ∀ j : Fin M, cnt D idx (P.v j) 0 = 1 ∧ cnt D idx (P.v j) 1 = 1 ∧ cnt D idx (P.v j) 2 = 0)
    {E F : Plane} (hE : E ∈ excVerts2 D idx P) (hF : F ∈ excVerts2 D idx P) (hEF : E ≠ F) {i l : Fin M} (hil : i ≠ l)
    (hi : GExc D idx (P.v i) E) (hl : GExc D idx (P.v l) F) :
    ∀ X, X ∈ segment ℝ (P.v i) E → X ∈ segment ℝ (P.v l) F → False := by
  classical
  intro X hX1 hX2
  have hEint : E ∈ interior P.carrier := by
    have := (gexc_exc_interior_exact D P hreg idx hC hab hac h1 h3 G hcor E hE).1; rwa [hreg] at this
  have hFint : F ∈ interior P.carrier := by
    have := (gexc_exc_interior_exact D P hreg idx hC hab hac h1 h3 G hcor F hF).1; rwa [hreg] at this
  have hAint : P.v i ∉ interior P.carrier := vertex_not_interior P i
  have hBint : P.v l ∉ interior P.carrier := vertex_not_interior P l
  have hAB : P.v i ≠ P.v l := fun h => hil (vtx_inj' P h)
  have hEcar : E ∈ P.carrier := interior_subset hEint
  have hFcar : F ∈ P.carrier := interior_subset hFint
  have hnc : ∀ Z ∈ interior P.carrier, ∀ k : Fin M, Z ≠ P.v (k + 1) := fun Z hZ k hk => vertex_not_interior P (k + 1) (hk ▸ hZ)
  have hAE_int : ∀ Z ∈ openSegment ℝ (P.v i) E, Z ∈ interior P.carrier := fun Z hZ =>
    openSegment_interior_of P hEint (vtx_mem' P i) (by rwa [openSegment_symm] at hZ)
  have hBF_int : ∀ Z ∈ openSegment ℝ (P.v l) F, Z ∈ interior P.carrier := fun Z hZ =>
    openSegment_interior_of P hFint (vtx_mem' P l) (by rwa [openSegment_symm] at hZ)
  have hBE : P.v l ≠ E := fun h => hBint (h ▸ hEint)
  have hAE : P.v i ≠ E := fun h => hAint (h ▸ hEint)
  have hAF : P.v i ≠ F := fun h => hAint (h ▸ hFint)
  have hBF : P.v l ≠ F := fun h => hBint (h ▸ hFint)
  by_cases hXE : X = E
  · subst hXE
    exact exc_not_inner D P hreg idx hC hab hac h1 h3 G hcor hE hl (mem_openSegment_of_ne_left_right hBE hEF.symm hX2)
  by_cases hXF : X = F
  · subst hXF
    exact exc_not_inner D P hreg idx hC hab hac h1 h3 G hcor hF hi (mem_openSegment_of_ne_left_right hAF hEF hX1)
  by_cases hXA : X = P.v i
  · subst hXA
    exact hAint (hBF_int _ (mem_openSegment_of_ne_left_right hAB.symm hAF.symm hX2))
  by_cases hXB : X = P.v l
  · subst hXB
    exact hBint (hAE_int _ (mem_openSegment_of_ne_left_right hAB hBE.symm hX1))
  have hX1' : X ∈ openSegment ℝ (P.v i) E := mem_openSegment_of_ne_left_right (Ne.symm hXA) (Ne.symm hXE) hX1
  have hX2' : X ∈ openSegment ℝ (P.v l) F := mem_openSegment_of_ne_left_right (Ne.symm hXB) (Ne.symm hXF) hX2
  have hXint : X ∈ interior P.carrier := hAE_int X hX1'
  by_cases hpar : crs (toV2 (E - P.v i)) (toV2 (F - P.v l)) = 0
  · -- collinear case
    obtain ⟨σ, hσ0, hσ1, hXσ⟩ := openSegment_param hX1'
    obtain ⟨τ, hτ0, hτ1, hXτ⟩ := openSegment_param hX2'
    set A := P.v i with hA
    set B := P.v l with hB
    have hb : B - A = σ • (E - A) - τ • (F - B) := by
      have h := hXσ.symm.trans hXτ
      calc B - A = (B + τ • (F - B)) - A - τ • (F - B) := by module
        _ = (A + σ • (E - A)) - A - τ • (F - B) := by rw [← h]
        _ = σ • (E - A) - τ • (F - B) := by module
    have hp0 : cross2 (E - A) (F - B) = 0 := by unfold cross2; unfold crs toV2 at hpar; simpa using hpar
    have gE : gl A B E = 0 := by
      unfold gl; rw [hb]; unfold cross2 at hp0 ⊢
      simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul] at hp0 ⊢
      nlinarith [hp0]
    have gF : gl A B F = 0 := by
      unfold gl
      have e : F - A = (F - B) + (B - A) := by abel
      rw [e, hb]; unfold cross2 at hp0 ⊢
      simp only [PiLp.sub_apply, PiLp.smul_apply, PiLp.add_apply, smul_eq_mul] at hp0 ⊢
      nlinarith [hp0]
    have hEs := chord_in_segment P hil hEcar gE
    have hFs := chord_in_segment P hil hFcar gF
    have hEo : E ∈ openSegment ℝ A B := mem_openSegment_of_ne_left_right hAE hBE hEs
    have hFo : F ∈ openSegment ℝ A B := mem_openSegment_of_ne_left_right hAF hBF hFs
    exact exc_not_inner D P hreg idx hC hab hac h1 h3 G hcor hE hl (col_E_in hAB hEo hFo hEF hX1' hX2')
  · have hXexc := cross_exc D P hreg idx hC h1 hi hl hX1' hX2' hpar (hnc X hXint)
    exact exc_not_inner D P hreg idx hC hab hac h1 h3 G hcor hXexc hi hX1'

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.spokes_disjoint
