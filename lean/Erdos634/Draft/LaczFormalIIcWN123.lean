-- Draft/LaczFormalIIcWN123.lean -- Laczkovich (DCG 48 (2012), Sect. 6.3, p. 358), Lemma 6.2, `ExcInsideAll` step (ii): an EXCEPTIONAL point lies on no edge of Gamma_kite.
-- Printed (implicit, p. 358): "(i) Y is a vertex of C; (ii) Y in C-degree and Y is a vertex of Gamma_kite; or (iii) Y in C-degree and Y is exceptional" -- the case of an exceptional end lying on the polygon C is not listed; here it is excluded.
-- Route: a Gamma_kite edge `X -> Y` is a full side of two tiles `i != j` (one on each side); an exceptional point `E` is an interior vertex of the tiling (`gexc_exc_interior_exact`), so the local angles at `E` add up to `2 pi` (`sum_localAngle_interior`);
-- if `E` were in the open side, tiles `i`, `j` would contribute `pi` each (`localAngle_open_side`) and the tile having `E` as a vertex a positive corner angle, a total above `2 pi`.  Endpoints are excluded by the vertex counts (`cnt = 2` at Gamma_kite vertices).
-- NOTE, UNAUDITED.  Hypotheses: the Case IIc block + AngGen.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcWN90
import Erdos634.Draft.LaczFormalIIcWN18
import Erdos634.Draft.LaczFormalIIcSharp7
import Erdos634.Draft.LaczFormalRGLoc
import Erdos634.AngleSumDissection
import Erdos634.MarchFlank

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ}

theorem w123_fin3_third : ∀ a b : Fin 3, a ≠ b → ∃ c : Fin 3, c ≠ a ∧ c ≠ b := by decide

theorem w123_fin3_other : ∀ c j a b : Fin 3, c ≠ a → c ≠ b → a ≠ b → j ≠ c → (j = a ∨ j = b) := by decide

/-- A point of the open side of a triangle has local angle `pi`. -/
theorem w123_localAngle_open_side (T : Tri) {a b : Fin 3} (hab : a ≠ b) {Y : Plane} (hY : Y ∈ openSegment ℝ (T.pts a) (T.pts b)) :
    T.localAngle Y = Real.pi := by
  classical
  obtain ⟨c, hca, hcb⟩ := w123_fin3_third a b hab
  have hc := fun m => Erdos634.Draft.LaczFormal.RG.coord_pos_iff T hab rfl rfl hY m
  have hnv : ¬ ∃ j, Y = T.pts j := by
    rintro ⟨j, hj⟩
    exact inner_not_vertex T hab hY hj
  have hc0 : T.basis.coord c Y = 0 := by
    have hcz : ¬ (0 < T.basis.coord c Y) := fun h => by
      rcases (hc c).1 h with h' | h'
      · exact hca h'
      · exact hcb h'
    obtain ⟨σ, h0, h1, hYσ⟩ := openSegment_param hY
    have := Erdos634.Draft.LaczFormal.RG.coord_lineSeg T c a b (σ := σ) rfl rfl
    rw [← hYσ] at this
    rw [this]; simp [hca, hcb]
  have hnall : ¬ ∀ j, 0 < T.basis.coord j Y := fun h => by
    have := h c; rw [hc0] at this; exact lt_irrefl _ this
  have hside : ∃ k, T.basis.coord k Y = 0 ∧ ∀ j, j ≠ k → 0 < T.basis.coord j Y :=
    ⟨c, hc0, fun j hj => (hc j).2 (w123_fin3_other c j a b hca hcb hab hj)⟩
  rw [Tri.localAngle, dif_neg hnv, if_neg hnall, if_pos hside]

set_option maxHeartbeats 3200000 in
/-- **An exceptional point lies on no edge of Gamma_kite.** -/
theorem exc_not_on_kite_edge [NeZero N] [NeZero M] (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hC : CaseC D idx) (hab : Comm (slen D 0) (slen D 1)) (hac : ¬ Comm (slen D 0) (slen D 2))
    (h1 : D.model.angleAt 2 < Real.pi / 2) (h3 : D.model.angleAt 2 ≠ Real.pi / 3) (G : AngGen (fun l => D.model.angleAt l))
    (hcor : ∀ j : Fin M, cnt D idx (P.v j) 0 = 1 ∧ cnt D idx (P.v j) 1 = 1 ∧ cnt D idx (P.v j) 2 = 0)
    {E X Y : Plane} (hE : E ∈ excVerts2 D idx P) (hXY : GKite D idx X Y) : E ∉ segment ℝ X Y := by
  intro hseg
  have hint := (gexc_exc_interior_exact D P hreg idx hC hab hac h1 h3 G hcor E hE).1
  have hlt : cnt D idx E 0 < cnt D idx E 2 := (Finset.mem_filter.mp hE).2
  have hEv : E ∈ vtxSet D.toRegionDissection := by
    have := (Finset.mem_filter.mp hE).1
    exact (Finset.mem_sdiff.mp this).1
  obtain ⟨⟨-, cy0, cy1, cy2⟩, ⟨-, cx0, cx1, cx2⟩⟩ := gkite_vertex_type D P hreg idx hC.hidxA hC.hregc h1 h3 hXY
  have hEX : E ≠ X := by rintro rfl; omega
  have hEY : E ≠ Y := by rintro rfl; omega
  have hopen : E ∈ openSegment ℝ X Y := mem_openSegment_of_ne_left_right hEX.symm hEY.symm hseg
  have hXYne : X ≠ Y := gkite_ne D idx hXY
  obtain ⟨i, j, d, kk, f, kk', f', hij, -, -, hk, hf, -, -, hk', hf', -, -⟩ := hXY
  have hkf : kk ≠ f := fun h => hXYne (by rw [← hk, ← hf, h])
  have hkf' : kk' ≠ f' := fun h => hXYne (by rw [← hk', ← hf', h]) |>.elim
  have hopen' : E ∈ openSegment ℝ ((D.tile i).pts kk) ((D.tile i).pts f) := by rw [hk, hf]; exact hopen
  have hopen'' : E ∈ openSegment ℝ ((D.tile j).pts kk') ((D.tile j).pts f') := by rw [hk', hf', openSegment_symm]; exact hopen
  have hli := w123_localAngle_open_side (D.tile i) hkf hopen'
  have hlj := w123_localAngle_open_side (D.tile j) hkf' hopen''
  obtain ⟨t, kt, hkt⟩ := mem_vtxSet.mp hEv
  have hti : t ≠ i := by
    intro h; rw [h] at hkt; exact inner_not_vertex (D.tile i) hkf hopen' hkt.symm
  have htj : t ≠ j := by
    intro h; rw [h] at hkt; exact inner_not_vertex (D.tile j) hkf' hopen'' hkt.symm
  have hpos : 0 < (D.tile t).localAngle E := by
    rw [← hkt, Tri.localAngle_vertex]; exact Erdos634.MarchFlank.cornerAngle_pos _ _
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hsum := sum_localAngle_interior D.toRegionDissection hN hint
  have hsub : ∑ x ∈ ({i, j, t} : Finset (Fin N)), (D.tile x).localAngle E ≤ ∑ x, (D.tile x).localAngle E :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun x _ _ => Tri.localAngle_nonneg _ _)
  rw [Finset.sum_insert (by simp [hij, hti.symm]), Finset.sum_insert (by simp [htj.symm]), Finset.sum_singleton] at hsub
  rw [hsum, hli, hlj] at hsub
  linarith

#print axioms exc_not_on_kite_edge

end Erdos634.Draft.LaczFormal.RG
