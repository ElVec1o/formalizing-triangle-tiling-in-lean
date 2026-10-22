-- Draft/LaczFormalRG12ShapeTile.lean -- **Lemma 4.8, shape of the pair** (Laczkovich DCG 48 (2012), Lemma 4.8, last sentence + angle data at `U`, `V`): two congruent tiles of a congruent region dissection with a common
-- side `UV` of length `c = slen 2` (`c` different from the other two side lengths), lying on opposite sides of the line `UV` (`TriStep` for `d` and `-d`).  Then the third vertices `W` (angle `gamma`), `W'`
-- satisfy: KITE (`W'` = reflection of `W` in the line `UV`; the type at `U` is the same in both tiles, the type at `V` is the same) or PARALLELOGRAM (`W' = U + V - W`; the type at `U` in the second tile is
-- the type of `V` in the first).  `pair_shape_tiles`.  NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Lemma 4.8), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalRG12Shape
import Erdos634.Draft.LaczFormalRG10Lemma48

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N : ℕ}

theorem dist_sq_plane (X Y : Plane) : dist X Y ^ 2 = (X 0 - Y 0) ^ 2 + (X 1 - Y 1) ^ 2 := by
  rw [EuclideanSpace.dist_eq, Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _)), Fin.sum_univ_two]
  simp [Real.dist_eq, sq_abs]

/-- The model side opposite the vertex of type `C` is the distance between the other two. -/
theorem dist_model_opp (D : CongruentRegionDissection N) (A B C : Fin 3) (hAB : A ≠ B) (hBC : B ≠ C) (hAC : A ≠ C) :
    dist (D.model.pts A) (D.model.pts B) = slen D C := by
  unfold slen
  revert hAB hBC hAC
  fin_cases A <;> fin_cases B <;> fin_cases C <;> simp <;> first | rfl | exact dist_comm _ _

theorem opp_eq_two (D : CongruentRegionDissection N) (h0 : slen D 0 ≠ slen D 2) (h1 : slen D 1 ≠ slen D 2) (C : Fin 3)
    (h : slen D C = slen D 2) : C = 2 := by
  revert h
  fin_cases C
  · intro h; exact absurd h h0
  · intro h; exact absurd h h1
  · intro _; rfl

set_option maxHeartbeats 3200000 in
/-- **Lemma 4.8, shape of the pair.** -/
theorem pair_shape_tiles (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    (h0 : slen D 0 ≠ slen D 2) (h1 : slen D 1 ≠ slen D 2) {i j : Fin N} {d : V2} {U V : Plane}
    (hS : TriStep (D.tile i) d U V) (hS' : TriStep (D.tile j) (neg2 d) V U) (hc : dist U V = slen D 2) :
    ∃ kk f g kk' f' g' : Fin 3, (D.tile i).pts kk = U ∧ (D.tile i).pts f = V ∧ (D.tile j).pts kk' = V ∧ (D.tile j).pts f' = U ∧
      idx i g = 2 ∧ idx j g' = 2 ∧
      (( (((V 0 - U 0) ^ 2 + (V 1 - U 1) ^ 2) * (((D.tile j).pts g') 0 - U 0) = 2 * ((V 0 - U 0) * ((D.tile i).pts g 0 - U 0) + (V 1 - U 1) * ((D.tile i).pts g 1 - U 1)) * (V 0 - U 0) - ((V 0 - U 0) ^ 2 + (V 1 - U 1) ^ 2) * ((D.tile i).pts g 0 - U 0) ∧
          ((V 0 - U 0) ^ 2 + (V 1 - U 1) ^ 2) * (((D.tile j).pts g') 1 - U 1) = 2 * ((V 0 - U 0) * ((D.tile i).pts g 0 - U 0) + (V 1 - U 1) * ((D.tile i).pts g 1 - U 1)) * (V 1 - U 1) - ((V 0 - U 0) ^ 2 + (V 1 - U 1) ^ 2) * ((D.tile i).pts g 1 - U 1)) ∧
        idx j f' = idx i kk ∧ idx j kk' = idx i f) ∨
       ((((D.tile j).pts g') 0 = U 0 + V 0 - (D.tile i).pts g 0 ∧ ((D.tile j).pts g') 1 = U 1 + V 1 - (D.tile i).pts g 1) ∧ idx j f' = idx i f ∧ idx j kk' = idx i kk)) := by
  classical
  obtain ⟨kk, f, g, hk, hf, hfk, hgk, hgf, hpar, hleft⟩ := hS
  obtain ⟨kk', f', g', hk', hf', hfk', hgk', hgf', hpar', hleft'⟩ := hS'
  refine ⟨kk, f, g, kk', f', g', hk, hf, hk', hf', ?_⟩
  have iA := (idx i).injective
  have iA' := (idx j).injective
  have hAB : idx i kk ≠ idx i f := fun h => hfk (iA h).symm
  have hBC : idx i f ≠ idx i g := fun h => hgf (iA h).symm
  have hAC : idx i kk ≠ idx i g := fun h => hgk (iA h).symm
  have hAB' : idx j kk' ≠ idx j f' := fun h => hfk' (iA' h).symm
  have hBC' : idx j f' ≠ idx j g' := fun h => hgf' (iA' h).symm
  have hAC' : idx j kk' ≠ idx j g' := fun h => hgk' (iA' h).symm
  have dUV : dist U V = slen D (idx i g) := by
    rw [← hk, ← hf, hidx]; exact dist_model_opp D _ _ _ hAB hBC hAC
  have dVU : dist V U = slen D (idx j g') := by
    rw [← hk', ← hf', hidx]; exact dist_model_opp D _ _ _ hAB' hBC' hAC'
  have hg2 : idx i g = 2 := opp_eq_two D h0 h1 _ (dUV.symm.trans hc)
  have hg2' : idx j g' = 2 := opp_eq_two D h0 h1 _ (dVU.symm.trans ((dist_comm V U).trans hc))
  refine ⟨hg2, hg2', ?_⟩
  -- orientation
  have hvec : toV2 (V - U) = ((hpar.smul).choose * d.1, (hpar.smul).choose * d.2) := (hpar.smul).choose_spec.2
  have hcpos := (hpar.smul).choose_spec.1
  have hvec' : toV2 (U - V) = ((hpar'.smul).choose * (neg2 d).1, (hpar'.smul).choose * (neg2 d).2) := (hpar'.smul).choose_spec.2
  have hcpos' := (hpar'.smul).choose_spec.1
  set c1 := (hpar.smul).choose
  set c2 := (hpar'.smul).choose
  have e1 : V 0 - U 0 = c1 * d.1 := by have := congrArg Prod.fst hvec; simpa [toV2] using this
  have e2 : V 1 - U 1 = c1 * d.2 := by have := congrArg Prod.snd hvec; simpa [toV2] using this
  set W := (D.tile i).pts g with hW
  set W' := (D.tile j).pts g' with hW'
  have s1 : 0 < (V 0 - U 0) * (W 1 - U 1) - (V 1 - U 1) * (W 0 - U 0) := by
    have : 0 < d.1 * (W 1 - U 1) - d.2 * (W 0 - U 0) := by simpa [crs, toV2] using hleft
    rw [e1, e2]
    have : (c1 * d.1) * (W 1 - U 1) - (c1 * d.2) * (W 0 - U 0) = c1 * (d.1 * (W 1 - U 1) - d.2 * (W 0 - U 0)) := by ring
    rw [this]; exact mul_pos hcpos ‹_›
  have s2 : (V 0 - U 0) * (W' 1 - U 1) - (V 1 - U 1) * (W' 0 - U 0) < 0 := by
    have : 0 < (neg2 d).1 * (W' 1 - V 1) - (neg2 d).2 * (W' 0 - V 0) := by simpa [crs, toV2] using hleft'
    have hn : (neg2 d).1 = -d.1 := rfl
    have hn2 : (neg2 d).2 = -d.2 := rfl
    rw [hn, hn2] at this
    have key : 0 < c1 * (d.2 * (W' 0 - V 0) - d.1 * (W' 1 - V 1)) := mul_pos hcpos (by linarith)
    -- cross(v, W'-U) = cross(v, W'-V)
    have : (V 0 - U 0) * (W' 1 - U 1) - (V 1 - U 1) * (W' 0 - U 0) = (V 0 - U 0) * (W' 1 - V 1) - (V 1 - U 1) * (W' 0 - V 0) := by ring
    rw [this, e1, e2]
    nlinarith [key]
  -- distances
  have hdU : dist U W = dist (D.model.pts (idx i kk)) (D.model.pts (idx i g)) := by rw [← hk, hW, hidx]
  have hdV : dist V W = dist (D.model.pts (idx i f)) (D.model.pts (idx i g)) := by rw [← hf, hW, hidx]
  have hdU' : dist U W' = dist (D.model.pts (idx j f')) (D.model.pts (idx j g')) := by rw [← hf', hW', hidx]
  have hdV' : dist V W' = dist (D.model.pts (idx j kk')) (D.model.pts (idx j g')) := by rw [← hk', hW', hidx]
  -- the types: {A', B'} = {A, B}
  have hmem : ∀ x : Fin 3, x ≠ 2 ↔ x = 0 ∨ x = 1 := by decide
  have tA : idx i kk = 0 ∨ idx i kk = 1 := (hmem _).mp (fun h => hAC (h.trans hg2.symm))
  have tB : idx i f = 0 ∨ idx i f = 1 := (hmem _).mp (fun h => hBC (h.trans hg2.symm))
  have tA' : idx j kk' = 0 ∨ idx j kk' = 1 := (hmem _).mp (fun h => hAC' (h.trans hg2'.symm))
  have tB' : idx j f' = 0 ∨ idx j f' = 1 := (hmem _).mp (fun h => hBC' (h.trans hg2'.symm))
  have sqU := dist_sq_plane U W
  have sqV := dist_sq_plane V W
  have sqU' := dist_sq_plane U W'
  have sqV' := dist_sq_plane V W'
  -- the real coordinate statement
  have hcase : (idx j f' = idx i f ∧ idx j kk' = idx i kk) ∨ (idx j f' = idx i kk ∧ idx j kk' = idx i f) := by
    have key : ∀ x y x' y' : Fin 3, (x = 0 ∨ x = 1) → (y = 0 ∨ y = 1) → (x' = 0 ∨ x' = 1) → (y' = 0 ∨ y' = 1) → x ≠ y → x' ≠ y' →
        (y' = y ∧ x' = x) ∨ (y' = x ∧ x' = y) := by decide
    exact key _ _ _ _ tA tB tA' tB' hAB hAB'
  have hq : ((V 0 - U 0) ^ 2 + (V 1 - U 1) ^ 2) ≠ 0 := by
    intro h
    have hp : V 0 - U 0 = 0 := by nlinarith [sq_nonneg (V 0 - U 0), sq_nonneg (V 1 - U 1)]
    have hq : V 1 - U 1 = 0 := by nlinarith [sq_nonneg (V 0 - U 0), sq_nonneg (V 1 - U 1)]
    rw [hp, hq] at s1; simp at s1
  rcases hcase with ⟨e1', e2'⟩ | ⟨e1', e2'⟩
  · -- parallelogram
    right
    have d1 : dist U W' = dist V W := by
      rw [hdU', hdV, e1', hg2', ← hg2]
    have d2 : dist V W' = dist U W := by
      rw [hdV', hdU, e2', hg2', ← hg2]
    have q1 := d1; have q2 := d2
    have r1 : (W' 0 - U 0) ^ 2 + (W' 1 - U 1) ^ 2 = ((W 0 - U 0) - (V 0 - U 0)) ^ 2 + ((W 1 - U 1) - (V 1 - U 1)) ^ 2 := by
      have := congrArg (· ^ 2) q1
      simp only at this
      rw [sqU', sqV] at this
      linear_combination this
    have r2 : ((W' 0 - U 0) - (V 0 - U 0)) ^ 2 + ((W' 1 - U 1) - (V 1 - U 1)) ^ 2 = (W 0 - U 0) ^ 2 + (W 1 - U 1) ^ 2 := by
      have := congrArg (· ^ 2) q2
      simp only at this
      rw [sqV', sqU] at this
      linear_combination this
    obtain ⟨x1, x2⟩ := para_real (V 0 - U 0) (V 1 - U 1) (W 0 - U 0) (W 1 - U 1) (W' 0 - U 0) (W' 1 - U 1) r1 r2 s1 s2
    exact ⟨⟨by linarith, by linarith⟩, e1', e2'⟩
  · -- kite
    left
    have d1 : dist U W' = dist U W := by
      rw [hdU', hdU, e1', hg2', ← hg2]
    have d2 : dist V W' = dist V W := by
      rw [hdV', hdV, e2', hg2', ← hg2]
    have r1 : (W' 0 - U 0) ^ 2 + (W' 1 - U 1) ^ 2 = (W 0 - U 0) ^ 2 + (W 1 - U 1) ^ 2 := by
      have := congrArg (· ^ 2) d1
      simp only at this
      rw [sqU', sqU] at this
      linear_combination this
    have r2 : ((W' 0 - U 0) - (V 0 - U 0)) ^ 2 + ((W' 1 - U 1) - (V 1 - U 1)) ^ 2 = ((W 0 - U 0) - (V 0 - U 0)) ^ 2 + ((W 1 - U 1) - (V 1 - U 1)) ^ 2 := by
      have := congrArg (· ^ 2) d2
      simp only at this
      rw [sqV', sqV] at this
      linear_combination this
    obtain ⟨x1, x2⟩ := kite_real (V 0 - U 0) (V 1 - U 1) (W 0 - U 0) (W 1 - U 1) (W' 0 - U 0) (W' 1 - U 1) r1 r2 s1 s2
    refine ⟨⟨?_, ?_⟩, e1', e2'⟩
    · linear_combination x1 + 0
    · linear_combination x2 + 0

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.pair_shape_tiles
