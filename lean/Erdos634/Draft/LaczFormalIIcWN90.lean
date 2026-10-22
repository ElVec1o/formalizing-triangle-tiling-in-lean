-- Draft/LaczFormalIIcWN90.lean -- Laczkovich (DCG 48 (2012), Sect. 6.3, Lemma 6.2), tile-level helpers for "an edge of Gamma_except misses the edges of Gamma_kite" (printed: "Clearly, the segment VW is in the exterior of C1").
-- (a) `inner_not_vertex`: a point of the open side of a tile is not a vertex of it;
-- (b) `left_tile_eq_inner`: two tiles with a LEFT step along the same direction `d` and a common point in both open sides are equal (half-discs);
-- (c) `left_tile_eq_head`: a tile with a left step ENDING at `V` along `d` (corner at `V`) and a tile with a left step along `d` having `V` in its open side are equal (the corner sector meets the half-disc).
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcWN14
import Erdos634.Draft.LaczFormalIIcWN16
import Erdos634.Draft.LaczFormalIIcWN17
import Erdos634.Draft.LaczFormalIIcSharp2
import Erdos634.Draft.LaczFormalRG12GExcEndT

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement Erdos634.CertCoord

namespace Erdos634.Draft.LaczFormal.RG

variable {N : ℕ}

theorem inner_not_vertex (T : Tri) {a b c : Fin 3} (hab : a ≠ b) {Y : Plane} (hY : Y ∈ openSegment ℝ (T.pts a) (T.pts b)) : Y ≠ T.pts c := by
  intro h
  have hc := fun m => coord_pos_iff T hab rfl rfl hY m
  have c1 := (hc a).2 (Or.inl rfl)
  have c2 := (hc b).2 (Or.inr rfl)
  have e : ∀ m, m ≠ c → T.basis.coord m Y = 0 := fun m hm => by
    rw [h]; exact Erdos634.Draft.NearBaseVertex.coord_other T hm
  have h1 : a = c := by by_contra hne; rw [e a hne] at c1; exact lt_irrefl _ c1
  have h2 : b = c := by by_contra hne; rw [e b hne] at c2; exact lt_irrefl _ c2
  exact hab (h1.trans h2.symm)

theorem tristep_dir_ne {T : Tri} {d : V2} {U U' : Plane} (h : TriStep T d U U') : d ≠ 0 := by
  obtain ⟨-, -, -, -, -, -, -, -, hp, -⟩ := h
  exact hp.ne_right

theorem crs_left_normal {d : V2} (hd : d ≠ 0) : 0 < crs d (-d.2, d.1) := by
  have : crs d (-d.2, d.1) = d.1 ^ 2 + d.2 ^ 2 := by unfold crs; ring
  rw [this]; exact v2_sq_pos hd

/-- Two tiles with a left step along the same `d` and a common point in both open sides coincide. -/
theorem left_tile_eq_inner (D : RegionDissection N) {d : V2} {i1 i2 : Fin N} {U1 U1' U2 U2' V : Plane}
    (h1 : TriStep (D.tile i1) d U1 U1') (h2 : TriStep (D.tile i2) d U2 U2') (hV1 : V ∈ openSegment ℝ U1 U1') (hV2 : V ∈ openSegment ℝ U2 U2') : i1 = i2 := by
  by_contra hne
  have hd : d ≠ 0 := tristep_dir_ne h1
  obtain ⟨t1, ht10, ht11, hVt1⟩ := openSegment_param hV1
  obtain ⟨t2, ht20, ht21, hVt2⟩ := openSegment_param hV2
  obtain ⟨r1, hr1, hd1⟩ := halfdisc (D.tile i1) h1 ht10 ht11
  obtain ⟨r2, hr2, hd2⟩ := halfdisc (D.tile i2) h2 ht20 ht21
  rw [← hVt1] at hd1
  rw [← hVt2] at hd2
  obtain ⟨ε, hε0, hεd⟩ := exists_eps V (mkPt (-d.2) d.1) (lt_min hr1 hr2)
  have hrot := crs_left_normal hd
  have hl : 0 < crs d (toV2 ((V + ε • mkPt (-d.2) d.1) - V)) := by
    rw [crs_shift d V ε (-d.2, d.1)]; exact mul_pos hε0 hrot
  have wi := hd1 _ (lt_of_lt_of_le hεd (min_le_left _ _)) hl
  have wj := hd2 _ (lt_of_lt_of_le hεd (min_le_right _ _)) hl
  exact Set.disjoint_left.1 (D.interiors_disjoint hne) wi wj

/-- A tile with a left step ENDING at `V` along `d` and a tile with a left step along `d` with `V` in its open side coincide. -/
theorem left_tile_eq_head (D : RegionDissection N) {d : V2} {i1 i2 : Fin N} {A0 V U U' : Plane}
    (h1 : TriStep (D.tile i1) d A0 V) (h2 : TriStep (D.tile i2) d U U') (hV : V ∈ openSegment ℝ U U') : i1 = i2 := by
  by_contra hne
  have hd : d ≠ 0 := tristep_dir_ne h1
  obtain ⟨t2, ht20, ht21, hVt2⟩ := openSegment_param hV
  obtain ⟨r2, hr2, hd2⟩ := halfdisc (D.tile i2) h2 ht20 ht21
  rw [← hVt2] at hd2
  obtain ⟨kk, f, g, hk, hf, hfk, hgk, hgf, hpar, hleft⟩ := h1
  set G := (D.tile i1).pts g with hG
  set vec : Plane := (A0 - V) + (G - V) with hvec
  obtain ⟨ε, hε0, hεd⟩ := exists_eps V vec hr2
  set ε' : ℝ := min ε (1 / 4) with hε'
  have hε'0 : 0 < ε' := lt_min hε0 (by norm_num)
  have hε'le : ε' ≤ ε := min_le_left _ _
  have hε'4 : ε' ≤ 1 / 4 := min_le_right _ _
  have hdist : dist (V + ε' • vec) V < r2 := by
    have e1 : dist (V + ε' • vec) V = ε' * ‖vec‖ := by rw [dist_eq_norm]; simp [norm_smul, abs_of_pos hε'0]
    have e2 : dist (V + ε • vec) V = ε * ‖vec‖ := by rw [dist_eq_norm]; simp [norm_smul, abs_of_pos hε0]
    rw [e1]; rw [e2] at hεd
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hε'le (norm_nonneg _)) hεd
  -- the point lies in the corner sector of tile i1 at V
  have hsec := sector_interior (D.tile i1) (kk := f) (f := kk) (g := g) (Ne.symm hfk) hgf hgk (s := ε') (s' := ε') hε'0 hε'0 (by linarith)
  rw [hf, hk] at hsec
  have hq : V + ε' • (A0 - V) + ε' • (G - V) = V + ε' • vec := by rw [hvec, smul_add, add_assoc]
  rw [hq] at hsec
  -- left of d
  have hA : crs d (toV2 (A0 - V)) = 0 := by
    have := hpar.1
    unfold crs at this ⊢
    simp only [toV2, PiLp.sub_apply] at this ⊢
    linarith
  have hGl : 0 < crs d (toV2 (G - V)) := by
    have e : toV2 (G - V) = toV2 (G - A0) + toV2 (A0 - V) := by
      unfold toV2; ext <;> simp
    have h0 := hleft
    have : crs d (toV2 (G - V)) = crs d (toV2 (G - A0)) + crs d (toV2 (A0 - V)) := by
      rw [e]; unfold crs; simp only [Prod.fst_add, Prod.snd_add]; ring
    rw [this, hA, add_zero]
    exact h0
  have hl : 0 < crs d (toV2 ((V + ε' • vec) - V)) := by
    have e : toV2 ((V + ε' • vec) - V) = (ε' * (toV2 (A0 - V)).1 + ε' * (toV2 (G - V)).1, ε' * (toV2 (A0 - V)).2 + ε' * (toV2 (G - V)).2) := by
      unfold toV2; ext <;> simp [hvec] <;> ring
    rw [e]
    unfold crs at hA hGl ⊢
    simp only at hA hGl ⊢
    nlinarith
  have wj := hd2 _ hdist hl
  exact Set.disjoint_left.1 (D.interiors_disjoint hne) hsec wj

#print axioms left_tile_eq_inner
#print axioms left_tile_eq_head

end Erdos634.Draft.LaczFormal.RG
