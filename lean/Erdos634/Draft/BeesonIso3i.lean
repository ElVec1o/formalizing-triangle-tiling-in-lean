import Erdos634.Draft.BeesonIso3h
import Erdos634.Draft.BeesonIso3a

/-!
# Beeson, "Tilings of an isosceles triangle" (arXiv 1206.1974 v7), Lemma 11.8 for a convex polygon (the chord layer assembled)

NOTE, UNAUDITED.  Credit: Michael Beeson (arXiv 1206.1974 v7, Lemma 11.8; arXiv 1206.2229), Laczkovich (DCG 48 (2012), Sect. 4), Beeson-Zhang, Herdt, Zhang.
Formalization debt, not progress on the /goal outcomes.

`chord_no_tile`: `C` a dissection of a convex polygon `P` into tiles with model angles `(alpha, pi - 3 alpha, 2 alpha)`, `alpha` irrational (H1), the interior angle at `B = v_{i+1}`
equal to `alpha + beta`, the tile rational (Beeson Thm 10.7, in the form `a = r b`, `c = s a`).  Then NO tile has a vertex `E` in the relative interior of the side `v_i v_{i+1}` and a vertex
`F` in the relative interior of the side `v_{i+1} v_{i+2}`.
Proof (printed, repaired): the tiles on the `B`-side of the chord `EF` form a right walk `E -> F` (`chord_walk`) with at least two steps (`single_step_false`: the angle step);
the step lengths are tile sides and add up to `|EF|`, itself a tile side (`tile_step`): contradiction with `chord_arith` (`l = a, b, c` are not sums of at least two edges).
PRINTED GAPS (Beeson 1206.1974 v7, Lemma 11.8): (1) the statement "no tile has one vertex on AB and another on BC" is FALSE as written for the vertex `B` itself (a tile at `B` has a vertex on both
sides) and for the corner configurations; the proof treats `E` on AB and `F` on BC both different from `B` ("E on AC" in the print is a typo); here `E`, `F` are in the open sides.  (2) "its angles at E and F must each
be alpha" is unjustified in the print: it needs the angle sum of `BEF` and H1 (`north_arith`).  (3) Case "Tile 1 has its b edge on EF": the print says "b is an integer multiple of a"; the
argument that works is mod `k` (`chord_arith_nat`).
-/

open scoped Classical
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ} [NeZero M]

/-- A list of reals each equal to `a`, `b` or `c`: its sum is `na a + nb b + nc c` with `na + nb + nc` its length. -/
theorem sum_abc_card (a b c : ℝ) (ds : List ℝ) (h : ∀ x ∈ ds, x = a ∨ x = b ∨ x = c) :
    ∃ na nb nc : ℕ, na + nb + nc = ds.length ∧ ds.sum = na * a + nb * b + nc * c := by
  induction ds with
  | nil => exact ⟨0, 0, 0, by simp, by simp⟩
  | cons x ds ih =>
    obtain ⟨na, nb, nc, hl, hs⟩ := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    rcases h x (List.mem_cons_self ..) with hx | hx | hx
    · exact ⟨na + 1, nb, nc, by simp only [List.length_cons]; omega, by simp only [List.sum_cons]; rw [hs, hx]; push_cast; ring⟩
    · exact ⟨na, nb + 1, nc, by simp only [List.length_cons]; omega, by simp only [List.sum_cons]; rw [hs, hx]; push_cast; ring⟩
    · exact ⟨na, nb, nc + 1, by simp only [List.length_cons]; omega, by simp only [List.sum_cons]; rw [hs, hx]; push_cast; ring⟩

theorem chord_no_tile (C : CongruentRegionDissection N) [HasFansC C.toRegionDissection] (P : ConvPoly M) (hreg : C.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((C.tile i).pts k) ((C.tile i).pts k') = dist (C.model.pts (idx i k)) (C.model.pts (idx i k')))
    (hidxA : ∀ i v, C.model.angleAt (idx i v) = (C.tile i).angleAt v)
    (hβ : C.model.angleAt 1 = Real.pi - 3 * C.model.angleAt 0) (hγ : C.model.angleAt 2 = 2 * C.model.angleAt 0)
    (hα : ¬ ∃ r : ℚ, C.model.angleAt 0 = (r : ℝ) * Real.pi)
    (i : Fin M) {t t' : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (ht0' : 0 < t') (ht1' : t' < 1)
    {E F : Plane} (hE : E = (1 - t) • P.v i + t • P.v (i + 1)) (hF : F = (1 - t') • P.v (i + 1) + t' • P.v (i + 1 + 1))
    (hB : P.angle (i + 1) = Real.pi - 2 * C.model.angleAt 0)
    {i0 : Fin N} {kE kF : Fin 3} (hkE : (C.tile i0).pts kE = E) (hkF : (C.tile i0).pts kF = F)
    (hrat : ∃ r s : ℚ, slen C 0 = (r : ℝ) * slen C 1 ∧ slen C 2 = (s : ℝ) * slen C 0)
    (hrel : slen C 2 ^ 2 = slen C 0 ^ 2 + slen C 0 * slen C 1) (htri : slen C 1 < slen C 0 + slen C 2) : False := by
  obtain ⟨hg1, -, -⟩ := chord_geo P i ht1 ht0' hE hF
  have hEF : E ≠ F := by
    intro h
    have : toV2 (F - E) = 0 := by rw [h]; unfold toV2; simp
    rw [this] at hg1; unfold crs at hg1; simp at hg1
  have hvE : ∃ j k, (C.tile j).pts k = E := ⟨i0, kE, hkE⟩
  have hvF : ∃ j k, (C.tile j).pts k = F := ⟨i0, kF, hkF⟩
  obtain ⟨LR, W, hLR⟩ := chord_walk C.toRegionDissection P hreg i ht0 ht1 ht0' hE hF hkE hkF hEF
  -- at least two steps
  have h2 : 2 ≤ LR.length := by
    rcases LR with _ | ⟨⟨j, X0, X1⟩, _ | ⟨e2, rest⟩⟩
    · exact absurd rfl hLR
    · exfalso
      cases W with
      | cons hS W' =>
        cases W'
        exact single_step_false C P hreg idx hidxA hβ hγ hα i ht0 ht1 ht0' ht1' hE hF hEF hB hvE hvF hS
    · simp
  -- the lengths
  have hmem : ∀ x ∈ LR.map (fun e => dist e.2.1 e.2.2), x = slen C 0 ∨ x = slen C 1 ∨ x = slen C 2 := by
    intro x hx
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
    have := side_len_mem C idx hidx (walkR_mem_step W e he)
    rw [dist_comm] at this
    exact this
  obtain ⟨na, nb, nc, hcount, hsum⟩ := sum_abc_card (slen C 0) (slen C 1) (slen C 2) _ hmem
  have hdist := walkR_dist_sum W
  rw [hsum] at hdist
  have hl : dist F E = slen C 0 ∨ dist F E = slen C 1 ∨ dist F E = slen C 2 := by
    rcases tile_step C.toRegionDissection hEF hkE hkF with hS | hS
    · have := side_len_mem C idx hidx hS
      rw [dist_comm] at this
      exact this
    · exact side_len_mem C idx hidx hS
  obtain ⟨r, s, hr, hs⟩ := hrat
  have ha := slen_pos C 0
  have hb := slen_pos C 1
  have hc := slen_pos C 2
  obtain ⟨t0, ht00, k, m, hcop, hlt, hm2, ea, eb, ec⟩ := Erdos634.Draft.BeesonIso3a.tile_param ha hb hc hrel htri hr hs
  have hcount' : na + nb + nc = LR.length := by rw [hcount, List.length_map]
  refine Erdos634.Draft.BeesonIso3a.chord_arith ht00 hcop hlt hm2 ea eb ec (l := dist F E) hl (na := na) (nb := nb) (nc := nc) (by omega) ?_
  rw [dist_comm]
  exact hdist.symm

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.chord_no_tile
