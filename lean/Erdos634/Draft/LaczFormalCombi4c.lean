-- Draft/LaczFormalCombi4c.lean -- Laczkovich, DCG 48 (2012), Lemma 3.8, IRREGULAR case, wired to an actual tiling:
-- a `PolyTiling N 4` of a rectangle (all four angles pi/2) whose model is a right triangle (angle at vertex 2 equal pi/2), irregular in the sense of
-- `IrregularIdx` (at some point the corner counts of types 0 and 1 differ): the ratio of the two sides of the rectangle is a rational multiple of
-- (leg a)/(leg b) or of (leg b)/(leg a)  [i.e. `side0/side3 = q a/b` or `side3/side0 = q a/b`].
-- Ingredients: `side_comb` (Combi4a), the area equation `poly4_area`, the vertex relation p alpha + q beta + r gamma = e pi/2 (`vertex_A`, the corner counts have
-- equal totals `sum_cnt_vtx`, so a point with p > q exists), the printed list (8) (`alpha_list`, Combi4b), the five cases (Combi2, Combi3c).
-- NOT in this file: the REGULAR case (Theorem 2.1 for the relabelled model), see (private working notes, not included).
-- NOTE, UNAUDITED.  Credit: Laczkovich (Discrete Comput. Geom. 48 (2012), Lemma 3.8, Theorem 2.1; Combinatorica 10 (1990)), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalCombi4a
import Erdos634.Draft.LaczFormalCombi4b

open scoped Classical
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement
open Erdos634.Draft.LaczFormal.RG

namespace Erdos634.Laczkovich.Combi4

/-- A point where the corner count of type `l` is strictly larger than that of type `l'`, as soon as the counts differ somewhere. -/
theorem exists_gt_cnt {N : ℕ} (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) (l l' : Fin 3)
    (h : ∃ X, cnt D idx X l ≠ cnt D idx X l') :
    ∃ X ∈ Erdos634.Draft.LaczFormal.RG.vtxSet D.toRegionDissection, cnt D idx X l' < cnt D idx X l := by
  classical
  by_contra hno
  push Not at hno
  obtain ⟨X0, hX0⟩ := h
  have hle : ∀ X ∈ Erdos634.Draft.LaczFormal.RG.vtxSet D.toRegionDissection, cnt D idx X l ≤ cnt D idx X l' := fun X hX => hno X hX
  have hsum : ∑ X ∈ Erdos634.Draft.LaczFormal.RG.vtxSet D.toRegionDissection, cnt D idx X l =
      ∑ X ∈ Erdos634.Draft.LaczFormal.RG.vtxSet D.toRegionDissection, cnt D idx X l' := by
    rw [sum_cnt_vtx D idx l, sum_cnt_vtx D idx l']
  have := (Finset.sum_eq_sum_iff_of_le hle).mp hsum
  exact hX0 (this X0 (mem_vtx_of_cnt_ne D idx hX0))

/-- At a vertex of a tiling of a rectangle the corner angles sum to `e pi/2`, `e in {1, 2, 4}`. -/
theorem Asum_half {N : ℕ} (T : PolyTiling N 4) (idx : Fin N → Equiv.Perm (Fin 3))
    (hidxA : ∀ i v, T.C.model.angleAt (idx i v) = (T.C.tile i).angleAt v) (hang : ∀ i, T.P.angle i = Real.pi / 2)
    {X : Plane} (hX : X ∈ Erdos634.Draft.LaczFormal.RG.vtxSet T.C.toRegionDissection) :
    ∃ e : ℕ, (e = 1 ∨ e = 2 ∨ e = 4) ∧ Asum T.C idx X = e * (Real.pi / 2) := by
  classical
  haveI : HasFansC T.C.toRegionDissection := hasFansC_poly _ T.P T.region_eq
  have hvert := Erdos634.Draft.LaczFormal.RG.mem_vtxSet.mp hX
  rcases vertex_A T.C T.P T.region_eq idx hidxA hvert with ⟨-, h | h⟩ | ⟨-, h | ⟨k, -, h⟩⟩
  · exact ⟨4, by simp, by rw [h]; ring⟩
  · exact ⟨2, by simp, by rw [h]; ring⟩
  · exact ⟨2, by simp, by rw [h]; ring⟩
  · exact ⟨1, by simp, by rw [h, hang]; ring⟩

/-- The arithmetic of the vertex relation: `p theta + q phi + r (pi/2) = e pi/2`, `theta + phi = pi/2`, `p > q`  ==>  `m theta = s pi/2`, `m >= 1`, `s <= 4`. -/
theorem rel_extract (θ φ : ℝ) (hθ : 0 < θ) (hsum : θ + φ = Real.pi / 2) (p q r e : ℕ) (he : e = 1 ∨ e = 2 ∨ e = 4) (hpq : q < p)
    (h : (p : ℝ) * θ + q * φ + r * (Real.pi / 2) = e * (Real.pi / 2)) :
    ∃ m s : ℕ, 0 < m ∧ s ≤ 4 ∧ (m : ℝ) * θ = s * Real.pi / 2 := by
  have hpi := Real.pi_pos
  have hφ : φ = Real.pi / 2 - θ := by linarith
  have h1 : ((p : ℝ) - q) * θ = ((e : ℝ) - q - r) * (Real.pi / 2) := by
    rw [hφ] at h; linarith
  have hpq' : (0 : ℝ) < (p : ℝ) - q := by
    have : (q : ℝ) < p := by exact_mod_cast hpq
    linarith
  have hpos : 0 < ((e : ℝ) - q - r) * (Real.pi / 2) := by rw [← h1]; positivity
  have hpos' : (0 : ℝ) < (e : ℝ) - q - r := by
    by_contra hc; push Not at hc; nlinarith
  have hqr : q + r < e := by
    have : (q : ℝ) + r < e := by linarith
    exact_mod_cast this
  refine ⟨p - q, e - q - r, by omega, by omega, ?_⟩
  have c1 : ((p - q : ℕ) : ℝ) = (p : ℝ) - q := Nat.cast_sub hpq.le
  have c2 : ((e - q - r : ℕ) : ℝ) = (e : ℝ) - q - r := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
  rw [c1, c2]; linarith

end Erdos634.Laczkovich.Combi4

#print axioms Erdos634.Laczkovich.Combi4.exists_gt_cnt
#print axioms Erdos634.Laczkovich.Combi4.Asum_half
#print axioms Erdos634.Laczkovich.Combi4.rel_extract
