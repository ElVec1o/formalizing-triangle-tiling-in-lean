-- Draft/LaczFormalBZL7h10.lean -- Beeson (arXiv 1206.1974v7) Lemma 10.6 (G5c): the tile at the corner A of angle alpha has edges b and c along the two sides at A, so one of the two sides carries a NON-c step at A;
--   with the pigeonhole `side_has_c_step` (BZL7h1) that side has both a c step and a non-c step, and `g5_of_steps` (BZL7h9) gives a boundary vertex starting a Gamma_c edge.
--   `g5c_of_corner` : the hypothesis G5c of `Thm107Open`, proved from ONE extra hypothesis: a corner of the polygon of angle alpha exists (true for the triangle ABC).
-- NOTE, UNAUDITED.  Credit: Beeson (arXiv 1206.1974v7, Lemma 10.6), Laczkovich (DCG 48 (2012), Sect. 4), Beeson-Zhang.
import Erdos634.Draft.LaczFormalBZL7h9

open scoped Classical
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ} [NeZero M]

theorem walkT_head_h10 {D : RegionDissection N} {d : V2} {X Y : Plane} {L : List (Fin N × Plane × Plane)} (W : WalkT D d X Y L) (hL : L ≠ []) :
    ∃ e L', L = e :: L' ∧ e.2.1 = X ∧ TriStep (D.tile e.1) d e.2.1 e.2.2 := by
  cases W with
  | nil => exact absurd rfl hL
  | cons hS W' => exact ⟨_, _, rfl, rfl, hS⟩

theorem walk_ne_nil (D : RegionDissection N) (P : ConvPoly M) (i : Fin M) {L : List (Fin N × Plane × Plane)}
    (W : WalkT D (toV2 (P.e i)) (P.v i) (P.v (i + 1)) L) : L ≠ [] := by
  intro hL0
  subst hL0
  have h := walkT_dist_sum W
  simp only [List.map_nil, List.sum_nil] at h
  have h0 : P.v i = P.v (i + 1) := dist_eq_zero.mp h.symm
  exact P.e_ne_zero P.three_le i (by unfold ConvPoly.e; rw [← h0]; simp)

/-- Consecutive edge vectors of a convex polygon turn left. -/
theorem crs_consecutive_pos (P : ConvPoly M) (k : Fin M) : 0 < crs (toV2 (P.e k)) (toV2 (P.e (k + 1))) := by
  have hf := ConvPoly.fin_facts P.three_le k
  have h := P.c_vertex_pos (j := k) (m := k + 2) hf.2.1 hf.2.2.1
  have h' : P.c k (P.v (k + 2)) = crs (toV2 (P.e k)) (toV2 (P.v (k + 2) - P.v k)) := rfl
  rw [h'] at h
  have e : toV2 (P.v (k + 2) - P.v k) = ((toV2 (P.e k)).1 + (toV2 (P.e (k + 1))).1, (toV2 (P.e k)).2 + (toV2 (P.e (k + 1))).2) := by
    unfold toV2 ConvPoly.e
    rw [hf.2.2.2.2.2]
    ext <;> simp
  rw [e] at h
  unfold crs at h ⊢
  simp only at h ⊢
  nlinarith [h]

theorem fin3_g_eq : ∀ kk f g k2 : Fin 3, f ≠ kk → g ≠ kk → g ≠ f → k2 ≠ kk → k2 ≠ f → g = k2 := by
  intro kk f g k2; fin_cases kk <;> fin_cases f <;> fin_cases g <;> fin_cases k2 <;> simp
theorem fin3_g2_eq : ∀ kk f k2 g2 : Fin 3, f ≠ kk → k2 ≠ kk → k2 ≠ f → g2 ≠ k2 → g2 ≠ kk → g2 = f := by
  intro kk f k2 g2; fin_cases kk <;> fin_cases f <;> fin_cases k2 <;> fin_cases g2 <;> simp
theorem fin3_one_of : ∀ a b c : Fin 3, a ≠ b → a ≠ c → b ≠ c → a = 0 → (b = 1 ∨ c = 1) := by
  intro a b c; fin_cases a <;> fin_cases b <;> fin_cases c <;> simp

/-- The corner counts at a polygon vertex of angle alpha: exactly one corner, of type alpha. -/
theorem corner_alpha_counts (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v)
    (hβ : D.model.angleAt 1 = Real.pi - 3 * D.model.angleAt 0) (hγ : D.model.angleAt 2 = 2 * D.model.angleAt 0)
    (hα : ¬ ∃ r : ℚ, D.model.angleAt 0 = (r : ℝ) * Real.pi) (kA : Fin M) (hkA : P.angle (kA + 1) = D.model.angleAt 0) :
    cnt D idx (P.v (kA + 1)) 0 = 1 ∧ cnt D idx (P.v (kA + 1)) 1 = 0 ∧ cnt D idx (P.v (kA + 1)) 2 = 0 := by
  have hv0 : ∃ j k, (D.tile j).pts k = P.v (kA + 1) := poly_vertex_is_tile_vertex D.toRegionDissection P hreg (kA + 1)
  have hcA := corner_A D P hreg idx hidxA kA hv0
  have hAexp : Asum D idx (P.v (kA + 1)) = (cnt D idx (P.v (kA + 1)) 0 : ℝ) * D.model.angleAt 0 + (cnt D idx (P.v (kA + 1)) 1 : ℝ) * D.model.angleAt 1
      + (cnt D idx (P.v (kA + 1)) 2 : ℝ) * (2 * D.model.angleAt 0) := by
    unfold Asum; rw [Fin.sum_univ_three, hγ]
  have := vtype_arith (α := D.model.angleAt 0) (β := D.model.angleAt 1) hβ hα _ _ _ 1 0 (by rw [← hAexp, hcA, hkA]; push_cast; ring)
  omega

end Erdos634.Draft.LaczFormal.RG
