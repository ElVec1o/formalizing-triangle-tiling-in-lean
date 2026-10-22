import Erdos634.Draft.BeesonIso4c

/-!
# Beeson, "Tilings of an isosceles triangle" (arXiv 1206.1974 v7), Lemma 11.10, first half: at least THREE tiles are supported by a side with two `alpha` corners

NOTE, UNAUDITED.  Credit: Michael Beeson (arXiv 1206.1974 v7, Lemma 11.10), Laczkovich (DCG 48 (2012), Sect. 4), Beeson-Zhang, Herdt, Zhang.
Formalization debt, not progress on the /goal outcomes.

`base_ge_three`: a dissection of a convex polygon by tiles with model angles `(alpha, pi - 3 alpha, 2 alpha)` (H1: `alpha` not in `Q pi`, `a < c`) and a side `k+1` whose two end corners both have
angle `alpha`: every walk of tiles along that side has at least 3 steps (the tiles supported by the side).  Printed: "Hence there are indeed at least three tiles supported by AC."
(Printed text: also for the tile `(alpha, beta, 2 pi/3)`; here only `gamma = 2 alpha`.)
Witness status: the hypotheses hold for the 1125-tiling (`witness_1125_thm107` of BZL7h17: model angles, H1, an `alpha` corner; `a < c` since `(a,c) = (64, 96)`), and the base of that
tiling is covered by more than 3 tiles.
-/

open scoped Classical
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ} [NeZero M]

/-- A corner of a tile located at an `alpha` vertex of the polygon has label `alpha`. -/
theorem corner_label0 (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v)
    (hβ : D.model.angleAt 1 = Real.pi - 3 * D.model.angleAt 0) (hγ : D.model.angleAt 2 = 2 * D.model.angleAt 0)
    (hα : ¬ ∃ r : ℚ, D.model.angleAt 0 = (r : ℝ) * Real.pi)
    (kA : Fin M) (hkA : P.angle (kA + 1) = D.model.angleAt 0) {j : Fin N} {kk : Fin 3} (hk : (D.tile j).pts kk = P.v (kA + 1)) :
    idx j kk = 0 := by
  obtain ⟨hn0, hn1, hn2⟩ := corner_alpha_counts D P hreg idx hidxA hβ hγ hα kA hkA
  have := cnt_pos_of_corner_h1 D idx hk (rfl : idx j kk = idx j kk)
  generalize idx j kk = z at this ⊢
  fin_cases z
  · rfl
  · simp at this; omega
  · simp at this; omega

theorem walkT_cons_inv' {D : RegionDissection N} {d : V2} {X Y : Plane} {i : Fin N} {X0 X1 : Plane} {L : List (Fin N × Plane × Plane)}
    (W : WalkT D d X Y ((i, X0, X1) :: L)) : X0 = X ∧ TriStep (D.tile i) d X X1 ∧ WalkT D d X1 Y L := by
  cases W with
  | cons hS W' => exact ⟨rfl, hS, W'⟩

theorem walkT_nil_inv' {D : RegionDissection N} {d : V2} {X Y : Plane} (W : WalkT D d X Y []) : X = Y := by
  cases W
  rfl

theorem base_ge_three (C : CongruentRegionDissection N) [HasFansC C.toRegionDissection] (P : ConvPoly M) (hreg : C.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((C.tile i).pts k) ((C.tile i).pts k') = dist (C.model.pts (idx i k)) (C.model.pts (idx i k')))
    (hidxA : ∀ i v, C.model.angleAt (idx i v) = (C.tile i).angleAt v)
    (hβ : C.model.angleAt 1 = Real.pi - 3 * C.model.angleAt 0) (hγ : C.model.angleAt 2 = 2 * C.model.angleAt 0)
    (hα : ¬ ∃ r : ℚ, C.model.angleAt 0 = (r : ℝ) * Real.pi) (hac : slen C 0 < slen C 2)
    (k : Fin M) (hi0 : P.angle (k + 1) = C.model.angleAt 0) (hi1 : P.angle (k + 1 + 1) = C.model.angleAt 0)
    {L : List (Fin N × Plane × Plane)} (W : WalkT C.toRegionDissection (toV2 (P.e (k + 1))) (P.v (k + 1)) (P.v (k + 1 + 1)) L) :
    3 ≤ L.length := by
  have hne := walk_ne_nil C.toRegionDissection P (k + 1) W
  rcases L with _ | ⟨e1, _ | ⟨e2, _ | ⟨e3, L'⟩⟩⟩
  · exact absurd rfl hne
  · exfalso
    obtain ⟨e1j, e10, e11⟩ := e1
    obtain ⟨-, hS, W'⟩ := walkT_cons_inv' W
    have hY := walkT_nil_inv' W'
    rw [hY] at hS
    obtain ⟨kk, f, g, hk, hf, hfk, -⟩ := hS
    have h1 := corner_label0 C P hreg idx hidxA hβ hγ hα k hi0 hk
    have h2 := corner_label0 C P hreg idx hidxA hβ hγ hα (k + 1) hi1 hf
    exact hfk ((idx e1j).injective (h2.trans h1.symm))
  · exfalso
    obtain ⟨t, ht0, ht1, hPm⟩ := walkT_open_side C.toRegionDissection P (k + 1) W (L1 := []) (x := e1) (y := e2) (L2 := []) rfl
    obtain ⟨e1j, e10, e11⟩ := e1
    obtain ⟨e2j, e20, e21⟩ := e2
    obtain ⟨h0, hS1, W'⟩ := walkT_cons_inv' W
    obtain ⟨h0', hS2, W''⟩ := walkT_cons_inv' W'
    have hY := walkT_nil_inv' W''
    rw [hY] at hS2
    simp only at hPm
    rw [h0'] at hPm
    exact two_tile_contra C P hreg idx hidx hidxA hβ hγ hα hac k hi0 hi1 hS1 hS2 ht0 ht1 hPm
  · simp

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.base_ge_three
