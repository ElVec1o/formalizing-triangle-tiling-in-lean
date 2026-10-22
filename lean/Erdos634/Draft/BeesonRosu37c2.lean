import Mathlib
import Erdos634.Draft.BeesonRosu37c1
import Erdos634.Draft.SideRunGCornerMainB

/-!
# Beeson-Rosu Theorem 37, gap (2): Lemma 34 on the leg for every `m < k`, from the printed hypothesis (no mirror beside the first tile)

NOTE, UNAUDITED.  Credit: Michael Beeson and Rosu (arXiv 2607.23453 v2, Lemma 34, Theorem 37), Beeson, Laczkovich.
Formalization debt, not progress on the /goal outcomes.

AUDIT WARNING 2026-10-22 (automated audit AUDIT_UNAUDITED_2026-10-22L): the existential conclusions of base_edges, leg_counts_thick (as used in thm37_no_a_edges_thick) are witnessed by (0,m,2m) / (0,0,k) by arithmetic alone, so the 'no a edge' claim is NOT in those statements; the tie to the chain's letters is only in the proofs. Do not cite them as geometry. The tied statement (counts = explicit sums of cA over the chain) is in BeesonRosu37c4a.counts_sums and the final theorem to come. base_counts (k<=z with the equation) is non-hollow; its (3,8,9)-(27,27,26) case agrees with the registry row NO_TILING (N=26).

Printed hypothesis of Lemma 34 on a side `S` at an end `V`: "whenever a tile `R` has its `alpha` angle at `V` and its `c` edge on `S`, some other tile
has a vertex at `V` and its `a` or `c` edge on the ray from `V` along the `b` edge of `R`".  The project's `corner_run_mirror` shows the
dichotomy for the tile `T` beside `R` across its `b`-edge: it lays `a` or `c` there (the printed hypothesis) or it is the mirror image of `R`
(`MirrorBeside`).  Hence, with the printed hypothesis in the form `hNoM` (the tile beside the first tile is not its mirror image), alternative
(ii) of `thm:cornerrun` is empty and `k <= z` holds on the leg for EVERY `m < k` (`leg_counts_nomirror`).

NAMED HYPOTHESIS `hNoM` (not derived here): for the first tile `i0` of the leg (it lays `C1` at position 0 from the apex), no tile `T` is the mirror
image of `i0` in its `b`-edge.  Printed derivation (Theorem 37): three tiles with angle `alpha` at the apex, the middle one has its `c` edge on one of the
two inner rays "without loss of generality at the west"; the choice of the leg `AB` versus `CB` is that choice.  Not in the repo: the three-tile
vertex figure at `B`, the identification of the middle tile as the tile beside `i0`, and the either-or between the two legs.
-/

open scoped Classical
set_option linter.unusedVariables false

namespace Erdos634.BeesonRosu37c2

open Erdos634.Geometry Erdos634.Draft.FDBBaseBetaE1 Erdos634.Draft.SideRunG Erdos634.Draft.SideRunGA
  Erdos634.Draft.SideRun Erdos634.Draft.W2E1 Erdos634.BaseBetaTargetCoord Erdos634.TilePlacement Erdos634.Geometry.Dissection
  Erdos634.BeesonRosu37b1

variable {N : ℕ}

/-- **Lemma 34 on the leg `AB`, every `m < k`**, with the printed hypothesis in the form "no mirror beside the first tile":
`k <= z` for the counts of the leg. -/
theorem leg_counts_nomirror (k m : ℕ) (hm : 1 ≤ m) (hmk : m < k) (hco : Nat.Coprime m k) (D₀ : CongruentDissection N)
    (hMod : HasSides D₀.model ((m : ℝ) * k) ((k : ℝ) ^ 2 - (m : ℝ) ^ 2) ((k : ℝ) ^ 2))
    (τ : Equiv.Perm (Fin 3))
    (hApex : cornerAngle (D₀.target.pts (τ 2)) (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) =
      3 * modelAlpha (m : ℝ) (k : ℝ))
    (hBeta : cornerAngle (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) (D₀.target.pts (τ 2)) =
      modelBeta (m : ℝ) (k : ℝ))
    (hlen : dist (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) = (k : ℝ) ^ 3)
    (hNoM : ∀ i₀ T : Fin N, LaysBaseOn D₀ (m : ℝ) (k : ℝ) (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) i₀ Ty.C1 0 →
      ¬ MirrorBeside D₀ (m : ℝ) (k : ℝ) (D₀.target.pts (τ 0)) i₀ T) :
    ∃ x y z : ℕ, (x : ℤ) * ((k : ℤ) * m) + y * ((k : ℤ) ^ 2 - (m : ℤ) ^ 2) + z * (k : ℤ) ^ 2 = (k : ℤ) ^ 3 ∧ k ≤ z := by
  obtain ⟨D, g, L, ax, ay, hL, hdist, hD, hP, hB, S, Co, -⟩ :=
    setup_of_corners m k hm hmk hco D₀ hMod τ (Or.inr hApex) (Or.inl hBeta)
  obtain ⟨c, X, tile, τ', Ch⟩ := S.exists_chainG
  obtain ⟨x, y, z, hxyz, hz, hz'⟩ := counts_gen S Ch
  refine ⟨x, y, z, ?_, ?_⟩
  · have : (((x : ℤ) * ((k : ℤ) * m) + y * ((k : ℤ) ^ 2 - (m : ℤ) ^ 2) + z * (k : ℤ) ^ 2 : ℤ) : ℝ) =
        (((k : ℤ) ^ 3 : ℤ) : ℝ) := by
      push_cast
      rw [← hlen, hdist]
      linarith [hxyz]
    exact_mod_cast this
  · rcases corner_side_theorem S Co Ch with h | ⟨k', hk1, hkf, hkm, hrun, hsucc⟩
    · exact hz h
    · exfalso
      have hsucc' : k' = c ∨ (k' < c ∧ τ' k' ≠ Ty.B1 ∧ τ' k' ≠ Ty.C1) := by
        rcases hsucc with h | ⟨h, h'⟩
        · exact Or.inl h
        · refine Or.inr ⟨h, ?_, ?_⟩ <;> rcases h' with h' | h' | h' <;> rw [h'] <;> decide
      have hM := corner_run_mirror S Co Ch hk1 hkf hrun hsucc'
      have hU := Ch.htile 0 (by omega)
      rw [hrun 0 (by omega), Ch.hX0] at hU
      obtain ⟨T, hT⟩ := mirrorBeside_of_mirrorAt hD hP S hU hM
      exact hNoM (tile 0) T (laysOn_of_baseTile hL hD hP hB hU) hT

/-- **Neither side carries an `a` edge, every `m < k`** (counts of `AC` and of the leg `AB`): the sides of the target and the model are
hypotheses (`τ` is the labelling of `HasSides`: `τ 2` the apex, `τ 0`, `τ 1` the base corners, the leg is `[τ 2, τ 0]`), the corner angles are
derived (`corners_of_dists`), and the printed hypothesis of Lemma 34 on the leg is the named `hNoM`. -/
theorem thm37_no_a_edges_nomirror (k m : ℕ) (hm : 1 ≤ m) (hmk : m < k) (hco : Nat.Coprime m k) (D₀ : CongruentDissection N)
    (τ : Equiv.Perm (Fin 3))
    (h1 : dist (D₀.target.pts (τ 1)) (D₀.target.pts (τ 2)) = (k : ℝ) ^ 3)
    (h2 : dist (D₀.target.pts (τ 2)) (D₀.target.pts (τ 0)) = (k : ℝ) ^ 3)
    (h3 : dist (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) = (m : ℝ) * (3 * (k : ℝ) ^ 2 - (m : ℝ) ^ 2))
    (hMod : HasSides D₀.model ((m : ℝ) * k) ((k : ℝ) ^ 2 - (m : ℝ) ^ 2) ((k : ℝ) ^ 2))
    (hNoM : ∀ i₀ T : Fin N, LaysBaseOn D₀ (m : ℝ) (k : ℝ) (D₀.target.pts (τ 2)) (D₀.target.pts (τ 0)) i₀ Ty.C1 0 →
      ¬ MirrorBeside D₀ (m : ℝ) (k : ℝ) (D₀.target.pts (τ 2)) i₀ T) :
    (∃ x y z : ℕ, x = 0 ∧ y = m ∧ z = 2 * m) ∧
    ∃ x y z : ℕ, x = 0 ∧ (x : ℤ) * ((k : ℤ) * m) + y * ((k : ℤ) ^ 2 - (m : ℤ) ^ 2) + z * (k : ℤ) ^ 2 = (k : ℤ) ^ 3 := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hmkR : (m : ℝ) < k := by exact_mod_cast hmk
  obtain ⟨cA, cB, cC⟩ := Erdos634.BeesonRosu37c1.corners_of_dists D₀.target hmR hmkR τ h1 h2 h3
  obtain ⟨x0, y0, z0, h0x, h0y, h0z, -⟩ := base_edges k m hm hmk hco D₀ ⟨τ, h1, h2, h3⟩ hMod
  have e2 : (finRotate 3).symm.trans τ 2 = τ 1 := rfl
  have e0 : (finRotate 3).symm.trans τ 0 = τ 2 := rfl
  have e1 : (finRotate 3).symm.trans τ 1 = τ 0 := rfl
  obtain ⟨x, y, z, h, hz⟩ := leg_counts_nomirror k m hm hmk hco D₀ hMod ((finRotate 3).symm.trans τ)
    (by rw [e2, e0, e1, Erdos634.Geometry.cornerAngle, EuclideanGeometry.angle_comm]; exact cC)
    (by rw [e2, e0, e1, Erdos634.Geometry.cornerAngle, EuclideanGeometry.angle_comm]; exact cA)
    (by rw [e0, e1]; exact h2)
    (by rw [e0, e1]; exact hNoM)
  refine ⟨⟨x0, y0, z0, h0x, h0y, h0z⟩, x, y, z, ?_, h⟩
  have := leg_p1_zero (k := (k : ℤ)) (m := (m : ℤ)) (p1 := (x : ℤ)) (q1 := (y : ℤ)) (r1 := (z : ℤ)) (by exact_mod_cast hm)
    (by exact_mod_cast hmk) (Int.natCast_nonneg x) (Int.natCast_nonneg y) (by linear_combination h) (by exact_mod_cast hz)
  exact_mod_cast this

end Erdos634.BeesonRosu37c2

#print axioms Erdos634.BeesonRosu37c2.leg_counts_nomirror
#print axioms Erdos634.BeesonRosu37c2.thm37_no_a_edges_nomirror
