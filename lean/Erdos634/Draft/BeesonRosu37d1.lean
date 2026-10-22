import Mathlib
import Erdos634.Draft.BeesonRosu37c4a

/-!
# Beeson-Rosu Theorem 37: the edge decomposition of a side as a statement about the dissection (replaces the tautological existentials)

NOTE, UNAUDITED.  Credit: Michael Beeson and Rosu (arXiv 2607.23453 v2, Theorem 37, Lemma 34, Lemma 30(D)), Beeson, Laczkovich.
Formalization debt, not progress on the /goal outcomes.

Why: the conclusions `base_edges`, `leg_counts`, `thm37_no_a_edges_*` (BeesonRosu37b1, 37c2) are existentials over naturals witnessed by `(0,m,2m)`,
`(0,0,k)` by arithmetic alone.  Here the conclusion is `SideTiling D₀ e f P B c X tile ty`: a list of `c` tiles of the REAL dissection `D₀`, tile `k`
laying a base of type `ty k` on the segment `[P, B]` at distance `X k` from `P` (`LaysBaseOn`: two of its vertices are the points of `[P,B]` at `X k`
and `X k + len`, its third vertex at the two side distances), the steps `X (k+1) = X k + len (ty k)`, `X 0 = 0`, `X c = dist P B`.  The letters
`cA, cB, cC` (number of `a`, `b`, `c` edges) are summed over THIS list, and "no `a` edge on the side" is `∑ cA = 0`, hence every tile of the list has
its `b` or `c` edge on the side.
-/

open scoped Classical
set_option linter.unusedVariables false

namespace Erdos634.BeesonRosu37d1

open Erdos634.Geometry Erdos634.Draft.FDBBaseBetaE1 Erdos634.Draft.SideRunG Erdos634.Draft.SideRunGA
  Erdos634.Draft.SideRun Erdos634.Draft.W2E1 Erdos634.BaseBetaTargetCoord Erdos634.TilePlacement Erdos634.Geometry.Dissection
  Erdos634.BeesonRosu37b1 Erdos634.BeesonRosu37c2

variable {N : ℕ}

/-- **The tile list along the side `[P, B]`**: tile `k` of `D₀` lays a base of type `ty k` on `[P,B]` at distance `X k`; consecutive; covering `[P,B]`. -/
def SideTiling (D₀ : CongruentDissection N) (e f : ℝ) (P B : Plane) (c : ℕ) (X : ℕ → ℝ) (tile : ℕ → Fin N) (ty : ℕ → Ty) : Prop :=
  0 < c ∧ X 0 = 0 ∧ X c = dist P B ∧ (∀ k, k < c → X (k + 1) = X k + (ty k).lenG e f) ∧
    ∀ k, k < c → LaysBaseOn D₀ e f P B (tile k) (ty k) (X k)

/-- the number of `a`, `b`, `c` edges on the side, summed over the list -/
def edgeCounts (c : ℕ) (ty : ℕ → Ty) : ℕ × ℕ × ℕ :=
  (∑ k ∈ Finset.range c, (ty k).cA, ∑ k ∈ Finset.range c, (ty k).cB, ∑ k ∈ Finset.range c, (ty k).cC)

/-- **Base `AC` of `T_1(m,k)`**: the tile list along the base has edge counts exactly `(0, m, 2m)`: no `a` edge, `m` edges `b`, `2m` edges `c`. -/
theorem base_tiling (k m : ℕ) (hm : 1 ≤ m) (hmk : m < k) (hco : Nat.Coprime m k) (D₀ : CongruentDissection N)
    (τ : Equiv.Perm (Fin 3))
    (h1 : dist (D₀.target.pts (τ 1)) (D₀.target.pts (τ 2)) = (k : ℝ) ^ 3)
    (h2 : dist (D₀.target.pts (τ 2)) (D₀.target.pts (τ 0)) = (k : ℝ) ^ 3)
    (h3 : dist (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) = (m : ℝ) * (3 * (k : ℝ) ^ 2 - (m : ℝ) ^ 2))
    (hMod : HasSides D₀.model ((m : ℝ) * k) ((k : ℝ) ^ 2 - (m : ℝ) ^ 2) ((k : ℝ) ^ 2)) :
    ∃ (c : ℕ) (X : ℕ → ℝ) (tile : ℕ → Fin N) (ty : ℕ → Ty),
      SideTiling D₀ (m : ℝ) (k : ℝ) (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) c X tile ty ∧
      edgeCounts c ty = (0, m, 2 * m) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hkR : (0 : ℝ) < k := by have : (m : ℝ) < k := by exact_mod_cast hmk
                               linarith
  have hK : (0 : ℝ) < 3 * (k : ℝ) ^ 2 - (m : ℝ) ^ 2 := by
    have hmk' : (m : ℝ) < k := by exact_mod_cast hmk
    nlinarith [mul_pos hmR hmR, mul_pos hkR hkR]
  obtain ⟨D, g, ax, ay, hD, hP, hB, S, Co⟩ := setup_TG_pinned m k hm hmk hco one_pos D₀ τ
    (by rw [one_mul]; exact h1) (by rw [one_mul]; exact h2) (by rw [one_mul]; exact h3) hMod
  have hL : 0 < (1 : ℝ) * ((m : ℝ) * (3 * (k : ℝ) ^ 2 - (m : ℝ) ^ 2)) := by rw [one_mul]; positivity
  obtain ⟨c, X, tile, ty, Ch, hrun⟩ := S.side_theoremG_chain Co
  obtain ⟨hsum, hrunz⟩ := Erdos634.BeesonRosu37c4a.counts_sums S Ch
  have hz := hrunz hrun
  have hsumZ : (((∑ k ∈ Finset.range c, (ty k).cA : ℕ) : ℤ) * ((k : ℤ) * m) + ((∑ k ∈ Finset.range c, (ty k).cB : ℕ) : ℤ) * ((k : ℤ) ^ 2 - (m : ℤ) ^ 2)
      + ((∑ k ∈ Finset.range c, (ty k).cC : ℕ) : ℤ) * (k : ℤ) ^ 2) = (m : ℤ) * (((k : ℤ) ^ 2 - (m : ℤ) ^ 2) + 2 * (k : ℤ) ^ 2) := by
    have : ((((∑ k ∈ Finset.range c, (ty k).cA : ℕ) : ℤ) * ((k : ℤ) * m) + ((∑ k ∈ Finset.range c, (ty k).cB : ℕ) : ℤ) * ((k : ℤ) ^ 2 - (m : ℤ) ^ 2)
      + ((∑ k ∈ Finset.range c, (ty k).cC : ℕ) : ℤ) * (k : ℤ) ^ 2 : ℤ) : ℝ) = (((m : ℤ) * (((k : ℤ) ^ 2 - (m : ℤ) ^ 2) + 2 * (k : ℤ) ^ 2) : ℤ) : ℝ) := by
      push_cast at hsum ⊢
      linarith [hsum]
    exact_mod_cast this
  have hcz : IsCoprime (m : ℤ) (k : ℤ) := Nat.isCoprime_iff_coprime.mpr hco
  have hD30 := Erdos634.BeesonRowL30.lemma30_D (k := (k : ℤ)) (m := (m : ℤ)) (by exact_mod_cast hm)
    (by exact_mod_cast hmk) hcz (Int.natCast_nonneg _) (Int.natCast_nonneg _) (by exact_mod_cast hz) hsumZ
  refine ⟨c, X, tile, ty, ⟨Ch.hm0, Ch.hX0, ?_, Ch.hstep, fun j hj => ?_⟩, ?_⟩
  · rw [Ch.hXm, ← h3, one_mul]
  · exact laysOn_of_baseTile hL hD hP hB (Ch.htile j hj)
  · unfold edgeCounts
    obtain ⟨a1, a2, a3⟩ := hD30
    simp only [Prod.mk.injEq]
    refine ⟨by exact_mod_cast a1, by exact_mod_cast a2, by exact_mod_cast a3⟩


/-- **Leg `AB` of `T_1(m,k)`** (`[τ 2, τ 0]`, `3α` at the apex `τ 2`, `β` at `τ 0`), every `m < k`, under the named hypothesis `hNoM` (no mirror beside the
first tile; the printed hypothesis of Lemma 34): the tile list along the leg has NO `a` edge, and `k` of its edges are `c` edges.  `hNoM` is NOT derived. -/
theorem leg_tiling (k m : ℕ) (hm : 1 ≤ m) (hmk : m < k) (hco : Nat.Coprime m k) (D₀ : CongruentDissection N)
    (τ : Equiv.Perm (Fin 3))
    (h1 : dist (D₀.target.pts (τ 1)) (D₀.target.pts (τ 2)) = (k : ℝ) ^ 3)
    (h2 : dist (D₀.target.pts (τ 2)) (D₀.target.pts (τ 0)) = (k : ℝ) ^ 3)
    (h3 : dist (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) = (m : ℝ) * (3 * (k : ℝ) ^ 2 - (m : ℝ) ^ 2))
    (hMod : HasSides D₀.model ((m : ℝ) * k) ((k : ℝ) ^ 2 - (m : ℝ) ^ 2) ((k : ℝ) ^ 2))
    (hNoM : ∀ i₀ T : Fin N, LaysBaseOn D₀ (m : ℝ) (k : ℝ) (D₀.target.pts (τ 2)) (D₀.target.pts (τ 0)) i₀ Ty.C1 0 →
      ¬ MirrorBeside D₀ (m : ℝ) (k : ℝ) (D₀.target.pts (τ 2)) i₀ T) :
    ∃ (c : ℕ) (X : ℕ → ℝ) (tile : ℕ → Fin N) (ty : ℕ → Ty),
      SideTiling D₀ (m : ℝ) (k : ℝ) (D₀.target.pts (τ 2)) (D₀.target.pts (τ 0)) c X tile ty ∧
      (edgeCounts c ty).1 = 0 ∧ k ≤ (edgeCounts c ty).2.2 := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hmkR : (m : ℝ) < k := by exact_mod_cast hmk
  obtain ⟨cA, cB, cC⟩ := Erdos634.BeesonRosu37c1.corners_of_dists D₀.target hmR hmkR τ h1 h2 h3
  have e2 : (finRotate 3).symm.trans τ 2 = τ 1 := rfl
  have e0 : (finRotate 3).symm.trans τ 0 = τ 2 := rfl
  have e1 : (finRotate 3).symm.trans τ 1 = τ 0 := rfl
  have hApex : cornerAngle (D₀.target.pts (τ 1)) (D₀.target.pts (τ 2)) (D₀.target.pts (τ 0)) = 3 * modelAlpha (m : ℝ) (k : ℝ) := by
    rw [Erdos634.Geometry.cornerAngle, EuclideanGeometry.angle_comm]; exact cC
  have hBeta : cornerAngle (D₀.target.pts (τ 2)) (D₀.target.pts (τ 0)) (D₀.target.pts (τ 1)) = modelBeta (m : ℝ) (k : ℝ) := by
    rw [Erdos634.Geometry.cornerAngle, EuclideanGeometry.angle_comm]; exact cA
  obtain ⟨D, g, L, ax, ay, hL, hdist, hD, hP, hB, S, Co, -⟩ :=
    setup_of_corners m k hm hmk hco D₀ hMod ((finRotate 3).symm.trans τ)
      (Or.inr (by rw [e2, e0, e1]; exact hApex)) (Or.inl (by rw [e2, e0, e1]; exact hBeta))
  replace hdist : dist (D₀.target.pts (τ 2)) (D₀.target.pts (τ 0)) = L := hdist
  replace hP : g (D₀.target.pts (τ 2)) = CertCoord.mkPt 0 0 := hP
  replace hB : g (D₀.target.pts (τ 0)) = CertCoord.mkPt L 0 := hB
  obtain ⟨c, X, tile, ty, Ch⟩ := S.exists_chainG
  obtain ⟨hsum, hrunz⟩ := Erdos634.BeesonRosu37c4a.counts_sums S Ch
  have hlen : L = (k : ℝ) ^ 3 := by rw [← hdist, h2]
  -- k <= sum cC (Lemma 34 on the leg, from hNoM)
  have hkz : k ≤ ∑ j ∈ Finset.range c, (ty j).cC := by
    rcases corner_side_theorem S Co Ch with h | ⟨k', hk1, hkf, hkm, hrun, hsucc⟩
    · exact hrunz h
    · exfalso
      have hsucc' : k' = c ∨ (k' < c ∧ ty k' ≠ Ty.B1 ∧ ty k' ≠ Ty.C1) := by
        rcases hsucc with h | ⟨h, h'⟩
        · exact Or.inl h
        · refine Or.inr ⟨h, ?_, ?_⟩ <;> rcases h' with h' | h' | h' <;> rw [h'] <;> decide
      have hM := corner_run_mirror S Co Ch hk1 hkf hrun hsucc'
      have hU := Ch.htile 0 (by omega)
      rw [hrun 0 (by omega), Ch.hX0] at hU
      obtain ⟨T, hT⟩ := mirrorBeside_of_mirrorAt hD hP S hU hM
      exact hNoM (tile 0) T (laysOn_of_baseTile hL hD hP hB hU) hT
  have hsumZ : (((∑ j ∈ Finset.range c, (ty j).cA : ℕ) : ℤ) * ((k : ℤ) * m) + ((∑ j ∈ Finset.range c, (ty j).cB : ℕ) : ℤ) * ((k : ℤ) ^ 2 - (m : ℤ) ^ 2)
      + ((∑ j ∈ Finset.range c, (ty j).cC : ℕ) : ℤ) * (k : ℤ) ^ 2) = (k : ℤ) * (k : ℤ) ^ 2 := by
    have : ((((∑ j ∈ Finset.range c, (ty j).cA : ℕ) : ℤ) * ((k : ℤ) * m) + ((∑ j ∈ Finset.range c, (ty j).cB : ℕ) : ℤ) * ((k : ℤ) ^ 2 - (m : ℤ) ^ 2)
      + ((∑ j ∈ Finset.range c, (ty j).cC : ℕ) : ℤ) * (k : ℤ) ^ 2 : ℤ) : ℝ) = (((k : ℤ) * (k : ℤ) ^ 2 : ℤ) : ℝ) := by
      push_cast at hsum ⊢
      rw [hlen] at hsum
      linarith [hsum]
    exact_mod_cast this
  have hp0 := leg_p1_zero (k := (k : ℤ)) (m := (m : ℤ)) (by exact_mod_cast hm) (by exact_mod_cast hmk)
    (Int.natCast_nonneg _) (Int.natCast_nonneg _) hsumZ (by exact_mod_cast hkz)
  refine ⟨c, X, tile, ty, ⟨Ch.hm0, Ch.hX0, ?_, Ch.hstep, fun j hj => ?_⟩, ?_, hkz⟩
  · rw [Ch.hXm, hdist]
  · exact laysOn_of_baseTile hL hD hP hB (Ch.htile j hj)
  · unfold edgeCounts; exact_mod_cast hp0

end Erdos634.BeesonRosu37d1

#print axioms Erdos634.BeesonRosu37d1.base_tiling
#print axioms Erdos634.BeesonRosu37d1.leg_tiling
