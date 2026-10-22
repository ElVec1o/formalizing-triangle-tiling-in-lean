-- Draft/LaczFormalIIcWN67.lean -- Laczkovich (DCG 48 (2012), Sect. 6.3), Lemma 6.2 (`IIcNoKites`): ASSEMBLY of the pure-geometry pieces.
-- `KiteLayer M` collects EXACTLY the tile-level claims that are NOT proved (named fields); `kiteLayer_false : KiteLayer M -> False` derives the contradiction of the
-- printed proof from them using: (h) `no_concave`, the angle sum `OrientOK` (so C1 has M vertices), (i) `RingSetup.ring_order`, and the metric step `ring_monotone`.
-- Remaining named inputs (all tile-level): turn (each vertex of the innermost Gamma_kite cycle turns by gamma, 0 or -gamma: WN28/29 `gkite_turn`, not yet exported for this C);
-- fam (the Gamma_except edges of the concave vertices form a ChordFam: direction into the exterior sector Fig. 5(B), no crossing of Gamma_kite edges, disjointness);
-- nostraight (no straight Fig. 5(A) vertex on C1: a gap of the printed proof); ring (A and C1 are strictly convex, C1 inside A, the Gamma_except edges of the vertices of A are
-- exterior chords, pairwise disjoint); fig8 (the quadrilaterals V_{i-1} V_i W_i W_{i-1} are those of Fig. 8, in the form `RingQuadA/B`).
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.3, proof of Lemma 6.2), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcWN66
import Erdos634.Draft.LaczFormalRG12Ring

open scoped Classical Fin.NatCast
open Complex

namespace Erdos634.Draft.LaczFormal.WN

/-- The unproved tile-level input of the proof of Lemma 6.2 (generic angles), for a polygon A with `M` vertices (the paper's `N`, `gamma = 2 pi / M`). -/
structure KiteLayer (M : ℕ) [NeZero M] where
  α : ℝ
  β : ℝ
  γ : ℝ
  hsum : α + β + γ = Real.pi
  hα : 0 < α
  hβ : 0 < β
  hγ : 0 < γ
  hγM : γ = 2 * Real.pi / M
  hne : α ≠ β
  hM : 3 ≤ M
  /-- the innermost cycle of Gamma_kite, as a polygon -/
  m : ℕ
  [hmne : NeZero m]
  C : Fin m → ℂ
  hm : 3 ≤ m
  hCs : SimplePoly C
  hCi : Function.Injective C
  σ : ℝ
  hO : OrientOK C σ
  /-- every vertex of the cycle turns by `gamma`, `-gamma` or `0` (in the direction of the interior) -/
  turn : ∀ k : Fin m, σ * extAng C k = γ ∨ σ * extAng C k = -γ ∨ σ * extAng C k = 0
  J : Fin m → Fin m
  /-- the Gamma_except edges of the concave vertices -/
  fam : ChordFam C σ J
  /-- no straight (Fig. 5 (A)) vertex on the innermost cycle -/
  nostraight : ∀ k : Fin m, σ * extAng C k ≠ 0
  /-- the outer polygon A and the exterior chords from its vertices to the cycle -/
  A : Fin M → ℂ
  w : Fin M → Fin M
  τA : ℝ
  τC : ℝ
  ring : ∀ h : m = M, RingSetup A (fun j : Fin M => C (Fin.cast h.symm j)) w τA τC
  /-- Fig. 8: if the W_i follow the cyclic order of the V_i, the ring quadrilaterals have the shapes (A) or (B) -/
  fig8 : ((∀ i, w (i + 1) = w i + 1) ∨ (∀ i, w (i + 1) = w i - 1)) →
    ∃ d L mm : ZMod M → ℝ, ∀ i, RG.RingQuadA α β γ (L i) (d i) (mm i) (d (i - 1)) ∨ RG.RingQuadB α β γ (L i) (d i) (mm i) (d (i - 1))

theorem kiteLayer_false {M : ℕ} [NeZero M] (K : KiteLayer M) : False := by
  haveI := K.hmne
  -- (h): no concave vertex
  have hnc := no_concave K.hCs K.hCi K.hm K.hO K.fam
  have hγ := K.hγ
  have hturn : ∀ k : Fin K.m, K.σ * extAng K.C k = K.γ := by
    intro k
    rcases K.turn k with h | h | h
    · exact h
    · exfalso; apply hnc k; rw [h]; linarith
    · exact absurd h (K.nostraight k)
  -- angle sum: m * gamma = 2 pi, so m = M
  have hsum : ∑ k : Fin K.m, (Real.pi - K.σ * extAng K.C k) = ((K.m : ℝ) - 2) * Real.pi := K.hO.2.2.1
  have hmM : K.m = M := by
    have h1 : ∑ k : Fin K.m, (Real.pi - K.σ * extAng K.C k) = K.m * (Real.pi - K.γ) := by
      rw [Finset.sum_congr rfl (fun k _ => by rw [hturn k])]
      simp
      ring
    rw [h1] at hsum
    have h2 : (K.m : ℝ) * K.γ = 2 * Real.pi := by linarith
    have hMpos : (0 : ℝ) < M := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne M)
    have h3 : (K.m : ℝ) * (2 * Real.pi / M) = 2 * Real.pi := by rw [← K.hγM]; exact h2
    have h4 : (K.m : ℝ) = M := by
      field_simp at h3
      have hpi := Real.pi_pos
      nlinarith
    exact_mod_cast h4
  have R := K.ring hmM
  have hord := R.ring_order
  obtain ⟨d, L, mm, hR⟩ := K.fig8 hord
  exact RG.ring_monotone K.hsum K.hα K.hβ K.hγ K.hne d L mm hR

#print axioms kiteLayer_false

end Erdos634.Draft.LaczFormal.WN
