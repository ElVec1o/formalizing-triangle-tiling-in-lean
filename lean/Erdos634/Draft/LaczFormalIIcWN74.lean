-- Draft/LaczFormalIIcWN74.lean -- Laczkovich (DCG 48 (2012), Sect. 6.3), Lemma 6.2: `KiteLayer2`, the supply WITHOUT the unproved field `nostraight`.
-- The printed proof assumes that every vertex of the outermost (C1 of the printed nesting C_{i+1} in C_i-interior) Gamma_kite cycle has angle alpha+beta or alpha+beta+2 gamma; Fig. 5(A) vertices (straight, angle pi) are not excluded by the printed text.
-- REPAIR (proved, WN71-WN73 `exists_corner`): replace the cycle `C` by a corner polygon `q` (straight vertices merged into the sides).  `KiteLayer2` keeps the turn of the full cycle in {gamma, 0, -gamma}
-- (this is now PROVED at tile level: WN70 `gkite_cycle_turn`) and states the chord family, the ring and Fig. 8 for EVERY corner polygon `q` of `C`; `kiteLayer2_false` derives the contradiction.
-- What remains tile-level (named fields): `turn` (proved by WN70 for closed injective chains, not yet plugged), `corner` (chord family: chord ends are never straight vertices because `gexc_not_arrive_of_straight`; direction/non-crossing; ring; Fig. 8).
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.3, proof of Lemma 6.2), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcWN73
import Erdos634.Draft.LaczFormalIIcWN68

open scoped Classical Fin.NatCast
open Complex

namespace Erdos634.Draft.LaczFormal.WN

/-- Tile-level data of the ring step for a corner polygon `q` with orientation sign `sigma`. -/
structure CornerRing (M : ℕ) [NeZero M] (α β γ : ℝ) {m : ℕ} [NeZero m] (q : Fin m → ℂ) (σ : ℝ) : Prop where
  fam : ∃ J : Fin m → Fin m, ChordFam q σ J
  ring : ∃ (A : Fin M → ℂ) (w : Fin M → Fin M) (τA τC : ℝ),
    (∀ h : m = M, RingSetup A (fun j : Fin M => q (Fin.cast h.symm j)) w τA τC) ∧
    (((∀ i, w (i + 1) = w i + 1) ∨ (∀ i, w (i + 1) = w i - 1)) →
      ∃ d L mm : ZMod M → ℝ, ∀ i, RG.RingQuadA α β γ (L i) (d i) (mm i) (d (i - 1)) ∨ RG.RingQuadB α β γ (L i) (d i) (mm i) (d (i - 1)))

/-- The unproved tile-level input, version 2 (no `nostraight`). -/
structure KiteLayer2 (M : ℕ) [NeZero M] where
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
  m : ℕ
  [hmne : NeZero m]
  C : Fin m → ℂ
  hm : 3 ≤ m
  hCs : SimplePoly C
  hCi : Function.Injective C
  /-- every vertex of the full cycle turns by `gamma`, `0` or `-gamma` (PROVED for closed injective Gamma_kite chains by WN70) -/
  turn : ∀ k : Fin m, extAng C k = γ ∨ extAng C k = 0 ∨ extAng C k = -γ
  /-- the chord family, the ring and Fig. 8 for every corner polygon of the cycle -/
  corner : ∀ (m' : ℕ) [NeZero m'] (q : Fin m' → ℂ), IsCornerOf C q → ∀ σ, OrientOK q σ → CornerRing M α β γ q σ

theorem kiteLayer2_false {M : ℕ} [NeZero M] (K : KiteLayer2 M) : False := by
  haveI := K.hmne
  obtain ⟨m', hm', q, hq⟩ := exists_corner K.C K.hCs K.hCi K.hm
  obtain ⟨h3, hqs, hqi, hqne, hqe, hqv⟩ := hq
  obtain ⟨σ, hO⟩ := orient_exists hqs hqi h3
  have hCR := K.corner m' q ⟨h3, hqs, hqi, hqne, hqe, hqv⟩ σ hO
  obtain ⟨J, hJ⟩ := hCR.fam
  have hnc := no_concave hqs hqi h3 hO hJ
  have hγ := K.hγ
  have hσ := hO.1.1
  have hturn : ∀ k : Fin m', σ * extAng q k = K.γ := by
    intro k
    obtain ⟨k', -, hk'⟩ := hqv k
    have hne := hqne k
    have hnck := hnc k
    rcases K.turn k' with h | h | h
    · rcases hσ with rfl | rfl
      · rw [hk', h]; ring
      · exfalso; apply hnck; rw [hk', h]; linarith
    · exact absurd (hk'.trans h) hne
    · rcases hσ with rfl | rfl
      · exfalso; apply hnck; rw [hk', h]; linarith
      · rw [hk', h]; ring
  have hsum : ∑ k : Fin m', (Real.pi - σ * extAng q k) = ((m' : ℝ) - 2) * Real.pi := hO.2.2.1
  have hmM : m' = M := by
    have h1 : ∑ k : Fin m', (Real.pi - σ * extAng q k) = m' * (Real.pi - K.γ) := by
      rw [Finset.sum_congr rfl (fun k _ => by rw [hturn k])]
      simp
      ring
    rw [h1] at hsum
    have h2 : (m' : ℝ) * K.γ = 2 * Real.pi := by linarith
    have hMpos : (0 : ℝ) < M := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne M)
    have h3' : (m' : ℝ) * (2 * Real.pi / M) = 2 * Real.pi := by rw [← K.hγM]; exact h2
    have h4 : (m' : ℝ) = M := by
      field_simp at h3'
      have hpi := Real.pi_pos
      nlinarith
    exact_mod_cast h4
  obtain ⟨A, w, τA, τC, hR, hf⟩ := hCR.ring
  have R := hR hmM
  have hord := R.ring_order
  obtain ⟨d, L, mm, hRq⟩ := hf hord
  exact RG.ring_monotone K.hsum K.hα K.hβ K.hγ K.hne d L mm hRq

#print axioms kiteLayer2_false

end Erdos634.Draft.LaczFormal.WN

namespace Erdos634.Draft.LaczFormal.RG

open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

/-- The tile-level supply, version 2: a `KiteLayer2` for every tiling violating `IIcNoKites`. -/
def IIcKiteLayerSupply2 : Prop :=
  ∀ (N M : ℕ) [NeZero M] (T : PolyTiling N M) (idx : Fin N → Equiv.Perm (Fin 3)), CaseC T.C idx →
    angleAt T.C.model 2 < Real.pi / 2 → angleAt T.C.model 2 ≠ Real.pi / 3 → Comm (slen T.C 0) (slen T.C 1) → ¬ Comm (slen T.C 0) (slen T.C 2) →
    AngGen (fun l => T.C.model.angleAt l) →
    (∀ j : Fin M, cnt T.C idx (T.P.v j) 0 = 1 ∧ cnt T.C idx (T.P.v j) 1 = 1 ∧ cnt T.C idx (T.P.v j) 2 = 0) →
    kiteB T.C idx ≠ ∅ → Nonempty (Erdos634.Draft.LaczFormal.WN.KiteLayer2 M)

theorem iicNoKites_of_supply2 (H : IIcKiteLayerSupply2) : IIcNoKites := by
  intro N M _ T idx hC h1 h3 hab hac hAng hcor
  by_contra hne
  obtain ⟨K⟩ := H N M T idx hC h1 h3 hab hac hAng hcor hne
  exact Erdos634.Draft.LaczFormal.WN.kiteLayer2_false K

#print axioms iicNoKites_of_supply2

end Erdos634.Draft.LaczFormal.RG
