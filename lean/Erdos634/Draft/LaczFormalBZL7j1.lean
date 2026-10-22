import Erdos634.Draft.LaczFormalBZL7d6
import Erdos634.Draft.LaczFormalBZL7a
import Erdos634.Draft.LaczFormalRG9Geo

-- Draft/LaczFormalBZL7j1.lean -- POLYGON TARGETS (convex M-gon, not only triangles) for the Beeson-Zhang gamma = 2pi/3 analysis.
-- Hypothesis `NoGammaCorner C P`: no tile has its 2pi/3 angle at a vertex of the polygon (for a triangle not similar to the tile this is a THEOREM, `corner_gamma_zero`; for M >= 4 it is a genuine
-- hypothesis, the parallelogram of two tiles glued along c has gamma corners and need not be rational).
--   `bz_poly_ab_comm`        : PolyTiling T of an M-gon by the tile (alpha, pi/3 - alpha, 2pi/3), alpha not in Q pi, NoGammaCorner  ==>  Comm a b           (BZ Lemmas 3.5, 3.6, any M).
--   `bz_poly_sides_all_c`    : same, and c not commensurable with a  ==>  every side of the polygon is a positive integer multiple of c            (BZ Lemma 3.4, any M).
--   `poly_regular_of_balanced`, `bz_poly_balanced` : if moreover #alpha = #beta at every polygon corner then T is REGULAR and Laczkovich Thm 2.1 (via `thm21_partial4`, `bz_L7_polygon`) gives
--                              Concl1 (M = 4) or Comm a b /\ Comm a c or Concl6 (M = 6); hence Comm a b /\ Comm a c for M not in {4, 6}.
-- NOT proved (gap, quoted in (private working notes, not included)): for M >= 4 with ALL sides multiples of c and unbalanced corners the flux contradiction of `bz_allc_false` (triangle inequality + sign product) does not extend:
--   a rhombus pattern n = (1,1,1,1), signs (+,+,-,-) satisfies  sum eps_i n_i = 0,  prod eps_i = 1  and the polygon inequality.  NOTE, UNAUDITED.
-- Credit: Beeson-Zhang (arXiv 2604.01314v1, Lemmas 3.4-3.6), Laczkovich (DCG 48 (2012), Thm 2.1, Sect. 4, 7), Beeson.

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ} [NeZero M]

/-- No tile has an angle `2 pi/3` at a vertex of the polygon. -/
def NoGammaCorner (C : CongruentRegionDissection N) (P : ConvPoly M) : Prop :=
  ∀ (k : Fin M) (i : Fin N) (v : Fin 3), (C.tile i).pts v = P.v k → (C.tile i).angleAt v ≠ 2 * Real.pi / 3

theorem hcorn_of_noGamma (Dr : CongruentRegionDissection N) (P : ConvPoly M) (idx : Fin N → Equiv.Perm (Fin 3))
    (hidxA : ∀ i v, Dr.model.angleAt (idx i v) = (Dr.tile i).angleAt v) (hγ : Dr.model.angleAt 2 = 2 * Real.pi / 3)
    (hn : NoGammaCorner Dr P) : ∀ k : Fin M, cnt Dr idx (P.v (k + 1)) 2 = 0 := by
  intro k
  unfold cnt
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro ⟨i, v⟩ _ ⟨h1, h2⟩
  apply hn (k + 1) i v h1
  rw [← hidxA i v]
  show Dr.model.angleAt (idx i v) = _
  rw [h2, hγ]

theorem poly_setup (T : PolyTiling N M) {α a b c : ℝ} (h : T.C.model.TwoPiThreeData α a b c) {R : Prop}
    (k : ∀ (Dr : CongruentRegionDissection N) [HasFansC Dr.toRegionDissection] (hreg : Dr.region = T.P.carrier)
      (idx : Fin N → Equiv.Perm (Fin 3))
      (hidx : ∀ i k k', dist ((Dr.tile i).pts k) ((Dr.tile i).pts k') = dist (Dr.model.pts (idx i k)) (Dr.model.pts (idx i k')))
      (hidxA : ∀ i v, Dr.model.angleAt (idx i v) = (Dr.tile i).angleAt v),
      slen Dr 0 = a → slen Dr 1 = b → slen Dr 2 = c →
      Dr.model.angleAt 0 = α → Dr.model.angleAt 1 = Real.pi / 3 - α → Dr.model.angleAt 2 = 2 * Real.pi / 3 →
      (∀ i, Dr.tile i = T.C.tile i) → R) : R := by
  obtain ⟨σ, h0, o0, h1, o1, h2, o2⟩ := h
  set Dr := relabel T.C σ with hDr
  have hreg : Dr.region = T.P.carrier := T.region_eq
  haveI : HasFansC Dr.toRegionDissection := hasFansC_poly _ T.P hreg
  obtain ⟨idx, hidx, hidxA⟩ := exists_idx_both Dr
  have hang : ∀ j, Dr.model.angleAt j = T.C.model.angleAt (σ j) := fun j => relabel_angleAt T.C σ j
  have hsl : ∀ t, slen Dr t = T.C.model.oppLen (σ t) := fun t => relabel_slen T.C σ t
  exact k Dr hreg idx hidx hidxA (by rw [hsl]; exact o0) (by rw [hsl]; exact o1) (by rw [hsl]; exact o2)
    (by rw [hang]; exact h0) (by rw [hang]; exact h1) (by rw [hang]; exact h2) (fun i => rfl)

theorem poly_lemma35 (T : PolyTiling N M) {α a b c : ℝ} (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (h : T.C.model.TwoPiThreeData α a b c) (hn : NoGammaCorner T.C T.P) : ¬ NotComb a b c := by
  intro hnc
  refine poly_setup T h ?_
  intro Dr _ hreg idx hidx hidxA e0 e1 e2 hA0 hA1 hA2 htile
  refine bz_lemma35_gen2 Dr T.P hreg idx hidx hidxA ?_ hA2 (by rw [hA0, hA1]; ring) (by rw [hA0]; exact hα)
    (fun i => (polyAngle_bounds T.P i).2)
    (hcorn_of_noGamma Dr T.P idx hidxA hA2 (fun k i v hv => by rw [htile i] at hv ⊢; exact hn k i v hv))
  rw [e0, e1, e2]; exact hnc

/-- **Beeson-Zhang Lemmas 3.5, 3.6 for a convex polygon target** with no `γ` corner at a polygon vertex: `a` and `b` are commensurable. -/
theorem bz_poly_ab_comm (T : PolyTiling N M) {α a b c : ℝ} (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (h : T.C.model.TwoPiThreeData α a b c) (hn : NoGammaCorner T.C T.P) : Comm a b := by
  have h1 := poly_lemma35 T hα h hn
  have hα' : ¬ ∃ r : ℚ, Real.pi / 3 - α = (r : ℝ) * Real.pi := by
    rintro ⟨r, hr⟩
    apply hα
    refine ⟨1 / 3 - r, ?_⟩
    push_cast
    linarith
  have h2 := poly_lemma35 T hα' (tpt_swap h) hn
  unfold NotComb at h1 h2
  push Not at h1 h2
  obtain ⟨r, p, q, hr, e1⟩ := h1
  obtain ⟨r', p', q', hr', e2⟩ := h2
  have ha : 0 < a := by
    obtain ⟨σ, -, o0, -⟩ := h
    rw [← o0]; exact T.C.model.oppLen_pos' _
  have hb : 0 < b := by
    obtain ⟨σ, -, -, -, o1, -⟩ := h
    rw [← o1]; exact T.C.model.oppLen_pos' _
  exact comm_of_two_combs ha hb hr e1 hr' e2

/-- **Beeson-Zhang Lemma 3.4 for a convex polygon target**: with `Comm a b`, `c` not commensurable with `a`, and no `γ` corner at a vertex, every side of the polygon is a positive multiple of `c`. -/
theorem bz_poly_sides_all_c (T : PolyTiling N M) {α a b c : ℝ} (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (h : T.C.model.TwoPiThreeData α a b c) (hn : NoGammaCorner T.C T.P) (hac : ¬ Comm a c) :
    ∀ i : Fin M, ∃ m : ℕ, 0 < m ∧ T.P.side i = m * c := by
  have hab := bz_poly_ab_comm T hα h hn
  have hc : 0 < c := by
    obtain ⟨σ, -, -, -, -, -, o2⟩ := h
    rw [← o2]; exact T.C.model.oppLen_pos' _
  refine poly_setup T h ?_
  intro Dr _ hreg idx hidx hidxA e0 e1 e2 hA0 hA1 hA2 htile
  have hnc : NotComb (slen Dr 2) (slen Dr 1) (slen Dr 0) := by
    rw [e0, e1, e2]; exact notComb_c_of_comm hc hab hac
  have hall := sides_all_c Dr T.P hreg idx hidx hidxA hnc hA2 (by rw [hA0, hA1]; ring) (by rw [hA0]; exact hα)
    (hcorn_of_noGamma Dr T.P idx hidxA hA2 (fun k i v hv => by rw [htile i] at hv ⊢; exact hn k i v hv))
  intro i
  obtain ⟨m, hm, hmi⟩ := hall i
  exact ⟨m, hm, by rw [hmi, e2]⟩

/-- Balanced polygon corners + no `γ` corner (in the normalised labelling `α, β, γ = vertices 0, 1, 2`): the tiling is REGULAR in Laczkovich's sense. -/
theorem poly_regular_of_balanced (T : PolyTiling N M) (hγ : T.C.model.angleAt 2 = 2 * Real.pi / 3)
    (hαβ : T.C.model.angleAt 0 + T.C.model.angleAt 1 = Real.pi / 3) (hα : ¬ ∃ r : ℚ, T.C.model.angleAt 0 = (r : ℝ) * Real.pi)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hidxA : ∀ i v, T.C.model.angleAt (idx i v) = (T.C.tile i).angleAt v)
    (hn : NoGammaCorner T.C T.P) (hbal : ∀ k : Fin M, cnt T.C idx (T.P.v k) 0 = cnt T.C idx (T.P.v k) 1) : RegularPQ T.C := by
  haveI : HasFansC T.C.toRegionDissection := hasFansC_poly _ T.P T.region_eq
  have hcorn := hcorn_of_noGamma T.C T.P idx hidxA hγ hn
  refine ⟨idx, fun i v => hidxA i v, fun X => ?_⟩
  by_cases hv : ∃ j k, (T.C.tile j).pts k = X
  · rcases vertex_type_gen2 T.C T.P T.region_eq idx hidxA hγ hαβ hα hcorn hv with ⟨h01, -⟩ | ⟨-, k, hk⟩
    · exact h01
    · have := hbal (k + 1)
      rw [hk]; exact this
  · have e : ∀ l : Fin 3, cntR T.C idx X l = 0 := by
      intro l
      unfold cntR
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      rintro ⟨i, v⟩ _ ⟨h1, -⟩
      exact hv ⟨i, v, h1⟩
    rw [e 0, e 1]

/-- **Polygon targets with balanced corners** (Laczkovich Theorem 2.1 via the regular case): for `M` not in `{4, 6}` the sides of the tile are pairwise commensurable. -/
theorem bz_poly_balanced (T : PolyTiling N M) (hγ : T.C.model.angleAt 2 = 2 * Real.pi / 3)
    (hαβ : T.C.model.angleAt 0 + T.C.model.angleAt 1 = Real.pi / 3) (hα : ¬ ∃ r : ℚ, T.C.model.angleAt 0 = (r : ℝ) * Real.pi)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hidxA : ∀ i v, T.C.model.angleAt (idx i v) = (T.C.tile i).angleAt v)
    (hn : NoGammaCorner T.C T.P) (hbal : ∀ k : Fin M, cnt T.C idx (T.P.v k) 0 = cnt T.C idx (T.P.v k) 1)
    (h4 : M ≠ 4) (h6 : M ≠ 6) : Comm (slen T.C 0) (slen T.C 1) ∧ Comm (slen T.C 0) (slen T.C 2) := by
  have hreg := poly_regular_of_balanced T hγ hαβ hα idx hidxA hn hbal
  rcases bz_L7_polygon_sides T hreg hγ hα with h | h | h
  · exact absurd h.1.1 h4
  · exact h
  · exact absurd h.1 h6

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.hcorn_of_noGamma
#print axioms Erdos634.Draft.LaczFormal.RG.poly_lemma35
#print axioms Erdos634.Draft.LaczFormal.RG.bz_poly_ab_comm
#print axioms Erdos634.Draft.LaczFormal.RG.bz_poly_sides_all_c
#print axioms Erdos634.Draft.LaczFormal.RG.poly_regular_of_balanced
#print axioms Erdos634.Draft.LaczFormal.RG.bz_poly_balanced
