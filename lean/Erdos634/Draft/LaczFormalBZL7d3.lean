-- Draft/LaczFormalBZL7d3.lean -- Beeson-Zhang (arXiv 2604.01314v1) Lemmas 3.5 and 3.6 for EVERY triangle target not similar to the tile (CongruentDissection language):
--   `tri_setup`            : continuation-passing packaging of the standard set-up (relabelled model with angles (alpha, pi/3 - alpha, 2 pi/3), the convex 3-gon of the target, idx, fans) used by all later modules;
--   `bz_lemma35_notsim`    : `NotComb a b c` is impossible;
--   `bz_ab_comm_notsim`    : `a`, `b` are commensurable   (Thm 3.7's first half; Lemmas 3.5, 3.6).
-- Hypotheses: `CongruentDissection N` of a triangle (any N, reflections, not edge-to-edge), `TwoPiThreeData alpha a b c`, alpha not in Q pi, `NotSim D` (target angles not a permutation of the tile angles).
-- Non-vacuity: the 1215-tiling (equilateral target) and the 143-tiling (target (2 alpha, pi/3, 2 beta)) satisfy `NotSim`; see LaczFormalBZL7d8.  NOTE, UNAUDITED.
-- Credit: Beeson-Zhang (arXiv 2604.01314v1, Lemmas 3.5, 3.6, Thm 3.7), Laczkovich (DCG 48 (2012), Sect. 4, 7), Beeson.
import Erdos634.Draft.LaczFormalBZL7d2

open scoped Classical
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N : ℕ}

/-- Standard set-up for a triangle target (continuation form). -/
theorem tri_setup (D : CongruentDissection N) {α a b c : ℝ} (h : D.model.TwoPiThreeData α a b c) {R : Prop}
    (k : ∀ (Dr : CongruentRegionDissection N) [HasFansC Dr.toRegionDissection] (P : ConvPoly 3) (hreg : Dr.region = P.carrier)
      (idx : Fin N → Equiv.Perm (Fin 3))
      (hidx : ∀ i k k', dist ((Dr.tile i).pts k) ((Dr.tile i).pts k') = dist (Dr.model.pts (idx i k)) (Dr.model.pts (idx i k')))
      (hidxA : ∀ i v, Dr.model.angleAt (idx i v) = (Dr.tile i).angleAt v),
      slen Dr 0 = a → slen Dr 1 = b → slen Dr 2 = c →
      Dr.model.angleAt 0 = α → Dr.model.angleAt 1 = Real.pi / 3 - α → Dr.model.angleAt 2 = 2 * Real.pi / 3 →
      P.angle 0 + P.angle 1 + P.angle 2 = Real.pi → (∀ i, 0 < P.angle i) → (∀ i, P.angle i < Real.pi) →
      (NotSim D → ¬ ∃ ρ : Equiv.Perm (Fin 3), ∀ k : Fin 3, P.angle (k + 1) = Dr.model.angleAt (ρ k)) → R) : R := by
  obtain ⟨P, hPc, τ, hτ⟩ := exists_convpoly_of_tri D.target
  obtain ⟨σ, h0, o0, h1, o1, h2, o2⟩ := h
  set Dr := relabel D.toRegion σ with hDr
  have hreg : Dr.region = P.carrier := by rw [hPc]; rfl
  haveI : HasFansC Dr.toRegionDissection := hasFansC_poly _ P hreg
  obtain ⟨idx, hidx, hidxA⟩ := exists_idx_both Dr
  have hang : ∀ j, Dr.model.angleAt j = D.model.angleAt (σ j) := fun j => relabel_angleAt D.toRegion σ j
  have hsl : ∀ t, slen Dr t = D.model.oppLen (σ t) := fun t => relabel_slen D.toRegion σ t
  have hs : D.target.angleAt 0 + D.target.angleAt 1 + D.target.angleAt 2 = Real.pi := angleAt_sum D.target
  have hp : ∀ j, 0 < D.target.angleAt j := fun j => D.target.angleAt_pos'' j
  have hPsum : P.angle 0 + P.angle 1 + P.angle 2 = Real.pi := by
    simp only [hτ]
    have : ∑ i : Fin 3, D.target.angleAt (τ i) = ∑ i : Fin 3, D.target.angleAt i := Equiv.sum_comp τ (fun i => D.target.angleAt i)
    simp only [Fin.sum_univ_three] at this
    linarith
  refine k Dr P hreg idx hidx hidxA (by rw [hsl]; exact o0) (by rw [hsl]; exact o1) (by rw [hsl]; exact o2)
    (by rw [hang]; exact h0) (by rw [hang]; exact h1) (by rw [hang]; exact h2) hPsum (fun i => by rw [hτ]; exact hp _) (fun i => ?_) ?_
  · rw [hτ]
    have := hp (τ i)
    have e : ∀ j : Fin 3, D.target.angleAt j < Real.pi := by
      intro j
      have fin3 : ∀ k : Fin 3, k = 0 ∨ k = 1 ∨ k = 2 := by decide
      rcases fin3 j with rfl | rfl | rfl <;> linarith [hp 0, hp 1, hp 2]
    exact e _
  · intro hNS ⟨ρ, hρ⟩
    apply hNS
    refine ⟨τ.symm.trans ((Equiv.addRight (-1 : Fin 3)).trans (ρ.trans σ)), fun j => ?_⟩
    obtain ⟨m, rfl⟩ := τ.surjective j
    have := hρ (m - 1)
    rw [hτ, hang] at this
    simp only [Equiv.trans_apply, Equiv.symm_apply_apply, Equiv.coe_addRight]
    have e : m - 1 + 1 = m := by simp
    rw [e] at this
    rw [show m + -1 = m - 1 from by simp [sub_eq_add_neg]]
    exact this

/-- **Beeson-Zhang Lemma 3.5** for a triangle ABC not similar to the tile: `NotComb a b c` is impossible. -/
theorem bz_lemma35_notsim (D : CongruentDissection N) {α a b c : ℝ} (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (h : D.model.TwoPiThreeData α a b c) (hNS : NotSim D) : ¬ NotComb a b c := by
  intro hnc
  refine tri_setup D h ?_
  intro Dr _ P hreg idx hidx hidxA e0 e1 e2 hA0 hA1 hA2 hsum hpos hlt hns
  refine bz_lemma35_gen2 Dr P hreg idx hidx hidxA ?_ hA2 (by rw [hA0, hA1]; ring) (by rw [hA0]; exact hα) hlt
    (corner_gamma_zero Dr P hreg idx hidxA hα hA0 hA1 hA2 hsum hpos (hns hNS))
  rw [e0, e1, e2]; exact hnc

/-- **Beeson-Zhang Lemmas 3.5, 3.6 for a triangle ABC not similar to the tile**: `a` and `b` are commensurable. -/
theorem bz_ab_comm_notsim (D : CongruentDissection N) {α a b c : ℝ} (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (h : D.model.TwoPiThreeData α a b c) (hNS : NotSim D) : Comm a b := by
  have h1 := bz_lemma35_notsim D hα h hNS
  have hα' : ¬ ∃ r : ℚ, Real.pi / 3 - α = (r : ℝ) * Real.pi := by
    rintro ⟨r, hr⟩
    apply hα
    refine ⟨1 / 3 - r, ?_⟩
    push_cast
    linarith
  have h2 := bz_lemma35_notsim D hα' (tpt_swap h) hNS
  unfold NotComb at h1 h2
  push Not at h1 h2
  obtain ⟨r, p, q, hr, e1⟩ := h1
  obtain ⟨r', p', q', hr', e2⟩ := h2
  have ha : 0 < a := by
    obtain ⟨σ, -, o0, -⟩ := h
    rw [← o0]; exact D.model.oppLen_pos' _
  have hb : 0 < b := by
    obtain ⟨σ, -, -, -, o1, -⟩ := h
    rw [← o1]; exact D.model.oppLen_pos' _
  exact comm_of_two_combs ha hb hr e1 hr' e2

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.tri_setup
#print axioms Erdos634.Draft.LaczFormal.RG.bz_lemma35_notsim
