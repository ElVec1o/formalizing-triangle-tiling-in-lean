-- Draft/LaczFormalBZL7h2.lean -- Beeson (arXiv 1206.1974v7) Lemmas 10.4 / 10.6, the link graphs, via LACZKOVICH's `GaEdge` (relabelled), with a WEIGHTED counting step.
--   * `ga_head_data`  : the head `H` of a `GaEdge` (tile side `a` = `slen D (sigma 0)`, `NotComb`) has corner sum `pi`, is interior, and starts an edge as soon as the parity
--                       `(cnt (sigma 1) + cnt (sigma 2))` is even (Laczkovich `ga_head_out_loc` on `relabel D sigma`).
--   * `ga_indeg_wrap` : in-degree <= 1 (Laczkovich `ga_indegree`).
--   * `weighted_contra`: sum (out - in) = 0 against the pointwise bound out - in >= - s(v) with one strict vertex.
-- PRINTED GAP recorded (see (private working notes, not included)): the printed Lemma 10.4 asserts in-degree 0 at stars; the printed reason fails for a single interior star (4,2,1) = (3,1,0)+(1,1,1).  Here the stars are handled by weights, not by that claim.
-- NOTE, UNAUDITED.  Credit: Beeson (arXiv 1206.1974v7, Lemmas 10.2-10.6), Laczkovich (DCG 48 (2012), Sect. 4: Gamma_a, in-degree, heads), Beeson-Zhang.
import Erdos634.Draft.LaczFormalBZL7h1
import Erdos634.Draft.LaczFormalRGRelabel
import Erdos634.Draft.LaczFormalRG9Ia2

open scoped Classical
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ} [NeZero M]

/-- The head of a `GaEdge` has corner angle sum `pi` (one straight tile, the other tiles' corners fill the opposite half-plane). -/
theorem ga_head_Asum (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    (hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v)
    (hnc : NotComb (slen D 0) (slen D 1) (slen D 2)) {X H : Plane} (hE : GaEdge D.toRegionDissection (slen D 0) X H) :
    Asum D idx H = Real.pi := by
  classical
  obtain ⟨κ, _, ⟨F⟩⟩ := HasFansC.fans (D := D.toRegionDissection) H (ga_edge_vertex _ _ hE)
  obtain ⟨d, hd, nb, hc⟩ := ga_edge_data D idx hidx hnc hE F
  have key : ∀ {e : V2} {u v s : AtV D.toRegionDissection H}, HeadCfg D F e u v s → Asum D idx H = Real.pi := by
    intro e u v s hc
    obtain ⟨hc1, hc2, hc3, hc4, hc5, hc6, hc7⟩ := hc
    have hcyc := F.head_cyc u v s hc1 hc2 hc3 hc4 hc5 hc6
    obtain ⟨-, hsum, -⟩ := head_counts D idx hidxA F hcyc.1 hc6 hc1
    exact hsum
  rcases hc with ⟨P, W, hP, a, b, s, h1, h2, h3, h4, h5, h6, h7, h8⟩ | ⟨P, W, hP, a, b, s, h1, h2, h3, h4, h5, h6, h7, h8⟩
  · exact key (HeadCfg.of_left D F a b s h1 h2 h3 h4 h5 h6 h7 h8)
  · exact key (HeadCfg.of_right D F a b s h1 h2 h3 h4 h5 h6 h7 h8)

theorem notComb_ne01 {a b c : ℝ} (h : NotComb a b c) : a ≠ b := by
  intro e; exact h 1 1 0 one_pos (by simp [e])

theorem notComb_ne02 {a b c : ℝ} (h : NotComb a b c) : a ≠ c := by
  intro e; exact h 1 0 1 one_pos (by simp [e])

theorem Asum_relabel (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) (σ : Equiv.Perm (Fin 3)) (X : Plane) :
    Asum (relabel D σ) (relabelIdx idx σ) X = Asum D idx X := by
  unfold Asum
  have : ∀ l, (cnt (relabel D σ) (relabelIdx idx σ) X l : ℝ) * (relabel D σ).model.angleAt l = (cnt D idx X (σ l) : ℝ) * D.model.angleAt (σ l) := by
    intro l; rw [relabel_cnt]; congr 1; exact relabel_angleAt D σ l
  simp_rw [this]
  exact Equiv.sum_comp σ (fun l => (cnt D idx X l : ℝ) * D.model.angleAt l)

/-- **Head data of a `GaEdge` of the relabelled tile.**  `a = slen D (sigma 0)`. -/
theorem ga_head_data (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (idx : Fin N → Equiv.Perm (Fin 3)) (σ : Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    (hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v)
    (hnc : NotComb (slen D (σ 0)) (slen D (σ 1)) (slen D (σ 2))) {X H : Plane} (hE : GaEdge D.toRegionDissection (slen D (σ 0)) X H) :
    Asum D idx H = Real.pi ∧ H ∈ interior D.region ∧
      ((cnt D idx H (σ 1) + cnt D idx H (σ 2)) % 2 = 0 → ∃ H', GaEdge D.toRegionDissection (slen D (σ 0)) H H') := by
  classical
  haveI : HasFansC (relabel D σ).toRegionDissection := (inferInstance : HasFansC D.toRegionDissection)
  have hnc' : NotComb (slen (relabel D σ) 0) (slen (relabel D σ) 1) (slen (relabel D σ) 2) := by
    rw [relabel_slen, relabel_slen, relabel_slen]; exact hnc
  have hE' : GaEdge (relabel D σ).toRegionDissection (slen (relabel D σ) 0) X H := by
    rw [relabel_slen]; exact hE
  have hidx' := relabel_hidx D idx σ hidx
  have hidxA' := relabel_hidxA D idx σ hidxA
  refine ⟨?_, ga_head_interior (relabel D σ) (relabelIdx idx σ) hidx' hnc' hE', ?_⟩
  · rw [← Asum_relabel D idx σ]
    exact ga_head_Asum (relabel D σ) (relabelIdx idx σ) hidx' hidxA' hnc' hE'
  · intro hpar
    have hab := notComb_ne01 hnc'
    have hac := notComb_ne02 hnc'
    have := ga_head_out_loc (relabel D σ) (relabelIdx idx σ) hidx' hidxA' hnc' hab hac hE' (by
      intro hsum
      have := relabel_cnt D idx σ H 1
      have := relabel_cnt D idx σ H 2
      simpa [relabel_cnt] using hpar)
    obtain ⟨H', hH'⟩ := this
    refine ⟨H', ?_⟩
    rw [relabel_slen] at hH'
    exact hH'

/-- **In-degree at most one** (Laczkovich `ga_indegree`, relabelled). -/
theorem ga_indeg_wrap (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (idx : Fin N → Equiv.Perm (Fin 3)) (σ : Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    (hnc : NotComb (slen D (σ 0)) (slen D (σ 1)) (slen D (σ 2))) {X X' H : Plane}
    (h1 : GaEdge D.toRegionDissection (slen D (σ 0)) X H) (h2 : GaEdge D.toRegionDissection (slen D (σ 0)) X' H) : X = X' := by
  haveI : HasFansC (relabel D σ).toRegionDissection := (inferInstance : HasFansC D.toRegionDissection)
  have hnc' : NotComb (slen (relabel D σ) 0) (slen (relabel D σ) 1) (slen (relabel D σ) 2) := by
    rw [relabel_slen, relabel_slen, relabel_slen]; exact hnc
  have h1' : GaEdge (relabel D σ).toRegionDissection (slen (relabel D σ) 0) X H := by rw [relabel_slen]; exact h1
  have h2' : GaEdge (relabel D σ).toRegionDissection (slen (relabel D σ) 0) X' H := by rw [relabel_slen]; exact h2
  exact ga_indegree (relabel D σ) (relabelIdx idx σ) (relabel_hidx D idx σ hidx) hnc' h1' h2'

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.ga_head_data
#print axioms Erdos634.Draft.LaczFormal.RG.ga_indeg_wrap
