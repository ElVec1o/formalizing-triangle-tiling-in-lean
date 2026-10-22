-- Draft/LaczFormalBZL7g1.lean -- Beeson (arXiv 1206.1974v7) Theorem 10.7 ASSEMBLY, with the geometric gaps G1-G6 as NAMED hypotheses.
--   `Thm107Gaps D idx`  : structure of the three link-graph statements (Lemmas 10.4 and 10.6 of the paper, geometric part):
--       linkB : NotComb b a c -> a link digraph on the vertices with in-degree <= 1, out>0 where in>0 (G2: Fig 13 casework on the b-side, G1: centre bridge, G5: Lemma 10.5 half-plane fan),
--               every centre having out>0 and in=0 (G1: Lemma 10.3 bridge from the real fan to abstract sector data; G4: Beeson's links vs Laczkovich's GaEdge);
--       linkA : same for NotComb a b c (G3: Fig 14 casework);
--       linkC : NotComb c a b -> link digraph with in<=1, out>0 where in>0, and one BOUNDARY vertex with out>0, in=0 (G5, G6: pigeonhole for a c edge on AC and AB).
--   `beeson_thm107`      : (alpha, pi-3 alpha, 2 alpha)-tiling of a convex polygon with corner angles alpha or pi-2 alpha (at least one of the latter), alpha not in Q pi, given `Thm107Gaps`:
--                          a/b and c/a are rational.  Proof: exists_center_a2 + link_graph_contra (x3) + thm107_algebra, all in Lean.
--   `beeson_thm107_of_comb` : the three relations as hypotheses (the form actually used).
-- Honest status: the three fields are the content of Lemmas 10.4/10.6 (geometric part) and are NOT proved here; the theorem names exactly this.  Witness: each field is an implication
-- with hypothesis NotComb, so it holds trivially for any tile with a/b, a/c rational (e.g. the 1125-tiling tile of BZL7f3): the structure is satisfiable.  NOTE, UNAUDITED.
-- Credit: Beeson (arXiv 1206.1974v7), Herdt, Zhang, Beeson-Zhang (arXiv 2604.01314), Laczkovich (DCG 48 (2012)).
import Erdos634.Draft.LaczFormalBZL7f1
import Erdos634.Draft.LaczFormalBZL7e1
import Erdos634.Draft.LaczFormalRGSideStep
import Erdos634.Draft.LaczFormalGraphGa

open scoped Classical
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ} [NeZero M]

/-- The vertex type of a region dissection. -/
abbrev Vt (D : CongruentRegionDissection N) : Type := {v // v ∈ vtxSet D.toRegionDissection}

/-- The counting conditions on a finite link digraph on `V`: in-degree `<= 1`, and out-degree `> 0` wherever in-degree `> 0`. -/
def LinkOK {V : Type} (E : Finset (V × V)) : Prop :=
  [DecidableEq V] → (∀ v, (E.filter fun e => e.2 = v).card ≤ 1) ∧
    (∀ v, 0 < (E.filter fun e => e.2 = v).card → 0 < (E.filter fun e => e.1 = v).card)

/-- A vertex `c` that is a source of the link digraph `E`: out-degree `> 0`, in-degree `0`. -/
def LinkSource {V : Type} (E : Finset (V × V)) (c : V) : Prop :=
  [DecidableEq V] → 0 < (E.filter fun e => e.1 = c).card ∧ (E.filter fun e => e.2 = c).card = 0

/-- **The geometric gaps G1-G6 of Beeson Thm 10.7** (printed Lemmas 10.3-10.6), as a structure.  See the file header. -/
structure Thm107Gaps (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) : Prop where
  linkB : NotComb (slen D 1) (slen D 0) (slen D 2) → ∃ E : Finset (Vt D × Vt D), LinkOK E ∧
    ∀ v : Vt D, cnt D idx v.1 0 = 0 → cnt D idx v.1 1 = 2 → cnt D idx v.1 2 = 3 → LinkSource E v
  linkA : NotComb (slen D 0) (slen D 1) (slen D 2) → ∃ E : Finset (Vt D × Vt D), LinkOK E ∧
    ∀ v : Vt D, cnt D idx v.1 0 = 0 → cnt D idx v.1 1 = 2 → cnt D idx v.1 2 = 3 → LinkSource E v
  linkC : NotComb (slen D 2) (slen D 0) (slen D 1) → ∃ E : Finset (Vt D × Vt D), LinkOK E ∧
    ∃ v : Vt D, LinkSource E v

/-- A tiling-level link digraph in the form of `link_graph_contra` yields `False`. -/
theorem linkOK_source_false {V : Type} [Fintype V] [DecidableEq V] (E : Finset (V × V)) (h : LinkOK E) (c : V) (hc : LinkSource E c) : False :=
  link_graph_contra E h.1 h.2 c hc.1 hc.2

theorem notComb_neg {x y z : ℝ} (h : ¬ NotComb x y z) : ∃ j p q : ℕ, 0 < j ∧ (j : ℝ) * x = p * y + q * z := by
  unfold NotComb at h
  push Not at h
  obtain ⟨r, p, q, hr, hh⟩ := h
  exact ⟨r, p, q, hr, hh⟩

/-- **Beeson Theorem 10.7 (assembly), conditional on the named gaps G1-G6.** -/
theorem beeson_thm107 (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v)
    (hβ : D.model.angleAt 1 = Real.pi - 3 * D.model.angleAt 0) (hγ : D.model.angleAt 2 = 2 * D.model.angleAt 0)
    (hα : ¬ ∃ r : ℚ, D.model.angleAt 0 = (r : ℝ) * Real.pi)
    (hPang : ∀ k : Fin M, P.angle (k + 1) = D.model.angleAt 0 ∨ P.angle (k + 1) = Real.pi - 2 * D.model.angleAt 0)
    (k0 : Fin M) (hk0 : P.angle (k0 + 1) = Real.pi - 2 * D.model.angleAt 0)
    (G : Thm107Gaps D idx) :
    ∃ r s : ℚ, slen D 0 = (r : ℝ) * slen D 1 ∧ slen D 2 = (s : ℝ) * slen D 0 := by
  obtain ⟨c0, hc0v, hc00, hc01, hc02⟩ := exists_center_a2 D P hreg idx hidxA hβ hγ hα hPang k0 hk0
  have ha := slen_pos D 0
  have hb := slen_pos D 1
  have hc := slen_pos D 2
  have hB : ¬ NotComb (slen D 1) (slen D 0) (slen D 2) := by
    intro hN
    obtain ⟨E, hE, hs⟩ := G.linkB hN
    exact linkOK_source_false E hE ⟨c0, hc0v⟩ (hs ⟨c0, hc0v⟩ hc00 hc01 hc02)
  have hA : ¬ NotComb (slen D 0) (slen D 1) (slen D 2) := by
    intro hN
    obtain ⟨E, hE, hs⟩ := G.linkA hN
    exact linkOK_source_false E hE ⟨c0, hc0v⟩ (hs ⟨c0, hc0v⟩ hc00 hc01 hc02)
  have hC : ¬ NotComb (slen D 2) (slen D 0) (slen D 1) := by
    intro hN
    obtain ⟨E, hE, v, hv⟩ := G.linkC hN
    exact linkOK_source_false E hE v hv
  obtain ⟨j, p, q, hj, h1⟩ := notComb_neg hA
  obtain ⟨J, P', Q, hJ, h2⟩ := notComb_neg hB
  obtain ⟨j', p', q', hj', h3⟩ := notComb_neg hC
  exact thm107_algebra ha hb hc j p q J P' Q j' p' q' hj hJ hj' h1 h2 h3

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.beeson_thm107
