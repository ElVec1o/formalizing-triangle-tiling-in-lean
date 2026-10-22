-- Draft/LaczFormalBZL7h3.lean -- Beeson (arXiv 1206.1974v7) Lemmas 10.4, 10.6: the WEIGHTED counting contradiction for the link graph `Gamma_a(sigma) = {GaEdge (slen D (sigma 0))}` of a real dissection.
--   `weighted_contra` (abstract digraph) and `gamma_contra` (real: in-degree <= 1 from Laczkovich, weights `s`, pointwise bound at heads / non-heads, one strict vertex => False).
-- NOTE, UNAUDITED.  Credit: Beeson (arXiv 1206.1974v7, Lemmas 10.2, 10.4, 10.6), Laczkovich (DCG 48 (2012), Sect. 4), Beeson-Zhang.
import Erdos634.Draft.LaczFormalBZL7h2

open scoped Classical
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ} [NeZero M]

/-- **Weighted counting step.**  `sum (out - in) = 0` in any finite digraph; if `out - in >= -s` pointwise, `sum s = 0`, and the inequality is strict somewhere: contradiction. -/
theorem weighted_contra {V : Type*} [Fintype V] [DecidableEq V] (E : Finset (V × V)) (s : V → ℤ) (hs : ∑ v, s v = 0)
    (hpt : ∀ v, -(s v) ≤ ((E.filter fun e => e.1 = v).card : ℤ) - (E.filter fun e => e.2 = v).card)
    (v0 : V) (hstrict : -(s v0) < ((E.filter fun e => e.1 = v0).card : ℤ) - (E.filter fun e => e.2 = v0).card) : False := by
  have h1 : E.card = ∑ v, (E.filter fun e => e.1 = v).card :=
    Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (t := Finset.univ) (fun _ _ => Finset.mem_univ _)
  have h2 : E.card = ∑ v, (E.filter fun e => e.2 = v).card :=
    Finset.card_eq_sum_card_fiberwise (f := Prod.snd) (t := Finset.univ) (fun _ _ => Finset.mem_univ _)
  have hsum : ∑ v, (((E.filter fun e => e.1 = v).card : ℤ) - (E.filter fun e => e.2 = v).card) = 0 := by
    rw [Finset.sum_sub_distrib]
    have a1 : (∑ v, ((E.filter fun e => e.1 = v).card : ℤ)) = (E.card : ℤ) := by rw [h1]; push_cast; rfl
    have a2 : (∑ v, ((E.filter fun e => e.2 = v).card : ℤ)) = (E.card : ℤ) := by rw [h2]; push_cast; rfl
    rw [a1, a2]; ring
  have hlt := Finset.sum_lt_sum (s := (Finset.univ : Finset V)) (f := fun v => -(s v))
    (g := fun v => ((E.filter fun e => e.1 = v).card : ℤ) - (E.filter fun e => e.2 = v).card) (fun v _ => hpt v) ⟨v0, Finset.mem_univ _, hstrict⟩
  rw [Finset.sum_neg_distrib, hs, hsum] at hlt
  omega

/-- **The real link-graph contradiction** for `GaEdge D (slen D (sigma 0))`.  Hypotheses: `NotComb`; weights `s` with `sum over the tiling vertices = 0`;
`hnonhead`: a vertex that is not a head has `s >= 0`, or `s = -1` and an outgoing edge; `hhead`: a head has `s >= 0` and an outgoing edge or `s >= 1`;
`hstrict`: a non-head with `s >= 1`, or with `s >= 0` and an outgoing edge. -/
theorem gamma_contra (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (idx : Fin N → Equiv.Perm (Fin 3)) (σ : Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    (hnc : NotComb (slen D (σ 0)) (slen D (σ 1)) (slen D (σ 2))) (s : Plane → ℤ)
    (hs : ∑ v ∈ vtxSet D.toRegionDissection, s v = 0)
    (hnonhead : ∀ v ∈ vtxSet D.toRegionDissection, (¬ ∃ X, GaEdge D.toRegionDissection (slen D (σ 0)) X v) →
      0 ≤ s v ∨ (s v = -1 ∧ ∃ H, GaEdge D.toRegionDissection (slen D (σ 0)) v H))
    (hhead : ∀ v ∈ vtxSet D.toRegionDissection, (∃ X, GaEdge D.toRegionDissection (slen D (σ 0)) X v) →
      0 ≤ s v ∧ ((∃ H, GaEdge D.toRegionDissection (slen D (σ 0)) v H) ∨ 1 ≤ s v))
    (hstrict : ∃ v0 ∈ vtxSet D.toRegionDissection, (¬ ∃ X, GaEdge D.toRegionDissection (slen D (σ 0)) X v0) ∧
      (1 ≤ s v0 ∨ (0 ≤ s v0 ∧ ∃ H, GaEdge D.toRegionDissection (slen D (σ 0)) v0 H))) : False := by
  classical
  set a := slen D (σ 0) with ha
  let E : Finset (Vt D × Vt D) := Finset.univ.filter (fun e => GaEdge D.toRegionDissection a e.1.1 e.2.1)
  have hEmem : ∀ e : Vt D × Vt D, e ∈ E ↔ GaEdge D.toRegionDissection a e.1.1 e.2.1 := by
    intro e; simp [E]
  have hmk : ∀ {X H : Plane}, GaEdge D.toRegionDissection a X H → ∃ x h : Vt D, x.1 = X ∧ h.1 = H ∧ (x, h) ∈ E := by
    intro X H hE
    have := ga_edge_endpoints D.toRegionDissection a hE
    refine ⟨⟨X, mem_vtxSet.mpr this.1⟩, ⟨H, mem_vtxSet.mpr this.2⟩, rfl, rfl, (hEmem _).mpr hE⟩
  have hin_le : ∀ v : Vt D, (E.filter fun e => e.2 = v).card ≤ 1 := by
    intro v
    rw [Finset.card_le_one]
    intro x hx y hy
    simp only [Finset.mem_filter] at hx hy
    have h1 := (hEmem x).mp hx.1
    have h2 := (hEmem y).mp hy.1
    rw [hx.2] at h1
    rw [hy.2] at h2
    have := ga_indeg_wrap D idx σ hidx hnc h1 h2
    exact Prod.ext (Subtype.ext this) (hx.2.trans hy.2.symm)
  have hin_pos : ∀ v : Vt D, (∃ X, GaEdge D.toRegionDissection a X v.1) → (E.filter fun e => e.2 = v).card = 1 := by
    intro v ⟨X, hX⟩
    obtain ⟨x, h, hx, hh, hxh⟩ := hmk hX
    have hhv : h = v := Subtype.ext hh
    subst hhv
    have : 0 < (E.filter fun e => e.2 = h).card := Finset.card_pos.mpr ⟨(x, h), by simp [hxh]⟩
    have := hin_le h
    omega
  have hin_zero : ∀ v : Vt D, (¬ ∃ X, GaEdge D.toRegionDissection a X v.1) → (E.filter fun e => e.2 = v).card = 0 := by
    intro v hv
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro e he hev
    exact hv ⟨e.1.1, by have := (hEmem e).mp he; rw [hev] at this; exact this⟩
  have hout_pos : ∀ v : Vt D, (∃ H, GaEdge D.toRegionDissection a v.1 H) → 1 ≤ (E.filter fun e => e.1 = v).card := by
    intro v ⟨H, hH⟩
    obtain ⟨x, h, hx, hh, hxh⟩ := hmk hH
    have hxv : x = v := Subtype.ext hx
    subst hxv
    exact Finset.card_pos.mpr ⟨(x, h), by simp [hxh]⟩
  obtain ⟨v0, hv0, hh0, hc0⟩ := hstrict
  refine weighted_contra E (fun v => s v.1) ?_ ?_ ⟨v0, hv0⟩ ?_
  · rw [Finset.sum_coe_sort (vtxSet D.toRegionDissection) s]; exact hs
  · intro v
    by_cases hh : ∃ X, GaEdge D.toRegionDissection a X v.1
    · rw [hin_pos v hh]
      obtain ⟨h0, h1 | h1⟩ := hhead v.1 v.2 hh
      · have := hout_pos v h1; push_cast; omega
      · push_cast; omega
    · rw [hin_zero v hh]
      rcases hnonhead v.1 v.2 hh with h0 | ⟨h0, h1⟩
      · push_cast; omega
      · have := hout_pos v h1; push_cast; omega
  · rw [hin_zero ⟨v0, hv0⟩ hh0]
    rcases hc0 with h1 | ⟨h1, h2⟩
    · show -(s v0) < _ - ((0 : ℕ) : ℤ)
      push_cast; omega
    · have := hout_pos ⟨v0, hv0⟩ h2
      show -(s v0) < _ - ((0 : ℕ) : ℤ)
      push_cast; omega

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.gamma_contra
