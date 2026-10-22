-- Draft/LaczFormalBZL7h4.lean -- Beeson (arXiv 1206.1974v7) Theorem 10.7, assembly WITHOUT the star hypothesis.  The link graphs are Laczkovich's `GaEdge` (relabelled); the printed counting at stars is replaced by weights.
--   `centre_contra` : (Lemma 10.4) for sigma 0 in {0,1}: NotComb (a-type side) and "every centre has an outgoing GaEdge" (G1, OPEN) => False.
--   `c_contra`      : (Lemma 10.6) NotComb c a b and "some boundary vertex has an outgoing Gamma_c edge" (G5/G6 transition, OPEN) => False.
--   `beeson_thm107_partial` : a/b and c/a rational, from the THREE open hypotheses `G1a`, `G1b`, `G5c` only.  Every other link-graph fact (in-degree, heads, interior, parity, stars, boundary) is proved.
-- NOTE, UNAUDITED.  Credit: Beeson (arXiv 1206.1974v7, Lemmas 10.2-10.7), Laczkovich (DCG 48 (2012), Sect. 4), Herdt, Zhang, Beeson-Zhang.
import Erdos634.Draft.LaczFormalBZL7h3
import Erdos634.Draft.LaczFormalBZL7f2
import Erdos634.Draft.LaczFormalRG5GammaC

open scoped Classical
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ} [NeZero M]

theorem notComb_swap {a b c : ℝ} (h : NotComb a b c) : NotComb a c b := by
  intro r p q hr e; exact h r q p hr (by linarith)

theorem cnt_sum_perm (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) (σ : Equiv.Perm (Fin 3)) (X : Plane) :
    cnt D idx X (σ 0) + cnt D idx X (σ 1) + cnt D idx X (σ 2) = cnt D idx X 0 + cnt D idx X 1 + cnt D idx X 2 := by
  have := Equiv.sum_comp σ (fun l => cnt D idx X l)
  simpa [Fin.sum_univ_three] using this

/-- Corner counts at a vertex with corner sum `pi`: `(3,1,0)` or `(1,1,1)`. -/
theorem head_classify (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3))
    (hβ : D.model.angleAt 1 = Real.pi - 3 * D.model.angleAt 0) (hγ : D.model.angleAt 2 = 2 * D.model.angleAt 0)
    (hα : ¬ ∃ r : ℚ, D.model.angleAt 0 = (r : ℝ) * Real.pi) {X : Plane} (h : Asum D idx X = Real.pi) :
    cnt D idx X 1 = 1 ∧ ((cnt D idx X 0 = 3 ∧ cnt D idx X 2 = 0) ∨ (cnt D idx X 0 = 1 ∧ cnt D idx X 2 = 1)) := by
  have hAexp : Asum D idx X = (cnt D idx X 0 : ℝ) * D.model.angleAt 0 + (cnt D idx X 1 : ℝ) * D.model.angleAt 1
      + (cnt D idx X 2 : ℝ) * (2 * D.model.angleAt 0) := by
    unfold Asum; rw [Fin.sum_univ_three, hγ]
  exact boundary_vtype (α := D.model.angleAt 0) (β := D.model.angleAt 1) hβ hα _ _ _ (by rw [← hAexp]; exact h)

/-- Every tiling vertex that is not a centre has `#beta >= #gamma` (Beeson Lemma 10.2, the pointwise part). -/
theorem s_nonneg (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v)
    (hβ : D.model.angleAt 1 = Real.pi - 3 * D.model.angleAt 0) (hγ : D.model.angleAt 2 = 2 * D.model.angleAt 0)
    (hα : ¬ ∃ r : ℚ, D.model.angleAt 0 = (r : ℝ) * Real.pi)
    (hPang : ∀ k : Fin M, P.angle (k + 1) = D.model.angleAt 0 ∨ P.angle (k + 1) = Real.pi - 2 * D.model.angleAt 0)
    {v : Plane} (hv : v ∈ vtxSet D.toRegionDissection)
    (hn : cnt D idx v 0 = 0 → cnt D idx v 1 = 2 → cnt D idx v 2 = 3 → False) : 0 ≤ (cnt D idx v 1 : ℤ) - cnt D idx v 2 := by
  have hAexp : Asum D idx v = (cnt D idx v 0 : ℝ) * D.model.angleAt 0 + (cnt D idx v 1 : ℝ) * D.model.angleAt 1
      + (cnt D idx v 2 : ℝ) * (2 * D.model.angleAt 0) := by
    unfold Asum; rw [Fin.sum_univ_three, hγ]
  have key : ∀ p : ℤ, ∀ q : ℕ, Asum D idx v = p * D.model.angleAt 0 + q * Real.pi →
      (cnt D idx v 1 : ℤ) = q ∧ (cnt D idx v 0 : ℤ) + 2 * cnt D idx v 2 - 3 * cnt D idx v 1 = p := by
    intro p q h
    refine vtype_arith (α := D.model.angleAt 0) (β := D.model.angleAt 1) hβ hα _ _ _ p q ?_
    rw [← hAexp]; exact h
  have hvert : ∃ j k, (D.tile j).pts k = v := mem_vtxSet.mp hv
  rcases vertex_A D P hreg idx hidxA hvert with ⟨_, h2 | h1⟩ | ⟨_, h1 | ⟨k, hXk, hk⟩⟩
  · have := key 0 2 (by rw [h2]; push_cast; ring)
    have h0 : cnt D idx v 1 = 2 := by omega
    have h2' : cnt D idx v 2 ≠ 3 := fun h3 => hn (by omega) h0 h3
    omega
  · have := key 0 1 (by rw [h1]; push_cast; ring)
    omega
  · have := key 0 1 (by rw [h1]; push_cast; ring)
    omega
  · rcases hPang k with hk1 | hk1
    · have := key 1 0 (by rw [hk, hk1]; push_cast; ring)
      omega
    · have := key (-2) 1 (by rw [hk, hk1]; push_cast; ring)
      omega

/-- The vertex `B` (polygon angle `pi - 2 alpha`) has `#beta - #gamma = 1`. -/
theorem s_B (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v)
    (hβ : D.model.angleAt 1 = Real.pi - 3 * D.model.angleAt 0) (hγ : D.model.angleAt 2 = 2 * D.model.angleAt 0)
    (hα : ¬ ∃ r : ℚ, D.model.angleAt 0 = (r : ℝ) * Real.pi) (k0 : Fin M) (hk0 : P.angle (k0 + 1) = Real.pi - 2 * D.model.angleAt 0) :
    (cnt D idx (P.v (k0 + 1)) 1 : ℤ) - cnt D idx (P.v (k0 + 1)) 2 = 1 := by
  have hv0 : ∃ j k, (D.tile j).pts k = P.v (k0 + 1) := poly_vertex_is_tile_vertex D.toRegionDissection P hreg (k0 + 1)
  have hcA := corner_A D P hreg idx hidxA k0 hv0
  have hAexp : Asum D idx (P.v (k0 + 1)) = (cnt D idx (P.v (k0 + 1)) 0 : ℝ) * D.model.angleAt 0 + (cnt D idx (P.v (k0 + 1)) 1 : ℝ) * D.model.angleAt 1
      + (cnt D idx (P.v (k0 + 1)) 2 : ℝ) * (2 * D.model.angleAt 0) := by
    unfold Asum; rw [Fin.sum_univ_three, hγ]
  have := vtype_arith (α := D.model.angleAt 0) (β := D.model.angleAt 1) hβ hα _ _ _ (-2) 1 (by rw [← hAexp, hcA, hk0]; push_cast; ring)
  omega

theorem sum_s_zero (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) :
    ∑ v ∈ vtxSet D.toRegionDissection, ((cnt D idx v 1 : ℤ) - cnt D idx v 2) = 0 := by
  have hs1 : ∑ v ∈ vtxSet D.toRegionDissection, (cnt D idx v 1 : ℤ) = N := by exact_mod_cast sum_cnt_vtx D idx 1
  have hs2 : ∑ v ∈ vtxSet D.toRegionDissection, (cnt D idx v 2 : ℤ) = N := by exact_mod_cast sum_cnt_vtx D idx 2
  rw [Finset.sum_sub_distrib, hs1, hs2]; ring

/-- **Lemma 10.4 (counting part).**  `a`-type side `slen D (sigma 0)` with `sigma 0 in {0,1}`, `NotComb`, and G1: every centre has an outgoing `GaEdge`.  Then `False`. -/
theorem centre_contra (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    (hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v)
    (hβ : D.model.angleAt 1 = Real.pi - 3 * D.model.angleAt 0) (hγ : D.model.angleAt 2 = 2 * D.model.angleAt 0)
    (hα : ¬ ∃ r : ℚ, D.model.angleAt 0 = (r : ℝ) * Real.pi)
    (hPang : ∀ k : Fin M, P.angle (k + 1) = D.model.angleAt 0 ∨ P.angle (k + 1) = Real.pi - 2 * D.model.angleAt 0)
    (k0 : Fin M) (hk0 : P.angle (k0 + 1) = Real.pi - 2 * D.model.angleAt 0)
    (σ : Equiv.Perm (Fin 3)) (hσ : σ 0 = 0 ∨ σ 0 = 1)
    (hnc : NotComb (slen D (σ 0)) (slen D (σ 1)) (slen D (σ 2)))
    (G1 : ∀ v ∈ vtxSet D.toRegionDissection, cnt D idx v 0 = 0 → cnt D idx v 1 = 2 → cnt D idx v 2 = 3 →
      ∃ H, GaEdge D.toRegionDissection (slen D (σ 0)) v H) : False := by
  classical
  refine gamma_contra D idx σ hidx hnc (fun v => (cnt D idx v 1 : ℤ) - cnt D idx v 2) (sum_s_zero D idx) ?_ ?_ ?_
  · intro v hv hnh
    by_cases hc : cnt D idx v 0 = 0 ∧ cnt D idx v 1 = 2 ∧ cnt D idx v 2 = 3
    · right
      refine ⟨by simp only; omega, G1 v hv hc.1 hc.2.1 hc.2.2⟩
    · left
      exact s_nonneg D P hreg idx hidxA hβ hγ hα hPang hv (fun h0 h1 h2 => hc ⟨h0, h1, h2⟩)
  · intro v hv ⟨X, hX⟩
    obtain ⟨hAs, -, hout⟩ := ga_head_data D idx σ hidx hidxA hnc hX
    obtain ⟨h1, h3 | h3⟩ := head_classify D idx hβ hγ hα hAs
    · refine ⟨by simp only; omega, Or.inr (by simp only; omega)⟩
    · refine ⟨by simp only; omega, Or.inl (hout ?_)⟩
      have := cnt_sum_perm D idx σ v
      rcases hσ with e | e <;> rw [e] at this <;> omega
  · refine ⟨P.v (k0 + 1), mem_vtxSet.mpr (poly_vertex_is_tile_vertex D.toRegionDissection P hreg (k0 + 1)), ?_, Or.inl ?_⟩
    · rintro ⟨X, hX⟩
      have := (ga_head_data D idx σ hidx hidxA hnc hX).2.1
      rw [hreg] at this
      exact polyVertex_not_interior P (k0 + 1) this
    · have := s_B D P hreg idx hidxA hβ hγ hα k0 hk0
      simp only; omega

/-- **Lemma 10.6 (counting part).**  `NotComb c a b` and a boundary vertex with an outgoing `Gamma_c` edge (G5, OPEN) give `False`: every head of `Gamma_c` has an outgoing edge. -/
theorem c_contra (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    (hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v)
    (hβ : D.model.angleAt 1 = Real.pi - 3 * D.model.angleAt 0) (hγ : D.model.angleAt 2 = 2 * D.model.angleAt 0)
    (hα : ¬ ∃ r : ℚ, D.model.angleAt 0 = (r : ℝ) * Real.pi)
    (hnc : NotComb (slen D 2) (slen D 0) (slen D 1))
    (G5 : ∃ Q, Q ∉ interior D.region ∧ ∃ H, GaEdge D.toRegionDissection (slen D 2) Q H) : False := by
  classical
  have hs02 : (Equiv.swap (0 : Fin 3) 2) 0 = 2 := swap02_0
  have hs12 : (Equiv.swap (0 : Fin 3) 2) 1 = 1 := swap02_1
  have hs22 : (Equiv.swap (0 : Fin 3) 2) 2 = 0 := swap02_2
  have hnc' : NotComb (slen D ((Equiv.swap (0 : Fin 3) 2) 0)) (slen D ((Equiv.swap (0 : Fin 3) 2) 1)) (slen D ((Equiv.swap (0 : Fin 3) 2) 2)) := by
    rw [hs02, hs12, hs22]; exact notComb_swap hnc
  obtain ⟨Q, hQ, H, hQH⟩ := G5
  refine gamma_contra D idx (Equiv.swap 0 2) hidx hnc' (fun _ => 0) (by simp) ?_ ?_ ?_
  · intro v hv hnh; left; exact le_rfl
  · intro v hv ⟨X, hX⟩
    obtain ⟨hAs, -, hout⟩ := ga_head_data D idx _ hidx hidxA hnc' hX
    refine ⟨le_rfl, Or.inl (hout ?_)⟩
    rw [hs12, hs22]
    obtain ⟨h1, h3 | h3⟩ := head_classify D idx hβ hγ hα hAs <;> omega
  · have hendp := ga_edge_endpoints D.toRegionDissection (slen D ((Equiv.swap (0 : Fin 3) 2) 0)) (by rw [hs02]; exact hQH)
    refine ⟨Q, mem_vtxSet.mpr hendp.1, ?_, Or.inr ⟨le_rfl, H, by rw [hs02]; exact hQH⟩⟩
    rintro ⟨X, hX⟩
    have := (ga_head_data D idx _ hidx hidxA hnc' hX).2.1
    exact hQ this

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.centre_contra
#print axioms Erdos634.Draft.LaczFormal.RG.c_contra
