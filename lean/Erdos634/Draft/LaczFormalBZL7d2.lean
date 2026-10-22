-- Draft/LaczFormalBZL7d2.lean -- Beeson-Zhang (arXiv 2604.01314v1), proofs of Lemma 3.4 and Lemma 3.5: "There is no gamma angle of a tile at any vertex of ABC, since if there were, the other angles would have to be alpha and beta,
-- making ABC similar to the tile" -- the arithmetic core, formal.
--   `corner_split_core` : real numbers `theta_k = sum_l c k l * ang l` (k, l in Fin 3, `ang = (alpha, pi/3 - alpha, 2 pi/3)`, alpha not in Q pi), sum theta = pi, every theta_k > 0, some `c k0 2 >= 1`
--                        ==> there is a permutation rho with theta_k = ang (rho k) for all k   (the three corner angles are exactly alpha, beta, gamma).
--   `NotSim D`          : the target angles are not a permutation of the model angles (ABC is not similar to the tile).
--   `corner_gamma_zero_tri` : D : CongruentDissection of a triangle with NotSim, TwoPiThreeData, alpha irrational: no polygon corner carries a gamma angle (cnt = 0), in the ConvPoly 3 built by `exists_convpoly_of_tri`.
-- NOTE, UNAUDITED.  Credit: Beeson-Zhang (arXiv 2604.01314v1, proofs of Lemmas 3.4, 3.5), Laczkovich (DCG 48 (2012)), Beeson.
import Erdos634.Draft.LaczFormalBZL7d1
import Erdos634.Draft.LaczFormalBZL7c3

open scoped Classical
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

/-- Pure arithmetic: three positive corner angles made of `alpha, beta, gamma` with a `gamma` among them are exactly `alpha, beta, gamma` in some order. -/
theorem corner_split_core {α : ℝ} (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (θ : Fin 3 → ℝ) (c : Fin 3 → Fin 3 → ℕ)
    (ang : Fin 3 → ℝ) (h0 : ang 0 = α) (h1 : ang 1 = Real.pi / 3 - α) (h2 : ang 2 = 2 * Real.pi / 3)
    (hθ : ∀ k, θ k = ∑ l, (c k l : ℝ) * ang l) (hsum : θ 0 + θ 1 + θ 2 = Real.pi) (hpos : ∀ k, 0 < θ k)
    (k0 : Fin 3) (hk0 : 1 ≤ c k0 2) : ∃ ρ : Equiv.Perm (Fin 3), ∀ k, θ k = ang (ρ k) := by
  have hpi := Real.pi_pos
  simp only [Fin.sum_univ_three] at hθ
  have hs' : ∀ t0 t1 t2 : ℕ, (t0 : ℝ) * α + (t1 : ℝ) * (Real.pi / 3 - α) + (t2 : ℝ) * (2 * Real.pi / 3) = Real.pi → t0 = t1 ∧ t1 + 2 * t2 = 3 := by
    intro t0 t1 t2 h
    have := irr_coeff hα ((t0 : ℤ) - t1) (3 - (t1 : ℤ) - 2 * t2) (by push_cast; linear_combination h)
    omega
  have key := hs' (c 0 0 + c 1 0 + c 2 0) (c 0 1 + c 1 1 + c 2 1) (c 0 2 + c 1 2 + c 2 2)
    (by
      have hh := hsum
      rw [hθ 0, hθ 1, hθ 2, h0, h1, h2] at hh
      push_cast
      linear_combination hh)
  have fin3 : ∀ k : Fin 3, k = 0 ∨ k = 1 ∨ k = 2 := by decide
  have hT2 : 1 ≤ c 0 2 + c 1 2 + c 2 2 := by
    rcases fin3 k0 with rfl | rfl | rfl <;> omega
  have hT0 : c 0 0 + c 1 0 + c 2 0 = 1 := by omega
  have hT1 : c 0 1 + c 1 1 + c 2 1 = 1 := by omega
  have hT2' : c 0 2 + c 1 2 + c 2 2 = 1 := by omega
  -- each corner carries at least one angle
  have hone : ∀ k, c k 0 + c k 1 + c k 2 ≥ 1 := by
    intro k
    by_contra hlt
    have e0 : c k 0 = 0 := by omega
    have e1 : c k 1 = 0 := by omega
    have e2 : c k 2 = 0 := by omega
    have hk := hθ k
    rw [e0, e1, e2] at hk
    simp at hk
    linarith [hpos k]
  have hone0 := hone 0
  have hone1 := hone 1
  have hone2 := hone 2
  have hs0 : c 0 0 + c 0 1 + c 0 2 = 1 := by omega
  have hs1 : c 1 0 + c 1 1 + c 1 2 = 1 := by omega
  have hs2 : c 2 0 + c 2 1 + c 2 2 = 1 := by omega
  -- the permutation
  let f : Fin 3 → Fin 3 := fun k => if c k 0 = 1 then 0 else if c k 1 = 1 then 1 else 2
  have hrow : ∀ k, c k 0 + c k 1 + c k 2 = 1 := by
    intro k
    match k with
    | 0 => exact hs0
    | 1 => exact hs1
    | 2 => exact hs2
  have hθf : ∀ k, θ k = ang (f k) := by
    intro k
    have hr := hrow k
    rw [hθ k]
    simp only [f]
    by_cases a0 : c k 0 = 1
    · have : c k 1 = 0 := by omega
      have : c k 2 = 0 := by omega
      simp [a0, *]
    · by_cases a1 : c k 1 = 1
      · have : c k 0 = 0 := by omega
        have : c k 2 = 0 := by omega
        simp [a1, *]
      · have : c k 2 = 1 := by omega
        have : c k 0 = 0 := by omega
        have : c k 1 = 0 := by omega
        simp [*]
  have inj : Function.Injective f := by
    intro k k' h
    by_contra hne
    have r0 := hrow 0
    have r1 := hrow 1
    have r2 := hrow 2
    rcases fin3 k with rfl | rfl | rfl <;> rcases fin3 k' with rfl | rfl | rfl <;>
      first | exact hne rfl | (simp only [f] at h; split_ifs at h <;> omega)
  refine ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp inj), fun k => ?_⟩
  simpa using hθf k

/-- Target not similar to the tile: the target angles are not a permutation of the model angles. -/
def NotSim {N : ℕ} (D : CongruentDissection N) : Prop :=
  ¬ ∃ ρ : Equiv.Perm (Fin 3), ∀ j, D.target.angleAt j = D.model.angleAt (ρ j)

/-- **No `γ` corner at a vertex of the polygon** (Beeson-Zhang, proofs of Lemmas 3.4/3.5): if the corner angles of the triangle are not a permutation of `α, β, γ`, no polygon vertex carries a `γ` corner. -/
theorem corner_gamma_zero {N : ℕ} (Dr : CongruentRegionDissection N) [HasFansC Dr.toRegionDissection] (P : ConvPoly 3) (hreg : Dr.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hidxA : ∀ i v, Dr.model.angleAt (idx i v) = (Dr.tile i).angleAt v) {α : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (h0 : Dr.model.angleAt 0 = α) (h1 : Dr.model.angleAt 1 = Real.pi / 3 - α)
    (h2 : Dr.model.angleAt 2 = 2 * Real.pi / 3) (hsum : P.angle 0 + P.angle 1 + P.angle 2 = Real.pi) (hpos : ∀ i, 0 < P.angle i)
    (hNS : ¬ ∃ ρ : Equiv.Perm (Fin 3), ∀ k : Fin 3, P.angle (k + 1) = Dr.model.angleAt (ρ k)) :
    ∀ k : Fin 3, cnt Dr idx (P.v (k + 1)) 2 = 0 := by
  by_contra hne
  push Not at hne
  obtain ⟨k0, hk0⟩ := hne
  have hcA : ∀ k : Fin 3, P.angle (k + 1) = ∑ l, (cnt Dr idx (P.v (k + 1)) l : ℝ) * Dr.model.angleAt l := by
    intro k
    have hv : ∃ j k', (Dr.tile j).pts k' = P.v (k + 1) := poly_vertex_is_tile_vertex Dr.toRegionDissection P hreg (k + 1)
    exact (corner_A Dr P hreg idx hidxA k hv).symm.trans rfl
  have hsum' : P.angle (0 + 1) + P.angle (1 + 1) + P.angle (2 + 1) = Real.pi := by
    have e1 : (0 : Fin 3) + 1 = 1 := by decide
    have e2 : (1 : Fin 3) + 1 = 2 := by decide
    have e3 : (2 : Fin 3) + 1 = 0 := by decide
    rw [e1, e2, e3]; linarith
  obtain ⟨ρ, hρ⟩ := corner_split_core hα (fun k => P.angle (k + 1)) (fun k l => cnt Dr idx (P.v (k + 1)) l) Dr.model.angleAt h0 h1 h2
    hcA hsum' (fun k => hpos _) k0 (Nat.one_le_iff_ne_zero.mpr hk0)
  exact hNS ⟨ρ, hρ⟩

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.corner_gamma_zero
