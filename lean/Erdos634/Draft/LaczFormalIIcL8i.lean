-- Draft/LaczFormalIIcL8i.lean -- Laczkovich (DCG 48 (2012)), Sect. 6.3, L8 `gexc_disjoint`, local geometry of tiles, step 2: `tiles_overlap`.
-- Tile T1 has Q in the OPEN side [A1,B1], the third vertex G1; tile T2 has Q in the closed side [A2,B2) (so the wedge at Q towards B2 is inside T2).  If B2 - Q points strictly to the G1 side of the line A1B1
-- (`0 < cross(B1-A1, B2-A2) * cross(B1-A1, G1-A1)`), then the interiors of T1 and T2 meet:  Z = A2 + (s2 + d)(B2-A2) + d^2 (G2-A2) for small d > 0 (Cramer coordinates in the frame of T1).
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcL8h

open Erdos634.Geometry Filter Topology

namespace Erdos634.Draft.LaczFormal.RG

theorem tiles_overlap (T1 T2 : Tri) {a1 b1 g1 a2 b2 g2 : Fin 3} (h1ab : a1 ≠ b1) (h1ag : a1 ≠ g1) (h1bg : b1 ≠ g1)
    (h2ab : a2 ≠ b2) (h2ag : a2 ≠ g2) (h2bg : b2 ≠ g2) {Q : Plane} {σ σ2 : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) (hσ20 : 0 ≤ σ2) (hσ21 : σ2 < 1)
    (hQ1 : Q = T1.pts a1 + σ • (T1.pts b1 - T1.pts a1)) (hQ2 : Q = T2.pts a2 + σ2 • (T2.pts b2 - T2.pts a2))
    (hsgn : 0 < cross (T1.pts b1 - T1.pts a1) (T2.pts b2 - T2.pts a2) * cross (T1.pts b1 - T1.pts a1) (T1.pts g1 - T1.pts a1)) :
    ∃ Z, Z ∈ interior T1.carrier ∧ Z ∈ interior T2.carrier := by
  set A1 := T1.pts a1; set B1 := T1.pts b1; set G1 := T1.pts g1
  set A2 := T2.pts a2; set B2 := T2.pts b2; set G2 := T2.pts g2
  have hκ := kappa_ne T1 h1ab h1ag h1bg
  set κ := cross (B1 - A1) (G1 - A1) with hκd
  set P1 := cross (B2 - A2) (G1 - A1)
  set P2 := cross (G2 - A2) (G1 - A1)
  set R1 := cross (B1 - A1) (B2 - A2)
  set R2 := cross (B1 - A1) (G2 - A2)
  let Zf : ℝ → Plane := fun δ => A2 + (σ2 + δ) • (B2 - A2) + δ ^ 2 • (G2 - A2)
  have hs1 : ∀ δ, cross (Zf δ - A1) (G1 - A1) / κ = σ + (δ * P1 + δ ^ 2 * P2) / κ := by
    intro δ
    have : cross (Zf δ - A1) (G1 - A1) = σ * κ + δ * P1 + δ ^ 2 * P2 := by
      have hZ : Zf δ - A1 = σ • (B1 - A1) + δ • (B2 - A2) + δ ^ 2 • (G2 - A2) := by
        have : Zf δ = Q + δ • (B2 - A2) + δ ^ 2 • (G2 - A2) := by
          rw [hQ2]; simp only [Zf, add_smul]; abel
        rw [this, hQ1]; abel
      rw [hZ]; simp only [P1, P2, κ, cross, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]; ring
    rw [this]; field_simp; ring
  have ht1 : ∀ δ, cross (B1 - A1) (Zf δ - A1) / κ = (δ * R1 + δ ^ 2 * R2) / κ := by
    intro δ
    have hZ : Zf δ - A1 = σ • (B1 - A1) + δ • (B2 - A2) + δ ^ 2 • (G2 - A2) := by
      have : Zf δ = Q + δ • (B2 - A2) + δ ^ 2 • (G2 - A2) := by
        rw [hQ2]; simp only [Zf, add_smul]; abel
      rw [this, hQ1]; abel
    rw [hZ]; congr 1
    simp only [R1, R2, cross, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]; ring
  have hR : 0 < R1 / κ := by
    have : R1 / κ = R1 * κ / κ ^ 2 := by field_simp
    rw [this]; exact div_pos hsgn (by positivity)
  -- smallness
  have c1 : ∀ᶠ δ in 𝓝 (0 : ℝ), 0 < σ + (δ * P1 + δ ^ 2 * P2) / κ := by
    have hc : Continuous fun δ : ℝ => σ + (δ * P1 + δ ^ 2 * P2) / κ := by fun_prop
    exact (hc.tendsto 0).eventually (lt_mem_nhds (by simpa using hσ0))
  have c2 : ∀ᶠ δ in 𝓝 (0 : ℝ), σ + (δ * P1 + δ ^ 2 * P2) / κ + (δ * R1 + δ ^ 2 * R2) / κ < 1 := by
    have hc : Continuous fun δ : ℝ => σ + (δ * P1 + δ ^ 2 * P2) / κ + (δ * R1 + δ ^ 2 * R2) / κ := by fun_prop
    exact (hc.tendsto 0).eventually (gt_mem_nhds (by simpa using hσ1))
  have c3 : ∀ᶠ δ in 𝓝 (0 : ℝ), 0 < (R1 + δ * R2) / κ := by
    have hc : Continuous fun δ : ℝ => (R1 + δ * R2) / κ := by fun_prop
    exact (hc.tendsto 0).eventually (lt_mem_nhds (by simpa using hR))
  have c4 : ∀ᶠ δ in 𝓝 (0 : ℝ), σ2 + δ + δ ^ 2 < 1 := by
    have hc : Continuous fun δ : ℝ => σ2 + δ + δ ^ 2 := by fun_prop
    exact (hc.tendsto 0).eventually (gt_mem_nhds (by simpa using hσ21))
  have hall := (c1.and (c2.and (c3.and c4))).filter_mono (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
  obtain ⟨δ, ⟨d1, d2, d3, d4⟩, hδ⟩ := (hall.and self_mem_nhdsWithin).exists
  have hδ0 : 0 < δ := hδ
  refine ⟨Zf δ, ?_, ?_⟩
  · apply cramer_interior T1 h1ab h1ag h1bg
    · rw [hs1]; exact d1
    · rw [ht1]
      have : (δ * R1 + δ ^ 2 * R2) / κ = δ * ((R1 + δ * R2) / κ) := by ring
      rw [this]; exact mul_pos hδ0 d3
    · rw [hs1, ht1]; exact d2
  · have := tri_interior_comb T2 h2ab h2ag h2bg (s := σ2 + δ) (t := δ ^ 2) (by linarith) (by positivity) (by linarith)
    exact this

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.tiles_overlap
