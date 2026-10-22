import Erdos634.Draft.LaczFormalW2Far
import Erdos634.Draft.LaczFormalC0

/-!
# Rule W2: the far tile of the corner chord, with its edge (copy of `corner_far_gamma` with more output)

Erdős #634, base-`β` band.  Credit: AI assistant (item 3, band program), Beeson–Roșu, Beeson, Laczkovich, Paliy.
UNAUDITED.  Axiom-clean; no `sorry`.  New file (the audited `corner_far_gamma` is untouched).
-/

namespace Erdos634.LaczJunction

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.Geometry.Dissection

variable {N : ℕ}

theorem corner_far_edge_oriented (D : CongruentDissection N) (e f : ℕ) (he : 1 ≤ e)
    (hef : e < f) (hcop : Nat.Coprime e f) (α β γ : ℝ)
    (hγdef : γ = 2 * α + β) (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hα0 : 0 < α) (hβ0 : 0 < β)
    (hα' : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hβ' : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hγ' : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    (hsa : sideOpp D.model 0 = (ta e f : ℝ)) (hsb : sideOpp D.model 1 = (tb e f : ℝ))
    (hsc : sideOpp D.model 2 = (tc e f : ℝ))
    {P G : Plane} {p q r : Fin 3} (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (hP : P ∈ openSegment ℝ (D.target.pts p) (D.target.pts q))
    (hG : G ∈ openSegment ℝ (D.target.pts p) (D.target.pts r))
    (hPG : dist P G = (tb e f : ℝ))
    (i1 : Fin N) (j1 : Fin 3) (hPv : (D.tile i1).pts j1 = P) (hGv : (D.tile i1).pts (j1+1) = G)
    (hα1 : (D.tile i1).localAngle P = α) :
    ∃ (i' : Fin N) (k : Fin 3), i' ≠ i1 ∧
      dist ((D.tile i').pts k) ((D.tile i').pts (k+1)) = sideOpp D.model 1 ∧
      (((D.tile i').pts k = P ∧ (D.tile i').pts (k+1) = G) ∨
       ((D.tile i').pts k = G ∧ (D.tile i').pts (k+1) = P)) ∧
      (D.tile i').localAngle P = γ := by
  have hB : 0 < tb e f := b_pos e f he hef
  have hneab : sideOpp D.model 0 ≠ sideOpp D.model 1 := by
    rw [hsa, hsb]; intro h
    have h' : ta e f = tb e f := by exact_mod_cast h
    exact a_not_dvd_b e f he hef hcop (h' ▸ dvd_refl _)
  have hnebc : sideOpp D.model 1 ≠ sideOpp D.model 2 := by
    rw [hsb, hsc]; intro h
    have h' : tb e f = tc e f := by exact_mod_cast h
    have := b_lt_c e f he hef; omega
  have hnec : sideOpp D.model 0 ≠ sideOpp D.model 2 := by
    rw [hsa, hsc]; intro h
    have h' : ta e f = tc e f := by exact_mod_cast h
    have hac : ta e f < tc e f := by unfold ta tc; nlinarith
    omega
  have hαγ : α ≠ γ := by rw [hγdef]; intro h; linarith
  have hαβ : α ≠ β := by
    intro h
    apply hirr
    refine ⟨1/5, ?_⟩
    have : α = Real.pi / 5 := by rw [← h] at hrel; linarith
    rw [this]; push_cast; ring
  have hfar := far_edge_exists D.toDissection hpq hpr hqr (ta e f) (tb e f) (tc e f)
    (fun x y z h => cover_unique e f x y z he hef hcop h)
    (fun i k => by
      rcases edge_length_mem D i k with h | h | h
      · exact Or.inr (Or.inr (by rw [h, hsc]))
      · exact Or.inr (Or.inl (by rw [h, hsb]))
      · exact Or.inl (by rw [h, hsa]))
    hP hG hPG hB i1 j1 hPv hGv
  obtain ⟨i', k, hi'1, hbk, hends⟩ := hfar
  have hends0 := hends
  have hbk' : dist ((D.tile i').pts k) ((D.tile i').pts (k+1)) = sideOpp D.model 1 := by
    rw [hbk, hsb]
  have hb1 : dist ((D.tile i1).pts j1) ((D.tile i1).pts (j1+1)) = sideOpp D.model 1 := by
    rw [hPv, hGv, hPG, hsb]
  obtain ⟨hfrontG, hnvG⟩ := side_frontier D.target hpr hpq hqr.symm hG
  -- tile `i1` presents `γ` at `G`
  have hG1 : (D.tile i1).localAngle G = γ := by
    rcases bedge_ends_perm D α β γ hα' hβ' hγ' hneab hnebc hnec i1 j1 hb1 with ⟨_, h2⟩ | ⟨h1, _⟩
    · rw [hGv] at h2; exact h2
    · rw [hPv] at h1; exact absurd (hα1.symm.trans h1) hαγ
  have hnoG : (D.tile i').localAngle G ≠ γ := by
    intro hg
    exact congruentDissection_no_double_gamma D α β γ hαβ hαγ
      (by intro h; have := Real.pi_pos; linarith) hα0.ne' (by rw [hγdef]; intro h; linarith)
      (by intro h; linarith) hβ0.ne' (by intro h; linarith) (by intro h; linarith)
      Real.pi_ne_zero hγdef hrel hirr hα' hβ' hγ' hfrontG hnvG i1 i' hi'1.symm hG1 hg
  refine ⟨i', k, hi'1, hbk', hends0, ?_⟩
  rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rcases bedge_ends_perm D α β γ hα' hβ' hγ' hneab hnebc hnec i' k hbk' with ⟨_, hb⟩ | ⟨ha, _⟩
    · rw [h2] at hb; exact absurd hb hnoG
    · rw [h1] at ha; exact ha
  · rcases bedge_ends_perm D α β γ hα' hβ' hγ' hneab hnebc hnec i' k hbk' with ⟨_, hb⟩ | ⟨hg, _⟩
    · rw [h2] at hb; exact hb
    · rw [h1] at hg; exact absurd hg hnoG



/-- Orientation-free form (the corner tile's labelling is arbitrary: `TileVerts`). -/
theorem corner_far_edge (D : CongruentDissection N) (e f : ℕ) (he : 1 ≤ e)
    (hef : e < f) (hcop : Nat.Coprime e f) (α β γ : ℝ)
    (hγdef : γ = 2 * α + β) (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hα0 : 0 < α) (hβ0 : 0 < β)
    (hα' : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hβ' : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hγ' : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    (hsa : sideOpp D.model 0 = (ta e f : ℝ)) (hsb : sideOpp D.model 1 = (tb e f : ℝ))
    (hsc : sideOpp D.model 2 = (tc e f : ℝ))
    {P G Qc : Plane} {p q r : Fin 3} (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (hP : P ∈ openSegment ℝ (D.target.pts p) (D.target.pts q))
    (hG : G ∈ openSegment ℝ (D.target.pts p) (D.target.pts r))
    (hPG : dist P G = (tb e f : ℝ))
    (i1 : Fin N) (hv : TileVerts (D.tile i1) P G Qc)
    (hα1 : (D.tile i1).localAngle P = α) :
    ∃ (i' : Fin N) (k : Fin 3), i' ≠ i1 ∧
      dist ((D.tile i').pts k) ((D.tile i').pts (k+1)) = sideOpp D.model 1 ∧
      (((D.tile i').pts k = P ∧ (D.tile i').pts (k+1) = G) ∨
       ((D.tile i').pts k = G ∧ (D.tile i').pts (k+1) = P)) ∧
      (D.tile i').localAngle P = γ := by
  rcases hv.oriented with ⟨j1, hPv, hGv, -⟩ | ⟨j1, hPv, hGv, -⟩
  · exact corner_far_edge_oriented D e f he hef hcop α β γ hγdef hrel hirr hα0 hβ0 hα' hβ' hγ' hsa
      hsb hsc hpq hpr hqr hP hG hPG i1 j1 hPv hGv hα1
  · obtain ⟨i', k, hne, hd, he', hγ⟩ := corner_far_edge_oriented (D.revAt i1) e f he hef hcop α β γ hγdef
      hrel hirr hα0 hβ0 hα' hβ' hγ' hsa hsb hsc hpq hpr hqr hP hG hPG i1 j1
      (by rw [revAt_tile_self]; exact hPv) (by rw [revAt_tile_self]; exact hGv)
      (by rw [revAt_tile_self, rev_localAngle]; exact hα1)
    rw [revAt_tile_ne D hne] at hd he' hγ
    exact ⟨i', k, hne, hd, he', hγ⟩

#print axioms corner_far_edge

end Erdos634.LaczJunction
