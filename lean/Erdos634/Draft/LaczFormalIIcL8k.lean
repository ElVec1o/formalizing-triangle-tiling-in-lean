-- Draft/LaczFormalIIcL8k.lean -- Laczkovich (DCG 48 (2012)), Sect. 6.3, L8 `gexc_disjoint`, step 4: `no_inner_cross` (B1).  See L8j for the idea.
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcL8j

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N : ℕ}

/-- a point in the open side `(a1,b1)` of a triangle that lies in the half-open side `[a2, b2)` forces the two sides to coincide. -/
theorem inner_vs_side (T : Tri) {a1 b1 a2 b2 : Fin 3} (hab1 : a1 ≠ b1) (hab2 : a2 ≠ b2) {Q : Plane} (hQ1 : Q ∈ openSegment ℝ (T.pts a1) (T.pts b1))
    {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ < 1) (hQ2 : Q = T.pts a2 + σ • (T.pts b2 - T.pts a2)) : (a1 = a2 ∧ b1 = b2) ∨ (a1 = b2 ∧ b1 = a2) := by
  rcases hσ0.eq_or_lt with h | h
  · exfalso
    subst h
    rw [zero_smul, add_zero] at hQ2
    have hc := fun m => coord_pos_iff T hab1 rfl rfl hQ1 m
    have c1 := (hc a1).2 (Or.inl rfl)
    have c2 := (hc b1).2 (Or.inr rfl)
    have e : ∀ m, m ≠ a2 → T.basis.coord m Q = 0 := fun m hm => by
      rw [hQ2]; exact Erdos634.Draft.NearBaseVertex.coord_other T hm
    have h1 : a1 = a2 := by by_contra hne; rw [e a1 hne] at c1; exact lt_irrefl _ c1
    have h2 : b1 = a2 := by by_contra hne; rw [e b1 hne] at c2; exact lt_irrefl _ c2
    exact hab1 (h1.trans h2.symm)
  · have hQ2' : Q ∈ openSegment ℝ (T.pts a2) (T.pts b2) := by
      refine ⟨1 - σ, σ, by linarith, h, by ring, ?_⟩
      rw [hQ2]; module
    exact tri_inner_side_unique T hab1 hab2 rfl rfl rfl rfl hQ1 hQ2'

theorem crs_zero_of_pm {u d : V2} {c1 c2 : ℝ} {w1 w2 : V2} (hw1 : w1 = (c1 * u.1, c1 * u.2)) (hw2 : w2 = (c2 * d.1, c2 * d.2))
    (hc1 : 0 < c1) (hc2 : 0 < c2) (h : w1 = w2 ∨ w1 = (-w2.1, -w2.2)) : crs u d = 0 := by
  subst hw1 hw2
  have key : c1 * c2 * crs u d = 0 := by
    rcases h with h | h
    · have e1 := congrArg Prod.fst h
      have e2 := congrArg Prod.snd h
      simp only at e1 e2
      unfold crs; linear_combination (d.2 * c2) * e1 - (d.1 * c2) * e2
    · have e1 := congrArg Prod.fst h
      have e2 := congrArg Prod.snd h
      simp only at e1 e2
      unfold crs; linear_combination (d.2 * c2) * e1 - (d.1 * c2) * e2
  have := mul_pos hc1 hc2
  exact (mul_eq_zero.mp key).resolve_left this.ne'

theorem toV2_neg_sub (x y : Plane) : toV2 (x - y) = (-(toV2 (y - x)).1, -(toV2 (y - x)).2) := by
  unfold toV2; ext <;> simp

/-- **(B1)**  A tile `T1` with `Q` in the open side of one of its sides cannot coexist with a left walk along a line NOT parallel to that side that passes through `Q` (strictly inside the walk). -/
theorem no_inner_cross (D : RegionDissection N) {i1 : Fin N} {u1 : V2} {A1 B1 Q : Plane} (h1 : TriStep (D.tile i1) u1 A1 B1) (hQ : Q ∈ openSegment ℝ A1 B1)
    {d : V2} (hd : d ≠ 0) {X Z : Plane} {L : List (Fin N × Plane × Plane)} (W : WalkU D true d X Z L) {T v : ℝ}
    (hT : toV2 (Z - X) = (T * d.1, T * d.2)) (hQd : toV2 (Q - X) = (v * d.1, v * d.2)) (hv0 : 0 < v) (hvT : v < T) (hnp : crs u1 d ≠ 0) : False := by
  obtain ⟨hfwd, hbck⟩ := walk_fwd_back D hd W hT hQd hv0 hvT
  obtain ⟨kk1, f1, g1, hk1, hf1, hfk1, hgk1, hgf1, hpar1, hleft1⟩ := id h1
  subst hk1; subst hf1
  obtain ⟨c1, hc1, hcw1⟩ := hpar1.smul
  obtain ⟨σ, hσ0, hσ1, hQσ⟩ := openSegment_param hQ
  have hκ : 0 < cross ((D.tile i1).pts f1 - (D.tile i1).pts kk1) ((D.tile i1).pts g1 - (D.tile i1).pts kk1) := by
    have : cross ((D.tile i1).pts f1 - (D.tile i1).pts kk1) ((D.tile i1).pts g1 - (D.tile i1).pts kk1)
        = c1 * crs u1 (toV2 ((D.tile i1).pts g1 - (D.tile i1).pts kk1)) := by
      rw [← crs_toV2, hcw1]; unfold crs; ring
    rw [this]; exact mul_pos hc1 hleft1
  rcases lt_or_gt_of_ne hnp with hneg | hpos
  · -- towards -d
    obtain ⟨i2, A2, B2, σ2, hS2, hQ2, h20, h21⟩ := hbck
    obtain ⟨kk2, f2, g2, hk2, hf2, hfk2, hgk2, hgf2, hpar2, hleft2⟩ := id hS2
    subst hk2; subst hf2
    obtain ⟨c2, hc2, hcw2⟩ := hpar2.smul
    have hsgn : 0 < cross ((D.tile i1).pts f1 - (D.tile i1).pts kk1) ((D.tile i2).pts kk2 - (D.tile i2).pts f2) *
        cross ((D.tile i1).pts f1 - (D.tile i1).pts kk1) ((D.tile i1).pts g1 - (D.tile i1).pts kk1) := by
      have : cross ((D.tile i1).pts f1 - (D.tile i1).pts kk1) ((D.tile i2).pts kk2 - (D.tile i2).pts f2) = c1 * c2 * (- crs u1 d) := by
        rw [← crs_toV2, hcw1, toV2_neg_sub, hcw2]; unfold crs; simp only; ring
      rw [this]; exact mul_pos (mul_pos (mul_pos hc1 hc2) (by linarith)) hκ
    obtain ⟨Z', hZ1, hZ2⟩ := tiles_overlap (D.tile i1) (D.tile i2) (a1 := kk1) (b1 := f1) (g1 := g1) (a2 := f2) (b2 := kk2) (g2 := g2)
      hfk1.symm (fun h => hgk1 h.symm) (fun h => hgf1 h.symm) hfk2 (fun h => hgf2 h.symm) (fun h => hgk2 h.symm) hσ0 hσ1 h20 h21 hQσ hQ2 hsgn
    have hi : i1 = i2 := by
      by_contra hne; exact (Set.disjoint_left.mp (D.interiors_disjoint hne)) hZ1 hZ2
    subst hi
    rcases inner_vs_side (D.tile i1) hfk1.symm hfk2 hQ h20 h21 hQ2 with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · -- kk1 = f2, f1 = kk2:  B1 - A1 = A2 - B2 = - (B2 - A2)
      subst e1; subst e2
      exact hnp (crs_zero_of_pm hcw1 hcw2 hc1 hc2 (Or.inr (by rw [toV2_neg_sub])))
    · subst e1; subst e2
      exact hnp (crs_zero_of_pm hcw1 hcw2 hc1 hc2 (Or.inl rfl))
  · -- towards +d
    obtain ⟨i2, A2, B2, σ2, hS2, hQ2, h20, h21⟩ := hfwd
    obtain ⟨kk2, f2, g2, hk2, hf2, hfk2, hgk2, hgf2, hpar2, hleft2⟩ := id hS2
    subst hk2; subst hf2
    obtain ⟨c2, hc2, hcw2⟩ := hpar2.smul
    have hsgn : 0 < cross ((D.tile i1).pts f1 - (D.tile i1).pts kk1) ((D.tile i2).pts f2 - (D.tile i2).pts kk2) *
        cross ((D.tile i1).pts f1 - (D.tile i1).pts kk1) ((D.tile i1).pts g1 - (D.tile i1).pts kk1) := by
      have : cross ((D.tile i1).pts f1 - (D.tile i1).pts kk1) ((D.tile i2).pts f2 - (D.tile i2).pts kk2) = c1 * c2 * crs u1 d := by
        rw [← crs_toV2, hcw1, hcw2]; unfold crs; simp only; ring
      rw [this]; exact mul_pos (mul_pos (mul_pos hc1 hc2) hpos) hκ
    obtain ⟨Z', hZ1, hZ2⟩ := tiles_overlap (D.tile i1) (D.tile i2) (a1 := kk1) (b1 := f1) (g1 := g1) (a2 := kk2) (b2 := f2) (g2 := g2)
      hfk1.symm (fun h => hgk1 h.symm) (fun h => hgf1 h.symm) hfk2.symm (fun h => hgk2 h.symm) (fun h => hgf2 h.symm) hσ0 hσ1 h20 h21 hQσ hQ2 hsgn
    have hi : i1 = i2 := by
      by_contra hne; exact (Set.disjoint_left.mp (D.interiors_disjoint hne)) hZ1 hZ2
    subst hi
    rcases inner_vs_side (D.tile i1) hfk1.symm hfk2.symm hQ h20 h21 hQ2 with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · subst e1; subst e2
      exact hnp (crs_zero_of_pm hcw1 hcw2 hc1 hc2 (Or.inl rfl))
    · subst e1; subst e2
      exact hnp (crs_zero_of_pm hcw1 hcw2 hc1 hc2 (Or.inr (by rw [toV2_neg_sub])))

end Erdos634.Draft.LaczFormal.RG
