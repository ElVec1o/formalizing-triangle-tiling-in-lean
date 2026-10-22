import Erdos634.Draft.LaczFormalW2Bridge
import Erdos634.Draft.LaczFormalW2Main

/-!
# Rule W2, step 1 from `BaseTok` data: the tile `T' = (P₁, G₁, G₂)`

Erdős #634, band program, rule W2 (`PROOF_W2.md`).  Credit: AI assistant (item 3, band program), Beeson–Roșu, Beeson,
Laczkovich, Paliy.  UNAUDITED.

`w2_step1_tok` is `w2_step1` with hypotheses in the form of the token statements of `W2Rule` (two `cBA` tokens), via
`cBA_data`.  It also records the common vectors `e0 = P₁ − A_p`, `v = G₁ − A_p` and the relations
`P₂ = P₁ + e0`, `G₂ = P₁ + v`.
-/

namespace Erdos634.LaczJunction.Walk

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.LaczJunction Erdos634.LaczJunction.Grammar
open Erdos634.Draft.LaczFormal.Graph

variable {N : ℕ}

theorem w2_step1_tok {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ} {p q r : Fin 3}
    (S : BandSetup D e f α β γ p q r)
    (hori : 0 < cross (D.target.pts q - D.target.pts p) (D.target.pts r - D.target.pts p))
    {i1 i2 : Fin N} {P1 P2 G1 G2 : Plane}
    (t1 : BaseTok D p q (angOf α β γ) (lenOf (ta e f) (tb e f) (tc e f)) .c .B .A i1
      (D.target.pts p) P1 G1)
    (t2 : BaseTok D p q (angOf α β γ) (lenOf (ta e f) (tb e f) (tc e f)) .c .B .A i2 P1 P2 G2) :
    ∃ (i' : Fin N) (kP kG kH : Fin 3), kG ≠ kP ∧ kH ≠ kP ∧ kH ≠ kG ∧ i' ≠ i1 ∧ i' ≠ i2 ∧
      (D.tile i').pts kP = P1 ∧ (D.tile i').pts kG = G1 ∧ (D.tile i').pts kH = G2 ∧
      (D.tile i').localAngle P1 = γ := by
  obtain ⟨hαβ, hβγ, hαγ, hab, hbc, hac⟩ := BandSetup.distinct S
  set LC := D.target.pts p with hLC
  set RC := D.target.pts q with hRC
  set AP := D.target.pts r with hAP
  obtain ⟨kk0, fi0, g0, hfk0, hgk0, hgf0, hk0, hf0, hg0, hYX0, hZX0, hγ0, hb0, hZa0, hleft0⟩ := cBA_data S hori t1
  obtain ⟨kk1, fi1, g1, hfk1, hgk1, hgf1, hk1, hf1, hg1, hYX1, hZX1, hγ1, hb1, hZa1, hleft1⟩ := cBA_data S hori t2
  set v : Plane := ((ta e f : ℝ) / dist LC AP) • (AP - LC) with hvdef
  set e0 : Plane := ((tc e f : ℝ) / dist LC RC) • (RC - LC) with he0def
  have hG1 : G1 = LC + v := by rw [← hZX0]; abel
  have hP1 : P1 = LC + e0 := by rw [← hYX0]; abel
  have hG2 : G2 = P1 + v := by rw [← hZX1]; abel
  have hP2 : P2 = P1 + e0 := by rw [← hYX1]; abel
  have hapos : (0:ℝ) < ta e f := by exact_mod_cast a_pos e f S.he S.hef
  have hcpos : (0:ℝ) < tc e f := by
    have h1 := b_lt_c e f S.he S.hef
    have h2 := b_pos e f S.he S.hef
    exact_mod_cast (by omega : 0 < tc e f)
  have hL' : (ta e f : ℝ) < dist LC AP := S.haL
  have hLpos : 0 < dist LC AP := lt_trans hapos hL'
  have hB' : (tc e f : ℝ) < dist LC RC := S.hcB
  have hBpos : 0 < dist LC RC := lt_trans hcpos hB'
  have hP1seg : P1 ∈ openSegment ℝ LC RC := by
    rw [hP1, he0def]
    exact mem_open_param (div_pos hcpos hBpos) ((div_lt_one hBpos).mpr hB')
  have hG1seg : G1 ∈ openSegment ℝ LC AP := by
    rw [hG1, hvdef]
    exact mem_open_param (div_pos hapos hLpos) ((div_lt_one hLpos).mpr hL')
  have hPG : dist P1 G1 = (tb e f : ℝ) := hb0
  have hcrossw : 0 < cross (RC - LC) (AP - LC) := hori
  have hs1 : 0 < ((tc e f : ℝ) / dist LC RC) := div_pos hcpos hBpos
  -- orientation of T0 at P1
  have hv0' : TileVerts (D.tile i1) P1 G1 LC := by
    have hv := t1.verts
    have := hv.swap12.swap23
    exact this
  have hα0' : (D.tile i1).localAngle P1 = α := by
    have := t1.right_angle
    simpa [angOf] using this
  obtain ⟨i', k, hi'ne, hd', hends, hγ'⟩ := corner_far_edge D e f S.he S.hef S.hcop α β γ S.hγdef S.hrel
    S.hirr S.hα0 S.hβ0 S.hα' S.hβ' S.hγ' S.hsa S.hsb S.hsc S.hpq S.hpr S.hqr hP1seg hG1seg hPG i1 hv0'
    hα0'
  have hP1Z0 : P1 ≠ G1 := by
    intro h; rw [h, dist_self] at hPG
    have : (0:ℝ) < tb e f := by exact_mod_cast b_pos e f S.he S.hef
    linarith
  obtain ⟨j0, hj0, hV0, hedge0⟩ : ∃ j0 : Fin 3,
      (((D.tile i1).pts j0 = P1 ∧ (D.tile i1).pts (j0 + 1) = G1) ∨
        ((D.tile i1).pts j0 = G1 ∧ (D.tile i1).pts (j0 + 1) = P1)) ∧
      (D.tile i1).pts (j0 + 2) = LC ∧ (D.tile i1).edge j0 = segment ℝ P1 G1 := by
    rcases fin3_pair fi0 g0 kk0 hgf0 (Ne.symm hfk0) (Ne.symm hgk0) with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · refine ⟨fi0, Or.inl ⟨hf0, by rw [← h1]; exact hg0⟩, by rw [← h2]; exact hk0, ?_⟩
      show segment ℝ _ _ = _
      rw [hf0, ← h1, hg0]
    · refine ⟨g0, Or.inr ⟨hg0, ?_⟩, ?_, ?_⟩
      · have : g0 + 1 = fi0 := by rw [h1]; exact fin3_p2p1 fi0
        rw [this]; exact hf0
      · have : g0 + 2 = kk0 := by rw [h1, h2]; exact fin3_p2p2 fi0
        rw [this]; exact hk0
      · show segment ℝ _ _ = _
        have : g0 + 1 = fi0 := by rw [h1]; exact fin3_p2p1 fi0
        rw [this, hf0, hg0, segment_symm]
  have hκ : cross (G1 - P1) (LC - P1) = ((tc e f : ℝ) / dist LC RC) * (((ta e f : ℝ) / dist LC AP) * cross (RC - LC) (AP - LC)) := by
    rw [hG1, hP1, hvdef, he0def]
    simp only [cross, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  have hκ2 : cross (G1 - P1) (G2 - P1) = - (((tc e f : ℝ) / dist LC RC) * (((ta e f : ℝ) / dist LC AP) * cross (RC - LC) (AP - LC))) := by
    rw [hG1, hG2, hP1, hvdef, he0def]
    simp only [cross, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  have hκpos : 0 < ((tc e f : ℝ) / dist LC RC) * (((ta e f : ℝ) / dist LC AP) * cross (RC - LC) (AP - LC)) :=
    mul_pos hs1 (mul_pos (div_pos hapos hLpos) hcrossw)
  have hfs := far_side_of_shared_edge D.toDissection hP1Z0 i1 i' hi'ne j0 k hedge0 hV0 hj0
    (by
      rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · show segment ℝ _ _ = _
        rw [h1, h2]
      · show segment ℝ _ _ = _
        rw [h1, h2, segment_symm])
    rfl hends
  have hnoeq : i' ≠ i2 := by
    intro h
    have h1 : (D.tile i').localAngle P1 = β := by
      rw [h]
      have := t2.left_angle
      simpa [angOf] using this
    rw [hγ'] at h1
    exact hβγ h1.symm
  have key : ∀ kP kG kH : Fin 3, kG ≠ kP → kH ≠ kP → kH ≠ kG →
      (D.tile i').pts kP = P1 → (D.tile i').pts kG = G1 → (D.tile i').pts kH = (D.tile i').pts (k + 2) →
      (D.tile i').pts kH = G2 := by
    intro kP kG kH hGP hHP hHG hP' hG' hH'
    have hbPG : dist ((D.tile i').pts kP) ((D.tile i').pts kG) = sideOpp D.model 1 := by
      rw [hP', hG', hPG, S.hsb]
    have hγkP : (D.tile i').localAngle ((D.tile i').pts kP) = γ := by rw [hP']; exact hγ'
    have hm := tri_ms D i' kP kG kH hGP.symm hHP.symm hHG.symm
    have hang := angle_of_opp D α β γ S.hα' S.hβ' S.hγ' hab hbc hac i' kP kG kH hGP.symm hHP.symm hHG.symm
    have hcase : dist ((D.tile i').pts kP) ((D.tile i').pts kH) = sideOpp D.model 0 ∧
        dist ((D.tile i').pts kG) ((D.tile i').pts kH) = sideOpp D.model 2 := by
      rcases perm3 hm hab hbc hac with ⟨hx, hy, hz⟩ | ⟨hx, hy, hz⟩ | ⟨hx, hy, hz⟩ | ⟨hx, hy, hz⟩ |
          ⟨hx, hy, hz⟩ | ⟨hx, hy, hz⟩
      · exact absurd (hx.symm.trans hbPG) hbc.symm
      · exact absurd (hx.symm.trans hbPG) hbc.symm
      · exact absurd (hγkP.symm.trans (hang.1 hz)) hαγ.symm
      · exact ⟨hy, hz⟩
      · exact absurd (hx.symm.trans hbPG) hab
      · exact absurd (hx.symm.trans hbPG) hab
    obtain ⟨hHa, hHc⟩ := hcase
    have hZ1P : dist P1 G2 = sideOpp D.model 0 := by rw [hZa1, S.hsa]
    have hZ01 : dist G1 G2 = sideOpp D.model 2 := by
      have e1 : G1 - G2 = LC - P1 := by rw [hG1, hG2, hP1]; abel
      rw [dist_eq_norm, e1, ← dist_eq_norm]
      have := t1.length
      simpa [lenOf, S.hsc] using this
    have hHpt : (D.tile i').pts kH = (D.tile i').pts (k + 2) := hH'
    have hfs' := hfs
    rw [hκ] at hfs'
    have hneg : cross (G1 - P1) ((D.tile i').pts (k + 2) - P1) < 0 := by
      by_contra hh; push_neg at hh
      have := mul_nonneg hκpos.le hh
      linarith
    have e1 : dist P1 ((D.tile i').pts kH) = sideOpp D.model 0 := by rw [← hP']; exact hHa
    have e2 : dist G1 ((D.tile i').pts kH) = sideOpp D.model 2 := by rw [← hG']; exact hHc
    refine two_circles (A := P1) (B := G1) hP1Z0 ?_ ?_ ?_
    · rw [e1, hZ1P]
    · rw [e2, hZ01]
    · rw [hHpt, hκ2]
      exact mul_pos_of_neg_of_neg hneg (by linarith)
  have fin3a : k + 1 ≠ k ∧ k + 2 ≠ k ∧ k + 2 ≠ k + 1 := fin3_aux k
  rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨i', k, k + 1, k + 2, fin3a.1, fin3a.2.1, fin3a.2.2, hi'ne, hnoeq, h1, h2,
      key k (k + 1) (k + 2) fin3a.1 fin3a.2.1 fin3a.2.2 h1 h2 rfl, hγ'⟩
  · exact ⟨i', k + 1, k, k + 2, fin3a.1.symm, fin3a.2.2, fin3a.2.1, hi'ne, hnoeq, h2, h1,
      key (k + 1) k (k + 2) fin3a.1.symm fin3a.2.2 fin3a.2.1 h2 h1 rfl, hγ'⟩

#print axioms w2_step1_tok

end Erdos634.LaczJunction.Walk
