import Erdos634.Draft.LaczFormalW2Corner
import Erdos634.Draft.LaczFormalW2Step1

/-!
# Rule W2, step 1: `T' = (P₁, G₁, G₂)` on the base walk (interface lemma I1)

Erdős #634, base-`β` band.  Credit: AI assistant (item 3, band program; `PROOF_W2.md` Step 1), Beeson–Roșu, Beeson,
Laczkovich, Paliy.  UNAUDITED.  Axiom-clean; no `sorry`.

`w2_step1`: if the first two tokens of the base walk are `cBA, cBA` (tiles `T₀, T₁`, apexes `G₁, G₂`, junction `P₁`),
the far tile `T'` of the chord `P₁G₁` has the vertices `P₁` (`γ`), `G₁`, `G₂`.  No fan machinery: coordinates
(`apex_dir`, `two_circles`, `far_side_of_shared_edge`).
-/

namespace Erdos634.LaczJunction.Walk

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.LaczJunction Erdos634.LaczJunction.Grammar
open Erdos634.Draft.LaczFormal.Graph

variable {N : ℕ}

theorem fin3_aux (k : Fin 3) : k + 1 ≠ k ∧ k + 2 ≠ k ∧ k + 2 ≠ k + 1 := by
  revert k; decide

theorem mem_open_param {P Q : Plane} {s : ℝ} (h0 : 0 < s) (h1 : s < 1) :
    P + s • (Q - P) ∈ openSegment ℝ P Q := by
  refine ⟨1 - s, s, by linarith, h0, by ring, ?_⟩
  module

theorem w2_step1 {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ} {p q r : Fin 3}
    (S : BandSetup D e f α β γ p q r)
    (hori : 0 < crs (toV2 (D.target.pts q - D.target.pts p)) (toV2 (D.target.pts r - D.target.pts p)))
    {L : List (Fin N × Plane × Plane)}
    (hL : WalkT D.toDissection (toV2 (D.target.pts q - D.target.pts p)) (D.target.pts p)
      (D.target.pts q) L)
    (hpar : ∀ x ∈ L, ∃ s t : ℝ, 0 ≤ s ∧ s < t ∧ t ≤ 1 ∧
        x.2.1 = D.target.pts p + s • (D.target.pts q - D.target.pts p) ∧
        x.2.2 = D.target.pts p + t • (D.target.pts q - D.target.pts p))
    (hstep : ∀ x ∈ L, StepData D e f α β γ p q x)
    {x0 x1 : Fin N × Plane × Plane} {L' : List (Fin N × Plane × Plane)} (hLeq : L = x0 :: x1 :: L')
    (he0 : elemTok D α β x0 = Tok.cBA) (he1 : elemTok D α β x1 = Tok.cBA) :
    ∃ (kk0 fi0 g0 kk1 fi1 g1 : Fin 3) (i' : Fin N) (kP kG kH : Fin 3),
      fi0 ≠ kk0 ∧ g0 ≠ kk0 ∧ g0 ≠ fi0 ∧ (D.tile x0.1).pts kk0 = x0.2.1 ∧ (D.tile x0.1).pts fi0 = x0.2.2 ∧
      fi1 ≠ kk1 ∧ g1 ≠ kk1 ∧ g1 ≠ fi1 ∧ (D.tile x1.1).pts kk1 = x1.2.1 ∧ (D.tile x1.1).pts fi1 = x1.2.2 ∧
      i' ≠ x0.1 ∧ i' ≠ x1.1 ∧ kG ≠ kP ∧ kH ≠ kP ∧ kH ≠ kG ∧
      (D.tile i').pts kP = x0.2.2 ∧ (D.tile i').pts kG = (D.tile x0.1).pts g0 ∧
      (D.tile i').pts kH = (D.tile x1.1).pts g1 ∧ (D.tile i').localAngle x0.2.2 = γ := by
  obtain ⟨hαβ, hβγ, hαγ, hab, hbc, hac⟩ := BandSetup.distinct S
  have hne : D.target.pts p ≠ D.target.pts q := by
    intro h
    have : crs (toV2 (D.target.pts q - D.target.pts p)) (toV2 (D.target.pts r - D.target.pts p)) = 0 := by
      rw [← h]; simp [crs, toV2]
    linarith
  have hw : D.target.pts q - D.target.pts p ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  have hx0 : x0.2.1 = D.target.pts p := walk_first hL x0 (x1 :: L') hLeq
  have hadj : x0.2.2 = x1.2.1 := walk_adjacent hL [] L' x0 x1 (by simpa using hLeq)
  have sd0 := hstep x0 (by rw [hLeq]; simp)
  have sd1 := hstep x1 (by rw [hLeq]; simp)
  have hp0 := hpar x0 (by rw [hLeq]; simp)
  have hp1 := hpar x1 (by rw [hLeq]; simp)
  obtain ⟨kk0, fi0, g0, hfk0, hgk0, hgf0, hk0, hf0, hleft0, hbt0⟩ := sd0
  obtain ⟨kk1, fi1, g1, hfk1, hgk1, hgf1, hk1, hf1, hleft1, hbt1⟩ := sd1
  have hc0 : dist x0.2.1 x0.2.2 = sideOpp D.model 2 :=
    tok_len_c S (t := elemTok D α β x0) hbt0 (by rw [he0]; rfl)
  have hc1 : dist x1.2.1 x1.2.2 = sideOpp D.model 2 :=
    tok_len_c S (t := elemTok D α β x1) hbt1 (by rw [he1]; rfl)
  have hang0 : (D.tile x0.1).localAngle ((D.tile x0.1).pts kk0) = β := by
    have := corner_tile_beta S p (corner_cyc D.target p q r S.hpq S.hpr S.hqr S.cornerP) x0.1 kk0
      (hk0.trans hx0)
    rwa [hk0, hx0]
  have hang1 : (D.tile x1.1).localAngle ((D.tile x1.1).pts kk1) = β := by
    have := hbt1.left_angle
    rw [he1] at this
    simp only [Tok.left, angOf] at this
    rw [hk1]; exact this
  have hα0' : (D.tile x0.1).localAngle x0.2.2 = α := by
    have := hbt0.right_angle
    rw [he0] at this
    simpa [Tok.right, angOf] using this
  have hv0 := apex_dir S hori hp0 kk0 fi0 g0 hfk0 hgk0 hgf0 hk0 hf0 hleft0 hang0 hc0
  have hv1 := apex_dir S hori hp1 kk1 fi1 g1 hfk1 hgk1 hgf1 hk1 hf1 hleft1 hang1 hc1
  set P := D.target.pts p with hP
  set Q := D.target.pts q with hQ
  set R := D.target.pts r with hR
  set Z0 := (D.tile x0.1).pts g0 with hZ0
  set Z1 := (D.tile x1.1).pts g1 with hZ1
  set v : Plane := ((ta e f : ℝ) / dist P R) • (R - P) with hvdef
  set P1 := x0.2.2 with hP1
  have hG1 : Z0 = P + v := by rw [← hx0]; rw [← hv0]; abel
  have hG2 : Z1 = P1 + v := by rw [hadj]; rw [← hv1]; abel
  -- parameters
  obtain ⟨s0, t0, h00, h0t, ht01, hs0, ht0⟩ := hp0
  obtain ⟨s1, t1, h10, h1t, ht11, hs1, ht1⟩ := hp1
  have hs0z : s0 = 0 := by
    have : P + s0 • (Q - P) = P + (0:ℝ) • (Q - P) := by rw [← hs0, hx0]; simp
    exact smul_injective_of_ne hw (add_left_cancel this)
  subst hs0z
  have hs1t0 : s1 = t0 := by
    have : P + s1 • (Q - P) = P + t0 • (Q - P) := by rw [← hs1, ← hadj, ht0]
    exact smul_injective_of_ne hw (add_left_cancel this)
  subst hs1t0
  have hP1seg : P1 ∈ openSegment ℝ P Q := by
    rw [ht0]; exact mem_open_param (by linarith) (by linarith)
  have hL' : (ta e f : ℝ) < dist P R := by exact_mod_cast S.haL
  have hapos : (0:ℝ) < ta e f := by exact_mod_cast a_pos e f S.he S.hef
  have hLpos : 0 < dist P R := lt_trans hapos hL'
  have hG1seg : Z0 ∈ openSegment ℝ P R := by
    rw [hG1, hvdef]
    exact mem_open_param (div_pos hapos hLpos) ((div_lt_one hLpos).mpr hL')
  have hc0' : dist ((D.tile x0.1).pts kk0) ((D.tile x0.1).pts fi0) = sideOpp D.model 2 := by
    rw [hk0, hf0]; exact hc0
  have hZa0 : dist ((D.tile x0.1).pts kk0) Z0 = sideOpp D.model 0 :=
    beta_corner_other_edge S x0.1 kk0 fi0 g0 hfk0 hgk0 hgf0 hang0 hc0'
  have hc1' : dist ((D.tile x1.1).pts kk1) ((D.tile x1.1).pts fi1) = sideOpp D.model 2 := by
    rw [hk1, hf1]; exact hc1
  have hZa1 : dist ((D.tile x1.1).pts kk1) Z1 = sideOpp D.model 0 :=
    beta_corner_other_edge S x1.1 kk1 fi1 g1 hfk1 hgk1 hgf1 hang1 hc1'
  -- |P1 G1| = b
  have hb0 : dist ((D.tile x0.1).pts fi0) Z0 = sideOpp D.model 1 := by
    have hm := tri_ms D x0.1 kk0 fi0 g0 hfk0.symm hgk0.symm hgf0.symm
    rcases perm3 hm hab hbc hac with ⟨hx, hy, hz⟩ | ⟨hx, hy, hz⟩ | ⟨hx, hy, hz⟩ | ⟨hx, hy, hz⟩ |
        ⟨hx, hy, hz⟩ | ⟨hx, hy, hz⟩
    · exact absurd (hy.symm.trans hZa0) hab.symm
    · exact hz
    · exact absurd (hx.symm.trans hc0') hbc
    · exact absurd (hx.symm.trans hc0') hbc
    · exact absurd (hx.symm.trans hc0') hac
    · exact absurd (hx.symm.trans hc0') hac
  have hPG : dist P1 Z0 = (tb e f : ℝ) := by
    rw [← hf0, hb0, S.hsb]
  have hv0' : TileVerts (D.tile x0.1) P1 Z0 P := by
    have := hbt0.verts.swap12.swap23
    rw [hx0] at this
    exact this
  obtain ⟨i', k, hi'ne, hd', hends, hγ'⟩ := corner_far_edge D e f S.he S.hef S.hcop α β γ S.hγdef S.hrel
    S.hirr S.hα0 S.hβ0 S.hα' S.hβ' S.hγ' S.hsa S.hsb S.hsc S.hpq S.hpr S.hqr hP1seg hG1seg hPG x0.1 hv0'
    hα0'
  -- positions: t = P1 - P
  have hP1eq : P1 = P + s1 • (Q - P) := ht0
  have hcrossw : 0 < cross (Q - P) (R - P) := by rwa [← crs_toV2]
  have hκ : cross (Z0 - P1) (P - P1) = s1 * (((ta e f : ℝ) / dist P R) * cross (Q - P) (R - P)) := by
    rw [hG1, hP1eq, hvdef]
    simp only [cross, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  have hκ2 : cross (Z0 - P1) (Z1 - P1) = - (s1 * (((ta e f : ℝ) / dist P R) * cross (Q - P) (R - P))) := by
    rw [hG1, hG2, hP1eq, hvdef]
    simp only [cross, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  have hκpos : 0 < s1 * (((ta e f : ℝ) / dist P R) * cross (Q - P) (R - P)) :=
    mul_pos (by linarith) (mul_pos (div_pos hapos hLpos) hcrossw)
  -- the edge of T0 and the far tile
  have hP1Z0 : P1 ≠ Z0 := by
    intro h; rw [h, dist_self] at hPG
    have : (0:ℝ) < tb e f := by exact_mod_cast b_pos e f S.he S.hef
    linarith
  obtain ⟨j0, hj0, hV0, hedge0⟩ : ∃ j0 : Fin 3,
      (((D.tile x0.1).pts j0 = P1 ∧ (D.tile x0.1).pts (j0 + 1) = Z0) ∨
        ((D.tile x0.1).pts j0 = Z0 ∧ (D.tile x0.1).pts (j0 + 1) = P1)) ∧
      (D.tile x0.1).pts (j0 + 2) = P ∧ (D.tile x0.1).edge j0 = segment ℝ P1 Z0 := by
    rcases fin3_pair fi0 g0 kk0 hgf0 (Ne.symm hfk0) (Ne.symm hgk0) with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · refine ⟨fi0, Or.inl ⟨hf0, by rw [← h1]⟩, by rw [← h2]; exact hk0.trans hx0, ?_⟩
      show segment ℝ _ _ = _
      rw [hf0, ← h1]
    · refine ⟨g0, Or.inr ⟨rfl, ?_⟩, ?_, ?_⟩
      · have : g0 + 1 = fi0 := by rw [h1]; exact fin3_p2p1 fi0
        rw [this]; exact hf0
      · have : g0 + 2 = kk0 := by rw [h1, h2]; exact fin3_p2p2 fi0
        rw [this]; exact hk0.trans hx0
      · show segment ℝ _ _ = _
        have : g0 + 1 = fi0 := by rw [h1]; exact fin3_p2p1 fi0
        rw [this, hf0, segment_symm]
  have hfs := far_side_of_shared_edge D.toDissection hP1Z0 x0.1 i' hi'ne j0 k hedge0 hV0 hj0
    (by
      rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · show segment ℝ _ _ = _
        rw [h1, h2]
      · show segment ℝ _ _ = _
        rw [h1, h2, segment_symm])
    rfl hends
  -- T' has the vertices P1 (gamma), Z0, H; show H = Z1
  have hnoeq : i' ≠ x1.1 := by
    intro h
    have h1 : (D.tile i').localAngle P1 = β := by
      rw [h]
      have : (D.tile x1.1).pts kk1 = P1 := hk1.trans hadj.symm
      rw [← this]; exact hang1
    rw [hγ'] at h1
    exact hβγ h1.symm
  have key : ∀ kP kG kH : Fin 3, kG ≠ kP → kH ≠ kP → kH ≠ kG →
      (D.tile i').pts kP = P1 → (D.tile i').pts kG = Z0 → (D.tile i').pts kH = (D.tile i').pts (k + 2) →
      (D.tile i').pts kH = Z1 := by
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
      · -- x = b, y = c, z = a : the angle at kP would be alpha
        exact absurd (hγkP.symm.trans (hang.1 hz)) hαγ.symm
      · exact ⟨hy, hz⟩
      · exact absurd (hx.symm.trans hbPG) hab
      · exact absurd (hx.symm.trans hbPG) hab
    obtain ⟨hHa, hHc⟩ := hcase
    have hZ1P : dist P1 Z1 = sideOpp D.model 0 := by
      have : (D.tile x1.1).pts kk1 = P1 := hk1.trans hadj.symm
      rw [← this]; exact hZa1
    have hZ01 : dist Z0 Z1 = sideOpp D.model 2 := by
      have e1 : Z0 - Z1 = P - P1 := by rw [hG1, hG2]; abel
      rw [dist_eq_norm, e1, ← dist_eq_norm, ← hx0]; exact hc0
    have hHpt : (D.tile i').pts kH = (D.tile i').pts (k + 2) := hH'
    have hfs' := hfs
    rw [hκ] at hfs'
    have hneg : cross (Z0 - P1) ((D.tile i').pts (k + 2) - P1) < 0 := by
      by_contra hh; push_neg at hh
      have := mul_nonneg hκpos.le hh
      linarith
    have e1 : dist P1 ((D.tile i').pts kH) = sideOpp D.model 0 := by rw [← hP']; exact hHa
    have e2 : dist Z0 ((D.tile i').pts kH) = sideOpp D.model 2 := by rw [← hG']; exact hHc
    refine two_circles (A := P1) (B := Z0) hP1Z0 ?_ ?_ ?_
    · rw [e1, hZ1P]
    · rw [e2, hZ01]
    · rw [hHpt, hκ2]
      exact mul_pos_of_neg_of_neg hneg (by linarith)
  have fin3a : k + 1 ≠ k ∧ k + 2 ≠ k ∧ k + 2 ≠ k + 1 := fin3_aux k
  rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨kk0, fi0, g0, kk1, fi1, g1, i', k, k + 1, k + 2, hfk0, hgk0, hgf0, hk0, hf0, hfk1, hgk1, hgf1,
      hk1, hf1, hi'ne, hnoeq, fin3a.1, fin3a.2.1, fin3a.2.2, h1, h2,
      key k (k + 1) (k + 2) fin3a.1 fin3a.2.1 fin3a.2.2 h1 h2 rfl, hγ'⟩
  · exact ⟨kk0, fi0, g0, kk1, fi1, g1, i', k + 1, k, k + 2, hfk0, hgk0, hgf0, hk0, hf0, hfk1, hgk1, hgf1,
      hk1, hf1, hi'ne, hnoeq, fin3a.1.symm, fin3a.2.2, fin3a.2.1, h2, h1,
      key (k + 1) k (k + 2) fin3a.1.symm fin3a.2.2 fin3a.2.1 h2 h1 rfl, hγ'⟩

#print axioms w2_step1

end Erdos634.LaczJunction.Walk
