import Erdos634.Draft.LaczFormalW2Oriented

/-!
# Lemma `M(2)(b)`: after `cBA, cBA, cBA` the second down tile is the standard one

Erdős #634, band program (`PROOF_BAND.md` §3, the case `j = 2` of part (b)).  Credit: AI assistant (item 3, band program),
Beeson–Roșu, Beeson, Laczkovich, Paliy.  UNAUDITED.

`m2b_down_tile`: let the first three base tokens be `cBA, cBA, cBA` (tiles `i1, i2, i3`, junctions `P₁, P₂`, apexes `G₁, G₂, Z₃`) in a
counterclockwise band target with `e ≥ 2`, `f ≥ 3`, left leg `> 2a`.  Then a fourth tile `T₂` has the vertices `P₂` (angle
`γ`), `G₂` (angle `α`) and `Z₃` (angle `β`): the standard down tile between `A₂` and `A₃`; it lies on the far
side of the line `P₂G₂`.  (Part (b) of `M(2)`; part (a), the non-`cBA` third token, is `w2_oriented`.)
-/

namespace Erdos634.LaczJunction.Walk

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.LaczJunction Erdos634.LaczJunction.Grammar
open Erdos634.Draft.LaczFormal.Graph

variable {N : ℕ}

theorem m2b_down_tile {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ} {p q r : Fin 3}
    (S : BandSetup D e f α β γ p q r) (he2 : 2 ≤ e) (hf3 : 3 ≤ f)
    (hori : 0 < cross (D.target.pts q - D.target.pts p) (D.target.pts r - D.target.pts p))
    (hL2 : 2 * (ta e f : ℝ) < dist (D.target.pts p) (D.target.pts r))
    {i1 i2 i3 : Fin N}
    {P1 P2 P3 G1 G2 Z3 : Plane}
    (t1 : BaseTok D p q (angOf α β γ) (lenOf (ta e f) (tb e f) (tc e f)) .c .B .A i1
      (D.target.pts p) P1 G1)
    (t2 : BaseTok D p q (angOf α β γ) (lenOf (ta e f) (tb e f) (tc e f)) .c .B .A i2 P1 P2 G2)
    (t3 : BaseTok D p q (angOf α β γ) (lenOf (ta e f) (tb e f) (tc e f)) .c .B .A i3 P2 P3 Z3) :
    ∃ (iT : Fin N) (kP kG kK : Fin 3), kP ≠ kG ∧ kP ≠ kK ∧ kG ≠ kK ∧ iT ≠ i2 ∧ iT ≠ i3 ∧
      (D.tile iT).pts kP = P2 ∧ (D.tile iT).pts kG = G2 ∧ (D.tile iT).pts kK = Z3 ∧
      (D.tile iT).localAngle P2 = γ ∧ (D.tile iT).localAngle G2 = α ∧ (D.tile iT).localAngle Z3 = β := by
  classical
  obtain ⟨hαβ, hβγ, hαγ, hab, hbc, hac⟩ := BandSetup.distinct S
  set LC := D.target.pts p with hLC
  set RC := D.target.pts q with hRC
  set AP := D.target.pts r with hAP
  have hne : LC ≠ RC := by
    intro h
    have : cross (RC - LC) (AP - LC) = 0 := by rw [← h]; simp [cross]
    linarith
  obtain ⟨e0, v, hP1, hP2, hG1, hG2, hce, hva, hub, hcr, ⟨μ, hμ, hAPv⟩, ⟨lam, hlam, hRCe⟩⟩ :=
    w2_vectors S hori t1 t2
  have hP1 : P1 = LC + e0 := hP1
  have hP2ne : P2 ≠ LC := by
    intro h
    have : e0 + e0 = 0 := by
      have h1 : P2 = LC + (e0 + e0) := by rw [hP2, hP1]; abel
      rw [h1] at h
      simpa using h
    have : cross e0 v = 0 := by
      have : e0 = 0 := by
        have h2 : (2:ℝ) • e0 = 0 := by rw [two_smul]; exact this
        simpa using h2
      rw [this]; simp [cross]
    linarith
  have hP2seg : P2 ∈ openSegment ℝ LC RC := basetok_left_open hne t3 hP2ne
  -- the apex of the third token
  obtain ⟨kk3, fi3, g3, hfk3, hgk3, hgf3, hk3, hf3', hg3, hYX3, hZX3, hγ3, hb3, hZa3, hleft3⟩ := cBA_data S hori t3
  obtain ⟨kk0, fi0, g0, hfk0, hgk0, hgf0, hk0, hf0, hg0, hYX0, hZX0, hγ0, hb0, hZa0, hleft0⟩ := cBA_data S hori t1
  have hZ3 : Z3 = P2 + v := by
    have h1 : Z3 - P2 = G1 - LC := by rw [hZX3, hZX0]
    have h2 : G1 = LC + v := hG1
    rw [h2] at h1
    have : Z3 = P2 + (LC + v - LC) := by rw [← h1]; abel
    rw [this]; abel
  have hu : G2 - P2 = v - e0 := by rw [hG2, hP2]; abel
  have hdPG : dist P2 G2 = (tb e f : ℝ) := by rw [dist_comm, dist_eq_norm, hu, hub]
  have hα2 : (D.tile i2).localAngle P2 = α := by simpa [angOf] using t2.right_angle
  have hβ3 : (D.tile i3).localAngle P2 = β := by simpa [angOf] using t3.left_angle
  refine w2_core S he2 hf3 hori hL2 t1 t2 hP2seg ?_
  intro iW kP kG hkne hkP hkG hWP hWG hne2 hside
  have F3d : ∀ a b : Fin 3, a ≠ b → ∃ c : Fin 3, c ≠ a ∧ c ≠ b := by decide
  obtain ⟨kK, hKP, hKG⟩ := F3d kP kG hkne
  have hdPG' : dist ((D.tile iW).pts kP) ((D.tile iW).pts kG) = sideOpp D.model 1 := by
    rw [hkP, hkG, hdPG, S.hsb]
  have hWP' : (D.tile iW).localAngle ((D.tile iW).pts kP) = γ := by rw [hkP]; exact hWP
  have hWG' : (D.tile iW).localAngle ((D.tile iW).pts kG) = α := by rw [hkG]; exact hWG
  have hadjG := tile_adj_G S iW kP kG kK hkne hKP.symm hKG.symm hWP'
  have hdPK : dist ((D.tile iW).pts kP) ((D.tile iW).pts kK) = sideOpp D.model 0 := by
    rcases hadjG with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact h2
    · exact absurd (h1.symm.trans hdPG') hab
  have hadjA := tile_adj_A S iW kG kP kK hkne.symm hKG.symm hKP.symm hWG'
  have hdGK : dist ((D.tile iW).pts kG) ((D.tile iW).pts kK) = sideOpp D.model 2 := by
    rcases hadjA with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact h2
    · rw [dist_comm] at h1; exact absurd (h1.symm.trans hdPG') hbc.symm
  -- the third vertex is Z3 (two circles)
  have hZ3P : Z3 - P2 = v := by rw [hZ3]; abel
  have hZ3G : Z3 - G2 = e0 := by rw [hZ3, hG2, hP2]; abel
  have hPG : P2 ≠ G2 := by
    intro h; rw [h, dist_self] at hdPG
    have : (0:ℝ) < tb e f := by exact_mod_cast b_pos e f S.he S.hef
    linarith
  have hKcr : cross (G2 - P2) ((D.tile iW).pts kK - P2) < 0 := by
    have h0 := hside kK
    have h2 := tile_cross_ne (D.tile iW) kP kG kK hkne hKP.symm hKG.symm
    rw [hkP, hkG] at h2
    exact lt_of_le_of_ne h0 h2
  have hZcr : cross (G2 - P2) (Z3 - P2) < 0 := by
    rw [hu, hZ3P]
    have : cross (v - e0) v = - cross e0 v := by
      simp only [cross, PiLp.sub_apply]; ring
    rw [this]; linarith
  have hKZ : (D.tile iW).pts kK = Z3 := by
    refine two_circles hPG ?_ ?_ (mul_pos_of_neg_of_neg hKcr hZcr)
    · have e1 : dist P2 ((D.tile iW).pts kK) = (ta e f : ℝ) := by
        rw [← hkP, hdPK, S.hsa]
      rw [e1, dist_comm, dist_eq_norm, hZ3P, hva]
    · have e1 : dist G2 ((D.tile iW).pts kK) = (tc e f : ℝ) := by
        rw [← hkG, hdGK, S.hsc]
      rw [e1, dist_comm G2 Z3, dist_eq_norm, hZ3G, hce]
  have hZβ : (D.tile iW).localAngle Z3 = β := by
    have := (angle_of_opp D α β γ S.hα' S.hβ' S.hγ' hab hbc hac iW kK kP kG hKP hKG hkne).2.1 hdPG'
    rw [hKZ] at this; exact this
  refine ⟨iW, kP, kG, kK, hkne, hKP.symm, hKG.symm, hne2, ?_, hkP, hkG, hKZ, hWP, hWG, hZβ⟩
  intro h
  rw [h] at hWP
  exact hβγ (hβ3.symm.trans hWP)

#print axioms m2b_down_tile

end Erdos634.LaczJunction.Walk
