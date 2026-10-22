import Erdos634.Draft.LaczFormalW2G1
import Erdos634.Draft.LaczFormalWalkRules

/-!
# Rule W2: from `BaseTok` data to coordinates

Erdős #634, band program, rule W2.  Credit: AI assistant (item 3, band program), Beeson–Roșu, Beeson, Laczkovich,
Paliy.  UNAUDITED.

`cBA_data`: a base token `c B A` (a tile `i` with vertices `X, Y, Z`, `X, Y` on the base, `c` on the base, `β` at `X`)
in an oriented target has `Y − X = (c/|A_pA_q|)(A_q − A_p)`, `Z − X = (a/|A_pA_r|)(A_r − A_p)`, `|YZ| = b`,
angle `γ` at `Z`, and `Z` strictly to the left of the base.
-/

namespace Erdos634.LaczJunction.Walk

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.LaczJunction Erdos634.LaczJunction.Grammar
open Erdos634.Draft.LaczFormal.Graph

variable {N : ℕ}

theorem seg_param_of_mem {A B X : Plane} (h : X ∈ segment ℝ A B) :
    ∃ s : ℝ, 0 ≤ s ∧ s ≤ 1 ∧ X = A + s • (B - A) := by
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := h
  refine ⟨b, hb, by linarith, ?_⟩
  have : a = 1 - b := by linarith
  rw [this]; module

theorem dist_param_left (A w : Plane) {s : ℝ} (hs : 0 ≤ s) : dist A (A + s • w) = s * ‖w‖ := by
  rw [dist_comm, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hs]

theorem basetok_hleft {D : CongruentDissection N} {p q r : Fin 3} (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (hori : 0 < cross (D.target.pts q - D.target.pts p) (D.target.pts r - D.target.pts p))
    {ang : Corner → ℝ} {len : Side → ℝ} {x : Side} {l rr : Corner} {i : Fin N} {X Y Z : Plane}
    (h : BaseTok D p q ang len x l rr i X Y Z) :
    0 < cross (D.target.pts q - D.target.pts p) (Z - X) := by
  set LC := D.target.pts p with hLC
  set RC := D.target.pts q with hRC
  obtain ⟨sx, hsx0, hsx1, hX⟩ := seg_param_of_mem h.left_mem
  obtain ⟨sy, hsy0, hsy1, hY⟩ := seg_param_of_mem h.right_mem
  have hZmem : Z ∈ (D.tile i).carrier := by
    obtain ⟨j, hj | hj⟩ := h.verts
    · rw [← hj.2.2]; exact subset_convexHull ℝ _ (Set.mem_range_self _)
    · rw [← hj.2.1]; exact subset_convexHull ℝ _ (Set.mem_range_self _)
  have hZt : Z ∈ D.target.carrier := Erdos634.BaseSelection.tile_subset_target D.toDissection i hZmem
  have hle := target_left hpq hpr hqr hori Z hZt
  have e1 : cross (RC - LC) (Z - X) = cross (RC - LC) (Z - LC) := by
    have : Z - X = (Z - LC) - sx • (RC - LC) := by rw [hX]; module
    rw [this, cross_sub_right, cross_smul_right, Erdos634.Geometry.cross_self]; ring
  have hne : cross (RC - LC) (Z - X) ≠ 0 := by
    intro h0
    obtain ⟨j, hj | hj⟩ := h.verts
    · have hd := (D.tile i).det_cyclic j
      rw [hj.1, hj.2.1, hj.2.2] at hd
      have : Y - X = (sy - sx) • (RC - LC) := by rw [hX, hY]; module
      rw [this, cross_smul_left, h0, mul_zero] at hd
      exact (D.tile i).det_ne_zero hd.symm
    · have hd := (D.tile i).det_cyclic j
      rw [hj.1, hj.2.1, hj.2.2] at hd
      have : Y - X = (sy - sx) • (RC - LC) := by rw [hX, hY]; module
      rw [this, cross_smul_right, cross_swap (Z - X) (RC - LC), h0] at hd
      simp at hd
      exact (D.tile i).det_ne_zero hd.symm
  rw [e1] at hne ⊢
  exact lt_of_le_of_ne hle (Ne.symm hne)


theorem fin3_aux' (k : Fin 3) : k + 1 ≠ k ∧ k + 2 ≠ k ∧ k + 2 ≠ k + 1 := by
  revert k; decide

/-- **Coordinates of a `cBA` token.** -/
theorem cBA_data {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ} {p q r : Fin 3}
    (S : BandSetup D e f α β γ p q r)
    (hori : 0 < cross (D.target.pts q - D.target.pts p) (D.target.pts r - D.target.pts p))
    {i : Fin N} {X Y Z : Plane}
    (h : BaseTok D p q (angOf α β γ) (lenOf (ta e f) (tb e f) (tc e f)) .c .B .A i X Y Z) :
    ∃ kk fi g : Fin 3, fi ≠ kk ∧ g ≠ kk ∧ g ≠ fi ∧ (D.tile i).pts kk = X ∧ (D.tile i).pts fi = Y ∧
      (D.tile i).pts g = Z ∧
      Y - X = ((tc e f : ℝ) / dist (D.target.pts p) (D.target.pts q)) • (D.target.pts q - D.target.pts p) ∧
      Z - X = ((ta e f : ℝ) / dist (D.target.pts p) (D.target.pts r)) • (D.target.pts r - D.target.pts p) ∧
      (D.tile i).localAngle Z = γ ∧ dist Y Z = (tb e f : ℝ) ∧ dist X Z = (ta e f : ℝ) ∧
      0 < cross (D.target.pts q - D.target.pts p) (Z - X) := by
  obtain ⟨hαβ, hβγ, hαγ, hab, hbc, hac⟩ := BandSetup.distinct S
  set LC := D.target.pts p with hLC
  set RC := D.target.pts q with hRC
  set AP := D.target.pts r with hAP
  have hleft := basetok_hleft S.hpq S.hpr S.hqr hori h
  have hori' : 0 < crs (toV2 (RC - LC)) (toV2 (AP - LC)) := by rw [crs_toV2]; exact hori
  obtain ⟨kk, fi, g, hfk, hgk, hgf, hk, hf, hg⟩ : ∃ kk fi g : Fin 3, fi ≠ kk ∧ g ≠ kk ∧ g ≠ fi ∧
      (D.tile i).pts kk = X ∧ (D.tile i).pts fi = Y ∧ (D.tile i).pts g = Z := by
    obtain ⟨j, hj | hj⟩ := h.verts
    · obtain ⟨n1, n2, n3⟩ := fin3_aux' j
      exact ⟨j, j + 1, j + 2, n1, n2, n3, hj.1, hj.2.1, hj.2.2⟩
    · obtain ⟨n1, n2, n3⟩ := fin3_aux' j
      exact ⟨j, j + 2, j + 1, n2, n1, n3.symm, hj.1, hj.2.2, hj.2.1⟩
  have hc : dist X Y = sideOpp D.model 2 := by
    have := h.length; simpa [lenOf, S.hsc] using this
  have hc' : dist ((D.tile i).pts kk) ((D.tile i).pts fi) = sideOpp D.model 2 := by rw [hk, hf]; exact hc
  have hang : (D.tile i).localAngle ((D.tile i).pts kk) = β := by
    rw [hk]; simpa [angOf] using h.left_angle
  have hne : LC ≠ RC := by
    intro h0
    have : cross (RC - LC) (AP - LC) = 0 := by rw [← h0]; simp [cross]
    linarith
  have hw : RC - LC ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  obtain ⟨sx, hsx0, hsx1, hX⟩ := seg_param_of_mem h.left_mem
  obtain ⟨sy, hsy0, hsy1, hY⟩ := seg_param_of_mem h.right_mem
  have hlt : sx < sy := by
    have := h.order
    rw [hX, hY, dist_param_left _ _ hsx0, dist_param_left _ _ hsy0] at this
    have hwn : 0 < ‖RC - LC‖ := norm_pos_iff.mpr hw
    by_contra hh; push_neg at hh
    nlinarith
  have hpar : ∃ s t : ℝ, 0 ≤ s ∧ s < t ∧ t ≤ 1 ∧ (i, X, Y).2.1 = LC + s • (RC - LC) ∧
      (i, X, Y).2.2 = LC + t • (RC - LC) := ⟨sx, sy, hsx0, hlt, hsy1, hX, hY⟩
  have hleft' : 0 < crs (toV2 (RC - LC)) (toV2 ((D.tile (i, X, Y).1).pts g - (i, X, Y).2.1)) := by
    rw [crs_toV2]; simpa [hg] using hleft
  have hvec := apex_dir S hori' (x := (i, X, Y)) hpar kk fi g hfk hgk hgf (by simpa using hk) (by simpa using hf)
    hleft' (by simpa [hk] using hang) (by simpa using hc)
  simp only [hg] at hvec
  refine ⟨kk, fi, g, hfk, hgk, hgf, hk, hf, hg, ?_, hvec, ?_, ?_, ?_, hleft⟩
  · -- Y - X
    have hdist : dist X Y = (sy - sx) * ‖RC - LC‖ := by
      have : Y = X + (sy - sx) • (RC - LC) := by rw [hX, hY]; module
      rw [this, dist_comm, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg (by linarith)]
    have hB : dist LC RC = ‖RC - LC‖ := by rw [dist_comm, dist_eq_norm]
    rw [hB]
    have hwn : 0 < ‖RC - LC‖ := norm_pos_iff.mpr hw
    have hcs : (tc e f : ℝ) = (sy - sx) * ‖RC - LC‖ := by rw [← S.hsc, ← hc, hdist]
    have : Y - X = (sy - sx) • (RC - LC) := by rw [hX, hY]; module
    rw [this]; congr 1; field_simp; linarith
  · -- angle at Z
    have := (angle_of_opp D α β γ S.hα' S.hβ' S.hγ' hab hbc hac i g kk fi hgk hgf hfk.symm).2.2 hc'
    rw [hg] at this; exact this
  · -- |YZ| = b
    have hZa : dist ((D.tile i).pts kk) ((D.tile i).pts g) = sideOpp D.model 0 :=
      beta_corner_other_edge S i kk fi g hfk hgk hgf hang hc'
    have hm := tri_ms D i kk fi g hfk.symm hgk.symm hgf.symm
    have hb0 : dist ((D.tile i).pts fi) ((D.tile i).pts g) = sideOpp D.model 1 := by
      rcases perm3 hm hab hbc hac with ⟨hx, hy, hz⟩ | ⟨hx, hy, hz⟩ | ⟨hx, hy, hz⟩ | ⟨hx, hy, hz⟩ |
          ⟨hx, hy, hz⟩ | ⟨hx, hy, hz⟩
      · exact absurd (hy.symm.trans hZa) hab.symm
      · exact hz
      · exact absurd (hx.symm.trans hc') hbc
      · exact absurd (hx.symm.trans hc') hbc
      · exact absurd (hx.symm.trans hc') hac
      · exact absurd (hx.symm.trans hc') hac
    rw [hf, hg, S.hsb] at hb0; exact hb0
  · have hZa : dist ((D.tile i).pts kk) ((D.tile i).pts g) = sideOpp D.model 0 :=
      beta_corner_other_edge S i kk fi g hfk hgk hgf hang hc'
    rw [hk, hg, S.hsa] at hZa; exact hZa

end Erdos634.LaczJunction.Walk
