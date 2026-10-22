import Erdos634.Draft.LaczFormalWalkRules
import Erdos634.Draft.LaczFormalL3

/-!
# Rule W2, step 1: the tile `T' = (P₁, G₁, G₂)` (interface lemma I1)

Erdős #634, base-`β` band.  Credit: AI assistant (item 3, band program, `PROOF_W2.md` Step 1), Beeson–Roșu, Beeson,
Laczkovich, Paliy.  UNAUDITED.  Axiom-clean; no `sorry`.  New file; depends on the walk layer, does not modify it.

* `apex_dir` (I0): the apex of a walk tile with `β` at its left vertex and `c` on the base lies at
  `U + (a/L)(R − P)`: the direction of the left leg.  (Vector form of `first_apex`, for any entry.)
* `two_circles`: two points at the same distances from `A` and `B` on the same side of `AB` coincide.
-/

namespace Erdos634.LaczJunction.Walk

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.LaczJunction Erdos634.LaczJunction.Grammar
open Erdos634.Draft.LaczFormal.Graph

variable {N : ℕ}

/-- **I0.** The apex of a base tile with `β` at its left vertex and `c` on the base. -/
theorem apex_dir {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ} {p q r : Fin 3}
    (S : BandSetup D e f α β γ p q r)
    (hori : 0 < crs (toV2 (D.target.pts q - D.target.pts p)) (toV2 (D.target.pts r - D.target.pts p)))
    {x : Fin N × Plane × Plane}
    (hpar : ∃ s t : ℝ, 0 ≤ s ∧ s < t ∧ t ≤ 1 ∧ x.2.1 = D.target.pts p + s • (D.target.pts q - D.target.pts p) ∧
        x.2.2 = D.target.pts p + t • (D.target.pts q - D.target.pts p))
    (kk fi g : Fin 3) (hfk : fi ≠ kk) (hgk : g ≠ kk) (hgf : g ≠ fi)
    (hk : (D.tile x.1).pts kk = x.2.1) (hf : (D.tile x.1).pts fi = x.2.2)
    (hleft : 0 < crs (toV2 (D.target.pts q - D.target.pts p)) (toV2 ((D.tile x.1).pts g - x.2.1)))
    (hang : (D.tile x.1).localAngle ((D.tile x.1).pts kk) = β)
    (hc : dist x.2.1 x.2.2 = sideOpp D.model 2) :
    (D.tile x.1).pts g - x.2.1 =
      ((ta e f : ℝ) / dist (D.target.pts p) (D.target.pts r)) • (D.target.pts r - D.target.pts p) := by
  obtain ⟨hαβ, hβγ, hαγ, hab, hbc, hac⟩ := BandSetup.distinct S
  set P := D.target.pts p with hP
  set Q := D.target.pts q with hQ
  set R := D.target.pts r with hR
  set Z := (D.tile x.1).pts g with hZ
  have hc' : dist ((D.tile x.1).pts kk) ((D.tile x.1).pts fi) = sideOpp D.model 2 := by
    rw [hk, hf]; exact hc
  have hZa : dist ((D.tile x.1).pts kk) Z = sideOpp D.model 0 :=
    beta_corner_other_edge S x.1 kk fi g hfk hgk hgf hang hc'
  rw [hk] at hZa
  have hβang : cornerAngle ((D.tile x.1).pts fi) ((D.tile x.1).pts kk) Z = β := by
    rw [← localAngle_as_angle _ kk fi g hfk hgk hgf]; exact hang
  rw [hf, hk] at hβang
  obtain ⟨s, t, h0, hst, ht1, hs, ht⟩ := hpar
  have hne : P ≠ Q := by
    intro h
    have : crs (toV2 (Q - P)) (toV2 (R - P)) = 0 := by rw [← h]; simp [crs, toV2]
    linarith
  have hw : Q - P ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  have hv : x.2.2 - x.2.1 = (t - s) • (Q - P) := by rw [ht, hs, sub_smul]; abel
  have hZ0 : 0 < dist x.2.1 Z := by rw [hZa, S.hsa]; exact_mod_cast a_pos e f S.he S.hef
  have hPZ : Z - x.2.1 ≠ 0 := by
    intro h; rw [sub_eq_zero] at h; rw [h, dist_self] at hZ0; exact lt_irrefl _ hZ0
  have hL : ta e f < dist P R := by exact_mod_cast S.haL
  have hPR : R - P ≠ 0 := by
    intro h; rw [sub_eq_zero] at h; rw [h, dist_self] at hL
    have := a_pos e f S.he S.hef; have : (0:ℝ) < ta e f := by exact_mod_cast this
    linarith
  have hang1 : InnerProductGeometry.angle (Q - P) (Z - x.2.1) = β := by
    unfold cornerAngle at hβang
    rw [EuclideanGeometry.angle, vsub_eq_sub, vsub_eq_sub, hv,
      InnerProductGeometry.angle_smul_left_of_pos _ _ (by linarith)] at hβang
    exact hβang
  have hang2 : InnerProductGeometry.angle (Q - P) (R - P) = β := by
    have := S.cornerP
    unfold cornerAngle at this
    rw [EuclideanGeometry.angle, vsub_eq_sub, vsub_eq_sub] at this
    exact this
  have hc1 : 0 < cross (Q - P) (Z - x.2.1) := by rwa [← crs_toV2]
  have hc2 : 0 < cross (Q - P) (R - P) := by rwa [← crs_toV2]
  have hdir := dir_eq_of_angle hw hPZ hPR hc1 hc2 (hang1.trans hang2.symm)
  have hnZ : ‖Z - x.2.1‖ = ta e f := by
    rw [← dist_eq_norm, dist_comm, hZa, S.hsa]
  have hnR : ‖R - P‖ = dist P R := by rw [← dist_eq_norm, dist_comm]
  rw [hnZ, hnR] at hdir
  have hLpos : 0 < dist P R := lt_trans (by exact_mod_cast a_pos e f S.he S.hef) hL
  have h2 : (dist P R)⁻¹ • ((dist P R) • (Z - x.2.1)) = (dist P R)⁻¹ • ((ta e f : ℝ) • (R - P)) := by
    rw [hdir]
  rw [smul_smul, inv_mul_cancel₀ hLpos.ne', one_smul, smul_smul] at h2
  rw [h2]; congr 1; ring

/-- Two points at the same distances from `A` and `B`, on the same side of the line `AB`, coincide. -/
theorem two_circles {A B X Y : Plane} (hAB : A ≠ B) (h1 : dist A X = dist A Y) (h2 : dist B X = dist B Y)
    (hs : 0 < cross (B - A) (X - A) * cross (B - A) (Y - A)) : X = Y := by
  set s := B - A with hsdef
  have hs0 : s ≠ 0 := sub_ne_zero.mpr (Ne.symm hAB)
  set x := X - A
  set y := Y - A
  have n1 : ‖x‖ ^ 2 = ‖y‖ ^ 2 := by
    have := congrArg (· ^ 2) h1
    simp only [] at this
    rw [dist_comm A X, dist_comm A Y, dist_eq_norm, dist_eq_norm] at this
    exact this
  have n2 : ‖x - s‖ ^ 2 = ‖y - s‖ ^ 2 := by
    have := congrArg (· ^ 2) h2
    simp only [] at this
    rw [dist_comm B X, dist_comm B Y, dist_eq_norm, dist_eq_norm] at this
    have e1 : X - B = x - s := by simp [x, hsdef]
    have e2 : Y - B = y - s := by simp [y, hsdef]
    rw [e1, e2] at this; exact this
  have cx := Erdos634.Geometry.norm_sq_coords x
  have cy := Erdos634.Geometry.norm_sq_coords y
  have cxs := Erdos634.Geometry.norm_sq_coords (x - s)
  have cys := Erdos634.Geometry.norm_sq_coords (y - s)
  have cs := Erdos634.Geometry.norm_sq_coords s
  simp only [PiLp.sub_apply] at cxs cys
  have hd : s 0 * x 0 + s 1 * x 1 = s 0 * y 0 + s 1 * y 1 := by nlinarith
  have hsq : (cross s x) ^ 2 = (cross s y) ^ 2 := by
    have l1 : (cross s x) ^ 2 + (s 0 * x 0 + s 1 * x 1) ^ 2 = ‖s‖ ^ 2 * ‖x‖ ^ 2 := by
      rw [cs, cx]; simp only [cross]; ring
    have l2 : (cross s y) ^ 2 + (s 0 * y 0 + s 1 * y 1) ^ 2 = ‖s‖ ^ 2 * ‖y‖ ^ 2 := by
      rw [cs, cy]; simp only [cross]; ring
    rw [hd] at l1
    rw [n1] at l1
    linarith
  have hcr : cross s x = cross s y := by
    have h3 : (cross s x - cross s y) * (cross s x + cross s y) = 0 := by linear_combination hsq
    rcases mul_eq_zero.mp h3 with h | h
    · linarith
    · exfalso
      have : cross s y = - cross s x := by linarith
      rw [this] at hs
      nlinarith [sq_nonneg (cross s x)]
  have hns : 0 < s 0 ^ 2 + s 1 ^ 2 := by
    rw [← cs]; exact pow_pos (norm_pos_iff.mpr hs0) 2
  have e0 : x 0 = y 0 := by
    have : (s 0 ^ 2 + s 1 ^ 2) * (x 0 - y 0) = 0 := by
      simp only [cross] at hcr; linear_combination (s 0) * hd - (s 1) * hcr
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hns.ne'
    · linarith
  have e1 : x 1 = y 1 := by
    have : (s 0 ^ 2 + s 1 ^ 2) * (x 1 - y 1) = 0 := by
      simp only [cross] at hcr; linear_combination (s 1) * hd + (s 0) * hcr
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hns.ne'
    · linarith
  have : x = y := by ext i; fin_cases i <;> simp [e0, e1]
  have := congrArg (· + A) this
  simpa [x, y] using this

#print axioms apex_dir
#print axioms two_circles

end Erdos634.LaczJunction.Walk
