import Erdos634.Draft.LaczFormalW2Oriented
import Erdos634.MirrorGauge

/-!
# Rule W2: dropping the orientation by reflecting the whole dissection

Erdős #634, band program, rule W2.  Credit: AI assistant (item 3, band program), Beeson–Roșu, Beeson, Laczkovich,
Paliy.  UNAUDITED.

`CongruentDissection.mirror` (reflection in the first axis, same model) carries a `BandSetup` and `BaseTok` data to the
same kind of data and reverses the sign of `cross`.  Hence `w2_oriented` (counterclockwise target) gives the rule for
every target.
-/

namespace Erdos634.LaczJunction.Walk

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.LaczJunction Erdos634.LaczJunction.Grammar
open Erdos634.MirrorGauge

variable {N : ℕ}

theorem mirrorPt_zero_vec : mirrorPt (0 : Plane) = 0 := by
  ext i; fin_cases i <;> simp [mirrorPt]

theorem mirrorPt_sub (u w : Plane) : mirrorPt u - mirrorPt w = mirrorPt (u - w) := by
  ext i; fin_cases i <;> simp [mirrorPt] <;> ring

theorem mirrorPt_add (u w : Plane) : mirrorPt u + mirrorPt w = mirrorPt (u + w) := by
  ext i; fin_cases i <;> simp [mirrorPt] <;> ring

theorem mirrorPt_smul (c : ℝ) (u : Plane) : c • mirrorPt u = mirrorPt (c • u) := by
  ext i; fin_cases i <;> simp [mirrorPt]

theorem norm_mirrorPt (u : Plane) : ‖mirrorPt u‖ = ‖u‖ := by
  have := mirrorPt_dist u 0
  rw [mirrorPt_zero_vec, dist_eq_norm, dist_eq_norm, sub_zero, sub_zero] at this
  exact this

theorem cross_mirror (u w : Plane) : cross (mirrorPt u) (mirrorPt w) = - cross u w := by
  simp only [cross, mirrorPt_zero, mirrorPt_one]; ring

noncomputable def mirrorLI : Plane →ₗᵢ[ℝ] Plane where
  toLinearMap := mirrorL
  norm_map' := fun x => norm_mirrorPt x

theorem cornerAngle_mirror (A B C : Plane) :
    cornerAngle (mirrorPt A) (mirrorPt B) (mirrorPt C) = cornerAngle A B C := by
  unfold cornerAngle EuclideanGeometry.angle
  simp only [vsub_eq_sub]
  rw [mirrorPt_sub, mirrorPt_sub]
  exact mirrorLI.angle_map (A - B) (C - B)


theorem coord_mirror (T : Tri) (j : Fin 3) (x : Plane) :
    (Tri.mirror T).basis.coord j (mirrorPt x) = T.basis.coord j x := by
  classical
  have hw : ∑ i, T.basis.coord i x = 1 := T.basis.sum_coord_apply_eq_one x
  have h1 : Finset.univ.affineCombination ℝ T.basis (fun i => T.basis.coord i x) = x :=
    T.basis.affineCombination_coord_eq_self x
  have h2 := Finset.map_affineCombination Finset.univ T.basis (fun i => T.basis.coord i x) hw
    mirrorL.toAffineMap
  rw [h1] at h2
  have hb : ((Tri.mirror T).basis : Fin 3 → Plane) = mirrorL.toAffineMap ∘ (T.basis : Fin 3 → Plane) := by
    funext i; rfl
  have h3 : mirrorPt x = Finset.univ.affineCombination ℝ (Tri.mirror T).basis (fun i => T.basis.coord i x) := by
    rw [hb]; exact h2
  rw [h3]
  exact (Tri.mirror T).basis.coord_apply_combination_of_mem (Finset.mem_univ j) (by simpa using hw)

theorem localAngle_mirror (T : Tri) (x : Plane) :
    (Tri.mirror T).localAngle (mirrorPt x) = T.localAngle x := by
  classical
  by_cases hv : ∃ j, x = T.pts j
  · obtain ⟨j, rfl⟩ := hv
    have := Tri.localAngle_vertex (Tri.mirror T) j
    simp only [Tri.mirror_pts] at this
    rw [this, cornerAngle_mirror, Tri.localAngle_vertex]
  · have hv' : ¬ ∃ j, mirrorPt x = (Tri.mirror T).pts j := by
      rintro ⟨j, hj⟩; apply hv; exact ⟨j, mirrorPt_injective (by rw [hj, Tri.mirror_pts])⟩
    simp only [Tri.localAngle, hv, hv', coord_mirror, dite_false]


theorem mirror_target_pts (D : CongruentDissection N) (k : Fin 3) :
    (CongruentDissection.mirror D).target.pts k = mirrorPt (D.target.pts k) := rfl

theorem bandSetup_mirror {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ} {p q r : Fin 3}
    (S : BandSetup D e f α β γ p q r) : BandSetup (CongruentDissection.mirror D) e f α β γ p q r where
  he := S.he
  hef := S.hef
  hcop := S.hcop
  hγdef := S.hγdef
  hrel := S.hrel
  hirr := S.hirr
  hα0 := S.hα0
  hβ0 := S.hβ0
  hα' := S.hα'
  hβ' := S.hβ'
  hγ' := S.hγ'
  hsa := S.hsa
  hsb := S.hsb
  hsc := S.hsc
  hpq := S.hpq
  hpr := S.hpr
  hqr := S.hqr
  cornerP := by
    rw [mirror_target_pts, mirror_target_pts, mirror_target_pts, cornerAngle_mirror]; exact S.cornerP
  cornerQ := by
    rw [mirror_target_pts, mirror_target_pts, mirror_target_pts, cornerAngle_mirror]; exact S.cornerQ
  hcB := by rw [mirror_target_pts, mirror_target_pts, mirrorPt_dist]; exact S.hcB
  haL := by rw [mirror_target_pts, mirror_target_pts, mirrorPt_dist]; exact S.haL
  haR := by rw [mirror_target_pts, mirror_target_pts, mirrorPt_dist]; exact S.haR

theorem basetok_mirror {D : CongruentDissection N} {p q : Fin 3} {ang : Corner → ℝ} {len : Side → ℝ}
    {x : Side} {l rr : Corner} {i : Fin N} {X Y Z : Plane}
    (h : BaseTok D p q ang len x l rr i X Y Z) :
    BaseTok (CongruentDissection.mirror D) p q ang len x l rr i (mirrorPt X) (mirrorPt Y) (mirrorPt Z) where
  left_mem := by
    obtain ⟨a, b, ha, hb, hab, hX⟩ := h.left_mem
    refine ⟨a, b, ha, hb, hab, ?_⟩
    rw [mirror_target_pts, mirror_target_pts, ← hX, ← mirrorPt_add, mirrorPt_smul, mirrorPt_smul]
  right_mem := by
    obtain ⟨a, b, ha, hb, hab, hX⟩ := h.right_mem
    refine ⟨a, b, ha, hb, hab, ?_⟩
    rw [mirror_target_pts, mirror_target_pts, ← hX, ← mirrorPt_add, mirrorPt_smul, mirrorPt_smul]
  order := by
    rw [mirror_target_pts, mirrorPt_dist, mirrorPt_dist]; exact h.order
  verts := by
    obtain ⟨j, hj | hj⟩ := h.verts
    · exact ⟨j, Or.inl ⟨by rw [CongruentDissection.mirror_tile, Tri.mirror_pts, hj.1],
        by rw [CongruentDissection.mirror_tile, Tri.mirror_pts, hj.2.1],
        by rw [CongruentDissection.mirror_tile, Tri.mirror_pts, hj.2.2]⟩⟩
    · exact ⟨j, Or.inr ⟨by rw [CongruentDissection.mirror_tile, Tri.mirror_pts, hj.1],
        by rw [CongruentDissection.mirror_tile, Tri.mirror_pts, hj.2.1],
        by rw [CongruentDissection.mirror_tile, Tri.mirror_pts, hj.2.2]⟩⟩
  length := by rw [mirrorPt_dist]; exact h.length
  left_angle := by
    rw [CongruentDissection.mirror_tile, localAngle_mirror]; exact h.left_angle
  right_angle := by
    rw [CongruentDissection.mirror_tile, localAngle_mirror]; exact h.right_angle

/-- **Rule W2, any orientation.** -/
theorem w2_holds {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ} {p q r : Fin 3}
    (S : BandSetup D e f α β γ p q r) (he2 : 2 ≤ e) (hf3 : 3 ≤ f)
    (hL2 : 2 * (ta e f : ℝ) < dist (D.target.pts p) (D.target.pts r))
    {i1 i2 i3 : Fin N} (hne3 : i3 ≠ i2)
    {P1 P2 P3 G1 G2 Z3 : Plane} {x3 : Side} {l3 r3 : Corner}
    (hlr : (x3 = .b ∧ l3 = .A) ∨ (x3 = .c ∧ l3 = .A) ∨ (x3 = .b ∧ l3 = .G ∧ r3 = .A))
    (t1 : BaseTok D p q (angOf α β γ) (lenOf (ta e f) (tb e f) (tc e f)) .c .B .A i1
      (D.target.pts p) P1 G1)
    (t2 : BaseTok D p q (angOf α β γ) (lenOf (ta e f) (tb e f) (tc e f)) .c .B .A i2 P1 P2 G2)
    (t3 : BaseTok D p q (angOf α β γ) (lenOf (ta e f) (tb e f) (tc e f)) x3 l3 r3 i3 P2 P3 Z3) :
    False := by
  have hne := tile_cross_ne D.target p q r S.hpq S.hpr S.hqr
  rcases lt_trichotomy (cross (D.target.pts q - D.target.pts p) (D.target.pts r - D.target.pts p)) 0 with
    hneg | hz | hpos
  · refine w2_oriented (bandSetup_mirror S) he2 hf3 ?_ ?_ hne3 hlr (basetok_mirror t1) (basetok_mirror t2)
      (basetok_mirror t3)
    · rw [mirror_target_pts, mirror_target_pts, mirror_target_pts, mirrorPt_sub, mirrorPt_sub, cross_mirror]
      linarith
    · rw [mirror_target_pts, mirror_target_pts, mirrorPt_dist]; exact hL2
  · exact absurd hz hne
  · exact w2_oriented S he2 hf3 hpos hL2 hne3 hlr t1 t2 t3

#print axioms w2_holds

end Erdos634.LaczJunction.Walk
