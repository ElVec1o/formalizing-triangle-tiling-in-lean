import Erdos634.Draft.LaczFormal9j
import Erdos634.Draft.LaczFormalSWWExist

/-!
# Witnesses for the Thm 5.3 `c(T)` clause (second lane, 2026-10-22)

NOTE, UNAUDITED.  Credit: Laczkovich (Discrete Math. 140 (1995) Thm 5.3), Beeson, Beeson-Rosu.

* `thm53_classify_witness`: hypotheses of `thm53_c_classify` on a real dissection (`lemma1b_witness`).
* `thm53_scalene_witness`: `thm53_c_scalene` on the one-tile dissection of the 30-60-90 triangle (the tile of `HBCFalse3.D3`).
* `triso`: the 30-30-120 triangle `(-sqrt 3, 0), (sqrt 3, 0), (0, 1)` (apex at vertex 2, base angle `pi/6`);
  `thm53_isosceles_witness`: the four-part `c(T) = 2` package `thm53_c_isosceles` on it.
-/

open scoped Classical
open Erdos634.Geometry Erdos634.CertCoord Erdos634.Draft.TheoremPConditional Erdos634.Draft.LaczFormal

namespace Erdos634.Laczkovich9

theorem thm53_classify_witness :
    ∃ (N : ℕ) (D : CongruentDissection N), ¬ Equilateral D ∧ CommAngles D.target ∧
      ((∃ σ : Equiv.Perm (Fin 3), ∀ k, D.model.angleAt (σ k) = D.target.angleAt k) ∨
        ∃ (α : ℝ) (j₁ j₂ : Fin 3), j₁ ≠ j₂ ∧ D.target.angleAt j₁ = α ∧ D.target.angleAt j₂ = α ∧
          TileAngles D α (Real.pi / 2 - α) (Real.pi / 2)) := by
  obtain ⟨N, D, hne, hc⟩ := lemma1b_witness
  exact ⟨N, D, hne, hc, thm53_c_classify D hne hc⟩

theorem thm53_scalene_witness :
    ∃ σ : Equiv.Perm (Fin 3), ∀ k, (selfDissection Erdos634.Draft.HBCFalse3.D3.model).model.angleAt (σ k) =
      (selfDissection Erdos634.Draft.HBCFalse3.D3.model).target.angleAt k := by
  have hpi := Real.pi_pos
  obtain ⟨σ, h0, h1, h2⟩ := D3_tileAngles
  set M := Erdos634.Draft.HBCFalse3.D3.model with hM
  -- the angles of M are pi/6, pi/3, pi/2 (at sigma 0, sigma 1, sigma 2): pairwise distinct
  have hs : ∀ i j : Fin 3, i ≠ j → M.angleAt i ≠ M.angleAt j := by
    intro i j hij hEq
    obtain ⟨a, rfl⟩ := σ.surjective i
    obtain ⟨b, rfl⟩ := σ.surjective j
    have hab : a ≠ b := fun h => hij (by rw [h])
    have va : ∀ c : Fin 3, M.angleAt (σ c) = ![Real.pi / 6, Real.pi / 3, Real.pi / 2] c := by
      intro c; fin_cases c
      · exact h0
      · exact h1
      · exact h2
    rw [va a, va b] at hEq
    fin_cases a <;> fin_cases b <;> simp at hab hEq <;> linarith
  have hne : ¬ Equilateral (selfDissection M) := by
    intro hE
    have e0 := hE 0
    have e1 := hE 1
    have : M.angleAt 0 = M.angleAt 1 := by
      show (selfDissection M).target.angleAt 0 = (selfDissection M).target.angleAt 1
      rw [e0, e1]
    exact hs 0 1 (by decide) this
  have hc : CommAngles (selfDissection M).target := by
    rw [commAngles_iff]
    intro k
    obtain ⟨c, hc⟩ := σ.surjective k
    show ∃ q : ℚ, M.angleAt k = q * Real.pi
    rw [← hc]
    have hc3 : c = 0 ∨ c = 1 ∨ c = 2 := by fin_cases c <;> simp
    rcases hc3 with rfl | rfl | rfl
    · exact ⟨1 / 6, by rw [h0]; push_cast; ring⟩
    · exact ⟨1 / 3, by rw [h1]; push_cast; ring⟩
    · exact ⟨1 / 2, by rw [h2]; push_cast; ring⟩
  exact thm53_c_scalene (selfDissection M) hne hc hs

/-! ### the 30-30-120 triangle -/

theorem triso_det : det3 (-Real.sqrt 3) 0 (Real.sqrt 3) 0 0 1 ≠ 0 := by
  have h : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  unfold det3; nlinarith

noncomputable def triso : Tri := mkTri (-Real.sqrt 3) 0 (Real.sqrt 3) 0 0 1 triso_det

theorem triso_pts : triso.pts = ![mkPt (-Real.sqrt 3) 0, mkPt (Real.sqrt 3) 0, mkPt 0 1] := mkTri_pts _ _ _ _ _ _ _

theorem triso_iso : dist (triso.pts 2) (triso.pts 0) = dist (triso.pts 2) (triso.pts 1) := by
  rw [triso_pts]
  show dist (mkPt 0 1) (mkPt (-Real.sqrt 3) 0) = dist (mkPt 0 1) (mkPt (Real.sqrt 3) 0)
  apply Erdos634.SssCongruent.dist_of_sq
  rw [dist_sq_mkPt, dist_sq_mkPt]; ring

theorem triso_angle0 : triso.angleAt 0 = Real.pi / 6 := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have d12 : triso.oppLen 0 = 2 := by
    unfold Tri.oppLen; rw [triso_pts]
    show dist (mkPt (Real.sqrt 3) 0) (mkPt 0 1) = 2
    apply Erdos634.Draft.FluxPaperWitness.dist_eq_of_sq (by norm_num)
    rw [dist_sq_mkPt]; nlinarith
  have d20 : triso.oppLen 1 = 2 := by
    unfold Tri.oppLen; rw [triso_pts]
    show dist (mkPt 0 1) (mkPt (-Real.sqrt 3) 0) = 2
    apply Erdos634.Draft.FluxPaperWitness.dist_eq_of_sq (by norm_num)
    rw [dist_sq_mkPt]; nlinarith
  have d01 : triso.oppLen 2 = 2 * Real.sqrt 3 := by
    unfold Tri.oppLen; rw [triso_pts]
    show dist (mkPt (-Real.sqrt 3) 0) (mkPt (Real.sqrt 3) 0) = 2 * Real.sqrt 3
    apply Erdos634.Draft.FluxPaperWitness.dist_eq_of_sq (by positivity)
    rw [dist_sq_mkPt]; nlinarith
  have hc := Erdos634.Draft.G3CAng.cos_angleAt_opp triso 0 (by
      show 0 < triso.oppLen 1; rw [d20]; norm_num) (by
      show 0 < triso.oppLen 2; rw [d01]; positivity)
  have e1 : (0 : Fin 3) + 1 = 1 := rfl
  have e2 : (0 : Fin 3) + 2 = 2 := rfl
  rw [e1, e2, d20, d01, show triso.oppLen 0 = 2 from d12] at hc
  have hcos : Real.cos (triso.angleAt 0) = Real.cos (Real.pi / 6) := by
    rw [hc, Real.cos_pi_div_six]
    field_simp
    nlinarith
  have hpi := Real.pi_pos
  exact Real.injOn_cos ⟨(Erdos634.MarchFlank.cornerAngle_pos triso 0).le,
    (Erdos634.RouteOneVertexKill.cornerAngle_lt_pi triso 0).le⟩ ⟨by positivity, by linarith⟩ hcos

/-- The `c(T) = 2` package of `thm53_c_isosceles`, for a given isosceles `S` (apex at vertex 2). -/
def C2Package (S : Tri) : Prop :=
    (∀ (N : ℕ) (D : CongruentDissection N), D.target = S →
      TileAngles D (S.angleAt 0) (S.angleAt 0) (Real.pi - 2 * S.angleAt 0) ∨
      TileAngles D (S.angleAt 0) (Real.pi / 2 - S.angleAt 0) (Real.pi / 2)) ∧
    (∃ D : CongruentDissection 1, D.target = S ∧ TileAngles D (S.angleAt 0) (S.angleAt 0) (Real.pi - 2 * S.angleAt 0)) ∧
    (∃ D : CongruentDissection 2, D.target = S ∧ TileAngles D (S.angleAt 0) (Real.pi / 2 - S.angleAt 0) (Real.pi / 2)) ∧
    (S.angleAt 0 < Real.pi / 2 →
      ∀ σ : Equiv.Perm (Fin 3), ¬ (∀ k, (![S.angleAt 0, Real.pi / 2 - S.angleAt 0, Real.pi / 2] : Fin 3 → ℝ) (σ k) =
        (![S.angleAt 0, S.angleAt 0, Real.pi - 2 * S.angleAt 0] : Fin 3 → ℝ) k))

theorem thm53_isosceles_witness : C2Package triso := thm53_c_isosceles triso triso_iso (by
    rw [commAngles_iff]
    obtain ⟨b1, b2⟩ := iso_base_angles triso triso_iso
    intro k; fin_cases k
    · exact ⟨1 / 6, by show triso.angleAt 0 = _; rw [triso_angle0]; push_cast; ring⟩
    · exact ⟨1 / 6, by show triso.angleAt 1 = _; rw [b1, triso_angle0]; push_cast; ring⟩
    · exact ⟨2 / 3, by show triso.angleAt 2 = _; rw [b2, triso_angle0]; push_cast; ring⟩)
  (by rw [triso_angle0]; intro h; have := Real.pi_pos; linarith)
  (by rw [triso_angle0]; intro h; have := Real.pi_pos; linarith)

end Erdos634.Laczkovich9

#print axioms Erdos634.Laczkovich9.thm53_classify_witness
#print axioms Erdos634.Laczkovich9.thm53_scalene_witness
#print axioms Erdos634.Laczkovich9.thm53_isosceles_witness
