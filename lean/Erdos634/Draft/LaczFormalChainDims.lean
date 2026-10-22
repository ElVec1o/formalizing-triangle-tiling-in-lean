import Erdos634.Draft.LaczFormalChain
import Erdos634.Draft.LaczFormalJunctionTarget

/-!
# `BandSetup` from the dimensions: the theorems U, U2 for a dissection of `T_M(e,f)`

Erdős #634, base-`β` band.  Credit: AI assistant (item 3, band program), Beeson–Roșu (the tile and the
isosceles target `T_M(e,f)`), Beeson, Laczkovich, Paliy.  UNAUDITED.  Axiom-clean; no `sorry`.

`BandSetup.of_dims`: if `D` is a congruent dissection whose model has the sides `(ef, f²−e², f²)` (side `j`
opposite vertex `j`) and whose target has base `[p,q]` of length `M e (3f²−e²)` and legs `[p,r]`, `[q,r]` of
length `M f³` (`1 ≤ e < f` coprime, `M ≥ 1`), then `BandSetup D e f α β γ p q r` holds with
`α = modelAlpha`, `β = modelBeta`, `γ = 2α+β`.  So the angles, the irrationality of `α/π`, the corner
angles of the model and of the target (law of cosines: `cos β = eN/(2f³)` both for the tile and for the
target corner) and the three size inequalities `c < base`, `a < leg` are *derived*, not hypotheses.

`U_dims`, `U2_dims`: the real-tiling theorems stated for `T_M(e,f)`.
-/

namespace Erdos634.LaczJunction

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.BaseBetaTargetCoord
open Erdos634.LaczJunction.Grammar

variable {N : ℕ}

theorem cornerAngle_eq_of_cos' {p q r : Plane} {a b d θ : ℝ} (ha : dist p q = a)
    (hb : dist r q = b) (hd : dist p r = d) (ha0 : 0 < a) (hb0 : 0 < b) (hθ0 : 0 ≤ θ)
    (hθπ : θ ≤ Real.pi) (hcos : Real.cos θ = (a ^ 2 + b ^ 2 - d ^ 2) / (2 * a * b)) :
    cornerAngle p q r = θ := by
  have hlaw :=
    EuclideanGeometry.dist_sq_eq_dist_sq_add_dist_sq_sub_two_mul_dist_mul_dist_mul_cos_angle p q r
  rw [ha, hb, hd] at hlaw
  have hc : Real.cos (cornerAngle p q r) = Real.cos θ := by
    rw [hcos]; unfold cornerAngle; field_simp; linarith
  exact Real.injOn_cos ⟨EuclideanGeometry.angle_nonneg _ _ _, EuclideanGeometry.angle_le_pi _ _ _⟩
    ⟨hθ0, hθπ⟩ hc

/-- The model angles from the model sides. -/
theorem model_angles_of_sides (R : Erdos634.Geometry.Tri) {e f : ℕ} (he : 1 ≤ e) (hef : e < f)
    (hs0 : sideOpp R 0 = (e : ℝ) * f) (hs1 : sideOpp R 1 = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (hs2 : sideOpp R 2 = (f : ℝ) ^ 2) :
    cornerAngle (R.pts 1) (R.pts 0) (R.pts 2) = modelAlpha (e : ℝ) (f : ℝ) ∧
    cornerAngle (R.pts 2) (R.pts 1) (R.pts 0) = modelBeta (e : ℝ) (f : ℝ) ∧
    cornerAngle (R.pts 0) (R.pts 2) (R.pts 1) =
      2 * modelAlpha (e : ℝ) (f : ℝ) + modelBeta (e : ℝ) (f : ℝ) := by
  have heR : (1 : ℝ) ≤ e := by exact_mod_cast he
  have hefR : (e : ℝ) < f := by exact_mod_cast hef
  have he0 : (0 : ℝ) < e := by linarith
  have hf0 : (0 : ℝ) < f := by linarith
  have hb0 : (0 : ℝ) < (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by nlinarith
  have d12 : dist (R.pts 1) (R.pts 2) = (e : ℝ) * f := by rw [← hs0]; rfl
  have d20 : dist (R.pts 2) (R.pts 0) = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by rw [← hs1]; rfl
  have d01 : dist (R.pts 0) (R.pts 1) = (f : ℝ) ^ 2 := by rw [← hs2]; rfl
  obtain ⟨hβ0, hβ2⟩ := modelBeta_mem he0 hefR
  have hrel := modelAngle_rel (e : ℝ) f
  have hα0 : 0 < modelAlpha (e : ℝ) f := by unfold modelAlpha; linarith
  have hαπ : modelAlpha (e : ℝ) f ≤ Real.pi := by unfold modelAlpha; linarith [Real.pi_pos]
  have hα' : cornerAngle (R.pts 1) (R.pts 0) (R.pts 2) = modelAlpha (e : ℝ) f := by
    have h1 : dist (R.pts 1) (R.pts 0) = (f : ℝ) ^ 2 := by rw [dist_comm]; exact d01
    refine cornerAngle_eq_of_cos' (a := (f : ℝ) ^ 2) (b := (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
      (d := (e : ℝ) * f) h1 d20 d12 (by positivity) hb0 hα0.le hαπ ?_
    rw [cos_modelAlpha he0 hefR]
    field_simp
    ring
  have hβ' : cornerAngle (R.pts 2) (R.pts 1) (R.pts 0) = modelBeta (e : ℝ) f := by
    have h1 : dist (R.pts 2) (R.pts 1) = (e : ℝ) * f := by rw [dist_comm]; exact d12
    refine cornerAngle_eq_of_cos' (a := (e : ℝ) * f) (b := (f : ℝ) ^ 2)
      (d := (f : ℝ) ^ 2 - (e : ℝ) ^ 2) h1 d01 d20 (by positivity) (by positivity)
      hβ0.le (by linarith [Real.pi_pos]) ?_
    obtain ⟨hc0, hc1⟩ := cosBeta_mem he0 hefR
    unfold modelBeta
    rw [Real.cos_arccos (by linarith) hc1.le]
    unfold baseLen Nq
    field_simp
    ring
  have hγ' : cornerAngle (R.pts 0) (R.pts 2) (R.pts 1) = 2 * modelAlpha (e : ℝ) f + modelBeta (e : ℝ) f := by
    have hsum := Erdos634.Geometry.cornerAngle_sum R
    rw [hα', hβ'] at hsum
    linarith
  exact ⟨hα', hβ', hγ'⟩

theorem tb_real (e f : ℕ) (hef : e < f) : (tb e f : ℝ) = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
  unfold tb
  have : e ^ 2 ≤ f ^ 2 := Nat.pow_le_pow_left hef.le 2
  push_cast [Nat.cast_sub this]
  ring

/-- **`BandSetup` from the dimensions of `T_M(e,f)`.** -/
theorem BandSetup.of_dims (D : CongruentDissection N) (e f M : ℕ) (he : 1 ≤ e) (hef : e < f)
    (hcop : Nat.Coprime e f) (hM : 1 ≤ M)
    (hsa : sideOpp D.model 0 = (ta e f : ℝ)) (hsb : sideOpp D.model 1 = (tb e f : ℝ))
    (hsc : sideOpp D.model 2 = (tc e f : ℝ))
    {p q r : Fin 3} (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (hbase : dist (D.target.pts p) (D.target.pts q) = ((M * e * (3 * f ^ 2 - e ^ 2) : ℕ) : ℝ))
    (hlegL : dist (D.target.pts p) (D.target.pts r) = ((M * f ^ 3 : ℕ) : ℝ))
    (hlegR : dist (D.target.pts q) (D.target.pts r) = ((M * f ^ 3 : ℕ) : ℝ)) :
    BandSetup D e f (modelAlpha (e : ℝ) f) (modelBeta (e : ℝ) f)
      (2 * modelAlpha (e : ℝ) f + modelBeta (e : ℝ) f) p q r := by
  have he0 : (0 : ℝ) < e := by exact_mod_cast he
  have hefR : (e : ℝ) < f := by exact_mod_cast hef
  have hf0 : (0 : ℝ) < f := by linarith
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  have hsa' : sideOpp D.model 0 = (e : ℝ) * f := by rw [hsa]; simp [ta]
  have hsb' : sideOpp D.model 1 = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by rw [hsb, tb_real e f hef]
  have hsc' : sideOpp D.model 2 = (f : ℝ) ^ 2 := by rw [hsc]; simp [tc]
  obtain ⟨hα', hβ', hγ'⟩ := model_angles_of_sides D.model he hef hsa' hsb' hsc'
  obtain ⟨hβ0, hβ2⟩ := modelBeta_mem he0 hefR
  have hα0 : 0 < modelAlpha (e : ℝ) f := by
    unfold modelAlpha; linarith [Real.pi_pos]
  -- the target corners
  have hbaseR : dist (D.target.pts p) (D.target.pts q) = (M : ℝ) * e * (3 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) := by
    rw [hbase]
    have : 3 * f ^ 2 ≥ e ^ 2 := by nlinarith
    push_cast [Nat.cast_sub this]; ring
  have hlegLR : dist (D.target.pts p) (D.target.pts r) = (M : ℝ) * (f : ℝ) ^ 3 := by
    rw [hlegL]; push_cast; ring
  have hlegRR : dist (D.target.pts q) (D.target.pts r) = (M : ℝ) * (f : ℝ) ^ 3 := by
    rw [hlegR]; push_cast; ring
  have hNq : 0 < 3 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by nlinarith
  have hbpos : 0 < (M : ℝ) * e * (3 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) := by positivity
  have hLpos : 0 < (M : ℝ) * (f : ℝ) ^ 3 := by positivity
  have hcosT : Real.cos (modelBeta (e : ℝ) f) =
      (((M : ℝ) * e * (3 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2)) ^ 2 + ((M : ℝ) * (f : ℝ) ^ 3) ^ 2 -
        ((M : ℝ) * (f : ℝ) ^ 3) ^ 2) /
      (2 * ((M : ℝ) * e * (3 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2)) * ((M : ℝ) * (f : ℝ) ^ 3)) := by
    rw [cos_modelBeta he0 hefR]
    unfold baseLen Nq
    field_simp
    ring
  have cP : cornerAngle (D.target.pts q) (D.target.pts p) (D.target.pts r) =
      modelBeta (e : ℝ) f := by
    refine cornerAngle_eq_of_cos' (a := (M : ℝ) * e * (3 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2))
      (b := (M : ℝ) * (f : ℝ) ^ 3) (d := (M : ℝ) * (f : ℝ) ^ 3) ?_ ?_ hlegRR hbpos hLpos hβ0.le
      (by linarith [Real.pi_pos]) hcosT
    · rw [dist_comm]; exact hbaseR
    · rw [dist_comm]; exact hlegLR
  have cQ : cornerAngle (D.target.pts p) (D.target.pts q) (D.target.pts r) =
      modelBeta (e : ℝ) f := by
    refine cornerAngle_eq_of_cos' (a := (M : ℝ) * e * (3 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2))
      (b := (M : ℝ) * (f : ℝ) ^ 3) (d := (M : ℝ) * (f : ℝ) ^ 3) hbaseR ?_ hlegLR hbpos hLpos
      hβ0.le (by linarith [Real.pi_pos]) hcosT
    · rw [dist_comm]; exact hlegRR
  exact
    { he := he
      hef := hef
      hcop := hcop
      hγdef := rfl
      hrel := modelAngle_rel (e : ℝ) f
      hirr := modelAlpha_irrational e f he hef
      hα0 := hα0
      hβ0 := hβ0
      hα' := hα'
      hβ' := hβ'
      hγ' := hγ'
      hsa := hsa
      hsb := hsb
      hsc := hsc
      hpq := hpq
      hpr := hpr
      hqr := hqr
      cornerP := cP
      cornerQ := cQ
      hcB := by rw [hbase]; exact_mod_cast base_gt_c e f M he hef hM
      haL := by rw [hlegL]; exact_mod_cast leg_gt_a e f M he hef hM
      haR := by rw [hlegR]; exact_mod_cast leg_gt_a e f M he hef hM }

/-- **Theorem U for a dissection of `T_M(e,f)` (`d = 2Me − f ≤ 1`).**  Hypotheses: the target dimensions,
the model sides, the base chain, and the band facts that are hand-proved elsewhere (no `a`-token and
exactly `2Me` `c`-tokens; the corner tokens have angle `β`; a run of `f` equal `c`-tokens). -/
theorem U_dims (D : CongruentDissection N) (e f M : ℕ) (he : 1 ≤ e) (hef : e < f)
    (hcop : Nat.Coprime e f) (hM : 1 ≤ M)
    (hsa : sideOpp D.model 0 = (ta e f : ℝ)) (hsb : sideOpp D.model 1 = (tb e f : ℝ))
    (hsc : sideOpp D.model 2 = (tc e f : ℝ))
    {p q r : Fin 3} (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (hbase : dist (D.target.pts p) (D.target.pts q) = ((M * e * (3 * f ^ 2 - e ^ 2) : ℕ) : ℝ))
    (hlegL : dist (D.target.pts p) (D.target.pts r) = ((M * f ^ 3 : ℕ) : ℝ))
    (hlegR : dist (D.target.pts q) (D.target.pts r) = ((M * f ^ 3 : ℕ) : ℝ))
    (ch : BaseChain D e f (modelAlpha (e : ℝ) f) (modelBeta (e : ℝ) f)
      (2 * modelAlpha (e : ℝ) f + modelBeta (e : ℝ) f) p q r)
    (hno : ∀ t ∈ ch.word, t.side ≠ .a)
    (hfirst : ∃ t, ch.word.head? = some t ∧ okFirst t)
    (hlast : ∃ t, ch.word.getLast? = some t ∧ okLast t)
    (hrun : HasRun f ch.word) (hcount : countC ch.word = 2 * M * e) (hf : 2 ≤ f)
    (hd : 2 * M * e ≤ f + 1) : False :=
  U_real (BandSetup.of_dims D e f M he hef hcop hM hsa hsb hsc hpq hpr hqr hbase hlegL hlegR)
    ch hno hfirst hlast hrun hcount hf hd

/-- **Theorem U2 for a dissection of `T_M(e,f)` (`d ≤ 2`), conditional on `W2Rule e f`.** -/
theorem U2_dims (D : CongruentDissection N) (e f M : ℕ) (he : 2 ≤ e) (hef : e < f)
    (hcop : Nat.Coprime e f) (hM : 1 ≤ M) (hW : W2Rule e f)
    (hsa : sideOpp D.model 0 = (ta e f : ℝ)) (hsb : sideOpp D.model 1 = (tb e f : ℝ))
    (hsc : sideOpp D.model 2 = (tc e f : ℝ))
    {p q r : Fin 3} (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (hbase : dist (D.target.pts p) (D.target.pts q) = ((M * e * (3 * f ^ 2 - e ^ 2) : ℕ) : ℝ))
    (hlegL : dist (D.target.pts p) (D.target.pts r) = ((M * f ^ 3 : ℕ) : ℝ))
    (hlegR : dist (D.target.pts q) (D.target.pts r) = ((M * f ^ 3 : ℕ) : ℝ))
    (ch : BaseChain D e f (modelAlpha (e : ℝ) f) (modelBeta (e : ℝ) f)
      (2 * modelAlpha (e : ℝ) f + modelBeta (e : ℝ) f) p q r)
    (hno : ∀ t ∈ ch.word, t.side ≠ .a)
    (hfirst : ∃ t, ch.word.head? = some t ∧ okFirst t)
    (hlast : ∃ t, ch.word.getLast? = some t ∧ okLast t)
    (hrun : HasRun f ch.word) (hcount : countC ch.word = 2 * M * e) (hf : 3 ≤ f)
    (hd : 2 * M * e ≤ f + 2) : False := by
  have S := BandSetup.of_dims D e f M (by omega) hef hcop hM hsa hsb hsc hpq hpr hqr hbase hlegL hlegR
  -- `2a < M f³`: `2 e f < M f³` since `e < f`
  have h2 : 2 * (ta e f : ℝ) < ((M * f ^ 3 : ℕ) : ℝ) := by
    unfold ta
    have h : 2 * (e * f) < M * f ^ 3 := by
      have h1 : e * f < f * f := Nat.mul_lt_mul_of_pos_right hef (by omega)
      have h2 : 2 * (f * f) ≤ f ^ 3 := by
        have : f ^ 3 = f * (f * f) := by ring
        rw [this]; nlinarith [Nat.mul_le_mul_right (f * f) hf]
      have h3 : f ^ 3 ≤ M * f ^ 3 := Nat.le_mul_of_pos_left _ hM
      omega
    exact_mod_cast h
  exact U2_real hW S he (by rw [hlegL]; exact h2) (by rw [hlegR]; exact h2) ch hno hfirst hlast
    hrun hcount hf hd

#print axioms U_dims
#print axioms U2_dims

end Erdos634.LaczJunction
