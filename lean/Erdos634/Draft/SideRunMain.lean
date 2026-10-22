/-
Draft/SideRunMain.lean -- Stage 5a of the formalization of the side theorem of room GAP3: Theorems B and C of
(private working notes, not included) in side-length form.

Tile `(n, n²−1, n²)`, `n ≥ 2`.
* `no_dissection_T` (**Theorem B**): for `1 ≤ M`, `2M < n`, no congruent dissection (any number of tiles) has a
  target with sides `M n³`, `M n³`, `M (3n²−1)` (the triangle `T_M(1,n)`) and a model with sides `n`, `n²−1`, `n²`.
* `no_dissection_W` (**Theorem C**): for `1 ≤ M < n`, no congruent dissection has a target with sides `M n³`,
  `M n (n²−1)`, `M (2n²−1)` (the triangle `W_M(1,n)`) and such a model.
Both are the side theorem (`Setup.no_tiling_of_length`) applied to the side of length `M (κ n² − 1)`, `κ = 3`, `2`,
after the normal form (`setup_of_sides`: SSS and `E1NormalForm.normalFormC`).

This file imports no certificate module (`Refl.*`) and none of the files that do.

Composite-N work (base-beta threshold program); not prime-case work.  No sorry, no native_decide.
-/
import Erdos634.Draft.SideRunRules
import Erdos634.Draft.FDBBaseBetaE1

namespace Erdos634.Draft.SideRun

open Erdos634.Geometry Erdos634.CertCoord Erdos634.MarchKillsFan Erdos634.MarchSlots
  Erdos634.MarchInduction Erdos634.BaseBetaTargetCoord Erdos634.MarchCompose
  Erdos634.Draft.FDBBaseBetaE1 Erdos634.Draft.W2E1 Set

theorem hasSides_cast' {T : Erdos634.Geometry.Tri} {a b c a' b' c' : ℝ} (h : HasSides T a b c)
    (ha : a = a') (hb : b = b') (hc : c = c') : HasSides T a' b' c' := by
  subst ha; subst hb; subst hc; exact h

/-- **The normal form.**  A congruent dissection whose target has the sides `t n`, `dq`, `L` of the triangle
`Q = (0,0)`, `B = (L,0)`, `A = (L − t u, t h)` and whose model has the sides `n`, `n²−1`, `n²` gives, after an
isometry, a `Setup` on that triangle. -/
theorem setup_of_sides (n : ℕ) (hn2 : 2 ≤ n) {L t dq : ℝ} (hL : 0 < L) (ht : 0 < t)
    (hdq : dist (mkPt (L - t * uu n) (t * hh n)) (mkPt 0 0) = dq) {N : ℕ}
    (D₀ : CongruentDissection N) (hT : HasSides D₀.target (t * n) dq L)
    (hMod : HasSides D₀.model (n:ℝ) ((n:ℝ) ^ 2 - 1) ((n:ℝ) ^ 2)) :
    ∃ D : CongruentDissection N, Setup D n (modelAlpha 1 n) (modelBeta 1 n)
      (2 * modelAlpha 1 n + modelBeta 1 n) L (L - t * uu n) (t * hh n) := by
  have hf2 : (2:ℝ) ≤ n := by exact_mod_cast hn2
  have hf1 : (1:ℝ) < n := by linarith
  have hf0 : (0:ℝ) < n := by linarith
  have hay : 0 < t * hh n := mul_pos ht (hh_pos hf1)
  have hsq := hh_sq hf1
  have h12 : dist ((Tg L (L - t * uu n) (t * hh n) hL hay).pts 1)
      ((Tg L (L - t * uu n) (t * hh n) hL hay).pts 2) = t * n := by
    show dist (mkPt L 0) (mkPt (L - t * uu n) (t * hh n)) = t * n
    refine dist_eq_of_sq_eq ?_ dist_nonneg (by positivity)
    rw [dist_sq_mkPt]
    linear_combination t ^ 2 * hsq
  have h20 : dist ((Tg L (L - t * uu n) (t * hh n) hL hay).pts 2)
      ((Tg L (L - t * uu n) (t * hh n) hL hay).pts 0) = dq := hdq
  have h01 : dist ((Tg L (L - t * uu n) (t * hh n) hL hay).pts 0)
      ((Tg L (L - t * uu n) (t * hh n) hL hay).pts 1) = L := by
    show dist (mkPt 0 0) (mkPt L 0) = L
    have := dist_mkPt_base 0 L hL.le
    rwa [zero_add] at this
  have htgt := congruent_of_hasSides hT h12 h20 h01
  have hmod : D₀.model.Congruent (modelTri n (by exact_mod_cast (show 1 < n by omega))) := by
    obtain ⟨s0, s1, s2⟩ := modelTri_sides hf2
    exact congruent_of_hasSides hMod s0 s1 s2
  obtain ⟨g, σ, hg⟩ := htgt
  exact ⟨Erdos634.E1NormalForm.normalFormC D₀ g σ hmod, hn2,
    Erdos634.E1NormalForm.modelData_of_model_eq _ n hn2 rfl,
    Erdos634.E1NormalForm.angleData_model n hn2, hL, hay,
    fun _ _ => Erdos634.E1NormalForm.normalFormC_target D₀ hg hmod⟩

theorem dq_T {n : ℝ} (hn : 1 < n) {L t : ℝ} (ht : 0 < t) (e : L - t * uu n = t * uu n) :
    dist (mkPt (L - t * uu n) (t * hh n)) (mkPt 0 0) = t * n := by
  have hsq := hh_sq hn
  refine dist_eq_of_sq_eq ?_ dist_nonneg (by nlinarith)
  rw [dist_sq_mkPt, e]
  linear_combination t ^ 2 * hsq

theorem dq_W {n : ℝ} (hn : 1 < n) {L t t' : ℝ} (ht' : 0 < t') (e1 : L - t * uu n = t')
    (e2 : t * hh n = t' * rt n) :
    dist (mkPt (L - t * uu n) (t * hh n)) (mkPt 0 0) = t' * (2 * n) := by
  have hr := rt_sq (f := n) hn.le
  refine dist_eq_of_sq_eq ?_ dist_nonneg (by nlinarith)
  rw [dist_sq_mkPt, e1, e2]
  linear_combination t' ^ 2 * hr

/-- the corners of the base of `T_M(1,n)`: `β` and `β` -/
theorem corners_T (n M : ℕ) (hn : (1:ℝ) < n) (hM : (0:ℝ) < M) :
    Corners n ((M:ℝ) * (3 * (n:ℝ) ^ 2 - 1))
      ((M:ℝ) * (3 * (n:ℝ) ^ 2 - 1) - (M:ℝ) * (n:ℝ) ^ 2 * uu n) ((M:ℝ) * (n:ℝ) ^ 2 * hh n) := by
  have hu := uu_spec hn
  have ht : (0:ℝ) < (M:ℝ) * (n:ℝ) ^ 2 := mul_pos hM (by nlinarith)
  exact ⟨⟨(M:ℝ) * (n:ℝ) ^ 2, ht, rfl, rfl⟩,
    Or.inl ⟨(M:ℝ) * (n:ℝ) ^ 2, ht, by linear_combination (-(M:ℝ)) * hu, rfl⟩⟩

/-- the corners of the side `QB` of `W_M(1,n)`: `α + β` and `β` -/
theorem corners_W (n M : ℕ) (hn : (1:ℝ) < n) (hM : (0:ℝ) < M) :
    Corners n ((M:ℝ) * (2 * (n:ℝ) ^ 2 - 1))
      ((M:ℝ) * (2 * (n:ℝ) ^ 2 - 1) - (M:ℝ) * (n:ℝ) ^ 2 * uu n) ((M:ℝ) * (n:ℝ) ^ 2 * hh n) := by
  have hu := uu_spec hn
  have hh' := hh_spec hn
  have ht : (0:ℝ) < (M:ℝ) * (n:ℝ) ^ 2 := mul_pos hM (by nlinarith)
  have ht' : (0:ℝ) < (M:ℝ) * ((n:ℝ) ^ 2 - 1) / 2 := by
    have : (0:ℝ) < (M:ℝ) * ((n:ℝ) ^ 2 - 1) := mul_pos hM (by nlinarith)
    linarith
  exact ⟨⟨(M:ℝ) * (n:ℝ) ^ 2, ht, rfl, rfl⟩,
    Or.inr ⟨(M:ℝ) * ((n:ℝ) ^ 2 - 1) / 2, ht', by linear_combination (-(M:ℝ) / 2) * hu,
      by linear_combination ((M:ℝ) / 2) * hh'⟩⟩

/-- the normal form of a dissection of `T_M(1,n)` -/
theorem setup_T (n M : ℕ) (hn2 : 2 ≤ n) (hM : 1 ≤ M) {N : ℕ} (D₀ : CongruentDissection N)
    (hT : HasSides D₀.target ((M:ℝ) * (n:ℝ) ^ 3) ((M:ℝ) * (n:ℝ) ^ 3) ((M:ℝ) * (3 * (n:ℝ) ^ 2 - 1)))
    (hMod : HasSides D₀.model (n:ℝ) ((n:ℝ) ^ 2 - 1) ((n:ℝ) ^ 2)) :
    ∃ D : CongruentDissection N, Setup D n (modelAlpha 1 n) (modelBeta 1 n)
      (2 * modelAlpha 1 n + modelBeta 1 n) ((M:ℝ) * (3 * (n:ℝ) ^ 2 - 1))
      ((M:ℝ) * (3 * (n:ℝ) ^ 2 - 1) - (M:ℝ) * (n:ℝ) ^ 2 * uu n) ((M:ℝ) * (n:ℝ) ^ 2 * hh n) := by
  have hf2 : (2:ℝ) ≤ n := by exact_mod_cast hn2
  have hf1 : (1:ℝ) < n := by linarith
  have hMr : (0:ℝ) < M := by exact_mod_cast hM
  have hu := uu_spec hf1
  have ht : (0:ℝ) < (M:ℝ) * (n:ℝ) ^ 2 := mul_pos hMr (by nlinarith)
  have hL : (0:ℝ) < (M:ℝ) * (3 * (n:ℝ) ^ 2 - 1) := mul_pos hMr (by nlinarith)
  have e : (M:ℝ) * (3 * (n:ℝ) ^ 2 - 1) - (M:ℝ) * (n:ℝ) ^ 2 * uu n = (M:ℝ) * (n:ℝ) ^ 2 * uu n := by
    linear_combination (-(M:ℝ)) * hu
  exact setup_of_sides n hn2 hL ht (dq_T hf1 ht e) D₀
    (hasSides_cast' hT (by ring) (by ring) rfl) hMod

/-- the normal form of a dissection of `W_M(1,n)` -/
theorem setup_W (n M : ℕ) (hn2 : 2 ≤ n) (hM : 1 ≤ M) {N : ℕ} (D₀ : CongruentDissection N)
    (hT : HasSides D₀.target ((M:ℝ) * (n:ℝ) ^ 3) ((M:ℝ) * ((n:ℝ) * ((n:ℝ) ^ 2 - 1)))
      ((M:ℝ) * (2 * (n:ℝ) ^ 2 - 1)))
    (hMod : HasSides D₀.model (n:ℝ) ((n:ℝ) ^ 2 - 1) ((n:ℝ) ^ 2)) :
    ∃ D : CongruentDissection N, Setup D n (modelAlpha 1 n) (modelBeta 1 n)
      (2 * modelAlpha 1 n + modelBeta 1 n) ((M:ℝ) * (2 * (n:ℝ) ^ 2 - 1))
      ((M:ℝ) * (2 * (n:ℝ) ^ 2 - 1) - (M:ℝ) * (n:ℝ) ^ 2 * uu n) ((M:ℝ) * (n:ℝ) ^ 2 * hh n) := by
  have hf2 : (2:ℝ) ≤ n := by exact_mod_cast hn2
  have hf1 : (1:ℝ) < n := by linarith
  have hMr : (0:ℝ) < M := by exact_mod_cast hM
  have hu := uu_spec hf1
  have hh' := hh_spec hf1
  have ht : (0:ℝ) < (M:ℝ) * (n:ℝ) ^ 2 := mul_pos hMr (by nlinarith)
  have hL : (0:ℝ) < (M:ℝ) * (2 * (n:ℝ) ^ 2 - 1) := mul_pos hMr (by nlinarith)
  have ht' : (0:ℝ) < (M:ℝ) * ((n:ℝ) ^ 2 - 1) / 2 := by
    have : (0:ℝ) < (M:ℝ) * ((n:ℝ) ^ 2 - 1) := mul_pos hMr (by nlinarith)
    linarith
  have e1 : (M:ℝ) * (2 * (n:ℝ) ^ 2 - 1) - (M:ℝ) * (n:ℝ) ^ 2 * uu n
      = (M:ℝ) * ((n:ℝ) ^ 2 - 1) / 2 := by
    linear_combination (-(M:ℝ) / 2) * hu
  have e2 : (M:ℝ) * (n:ℝ) ^ 2 * hh n = (M:ℝ) * ((n:ℝ) ^ 2 - 1) / 2 * rt n := by
    linear_combination ((M:ℝ) / 2) * hh'
  exact setup_of_sides n hn2 hL ht (dq_W hf1 ht' e1 e2) D₀
    (hasSides_cast' hT (by ring) (by ring) rfl) hMod

/-- **THEOREM B, side-length form.**  For `1 ≤ M` and `2M < n` no congruent dissection (any number of tiles) has a
target with sides `M n³`, `M n³`, `M (3n²−1)` and a model with sides `n`, `n²−1`, `n²`. -/
theorem no_dissection_T (n M : ℕ) (hM : 1 ≤ M) (h : 2 * M < n) {N : ℕ} (D₀ : CongruentDissection N)
    (hT : HasSides D₀.target ((M:ℝ) * (n:ℝ) ^ 3) ((M:ℝ) * (n:ℝ) ^ 3) ((M:ℝ) * (3 * (n:ℝ) ^ 2 - 1)))
    (hMod : HasSides D₀.model (n:ℝ) ((n:ℝ) ^ 2 - 1) ((n:ℝ) ^ 2)) : False := by
  have hn2 : 2 ≤ n := by omega
  have hf1 : (1:ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hMr : (0:ℝ) < M := by exact_mod_cast hM
  obtain ⟨D, S⟩ := setup_T n M hn2 hM D₀ hT hMod
  exact S.no_tiling_of_length (corners_T n M hf1 hMr) (M := M) (κ := 3) (by norm_num)
    (by simpa using h) (by push_cast; ring)

/-- **THEOREM C, side-length form.**  For `1 ≤ M < n` no congruent dissection (any number of tiles) has a target
with sides `M n³`, `M n (n²−1)`, `M (2n²−1)` and a model with sides `n`, `n²−1`, `n²`. -/
theorem no_dissection_W (n M : ℕ) (hM : 1 ≤ M) (h : M < n) {N : ℕ} (D₀ : CongruentDissection N)
    (hT : HasSides D₀.target ((M:ℝ) * (n:ℝ) ^ 3) ((M:ℝ) * ((n:ℝ) * ((n:ℝ) ^ 2 - 1)))
      ((M:ℝ) * (2 * (n:ℝ) ^ 2 - 1)))
    (hMod : HasSides D₀.model (n:ℝ) ((n:ℝ) ^ 2 - 1) ((n:ℝ) ^ 2)) : False := by
  have hn2 : 2 ≤ n := by omega
  have hf1 : (1:ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hMr : (0:ℝ) < M := by exact_mod_cast hM
  obtain ⟨D, S⟩ := setup_W n M hn2 hM D₀ hT hMod
  exact S.no_tiling_of_length (corners_W n M hf1 hMr) (M := M) (κ := 2) (by norm_num)
    (by simpa using h) (by push_cast; ring)

end Erdos634.Draft.SideRun

#print axioms Erdos634.Draft.SideRun.setup_of_sides
#print axioms Erdos634.Draft.SideRun.no_dissection_T
#print axioms Erdos634.Draft.SideRun.no_dissection_W
