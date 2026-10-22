/-
Draft/WClosedBase.lean -- the members `(1, f)`: from tilings of `W` at the scales `f, …, 2f − 1` to every scale `M ≥ f`.

`WAddF.WClosed f m` says that the triangle `W_m` of the member `(1, f)` (angles `2α, β, α + β`; sides
`m f (f² − 1)`, `m (2f² − 1)`, `m f³`) is cut into `(2f² − 1) m²` copies of the tile `(f, f² − 1, f²)`;
`WAddF.WClosed_add` is its closure under sums and `WtoDeltaF.delta_cd_of_W` the passage to the base-β target.
Neither had a base case.  Here:

    theorem WClosed_of_dissection   -- any `CongruentDissection` with the sides of `W_m` and of the tile gives `WClosed f m`
    theorem WClosed_seed            -- `WClosed f f` (from `WSeedG.w_seed 1 f`)
    theorem WClosed_ge              -- `WClosed f (f + r)` for `1 ≤ r < f`  ⟹  `WClosed f M` for every `M ≥ f`
    theorem betaTilable_of_WClosed  -- `WClosed f m ⟹ BetaTilable 1 f m`
    theorem betaTilable_ge          -- the same hypotheses  ⟹  `BetaTilable 1 f M` for every `M ≥ f`
    theorem betaTilable_ge_of_dissections  -- the same, the hypotheses stated for `CongruentDissection`s

So for the member `(1, f)` the half "`M ≥ f` gives a tiling" of the threshold statement is reduced to `f − 1`
tilings (scales `f + 1, …, 2f − 1`).  The existence of those tilings is announced by D. Paliy (collar construction,
unrefereed); none is proved here.  Constructive side of the composite problem; not prime-case work.
No sorry, no native_decide.
-/
import Erdos634.Draft.WPgramWrap
import Erdos634.Draft.WSeedGW
import Erdos634.Draft.UniformThreshold
import Erdos634.NormalPosition

open scoped Classical
open Erdos634.Geometry Erdos634.CertCoord

namespace Erdos634.Draft.WClosedBase
open Erdos634.Draft.WFrameF Erdos634.Draft.RegionTiling Erdos634.Draft.WBrickF
open Erdos634.Draft.WPgramF Erdos634.Draft.WGridF Erdos634.Draft.WAddF Erdos634.Draft.WtoDeltaF
open Erdos634.Draft.FDBBaseBetaE1 (HasSides hasSides_rot hasSides_swap congruent_of_hasSides')
open Erdos634.Draft.UniformThreshold (BetaTilable hasSides_congr)

theorem WS_convex (u v : ℝ) : Convex ℝ (WS u v) := by
  intro x hx y hy a b ha hb hab
  obtain ⟨x1, x2, x3⟩ := hx
  obtain ⟨y1, y2, y3⟩ := hy
  have hb' : b = 1 - a := by linarith
  subst hb'
  simp only [WS, Set.mem_setOf_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul]
  refine ⟨?_, ?_, ?_⟩
  · nlinarith [mul_le_mul_of_nonneg_left x1 ha, mul_le_mul_of_nonneg_left y1 hb]
  · nlinarith [mul_le_mul_of_nonneg_left x2 ha, mul_le_mul_of_nonneg_left y2 hb]
  · nlinarith [mul_le_mul_of_nonneg_left x3 ha, mul_le_mul_of_nonneg_left y3 hb]

/-- the region `WS u v` is the triangle `(u, 0), (u, v), (0, v)` -/
theorem hull_WS (u v : ℝ) (hu : 0 < u) (hv : 0 < v) :
    convexHull ℝ {((u : ℝ), (0 : ℝ)), (u, v), (0, v)} = WS u v := by
  apply Set.Subset.antisymm
  · refine convexHull_min ?_ (WS_convex u v)
    intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl <;> simp only [WS, Set.mem_setOf_eq] <;> refine ⟨?_, ?_, ?_⟩ <;>
      nlinarith [mul_pos hu hv]
  · intro p hp
    obtain ⟨p1, p2⟩ := p
    simp only [WS, Set.mem_setOf_eq] at hp
    obtain ⟨h1, h2, h3⟩ := hp
    refine Erdos634.Draft.S2L.mem_hull3' (A := (u, 0)) (B := (u, v)) (C := (0, v)) (u * v) (u * (v - p2))
      (v * p1 + u * p2 - u * v) (v * (u - p1)) (mul_pos hu hv) (mul_nonneg hu.le (by linarith)) (by linarith)
      (mul_nonneg hv.le (by linarith)) (by ring) (p1, p2) ?_ ?_
    · simp only; ring
    · simp only; ring

/-- the triangle `W`: `Φ_F hull{(u, 0), (u, v), (0, v)}` -/
noncomputable def WTriR (F : ℝ) (hF1 : 1 < F) (u v : ℝ) (hu : 0 < u) (hv : 0 < v) : Erdos634.Geometry.Tri :=
  triC F hF1 (u, 0) (u, v) (0, v) (by
    have e : ((u : ℝ) - u) * (v - 0) - (0 - u) * (v - 0) = u * v := by ring
    intro h
    have h' : u * v = 0 := by rw [← e]; exact h
    exact (mul_pos hu hv).ne' h')

theorem carrier_WTriR (F : ℝ) (hF1 : 1 < F) (u v : ℝ) (hu : 0 < u) (hv : 0 < v) :
    (WTriR F hF1 u v hu hv).carrier = Phi F '' WS u v := by
  rw [WTriR, carrier_triC, hull_WS u v hu hv]

theorem WTriR_sq (F : ℝ) (hF1 : 1 < F) (u v : ℝ) (hu : 0 < u) (hv : 0 < v) :
    dist ((WTriR F hF1 u v hu hv).pts 0) ((WTriR F hF1 u v hu hv).pts 1) ^ 2 = v ^ 2 ∧
    dist ((WTriR F hF1 u v hu hv).pts 1) ((WTriR F hF1 u v hu hv).pts 2) ^ 2 = u ^ 2 ∧
    dist ((WTriR F hF1 u v hu hv).pts 0) ((WTriR F hF1 u v hu hv).pts 2) ^ 2 = u ^ 2 + v ^ 2 - u * v / F := by
  simp only [WTriR, triC_pts, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  refine ⟨?_, ?_, ?_⟩
  · rw [sq_Phi hF1]; simp only; ring
  · rw [sq_Phi hF1]; simp only; ring
  · rw [sq_Phi hF1]; simp only; ring

/-- **A dissection with the sides of `W_m` and of the tile gives `WClosed f m`.** -/
theorem WClosed_of_dissection (f : ℕ) (hf : 2 ≤ f) (m : ℕ) (hm : 1 ≤ m)
    (D : CongruentDissection ((2 * f ^ 2 - 1) * m ^ 2))
    (hT : HasSides D.target ((f : ℝ) * ((f : ℝ) ^ 2 - 1) * m) ((m : ℝ) * (f : ℝ) ^ 3)
      ((2 * (f : ℝ) ^ 2 - 1) * m))
    (hM : HasSides D.model (f : ℝ) ((f : ℝ) ^ 2) ((f : ℝ) ^ 2 - 1)) : WClosed f hf m := by
  have hF1 := hF f hf
  have hF0 : (f : ℝ) ≠ 0 := by positivity
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hu := mul_pos (A_pos f hf) hm0
  have hv := mul_pos (B_pos f hf) hm0
  obtain ⟨q01, q12, q02⟩ := WTriR_sq (f : ℝ) hF1 _ _ hu hv
  have d01 : dist ((WTriR (f : ℝ) hF1 _ _ hu hv).pts 0) ((WTriR (f : ℝ) hF1 _ _ hu hv).pts 1)
      = (2 * (f : ℝ) ^ 2 - 1) * m := (sq_eq_sq₀ dist_nonneg hv.le).mp q01
  have d12 : dist ((WTriR (f : ℝ) hF1 _ _ hu hv).pts 1) ((WTriR (f : ℝ) hF1 _ _ hu hv).pts 2)
      = (f : ℝ) * ((f : ℝ) ^ 2 - 1) * m := (sq_eq_sq₀ dist_nonneg hu.le).mp q12
  have d02 : dist ((WTriR (f : ℝ) hF1 _ _ hu hv).pts 0) ((WTriR (f : ℝ) hF1 _ _ hu hv).pts 2)
      = (m : ℝ) * (f : ℝ) ^ 3 := by
    refine (sq_eq_sq₀ dist_nonneg (by positivity)).mp ?_
    rw [q02]; field_simp; ring
  have hTU := congruent_of_hasSides' hT d01 d12 d02
  obtain ⟨g, D', hD'T, hD'M, -⟩ := Erdos634.NormalPosition.exists_normal_position_congruent D hTU
  obtain ⟨m1, m2, m3⟩ := Erdos634.Draft.WPgramWrap.MF_sides hF1
  have hMF : D.model.Congruent (MF (f : ℝ) hF1) := congruent_of_hasSides' hM m1 m2 m3
  exact ⟨{ tile := D'.tile
           covers := by rw [D'.covers, hD'T, carrier_WTriR, WS_eq _ _ _ hm0]
           disj := D'.interiors_disjoint
           cong := fun i => (D'.tiles_congruent i).trans (by rw [hD'M]; exact hMF) }⟩

/-- **The seed: `W_f` of the member `(1, f)`.** -/
theorem WClosed_seed (f : ℕ) (hf : 2 ≤ f) : WClosed f hf f := by
  have hN : f ^ 2 * (2 * f ^ 2 - 1 ^ 2) = (2 * f ^ 2 - 1) * f ^ 2 := by rw [one_pow, mul_comm]
  have key := Erdos634.Draft.WSeedG.w_seed 1 f le_rfl (by omega)
  rw [hN] at key
  obtain ⟨D, hT, hM⟩ := key
  refine WClosed_of_dissection f hf f (by omega) D ?_ ?_
  · exact hasSides_congr (hasSides_rot (hasSides_swap hT)) (by push_cast; ring) (by push_cast; ring)
      (by push_cast; ring)
  · exact hasSides_congr (hasSides_rot (hasSides_swap hM)) (by push_cast; ring) (by push_cast; ring)
      (by push_cast; ring)

/-- **From the scales `f + 1, …, 2f − 1` to every scale `M ≥ f`.** -/
theorem WClosed_ge (f : ℕ) (hf : 2 ≤ f) (hbase : ∀ r, 1 ≤ r → r < f → WClosed f hf (f + r)) :
    ∀ M, f ≤ M → WClosed f hf M := by
  intro M
  induction M using Nat.strong_induction_on with
  | _ M ih =>
    intro hM
    by_cases h1 : M = f
    · rw [h1]; exact WClosed_seed f hf
    by_cases h2 : M < 2 * f
    · have h := hbase (M - f) (by omega) (by omega)
      rwa [show f + (M - f) = M by omega] at h
    · have h3 := ih (M - f) (by omega) (by omega)
      have h := WClosed_add f hf (m₁ := M - f) (m₂ := f) (by omega) (by omega) h3 (WClosed_seed f hf)
      rwa [show M - f + f = M by omega] at h

/-- **`W_m` gives the base-β target at scale `m`** (member `(1, f)`), in the form of `UniformThreshold.BetaTilable`. -/
theorem betaTilable_of_WClosed (f : ℕ) (hf : 2 ≤ f) (m : ℕ) (hm : 1 ≤ m) (hW : WClosed f hf m) :
    BetaTilable 1 f m := by
  have hF1 := hF f hf
  have hF0 : (f : ℝ) ≠ 0 := by positivity
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  obtain ⟨D, hT, hM⟩ := delta_cd_of_W f hf m hm hW
  obtain ⟨m1, m2, m3⟩ := Erdos634.Draft.WPgramWrap.MF_sides hF1
  have hTs : HasSides D.target ((m : ℝ) * (f : ℝ) ^ 3) ((m : ℝ) * (f : ℝ) ^ 3) ((3 * (f : ℝ) ^ 2 - 1) * m) := by
    refine ⟨Equiv.refl _, ?_, ?_, ?_⟩
    · simp only [Equiv.refl_apply]
      rw [hT]
      simp only [DeltaTri, DTriR, triC_pts, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons]
      refine (sq_eq_sq₀ dist_nonneg (by positivity)).mp ?_
      rw [sq_Phi hF1]; simp only; field_simp; ring
    · simp only [Equiv.refl_apply]
      rw [hT]
      simp only [DeltaTri, DTriR, triC_pts, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons]
      refine (sq_eq_sq₀ dist_nonneg (by positivity)).mp ?_
      rw [sq_Phi hF1]; simp only; field_simp; ring
    · simp only [Equiv.refl_apply]
      rw [hT]
      simp only [DeltaTri, DTriR, triC_pts, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons]
      refine (sq_eq_sq₀ dist_nonneg (mul_pos (hC_pos f hf) hm0).le).mp ?_
      rw [sq_Phi hF1]; simp only; ring
  have hMs : HasSides D.model (f : ℝ) ((f : ℝ) ^ 2) ((f : ℝ) ^ 2 - 1) :=
    ⟨Equiv.refl _, by simp only [Equiv.refl_apply]; rw [hM]; exact m2,
      by simp only [Equiv.refl_apply]; rw [hM, dist_comm]; exact m3,
      by simp only [Equiv.refl_apply]; rw [hM]; exact m1⟩
  exact ⟨_, D, hasSides_congr hTs (by ring) (by ring) (by push_cast; ring),
    hasSides_congr (hasSides_rot (hasSides_swap hMs)) (by push_cast; ring) (by push_cast; ring) (by ring)⟩

/-- **Every scale `M ≥ f` of the member `(1, f)`, from `f − 1` tilings.** -/
theorem betaTilable_ge (f : ℕ) (hf : 2 ≤ f) (hbase : ∀ r, 1 ≤ r → r < f → WClosed f hf (f + r)) :
    ∀ M, f ≤ M → BetaTilable 1 f M :=
  fun M hM => betaTilable_of_WClosed f hf M (by omega) (WClosed_ge f hf hbase M hM)

/-- The same with the hypothesis in the language of dissections: for `1 ≤ r < f` the triangle with sides
`(f + r) f (f² − 1)`, `(f + r) (2f² − 1)`, `(f + r) f³` is cut into `(2f² − 1)(f + r)²` copies of `(f, f² − 1, f²)`. -/
theorem betaTilable_ge_of_dissections (f : ℕ) (hf : 2 ≤ f)
    (h : ∀ r, 1 ≤ r → r < f → ∃ D : CongruentDissection ((2 * f ^ 2 - 1) * (f + r) ^ 2),
      HasSides D.target (((f + r : ℕ) : ℝ) * ((f : ℝ) * ((f : ℝ) ^ 2 - 1))) (((f + r : ℕ) : ℝ) * (2 * (f : ℝ) ^ 2 - 1))
        (((f + r : ℕ) : ℝ) * (f : ℝ) ^ 3) ∧
      HasSides D.model (f : ℝ) ((f : ℝ) ^ 2 - 1) ((f : ℝ) ^ 2)) :
    ∀ M, f ≤ M → BetaTilable 1 f M := by
  refine betaTilable_ge f hf (fun r hr1 hr2 => ?_)
  obtain ⟨D, hT, hM⟩ := h r hr1 hr2
  refine WClosed_of_dissection f hf (f + r) (by omega) D ?_ (hasSides_rot (hasSides_swap hM))
  exact hasSides_congr (hasSides_rot (hasSides_swap hT)) (by ring) (by ring) (by ring)

/-- the member `(1, f)` at scale `f`, through the W seed (a second proof of `betaTilable_self` for `e = 1`) -/
theorem betaTilable_seed (f : ℕ) (hf : 2 ≤ f) : BetaTilable 1 f f :=
  betaTilable_of_WClosed f hf f (by omega) (WClosed_seed f hf)

end Erdos634.Draft.WClosedBase

#print axioms Erdos634.Draft.WClosedBase.WClosed_of_dissection
#print axioms Erdos634.Draft.WClosedBase.WClosed_seed
#print axioms Erdos634.Draft.WClosedBase.WClosed_ge
#print axioms Erdos634.Draft.WClosedBase.betaTilable_ge
#print axioms Erdos634.Draft.WClosedBase.betaTilable_ge_of_dissections
