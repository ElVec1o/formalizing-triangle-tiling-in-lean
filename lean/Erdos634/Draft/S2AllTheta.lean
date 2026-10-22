-- Draft/S2AllTheta.lean — S2All, generic layer: tilings of an ARBITRARY parallelogram lattice in a skew frame.
-- `Th = Φ_f ∘ Lam u w` is a homeomorphism ℝ² → Plane for any lattice vectors `u w` (det ≠ 0); the brick/strip/grid
-- constructions of `S2GFrame` (which are tied to the axes of `Φ_f`) are redone for a general homeomorphism `Th`
-- that is additive.  Used for the b × p² parallelogram of D. Paliy's five-piece layout (see `S2All`).
-- UNAUDITED.  No sorry, no native_decide.
import Erdos634.Draft.S2GFrame

open scoped Classical
set_option linter.unusedSectionVars false
open Erdos634.Geometry Erdos634.CertCoord
open Erdos634.Draft.CollarParam (Sh Rect RTiling.cast RTiling.castN interior_disj_fst interior_disj_snd Sh_Rect)

namespace Erdos634.Draft.S2AllTheta
open Erdos634.Draft.WFrameF Erdos634.Draft.RegionTiling Erdos634.Draft.S2G
open Erdos634.Draft.WBrickF (LT UT hull_LT hull_UT LT_union_UT interior_disj_lin)

/-- the lattice parametrisation `z ↦ z.1 • u + z.2 • w` of skew coordinates. -/
def Lam (u w z : ℝ × ℝ) : ℝ × ℝ := z.1 • u + z.2 • w

noncomputable def LamL (u w : ℝ × ℝ) : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) :=
  (LinearMap.fst ℝ ℝ ℝ).smulRight u + (LinearMap.snd ℝ ℝ ℝ).smulRight w

theorem LamL_apply (u w z : ℝ × ℝ) : LamL u w z = Lam u w z := rfl

theorem Lam_add (u w x y : ℝ × ℝ) : Lam u w (x + y) = Lam u w x + Lam u w y := by
  simp only [Lam, Prod.fst_add, Prod.snd_add, add_smul]; abel

noncomputable def LamInv (u w q : ℝ × ℝ) : ℝ × ℝ :=
  ((w.2 * q.1 - w.1 * q.2) / (u.1 * w.2 - u.2 * w.1), (u.1 * q.2 - u.2 * q.1) / (u.1 * w.2 - u.2 * w.1))

theorem LamInv_Lam {u w : ℝ × ℝ} (hd : u.1 * w.2 - u.2 * w.1 ≠ 0) (z : ℝ × ℝ) :
    LamInv u w (Lam u w z) = z := by
  ext <;> simp only [LamInv, Lam, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;>
    rw [div_eq_iff hd] <;> ring

theorem Lam_LamInv {u w : ℝ × ℝ} (hd : u.1 * w.2 - u.2 * w.1 ≠ 0) (q : ℝ × ℝ) :
    Lam u w (LamInv u w q) = q := by
  ext <;> simp only [LamInv, Lam, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;>
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff hd] <;> ring

theorem Lam_hull3 (u w x y z : ℝ × ℝ) :
    Lam u w '' convexHull ℝ {x, y, z} = convexHull ℝ {Lam u w x, Lam u w y, Lam u w z} := by
  have := (LamL u w).image_convexHull ({x, y, z} : Set (ℝ × ℝ))
  simp only [Set.image_insert_eq, Set.image_singleton, LamL_apply] at this
  exact_mod_cast this

/-- the lattice frame as a homeomorphism `ℝ² ≃ₜ Plane`. -/
noncomputable def ThH {f : ℝ} (hf : 1 < 4 * f ^ 2) (u w : ℝ × ℝ) (hd : u.1 * w.2 - u.2 * w.1 ≠ 0) :
    (ℝ × ℝ) ≃ₜ Plane where
  toFun z := Phi f (Lam u w z)
  invFun q := LamInv u w (Psi f q)
  left_inv z := by simp only [Psi_Phi' hf, LamInv_Lam hd]
  right_inv q := by simp only [Lam_LamInv hd, Phi_Psi' hf]
  continuous_toFun := (Phi_cont f).comp (by unfold Lam; fun_prop)
  continuous_invFun := by
    have : Continuous (LamInv u w) := by unfold LamInv; fun_prop
    exact this.comp (Psi_cont f)

theorem ThH_apply {f : ℝ} (hf : 1 < 4 * f ^ 2) (u w : ℝ × ℝ) (hd : u.1 * w.2 - u.2 * w.1 ≠ 0) (z : ℝ × ℝ) :
    ThH hf u w hd z = Phi f (Lam u w z) := rfl

theorem ThH_add {f : ℝ} (hf : 1 < 4 * f ^ 2) (u w : ℝ × ℝ) (hd : u.1 * w.2 - u.2 * w.1 ≠ 0) (x y : ℝ × ℝ) :
    ThH hf u w hd (x + y) = ThH hf u w hd x + ThH hf u w hd y := by
  simp only [ThH_apply, Lam_add, Phi_add]

theorem ThH_image {f : ℝ} (hf : 1 < 4 * f ^ 2) (u w : ℝ × ℝ) (hd : u.1 * w.2 - u.2 * w.1 ≠ 0)
    (S : Set (ℝ × ℝ)) : ThH hf u w hd '' S = Phi f '' (Lam u w '' S) := by
  rw [Set.image_image]; rfl

/-! ### generic constructions for an additive homeomorphism -/
section gen
variable (Th : (ℝ × ℝ) ≃ₜ Plane) (hadd : ∀ x y, Th (x + y) = Th x + Th y)

theorem disjT {A B : Set (ℝ × ℝ)} (h : Disjoint (interior A) (interior B)) :
    Disjoint (interior (Th '' A)) (interior (Th '' B)) := by
  rw [← Th.image_interior A, ← Th.image_interior B]
  exact (Set.disjoint_image_iff Th.injective).mpr h

include hadd in
theorem image_shiftT (v : ℝ × ℝ) (S : Set (ℝ × ℝ)) :
    (fun x : Plane => x + Th v) '' (Th '' S) = Th '' Sh v S := by
  ext x
  constructor
  · rintro ⟨_, ⟨p, hp, rfl⟩, rfl⟩
    refine ⟨p + v, ?_, by rw [hadd]⟩
    show p + v - v ∈ S; simpa using hp
  · rintro ⟨p, hp, rfl⟩
    refine ⟨Th (p - v), ⟨p - v, hp, rfl⟩, ?_⟩
    show Th (p - v) + Th v = Th p
    rw [← hadd]; simp

noncomputable def shiftT {S : Set (ℝ × ℝ)} {M : Tri} {N : ℕ} (R : RTiling (Th '' S) M N) (v : ℝ × ℝ) :
    RTiling (Th '' Sh v S) M N :=
  RTiling.cast (image_shiftT Th hadd v S)
    (Erdos634.Draft.RegionTiling.map R (IsometryEquiv.addRight (Th v)))

noncomputable def hstackT {a b e c d : ℝ} {M : Tri} {N₁ N₂ : ℕ} (hab : a ≤ b) (hbe : b ≤ e)
    (R₁ : RTiling (Th '' Rect a b c d) M N₁) (R₂ : RTiling (Th '' Rect b e c d) M N₂) :
    RTiling (Th '' Rect a e c d) M (N₁ + N₂) := by
  have hd : Disjoint (interior (Th '' Rect a b c d)) (interior (Th '' Rect b e c d)) :=
    disjT Th (interior_disj_fst b (fun p hp => hp.2.1) (fun p hp => hp.1))
  refine RTiling.cast ?_ (union R₁ R₂ hd)
  rw [← Set.image_union, Erdos634.Draft.WPgram.Rect_union_fst a b e c d hab hbe]

noncomputable def vstackT {a b c d e : ℝ} {M : Tri} {N₁ N₂ : ℕ} (hcd : c ≤ d) (hde : d ≤ e)
    (R₁ : RTiling (Th '' Rect a b c d) M N₁) (R₂ : RTiling (Th '' Rect a b d e) M N₂) :
    RTiling (Th '' Rect a b c e) M (N₁ + N₂) := by
  have hd : Disjoint (interior (Th '' Rect a b c d)) (interior (Th '' Rect a b d e)) :=
    disjT Th (interior_disj_snd d (fun p hp => hp.2.2.2) (fun p hp => hp.2.2.1))
  refine RTiling.cast ?_ (union R₁ R₂ hd)
  rw [← Set.image_union, Erdos634.Draft.WPgram.Rect_union_snd a b c d e hcd hde]

noncomputable def shift_rectT {A B : ℝ} {M : Tri} {N : ℕ} (R : RTiling (Th '' Rect 0 A 0 B) M N)
    (x y x2 y2 : ℝ) (hx : x2 = A + x) (hy : y2 = B + y) : RTiling (Th '' Rect x x2 y y2) M N := by
  have h := shiftT Th hadd R (x, y)
  rw [Sh_Rect] at h
  simp only [zero_add] at h
  subst hx hy
  exact h

variable {A B : ℝ} (hA : 0 < A) (hB : 0 < B) {M : Tri} {n : ℕ} (R : RTiling (Th '' Rect 0 A 0 B) M n)

include hA in
noncomputable def stripT : (k : ℕ) → RTiling (Th '' Rect 0 (A * ((k : ℝ) + 1)) 0 B) M (n * (k + 1))
  | 0 => RTiling.cast (by norm_num) (RTiling.castN (by norm_num) R)
  | k + 1 => by
      have s := shift_rectT Th hadd R (A * ((k : ℝ) + 1)) 0 (A * (((k + 1 : ℕ) : ℝ) + 1)) B
        (by push_cast; ring) (by norm_num)
      have h := hstackT Th (by positivity)
        (by push_cast; nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]) (stripT k) s
      exact RTiling.castN (by ring) h

include hA hB in
noncomputable def gridT (k : ℕ) : (l : ℕ) →
    RTiling (Th '' Rect 0 (A * ((k : ℝ) + 1)) 0 (B * ((l : ℝ) + 1))) M (n * (k + 1) * (l + 1))
  | 0 => RTiling.cast (by norm_num) (RTiling.castN (by ring) (stripT Th hadd hA R k))
  | l + 1 => by
      have s := shift_rectT Th hadd (stripT Th hadd hA R k) 0 (B * ((l : ℝ) + 1))
        (A * ((k : ℝ) + 1) + 0) (B * (((l + 1 : ℕ) : ℝ) + 1)) (by ring) (by push_cast; ring)
      simp only [add_zero] at s
      have h := vstackT Th (by positivity)
        (by push_cast; nlinarith [(Nat.cast_nonneg l : (0 : ℝ) ≤ l)])
        (gridT k l) s
      exact RTiling.castN (by ring) h
end gen

/-! ### the cell: the parallelogram `Lam [0,1]²`, cut along the diagonal `u + w` into two triangles -/
section cell
variable {f : ℝ} (hf : 1 < 4 * f ^ 2) (u w : ℝ × ℝ) (hd : u.1 * w.2 - u.2 * w.1 ≠ 0)

include hd in
theorem det_TL : ((0 : ℝ × ℝ).1 - (u + w).1) * (u.2 - (u + w).2) - (u.1 - (u + w).1) * ((0 : ℝ × ℝ).2 - (u + w).2)
    ≠ 0 := by
  intro h; apply hd; simp only [Prod.fst_add, Prod.snd_add, Prod.fst_zero, Prod.snd_zero] at h; linarith

include hd in
theorem det_TU : ((u + w).1 - (0 : ℝ × ℝ).1) * (w.2 - (0 : ℝ × ℝ).2) - (w.1 - (0 : ℝ × ℝ).1) * ((u + w).2 - (0 : ℝ × ℝ).2)
    ≠ 0 := by
  intro h; apply hd; simp only [Prod.fst_add, Prod.snd_add, Prod.fst_zero, Prod.snd_zero] at h; linarith

/-- lower half of the cell, vertices `u + w, 0, u`. -/
noncomputable def TL : Tri := triC f hf (u + w) 0 u (det_TL u w hd)
/-- upper half of the cell, vertices `0, u + w, w`. -/
noncomputable def TU : Tri := triC f hf 0 (u + w) w (det_TU u w hd)

theorem carrier_TL : (TL hf u w hd).carrier = ThH hf u w hd '' LT 1 1 := by
  rw [TL, carrier_triC, ThH_image, ← hull_LT 1 1 one_pos one_pos, Lam_hull3]
  congr 2
  ext x
  simp only [Lam, Set.mem_insert_iff, Set.mem_singleton_iff, one_smul, zero_smul, add_zero, zero_add]
  constructor <;> intro h <;> rcases h with h | h | h <;> simp [h]

theorem carrier_TU : (TU hf u w hd).carrier = ThH hf u w hd '' UT 1 1 := by
  rw [TU, carrier_triC, ThH_image, ← hull_UT 1 1 one_pos one_pos, Lam_hull3]
  congr 2
  ext x
  simp only [Lam, Set.mem_insert_iff, Set.mem_singleton_iff, one_smul, zero_smul, add_zero, zero_add]
  constructor <;> intro h <;> rcases h with h | h | h <;> simp [h]

theorem disj_LU1 : Disjoint (interior (LT 1 1)) (interior (UT 1 1)) :=
  interior_disj_lin (-1) 1 0 (by norm_num)
    (by rintro p ⟨_, _, _, h⟩; linarith) (by rintro p ⟨_, _, _, h⟩; linarith)

/-- the cell is tiled by its two halves, if both are congruent to `M`. -/
noncomputable def cellRT (M : Tri) (c1 : (TL hf u w hd).Congruent M) (c2 : (TU hf u w hd).Congruent M) :
    RTiling (ThH hf u w hd '' Rect 0 1 0 1) M 2 where
  tile := ![TL hf u w hd, TU hf u w hd]
  covers := by
    rw [← LT_union_UT 1 1 one_pos one_pos, Set.image_union]
    ext x
    simp only [Set.mem_iUnion, Set.mem_union]
    constructor
    · rintro ⟨i, hi⟩
      fin_cases i
      · left; simpa [carrier_TL] using hi
      · right; simpa [carrier_TU] using hi
    · rintro (h | h)
      · exact ⟨0, by simpa [carrier_TL] using h⟩
      · exact ⟨1, by simpa [carrier_TU] using h⟩
  disj := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · simpa [carrier_TL, carrier_TU] using disjT (ThH hf u w hd) disj_LU1
    · simpa [carrier_TL, carrier_TU] using (disjT (ThH hf u w hd) disj_LU1).symm
    · exact absurd rfl hij
  cong := by
    intro i; fin_cases i
    · exact c1
    · exact c2

/-- SSS for triangles given in skew coordinates: equal skew-quadratic side lengths. -/
theorem triC_cong (a b c a' b' c' : ℝ × ℝ) (h h')
    (e01 : (a.1 - b.1) ^ 2 + (a.2 - b.2) ^ 2 + (a.1 - b.1) * (a.2 - b.2) / f
      = (a'.1 - b'.1) ^ 2 + (a'.2 - b'.2) ^ 2 + (a'.1 - b'.1) * (a'.2 - b'.2) / f)
    (e12 : (b.1 - c.1) ^ 2 + (b.2 - c.2) ^ 2 + (b.1 - c.1) * (b.2 - c.2) / f
      = (b'.1 - c'.1) ^ 2 + (b'.2 - c'.2) ^ 2 + (b'.1 - c'.1) * (b'.2 - c'.2) / f)
    (e20 : (c.1 - a.1) ^ 2 + (c.2 - a.2) ^ 2 + (c.1 - a.1) * (c.2 - a.2) / f
      = (c'.1 - a'.1) ^ 2 + (c'.2 - a'.2) ^ 2 + (c'.1 - a'.1) * (c'.2 - a'.2) / f) :
    (triC f hf a b c h).Congruent (triC f hf a' b' c' h') := by
  refine Erdos634.SssCongruent.congruent_of_dist_three ?_ ?_ ?_ <;> simp only [triC_pts] <;>
    (refine dPhi' _ _ _ _ ?_; rw [sq_Phi' hf, sq_Phi' hf])
  · exact e01
  · exact e12
  · exact e20
end cell

end Erdos634.Draft.S2AllTheta

#print axioms Erdos634.Draft.S2AllTheta.gridT
#print axioms Erdos634.Draft.S2AllTheta.cellRT
#print axioms Erdos634.Draft.S2AllTheta.triC_cong
