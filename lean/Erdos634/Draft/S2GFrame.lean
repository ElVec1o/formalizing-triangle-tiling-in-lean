-- Draft/S2GFrame.lean — S2G: skew frame / brick / grid / scaled triangle / SSS for the general-f frame with the
-- hypothesis `1 < 4 f^2` (so f may be NEGATIVE), copied and relaxed from WFrameF / WBrickF / BrickGridF / S2LCore.
-- UNAUDITED.  NOT imported into All.lean.  New file; no existing file edited.  No sorry, no native_decide.
-- Reused unchanged (no f-hypothesis): WFrameF.{sD,g1,g2,Phi,Phi_apply0,Phi_apply1,Phi_add,image_shift,shiftR},
--   WBrickF.{interior_disj_lin,det_Phi,mkPt_Phi,PhiL,LT,UT,hull_LT,hull_UT,LT_union_UT}, S2L.{tri_*,hull_*,mem_hull3',rect_subset,pack_exists,Phi_scale,Phi_lin}.
import Erdos634.Draft.S2LCore

open scoped Classical
open Erdos634.Geometry Erdos634.CertCoord
open Erdos634.Draft.CollarParam (Sh Tset Rect RTiling.cast RTiling.castN Sh_Rect interior_disj_fst interior_disj_snd)

namespace Erdos634.Draft.S2G
open Erdos634.Draft.WFrameF Erdos634.Draft.RegionTiling Erdos634.Draft.WBrickF

theorem f_ne {f : ℝ} (hf : 1 < 4 * f ^ 2) : f ≠ 0 := by
  rintro rfl; norm_num at hf

theorem sD_pos' {f : ℝ} (hf : 1 < 4 * f ^ 2) : 0 < sD f := by
  unfold sD; exact Real.sqrt_pos.mpr (by linarith)

theorem sD_sq' {f : ℝ} (hf : 1 < 4 * f ^ 2) : sD f ^ 2 = 4 * f ^ 2 - 1 := by
  unfold sD; rw [Real.sq_sqrt]; linarith

theorem Psi_Phi' {f : ℝ} (hf : 1 < 4 * f ^ 2) (p : ℝ × ℝ) : Psi f (Phi f p) = p := by
  have h := (sD_pos' hf).ne'
  have h2 : f ≠ 0 := f_ne hf
  ext
  · simp only [Psi, Phi_apply0, Phi_apply1]; field_simp; ring
  · simp only [Psi, Phi_apply1]; field_simp

theorem Phi_Psi' {f : ℝ} (hf : 1 < 4 * f ^ 2) (q : Plane) : Phi f (Psi f q) = q := by
  have h := (sD_pos' hf).ne'
  have h2 : f ≠ 0 := f_ne hf
  ext i
  fin_cases i
  · show Phi f (Psi f q) 0 = q 0
    rw [Phi_apply0]; simp only [Psi]; field_simp; ring
  · show Phi f (Psi f q) 1 = q 1
    rw [Phi_apply1]; simp only [Psi]; field_simp

noncomputable def PhiH' {f : ℝ} (hf : 1 < 4 * f ^ 2) : (ℝ × ℝ) ≃ₜ Plane where
  toFun := Phi f
  invFun := Psi f
  left_inv := Psi_Phi' hf
  right_inv := Phi_Psi' hf
  continuous_toFun := Phi_cont f
  continuous_invFun := Psi_cont f

theorem interior_image' {f : ℝ} (hf : 1 < 4 * f ^ 2) (S : Set (ℝ × ℝ)) :
    interior (Phi f '' S) = Phi f '' interior S :=
  ((PhiH' hf).image_interior S).symm

theorem disjoint_image' {f : ℝ} (hf : 1 < 4 * f ^ 2) {A B : Set (ℝ × ℝ)}
    (h : Disjoint (interior A) (interior B)) :
    Disjoint (interior (Phi f '' A)) (interior (Phi f '' B)) := by
  rw [interior_image' hf, interior_image' hf]
  exact (Set.disjoint_image_iff (PhiH' hf).injective).mpr h

theorem sq_Phi' {f : ℝ} (hf : 1 < 4 * f ^ 2) (a b : ℝ × ℝ) :
    dist (Phi f a) (Phi f b) ^ 2
      = (a.1 - b.1) ^ 2 + (a.2 - b.2) ^ 2 + (a.1 - b.1) * (a.2 - b.2) / f := by
  have e : ∀ c : ℝ × ℝ, Phi f c = mkPt (c.1 + c.2 / (2 * f)) (c.2 * (sD f / (2 * f))) :=
    fun c => by ext i; fin_cases i <;> simp [Phi_apply0, Phi_apply1]
  rw [e a, e b, dist_sq_mkPt]
  have h := sD_sq' hf
  have h2 : f ≠ 0 := f_ne hf
  field_simp
  ring_nf
  rw [h]; ring

/-- The triangle with skew-coordinate vertices `a b c` (frame parameter `f`, `1 < 4 f²`). -/
noncomputable def triC (f : ℝ) (hf : 1 < 4 * f ^ 2) (a b c : ℝ × ℝ)
    (h : (b.1 - a.1) * (c.2 - a.2) - (c.1 - a.1) * (b.2 - a.2) ≠ 0) : Tri :=
  mkTri (Phi f a 0) (Phi f a 1) (Phi f b 0) (Phi f b 1) (Phi f c 0) (Phi f c 1) (by
    rw [det_Phi]
    exact mul_ne_zero (div_ne_zero (sD_pos' hf).ne' (mul_ne_zero two_ne_zero (f_ne hf))) h)

theorem triC_pts (f : ℝ) (hf : 1 < 4 * f ^ 2) (a b c : ℝ × ℝ) (h) :
    (triC f hf a b c h).pts = ![Phi f a, Phi f b, Phi f c] := by
  simp only [triC, mkTri_pts, mkPt_Phi]

theorem carrier_triC (f : ℝ) (hf : 1 < 4 * f ^ 2) (a b c : ℝ × ℝ) (h) :
    (triC f hf a b c h).carrier = Phi f '' convexHull ℝ {a, b, c} := by
  have : Set.range (triC f hf a b c h).pts = Phi f '' {a, b, c} := by
    rw [triC_pts]
    ext x
    simp only [Set.mem_range, Set.image_insert_eq, Set.image_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    constructor
    · rintro ⟨k, rfl⟩; fin_cases k <;> simp
    · rintro (rfl | rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
  rw [Tri.carrier, this]
  have := (PhiL f).image_convexHull ({a, b, c} : Set (ℝ × ℝ))
  simp only [PhiL_eq] at this
  rw [← this]

noncomputable def brickL (f : ℝ) (hf : 1 < 4 * f ^ 2) (A B : ℝ) (hA : 0 < A) (hB : 0 < B) : Tri :=
  triC f hf (0, 0) (A, 0) (A, B) (by intro h; nlinarith [mul_pos hA hB])

noncomputable def brickU (f : ℝ) (hf : 1 < 4 * f ^ 2) (A B : ℝ) (hA : 0 < A) (hB : 0 < B) : Tri :=
  triC f hf (0, 0) (0, B) (A, B) (by intro h; nlinarith [mul_pos hA hB])

theorem carrier_brickL (f : ℝ) (hf : 1 < 4 * f ^ 2) (A B : ℝ) (hA : 0 < A) (hB : 0 < B) :
    (brickL f hf A B hA hB).carrier = Phi f '' LT A B := by
  rw [brickL, carrier_triC, hull_LT A B hA hB]

theorem carrier_brickU (f : ℝ) (hf : 1 < 4 * f ^ 2) (A B : ℝ) (hA : 0 < A) (hB : 0 < B) :
    (brickU f hf A B hA hB).carrier = Phi f '' UT A B := by
  rw [brickU, carrier_triC, hull_UT A B hA hB]

theorem disj_LU (f : ℝ) (hf : 1 < 4 * f ^ 2) (A B : ℝ) (hA : 0 < A) (hB : 0 < B) :
    Disjoint (interior (Phi f '' LT A B)) (interior (Phi f '' UT A B)) :=
  disjoint_image' hf (interior_disj_lin (-B) A 0 (by linarith)
    (by rintro p ⟨_, _, _, h⟩; linarith) (by rintro p ⟨_, _, _, h⟩; linarith))

noncomputable def brick_rt (f : ℝ) (hf : 1 < 4 * f ^ 2) (A B : ℝ) (hA : 0 < A) (hB : 0 < B) (M : Tri)
    (c1 : (brickL f hf A B hA hB).Congruent M) (c2 : (brickU f hf A B hA hB).Congruent M) :
    RTiling (Phi f '' Rect 0 A 0 B) M 2 where
  tile := ![brickL f hf A B hA hB, brickU f hf A B hA hB]
  covers := by
    rw [← LT_union_UT A B hA hB, Set.image_union]
    ext x
    simp only [Set.mem_iUnion, Set.mem_union]
    constructor
    · rintro ⟨i, hi⟩
      fin_cases i
      · left; simpa [carrier_brickL] using hi
      · right; simpa [carrier_brickU] using hi
    · rintro (h | h)
      · exact ⟨0, by simpa [carrier_brickL] using h⟩
      · exact ⟨1, by simpa [carrier_brickU] using h⟩
  disj := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · simpa [carrier_brickL, carrier_brickU] using disj_LU f hf A B hA hB
    · simpa [carrier_brickL, carrier_brickU] using (disj_LU f hf A B hA hB).symm
    · exact absurd rfl hij
  cong := by
    intro i; fin_cases i
    · exact c1
    · exact c2

/-- relaxed `dPhi`. -/
theorem dPhi' {f : ℝ} (a b c d : ℝ × ℝ)
    (h : dist (Phi f a) (Phi f b) ^ 2 = dist (Phi f c) (Phi f d) ^ 2) :
    dist (Phi f a) (Phi f b) = dist (Phi f c) (Phi f d) :=
  Erdos634.Draft.SumTwoSquares.eqsq dist_nonneg dist_nonneg h

/-- The upper half of the `(A,B)` cell is congruent to its lower half (always: SSS after swap 0<->2). -/
theorem cong_U_cell {f : ℝ} (hf : 1 < 4 * f ^ 2) (A B : ℝ) (hA : 0 < A) (hB : 0 < B) :
    (brickU f hf A B hA hB).Congruent (brickL f hf A B hA hB) := by
  have h0 : f ≠ 0 := f_ne hf
  refine ((brickU f hf A B hA hB).congruent_relabel (Equiv.swap (0 : Fin 3) 2)).trans ?_
  refine Erdos634.SssCongruent.congruent_of_dist_three ?_ ?_ ?_ <;>
    simp only [Tri.relabel, brickL, brickU, triC_pts] <;>
    (refine dPhi' _ _ _ _ ?_; rw [sq_Phi' hf, sq_Phi' hf]; field_simp; ring)

/-! ### grid -/

noncomputable def hstack {f : ℝ} (hf : 1 < 4 * f ^ 2) {a b e c d : ℝ} {M : Tri} {N₁ N₂ : ℕ}
    (hab : a ≤ b) (hbe : b ≤ e)
    (R₁ : RTiling (Phi f '' Rect a b c d) M N₁) (R₂ : RTiling (Phi f '' Rect b e c d) M N₂) :
    RTiling (Phi f '' Rect a e c d) M (N₁ + N₂) := by
  have hd : Disjoint (interior (Phi f '' Rect a b c d)) (interior (Phi f '' Rect b e c d)) :=
    disjoint_image' hf (interior_disj_fst b (fun p hp => hp.2.1) (fun p hp => hp.1))
  refine RTiling.cast ?_ (union R₁ R₂ hd)
  rw [← Set.image_union, Erdos634.Draft.WPgram.Rect_union_fst a b e c d hab hbe]

noncomputable def vstack {f : ℝ} (hf : 1 < 4 * f ^ 2) {a b c d e : ℝ} {M : Tri} {N₁ N₂ : ℕ}
    (hcd : c ≤ d) (hde : d ≤ e)
    (R₁ : RTiling (Phi f '' Rect a b c d) M N₁) (R₂ : RTiling (Phi f '' Rect a b d e) M N₂) :
    RTiling (Phi f '' Rect a b c e) M (N₁ + N₂) := by
  have hd : Disjoint (interior (Phi f '' Rect a b c d)) (interior (Phi f '' Rect a b d e)) :=
    disjoint_image' hf (interior_disj_snd d (fun p hp => hp.2.2.2) (fun p hp => hp.2.2.1))
  refine RTiling.cast ?_ (union R₁ R₂ hd)
  rw [← Set.image_union, Erdos634.Draft.WPgram.Rect_union_snd a b c d e hcd hde]

open Erdos634.Draft.BrickGridF (shift_rect)

section gridsec
variable {f : ℝ} (hf : 1 < 4 * f ^ 2) {A B : ℝ} (hA : 0 < A) (hB : 0 < B) {M : Tri} {n : ℕ}
  (R : RTiling (Phi f '' Rect 0 A 0 B) M n)

include hf hA in
noncomputable def strip : (k : ℕ) → RTiling (Phi f '' Rect 0 (A * ((k : ℝ) + 1)) 0 B) M (n * (k + 1))
  | 0 => RTiling.cast (by norm_num) (RTiling.castN (by norm_num) R)
  | k + 1 => by
      have s := shift_rect R (A * ((k : ℝ) + 1)) 0 (A * (((k + 1 : ℕ) : ℝ) + 1)) B
        (by push_cast; ring) (by norm_num)
      have h := hstack hf (by positivity)
        (by push_cast; nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]) (strip k) s
      exact RTiling.castN (by ring) h

include hf hA hB in
noncomputable def grid (k : ℕ) : (l : ℕ) →
    RTiling (Phi f '' Rect 0 (A * ((k : ℝ) + 1)) 0 (B * ((l : ℝ) + 1))) M (n * (k + 1) * (l + 1))
  | 0 => RTiling.cast (by norm_num) (RTiling.castN (by ring) (strip hf hA R k))
  | l + 1 => by
      have s := shift_rect (strip hf hA R k) 0 (B * ((l : ℝ) + 1)) (A * ((k : ℝ) + 1) + 0)
        (B * (((l + 1 : ℕ) : ℝ) + 1)) (by ring) (by push_cast; ring)
      simp only [add_zero] at s
      have h := vstack hf (by positivity)
        (by push_cast; nlinarith [(Nat.cast_nonneg l : (0 : ℝ) ≤ l)])
        (grid k l) s
      exact RTiling.castN (by ring) h
end gridsec

/-! ### scaled triangle, volume, SSS -/

open Erdos634.Draft.S2L (tri_eq_of_pts Phi_scale)

noncomputable def baseTri (f : ℝ) (hf : 1 < 4 * f ^ 2) (a V1 V2 : ℝ × ℝ) (k : ℕ) (hk : 0 < k)
    (h : (V1.1 - a.1) * (V2.2 - a.2) - (V2.1 - a.1) * (V1.2 - a.2) ≠ 0) : Tri :=
  triC f hf a (a + (1 / (k : ℝ)) • (V1 - a)) (a + (1 / (k : ℝ)) • (V2 - a)) (by
    have hk' : (0 : ℝ) < k := by exact_mod_cast hk
    intro hh
    apply h
    have e : ((a + (1 / (k : ℝ)) • (V1 - a)).1 - a.1) * ((a + (1 / (k : ℝ)) • (V2 - a)).2 - a.2)
        - ((a + (1 / (k : ℝ)) • (V2 - a)).1 - a.1) * ((a + (1 / (k : ℝ)) • (V1 - a)).2 - a.2)
        = (1 / (k : ℝ)) ^ 2 * ((V1.1 - a.1) * (V2.2 - a.2) - (V2.1 - a.1) * (V1.2 - a.2)) := by
      simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
        Prod.fst_sub, Prod.snd_sub]
      ring
    rw [e] at hh
    rcases mul_eq_zero.mp hh with h0 | h0
    · exfalso; have : (1 / (k : ℝ)) ≠ 0 := by positivity
      exact this (pow_eq_zero_iff (two_ne_zero) |>.mp h0)
    · exact h0)

noncomputable def scaledRT (f : ℝ) (hf : 1 < 4 * f ^ 2) (a V1 V2 : ℝ × ℝ) (k : ℕ) (hk : 0 < k)
    (h : (V1.1 - a.1) * (V2.2 - a.2) - (V2.1 - a.1) * (V1.2 - a.2) ≠ 0) (M : Tri)
    (hc : (baseTri f hf a V1 V2 k hk h).Congruent M) :
    RTiling (Phi f '' convexHull ℝ {a, V1, V2}) M (k * k) := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hind : AffineIndependent ℝ ![Phi f a, Phi f (a + (1 / (k : ℝ)) • (V1 - a)),
      Phi f (a + (1 / (k : ℝ)) • (V2 - a))] := by
    have := (baseTri f hf a V1 V2 k hk h).indep
    simpa only [baseTri, triC_pts] using this
  have hbase : (⟨![Phi f a, Phi f (a + (1 / (k : ℝ)) • (V1 - a)),
      Phi f (a + (1 / (k : ℝ)) • (V2 - a))], hind⟩ : Tri) = baseTri f hf a V1 V2 k hk h :=
    tri_eq_of_pts (by simp only [baseTri, triC_pts])
  have hbig : Erdos634.Subdivision.bigTri _ _ _ hind k hk = triC f hf a V1 V2 h := by
    apply tri_eq_of_pts
    rw [triC_pts]
    funext i
    fin_cases i
    · rfl
    · show (Erdos634.Subdivision.bigTri _ _ _ hind k hk).pts 1 = Phi f V1
      rw [Erdos634.Subdivision.bigTri_pts1]
      unfold Erdos634.Subdivision.P
      simp only [Nat.cast_zero, zero_smul, add_zero]
      exact Phi_scale f a V1 k hk'
    · show (Erdos634.Subdivision.bigTri _ _ _ hind k hk).pts 2 = Phi f V2
      rw [Erdos634.Subdivision.bigTri_pts2]
      unfold Erdos634.Subdivision.P
      simp only [Nat.cast_zero, zero_smul, add_zero]
      exact Phi_scale f a V2 k hk'
  set LD := Erdos634.Subdivision.ladderDissection _ _ _ hind k hk with hLD
  have hcar : LD.target.carrier = Phi f '' convexHull ℝ {a, V1, V2} := by
    show (Erdos634.Subdivision.bigTri _ _ _ hind k hk).carrier = _
    rw [hbig, carrier_triC]
  exact {
    tile := LD.tile
    covers := LD.covers.trans hcar
    disj := LD.interiors_disjoint
    cong := fun n => ((Erdos634.Subdivision.ladderDissection_congruent _ _ _ hind k hk n).symm).trans
      (by rw [hbase]; exact hc) }

theorem det_triC (f : ℝ) (hf : 1 < 4 * f ^ 2) (a b c : ℝ × ℝ) (h) :
    Erdos634.AreaDet.detTri (triC f hf a b c h)
      = (sD f / (2 * f)) * ((b.1 - a.1) * (c.2 - a.2) - (c.1 - a.1) * (b.2 - a.2)) := by
  rw [Erdos634.AreaDet.detTri_eq, triC_pts, ← det_Phi f a b c]
  simp [det3]

open MeasureTheory in
theorem vol_triC (f : ℝ) (hf : 1 < 4 * f ^ 2) (a b c : ℝ × ℝ) (h) :
    volume (triC f hf a b c h).carrier
      = ENNReal.ofReal |(sD f / (2 * f)) * ((b.1 - a.1) * (c.2 - a.2) - (c.1 - a.1) * (b.2 - a.2))|
        * volume Erdos634.AreaDet.stdCarrier := by
  rw [Erdos634.AreaDet.volume_eq_det_mul, det_triC]

/-- **SSS for the base tile (general frame).**  Model = the lower cell half `brickL f hf c b` (edges `c, b, a` on `01, 12, 20`
with `c² + b² + c b / f = a²`).  If the three skew-quadratic side lengths of `a0,V1,V2` are `k` times `c, b, a`,
the base tile `a0, a0+(V1-a0)/k, a0+(V2-a0)/k` is congruent to the model. -/
theorem baseTri_cong (f : ℝ) (hf : 1 < 4 * f ^ 2) (c b a2 : ℝ) (hc : 0 < c) (hb : 0 < b)
    (hab : c ^ 2 + b ^ 2 + c * b / f = a2)
    (a0 V1 V2 : ℝ × ℝ) (k : ℕ) (hk : 0 < k) (h)
    (H01 : (V1.1 - a0.1) ^ 2 + (V1.2 - a0.2) ^ 2 + (V1.1 - a0.1) * (V1.2 - a0.2) / f
      = ((k : ℝ) * c) ^ 2)
    (H12 : (V2.1 - V1.1) ^ 2 + (V2.2 - V1.2) ^ 2 + (V2.1 - V1.1) * (V2.2 - V1.2) / f
      = ((k : ℝ) * b) ^ 2)
    (H20 : (V2.1 - a0.1) ^ 2 + (V2.2 - a0.2) ^ 2 + (V2.1 - a0.1) * (V2.2 - a0.2) / f
      = (k : ℝ) ^ 2 * a2) :
    (baseTri f hf a0 V1 V2 k hk h).Congruent (brickL f hf c b hc hb) := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hf0 : f ≠ 0 := f_ne hf
  have hk0 : (k : ℝ) ≠ 0 := hk'.ne'
  have H01' : (1 / (k : ℝ)) ^ 2 * ((V1.1 - a0.1) ^ 2 + (V1.2 - a0.2) ^ 2 + (V1.1 - a0.1) * (V1.2 - a0.2) / f)
      = c ^ 2 := by rw [H01]; field_simp
  have H12' : (1 / (k : ℝ)) ^ 2 * ((V2.1 - V1.1) ^ 2 + (V2.2 - V1.2) ^ 2 + (V2.1 - V1.1) * (V2.2 - V1.2) / f)
      = b ^ 2 := by rw [H12]; field_simp
  have H20' : (1 / (k : ℝ)) ^ 2 * ((V2.1 - a0.1) ^ 2 + (V2.2 - a0.2) ^ 2 + (V2.1 - a0.1) * (V2.2 - a0.2) / f)
      = a2 := by rw [H20]; field_simp
  refine Erdos634.SssCongruent.congruent_of_dist_three ?_ ?_ ?_ <;>
    simp only [baseTri, brickL, triC_pts] <;>
    (refine dPhi' _ _ _ _ ?_; rw [sq_Phi' hf, sq_Phi' hf])
  · simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
      Prod.fst_sub, Prod.snd_sub]
    linear_combination H01'
  · simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
      Prod.fst_sub, Prod.snd_sub]
    linear_combination H12'
  · simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
      Prod.fst_sub, Prod.snd_sub]
    linear_combination H20' - hab

end Erdos634.Draft.S2G

#print axioms Erdos634.Draft.S2G.scaledRT
#print axioms Erdos634.Draft.S2G.baseTri_cong
#print axioms Erdos634.Draft.S2G.grid
#print axioms Erdos634.Draft.S2G.vol_triC
