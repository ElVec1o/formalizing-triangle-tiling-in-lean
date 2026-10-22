-- Draft/S2LCore.lean — S2L (S2 family N=(2q²-1)(3q²-1)), generic layer.  UNAUDITED.  Imported directly by All.lean (stale "NOT imported" header corrected 2026-10-04).
--
-- WHAT THIS FILE PROVES (no sorry, no native_decide; axioms printed at the foot):
--   * `hull_le`, `mem_hull3`, `rect_subset`: half-plane bounds on a convex hull, membership of a
--     point in a triangle hull from explicit barycentric weights, a rectangle in a convex set.
--   * `scaledRT`: for a scale-`k` triangle `a,V1,V2` in the skew frame `Φ_f` whose base tile
--     `a, a+(V1-a)/k, a+(V2-a)/k` is congruent to the model `M`, a `k*k`-tile `RTiling` of `Φ_f '' hull{a,V1,V2}`
--     (this is `Subdivision.ladderDissection`, i.e. the tile-scaling half of thm:ladder, in skew coordinates).
--   * `pack_exists`: a finite family of region tilings with pairwise interior-disjoint regions, all inside a
--     target triangle T, with total tile count N and `N * vol(M) = vol(T)`, gives a `CongruentDissection N`
--     of T (covering from `ConvexCover.ofCertificate`, a measure argument — no region-equality needed).
--   * `vol_triC`: `vol(triC a b c) = ofReal |sD/(2f) * cross| * vol(std)`.
import Erdos634.Draft.BrickGridF
import Erdos634.CellCoord
import Erdos634.AreaDet
import Erdos634.CongruentArea
import Erdos634.Ladder
import Erdos634.ConvexCover

open scoped Classical
open Erdos634.Geometry Erdos634.CertCoord
open Erdos634.Draft.CollarParam (Sh Rect RTiling.cast RTiling.castN interior_disj_fst interior_disj_snd)

namespace Erdos634.Draft.S2L
open Erdos634.Draft.WFrameF Erdos634.Draft.RegionTiling Erdos634.Draft.WBrickF

theorem hull_le {S : Set (ℝ × ℝ)} (a b c : ℝ) (h : ∀ v ∈ S, a * v.1 + b * v.2 ≤ c) :
    ∀ p ∈ convexHull ℝ S, a * p.1 + b * p.2 ≤ c := by
  have hconv : Convex ℝ {p : ℝ × ℝ | a * p.1 + b * p.2 ≤ c} := by
    intro x hx y hy s t hs ht hst
    simp only [Set.mem_setOf_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul] at *
    have hc' : s * c + t * c = c := by rw [← add_mul, hst, one_mul]
    nlinarith [mul_le_mul_of_nonneg_left hx hs, mul_le_mul_of_nonneg_left hy ht]
  exact fun p hp => convexHull_min (fun v hv => h v hv) hconv hp

theorem hull_ge {S : Set (ℝ × ℝ)} (a b c : ℝ) (h : ∀ v ∈ S, c ≤ a * v.1 + b * v.2) :
    ∀ p ∈ convexHull ℝ S, c ≤ a * p.1 + b * p.2 := by
  intro p hp
  have := hull_le (S := S) (-a) (-b) (-c) (fun v hv => by linarith [h v hv]) p hp
  linarith

theorem mem_hull3 {A B C : ℝ × ℝ} (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (hs : x + y + z = 1) (p : ℝ × ℝ) (hp1 : p.1 = x * A.1 + y * B.1 + z * C.1)
    (hp2 : p.2 = x * A.2 + y * B.2 + z * C.2) :
    p ∈ convexHull ℝ ({A, B, C} : Set (ℝ × ℝ)) := by
  have hc := convex_convexHull ℝ ({A, B, C} : Set (ℝ × ℝ))
  have := hc.sum_mem (t := (Finset.univ : Finset (Fin 3))) (w := ![x, y, z])
    (z := ![A, B, C])
    (by intro i _; fin_cases i <;> simp [hx, hy, hz])
    (by simp [Fin.sum_univ_three, hs])
    (by intro i _; fin_cases i <;> exact subset_convexHull ℝ _ (by simp))
  convert this using 1
  ext <;> simp [Fin.sum_univ_three, hp1, hp2]

/-- Barycentric membership with common denominator `D > 0`: no division in the hypotheses. -/
theorem mem_hull3' {A B C : ℝ × ℝ} (D x y z : ℝ) (hD : 0 < D) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (hs : x + y + z = D) (p : ℝ × ℝ) (hp1 : D * p.1 = x * A.1 + y * B.1 + z * C.1)
    (hp2 : D * p.2 = x * A.2 + y * B.2 + z * C.2) :
    p ∈ convexHull ℝ ({A, B, C} : Set (ℝ × ℝ)) := by
  refine mem_hull3 (x / D) (y / D) (z / D) (by positivity) (by positivity) (by positivity)
    (by rw [← add_div, ← add_div, hs, div_self hD.ne']) p ?_ ?_
  · field_simp; linarith
  · field_simp; linarith

theorem rect_subset {K : Set (ℝ × ℝ)} (hK : Convex ℝ K) {x0 x1 y0 y1 : ℝ} (h0 : x0 < x1)
    (h1 : y0 < y1) (c00 : (x0, y0) ∈ K) (c10 : (x1, y0) ∈ K) (c01 : (x0, y1) ∈ K)
    (c11 : (x1, y1) ∈ K) : Rect x0 x1 y0 y1 ⊆ K := by
  rintro p ⟨a, b, c, d⟩
  set u := (p.1 - x0) / (x1 - x0) with hu
  set v := (p.2 - y0) / (y1 - y0) with hv
  have hx : 0 < x1 - x0 := by linarith
  have hy : 0 < y1 - y0 := by linarith
  have hu0 : 0 ≤ u := div_nonneg (by linarith) hx.le
  have hu1 : u ≤ 1 := by rw [hu, div_le_one hx]; linarith
  have hv0 : 0 ≤ v := div_nonneg (by linarith) hy.le
  have hv1 : v ≤ 1 := by rw [hv, div_le_one hy]; linarith
  have eb := hK c00 c10 (by linarith : 0 ≤ 1 - u) hu0 (by ring)
  have et := hK c01 c11 (by linarith : 0 ≤ 1 - u) hu0 (by ring)
  have := hK eb et (by linarith : 0 ≤ 1 - v) hv0 (by ring)
  convert this using 1
  ext
  · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul, hu]
    field_simp; ring
  · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul, hv]
    field_simp; ring

theorem tri_le {A B C : ℝ × ℝ} (a b c : ℝ) (hA : a * A.1 + b * A.2 ≤ c) (hB : a * B.1 + b * B.2 ≤ c)
    (hC : a * C.1 + b * C.2 ≤ c) : ∀ p ∈ convexHull ℝ ({A, B, C} : Set (ℝ × ℝ)), a * p.1 + b * p.2 ≤ c :=
  hull_le a b c (by
    intro v hv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    rcases hv with rfl | rfl | rfl <;> assumption)

theorem tri_ge {A B C : ℝ × ℝ} (a b c : ℝ) (hA : c ≤ a * A.1 + b * A.2) (hB : c ≤ a * B.1 + b * B.2)
    (hC : c ≤ a * C.1 + b * C.2) : ∀ p ∈ convexHull ℝ ({A, B, C} : Set (ℝ × ℝ)), c ≤ a * p.1 + b * p.2 :=
  hull_ge a b c (by
    intro v hv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    rcases hv with rfl | rfl | rfl <;> assumption)

theorem tri_fst_le {A B C : ℝ × ℝ} (c : ℝ) (hA : A.1 ≤ c) (hB : B.1 ≤ c) (hC : C.1 ≤ c) :
    ∀ p ∈ convexHull ℝ ({A, B, C} : Set (ℝ × ℝ)), p.1 ≤ c := by
  intro p hp
  have := tri_le (A := A) (B := B) (C := C) 1 0 c (by simpa using hA) (by simpa using hB)
    (by simpa using hC) p hp
  simpa using this

theorem tri_fst_ge {A B C : ℝ × ℝ} (c : ℝ) (hA : c ≤ A.1) (hB : c ≤ B.1) (hC : c ≤ C.1) :
    ∀ p ∈ convexHull ℝ ({A, B, C} : Set (ℝ × ℝ)), c ≤ p.1 := by
  intro p hp
  have := tri_ge (A := A) (B := B) (C := C) 1 0 c (by simpa using hA) (by simpa using hB)
    (by simpa using hC) p hp
  simpa using this

theorem tri_snd_le {A B C : ℝ × ℝ} (c : ℝ) (hA : A.2 ≤ c) (hB : B.2 ≤ c) (hC : C.2 ≤ c) :
    ∀ p ∈ convexHull ℝ ({A, B, C} : Set (ℝ × ℝ)), p.2 ≤ c := by
  intro p hp
  have := tri_le (A := A) (B := B) (C := C) 0 1 c (by simpa using hA) (by simpa using hB)
    (by simpa using hC) p hp
  simpa using this

theorem tri_snd_ge {A B C : ℝ × ℝ} (c : ℝ) (hA : c ≤ A.2) (hB : c ≤ B.2) (hC : c ≤ C.2) :
    ∀ p ∈ convexHull ℝ ({A, B, C} : Set (ℝ × ℝ)), c ≤ p.2 := by
  intro p hp
  have := tri_ge (A := A) (B := B) (C := C) 0 1 c (by simpa using hA) (by simpa using hB)
    (by simpa using hC) p hp
  simpa using this

theorem tri_eq_of_pts {T U : Tri} (h : T.pts = U.pts) : T = U := by
  cases T; cases U; cases h; rfl


theorem Phi_lin (f : ℝ) (p : ℝ × ℝ) : Phi f p = PhiL f p := rfl

theorem Phi_scale (f : ℝ) (a V : ℝ × ℝ) (k : ℕ) (hk' : (0 : ℝ) < k) :
    Phi f a + (k : ℝ) • (Phi f (a + (1 / (k : ℝ)) • (V - a)) - Phi f a) = Phi f V := by
  rw [Phi_lin, Phi_lin, Phi_lin, map_add, map_smul, map_sub]
  simp only [add_sub_cancel_left, smul_smul, mul_one_div_cancel hk'.ne', one_smul]
  abel

/-- The base tile of a scale-`k` triangle `a,V1,V2` (skew coordinates). -/
noncomputable def baseTri (f : ℝ) (hf : 1 < f) (a V1 V2 : ℝ × ℝ) (k : ℕ) (hk : 0 < k)
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

/-- **Scale-`k` triangle tiled by `k²` copies of the model.** (`ladderDissection` in skew coordinates.) -/
noncomputable def scaledRT (f : ℝ) (hf : 1 < f) (a V1 V2 : ℝ × ℝ) (k : ℕ) (hk : 0 < k)
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


open MeasureTheory in
/-- **Packing lemma.**  Region tilings `R a` of regions `S a ⊆ T` with pairwise interior-disjoint
regions, whose total tile count `N` satisfies `N·|M| = |T|`, assemble to a `CongruentDissection N` of `T`.
The covering of `T` is *derived* from the area identity (`ConvexCover.ofCertificate`). -/
theorem pack_exists {m : ℕ} {M T : Tri} (S : Fin m → Set Plane) (n : Fin m → ℕ)
    (R : ∀ a, RTiling (S a) M (n a))
    (hS : ∀ a b, a ≠ b → Disjoint (interior (S a)) (interior (S b)))
    (hsub : ∀ a, S a ⊆ T.carrier)
    (hvol : ((∑ a, n a : ℕ) : ENNReal) * volume M.carrier = volume T.carrier) :
    ∃ D : CongruentDissection (∑ a, n a), D.model = M ∧ D.target = T := by
  classical
  let tile : Fin (∑ a, n a) → Tri := fun e =>
    (R (finSigmaFinEquiv.symm e).1).tile (finSigmaFinEquiv.symm e).2
  have tsub : ∀ (p : (a : Fin m) × Fin (n a)), ((R p.1).tile p.2).carrier ⊆ S p.1 := by
    intro p x hx
    rw [← (R p.1).covers]
    exact Set.mem_iUnion.mpr ⟨_, hx⟩
  have hsub' : ∀ e, (tile e).carrier ⊆ T.carrier := fun e => (tsub _).trans (hsub _)
  have key : ∀ (p q : (a : Fin m) × Fin (n a)), p ≠ q →
      Disjoint (interior ((R p.1).tile p.2).carrier) (interior ((R q.1).tile q.2).carrier) := by
    rintro ⟨a, x⟩ ⟨b, y⟩ hne
    by_cases hab : a = b
    · subst hab
      have : x ≠ y := fun h => hne (by rw [h])
      exact (R a).disj this
    · exact (hS a b hab).mono (interior_mono (tsub ⟨a, x⟩)) (interior_mono (tsub ⟨b, y⟩))
  have hdisj : Pairwise fun i j => Disjoint (interior (tile i).carrier) (interior (tile j).carrier) :=
    fun i j hij => key _ _ (fun h => hij (finSigmaFinEquiv.symm.injective h))
  have hcong : ∀ e, (tile e).Congruent M := fun e => (R _).cong _
  have hvol' : ∑ e, volume (tile e).carrier = volume T.carrier := by
    rw [Finset.sum_congr rfl (fun e _ => Erdos634.CongruentArea.volume_congruent (hcong e))]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact hvol
  exact ⟨{ Erdos634.ConvexCover.ofCertificate T tile hsub' hdisj hvol' with
           model := M
           tiles_congruent := hcong }, rfl, rfl⟩

theorem det_triC (f : ℝ) (hf : 1 < f) (a b c : ℝ × ℝ) (h) :
    Erdos634.AreaDet.detTri (triC f hf a b c h)
      = (sD f / (2 * f)) * ((b.1 - a.1) * (c.2 - a.2) - (c.1 - a.1) * (b.2 - a.2)) := by
  rw [Erdos634.AreaDet.detTri_eq, triC_pts, ← det_Phi f a b c]
  simp [det3]

open MeasureTheory in
theorem vol_triC (f : ℝ) (hf : 1 < f) (a b c : ℝ × ℝ) (h) :
    volume (triC f hf a b c h).carrier
      = ENNReal.ofReal |(sD f / (2 * f)) * ((b.1 - a.1) * (c.2 - a.2) - (c.1 - a.1) * (b.2 - a.2))|
        * volume Erdos634.AreaDet.stdCarrier := by
  rw [Erdos634.AreaDet.volume_eq_det_mul, det_triC]

/-- **SSS for the base tile.** If the three skew-quadratic side lengths of `a,V1,V2` are `k` times
`f²-1, f, f²`, the base tile `a,a+(V1-a)/k,a+(V2-a)/k` is congruent to the model `MF f`. -/
theorem baseTri_cong (f : ℝ) (hf : 1 < f) (a V1 V2 : ℝ × ℝ) (k : ℕ) (hk : 0 < k) (h)
    (H01 : (V1.1 - a.1) ^ 2 + (V1.2 - a.2) ^ 2 + (V1.1 - a.1) * (V1.2 - a.2) / f
      = ((k : ℝ) * (f ^ 2 - 1)) ^ 2)
    (H12 : (V2.1 - V1.1) ^ 2 + (V2.2 - V1.2) ^ 2 + (V2.1 - V1.1) * (V2.2 - V1.2) / f
      = ((k : ℝ) * f) ^ 2)
    (H20 : (V2.1 - a.1) ^ 2 + (V2.2 - a.2) ^ 2 + (V2.1 - a.1) * (V2.2 - a.2) / f
      = ((k : ℝ) * f ^ 2) ^ 2) :
    (baseTri f hf a V1 V2 k hk h).Congruent (MF f hf) := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hf0 : f ≠ 0 := by linarith
  have hk0 : (k : ℝ) ≠ 0 := hk'.ne'
  have hinv : f * f⁻¹ = 1 := mul_inv_cancel₀ hf0
  have H01' : (1 / (k : ℝ)) ^ 2 * ((V1.1 - a.1) ^ 2 + (V1.2 - a.2) ^ 2 + (V1.1 - a.1) * (V1.2 - a.2) / f)
      = (f ^ 2 - 1) ^ 2 := by rw [H01]; field_simp
  have H12' : (1 / (k : ℝ)) ^ 2 * ((V2.1 - V1.1) ^ 2 + (V2.2 - V1.2) ^ 2 + (V2.1 - V1.1) * (V2.2 - V1.2) / f)
      = f ^ 2 := by rw [H12]; field_simp
  have H20' : (1 / (k : ℝ)) ^ 2 * ((V2.1 - a.1) ^ 2 + (V2.2 - a.2) ^ 2 + (V2.1 - a.1) * (V2.2 - a.2) / f)
      = (f ^ 2) ^ 2 := by rw [H20]; field_simp
  refine Erdos634.SssCongruent.congruent_of_dist_three ?_ ?_ ?_ <;>
    simp only [baseTri, MF, brickL, triC_pts] <;>
    (refine dPhi _ _ _ _ ?_; rw [sq_Phi hf, sq_Phi hf])
  · simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
      Prod.fst_sub, Prod.snd_sub]
    linear_combination H01'
  · simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
      Prod.fst_sub, Prod.snd_sub]
    linear_combination H12'
  · simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
      Prod.fst_sub, Prod.snd_sub]
    linear_combination H20' + (1 - f ^ 2) * hinv

end Erdos634.Draft.S2L

#print axioms Erdos634.Draft.S2L.scaledRT
#print axioms Erdos634.Draft.S2L.pack_exists
#print axioms Erdos634.Draft.S2L.vol_triC
