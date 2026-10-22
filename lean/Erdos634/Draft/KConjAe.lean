-- Draft/KConjAe.lean — CASE A, node A3 (Lemma K, K2 half), route (b) "moments", step 4:
-- THE GALOIS-CONJUGATE TRIANGLES FORM A DISSECTION (PROOF_row0c.md §3.3 (iii), without winding
-- numbers).
--
-- Input: a `Dissection N` whose corners all have complex coordinate in K = ℚ(ζ_{4n}), whose tiles
-- all have |det| = P and whose target has |det| = N·P (true after normalising any congruent
-- dissection, Draft/KConjLemmaK.lean); σ : K → ℂ with σ(ζ) = ζ^m, m ≡ 1 (mod 4).
-- Φ applies σ to the complex coordinate of every corner (`phiTri`).  Output: `phiDissection`,
-- the conjugated tiles as a genuine `Dissection N` of the conjugated target.
--
-- Route: Σ_t ∫_t x^i y^j = ∫_T x^i y^j (a.e.-disjoint union) ⇒ Σ_t Λ_t = N Λ_T in ℝ
-- (Draft/KMomentTri.integral_tri) ⇒ the same identity in K ⇒ (apply σ, `map_Λ`) the identity for
-- the conjugated corners; |det Φt| = |σ(P)| for every tile and |det ΦT| = N|σ(P)| (the dets are
-- ±P, ±NP in K); so Σ_t ∫_{Φt} x^i y^j = ∫_{ΦT} x^i y^j for all i, j; moment determinacy
-- (Draft/KMomentDet) gives Σ_t 1_{Φt} = 1_{ΦT} a.e.; closed convex sets with nonempty interior
-- then give covering and disjoint interiors exactly.  Orientation: no sign bookkeeping is needed —
-- the dets enter only through |det| (see the header of Draft/KConjLemmaK.lean for the relation to
-- the paper's ε, ε_ABC).
-- Formalization debt on a paper-level PROVED node; NOT /goal progress.  Imported into All.lean (All.lean:678); on the theoremP_6 closure (UNAUDITED).
-- H59: no parameter pair (e, f) is evaluated here.
import Erdos634.Draft.KConjField
import Erdos634.Draft.KMomentDet
import Erdos634.CertCoord

open Complex MeasureTheory Set

namespace Erdos634.KConj

open Erdos634.Geometry Erdos634.Geometry.CaseA.LemmaV Erdos634.KMoment Erdos634.CertCoord

variable {n m : ℕ} (hn : 0 < n) (σ : Kf n →ₐ[ℚ] ℂ)
  (hσ : σ (IntermediateField.AdjoinSimple.gen ℚ (zeta n)) = zeta n ^ m) (hm4 : m % 4 = 1)

/-! ## Real and imaginary parts inside K -/

/-- `Re x` as an element of `K`. -/
noncomputable def reK (x : Kf n) : Kf n := (x + conjK n x) / 2
/-- `Im x` as an element of `K`. -/
noncomputable def imK (x : Kf n) : Kf n := (x - conjK n x) / (2 * ⟨I, I_mem hn⟩)

theorem coe_reK (x : Kf n) : ((reK x : Kf n) : ℂ) = (((x : ℂ).re : ℝ) : ℂ) := by
  rw [Complex.re_eq_add_conj, reK]; simp [coe_conjK]; norm_cast

theorem coe_imK (x : Kf n) : ((imK hn x : Kf n) : ℂ) = (((x : ℂ).im : ℝ) : ℂ) := by
  rw [Complex.im_eq_sub_conj, imK]; simp [coe_conjK]; norm_cast

include hσ in
theorem sigma_reK (x : Kf n) : σ (reK x) = (((σ x).re : ℝ) : ℂ) := by
  rw [reK, map_div₀, map_add, sigma_conj σ hσ, Complex.re_eq_add_conj, map_ofNat]

include hσ hm4 in
theorem sigma_imK (x : Kf n) : σ (imK hn x) = (((σ x).im : ℝ) : ℂ) := by
  rw [imK, map_div₀, map_sub, sigma_conj σ hσ, map_mul, sigma_I σ hσ hn hm4,
    Complex.im_eq_sub_conj, map_ofNat]

/-! ## Conjugated triangles -/

/-- Corner coordinates of `T` as elements of `K`. -/
noncomputable def cK (T : Tri) (hT : ∀ k, toC (T.pts k) ∈ Kf n) : Fin 3 → Fin 2 → Kf n :=
  fun k => ![reK ⟨toC (T.pts k), hT k⟩, imK hn ⟨toC (T.pts k), hT k⟩]

theorem alg_cK (T : Tri) (hT : ∀ k, toC (T.pts k) ∈ Kf n) (k : Fin 3) (v : Fin 2) :
    algebraMap (Kf n) ℂ (cK hn T hT k v) = ((cT T k v : ℝ) : ℂ) := by
  fin_cases v
  · show ((reK _ : Kf n) : ℂ) = _; rw [coe_reK]; simp [toC_re, cT]
  · show ((imK hn _ : Kf n) : ℂ) = _; rw [coe_imK]; simp [toC_im, cT]

theorem detc_cK (T : Tri) (hT : ∀ k, toC (T.pts k) ∈ Kf n) :
    algebraMap (Kf n) ℂ (detc (cK hn T hT)) = ((T.det : ℝ) : ℂ) := by
  rw [map_detc, ← detc_cT]
  simp only [alg_cK]
  rw [← Complex.ofRealHom_eq_coe, map_detc]; rfl

theorem alg_Λ (T : Tri) (hT : ∀ k, toC (T.pts k) ∈ Kf n) (i j : ℕ) :
    algebraMap (Kf n) ℂ (Λ (Qm (cK hn T hT) i j)) = ((Λ (Qm (cT T) i j) : ℝ) : ℂ) := by
  rw [map_Λ, map_Qm]
  have h2 := map_Λ Complex.ofRealHom (Qm (cT T) i j)
  rw [map_Qm] at h2
  rw [Complex.ofRealHom_eq_coe] at h2
  rw [h2]
  congr 2
  funext k v
  exact alg_cK hn T hT k v

/-- The conjugated corner, as a complex number. -/
noncomputable def sw (T : Tri) (hT : ∀ k, toC (T.pts k) ∈ Kf n) (k : Fin 3) : ℂ :=
  σ ⟨toC (T.pts k), hT k⟩

/-! ## Real side: integrals over a dissection add up -/

theorem dissection_integral_sum {N : ℕ} (D : Dissection N) {h : Plane → ℝ} (hh : Continuous h) :
    ∑ i, ∫ x in (D.tile i).carrier, h x = ∫ x in D.target.carrier, h x := by
  rw [← D.covers, integral_iUnion_ae (fun i => (D.tile i).nullMeasurableSet)
    (fun i j hij => D.aedisjoint hij), tsum_fintype]
  rw [D.covers]
  exact hh.continuousOn.integrableOn_compact D.target.isCompact

/-! ## From a.e. identity to a dissection -/

theorem vol_pos_of (T : Tri) {V : Set Plane} (hV : IsOpen V) {x : Plane} (hx : x ∈ V)
    (hxT : x ∈ T.carrier) : 0 < volume (V ∩ interior T.carrier) := by
  have hcl : x ∈ closure (interior T.carrier) := by
    rw [T.convex.closure_interior_eq_closure_of_nonempty_interior T.interior_nonempty]
    exact subset_closure hxT
  obtain ⟨y, hyV, hyI⟩ := mem_closure_iff.mp hcl V hV hx
  exact (hV.inter isOpen_interior).measure_pos volume ⟨y, hyV, hyI⟩

/-- A family of triangles whose indicators sum a.e. to the target's is a dissection. -/
noncomputable def dissectionOfAe (tile : Fin N → Tri) (target : Tri) (hN : 0 < N)
    (h : ∀ᵐ x, ∑ i, (tile i).carrier.indicator (1 : Plane → ℝ) x
      = target.carrier.indicator 1 x) : Dissection N where
  target := target
  tile := tile
  covers := by
    have hbad : volume {x | ¬ (∑ i, (tile i).carrier.indicator (1 : Plane → ℝ) x
        = target.carrier.indicator 1 x)} = 0 := ae_iff.mp h
    have hnn : ∀ x i, 0 ≤ (tile i).carrier.indicator (1 : Plane → ℝ) x := fun x i =>
      indicator_nonneg (fun _ _ => zero_le_one) x
    apply Subset.antisymm
    · intro x hx
      by_contra hxT
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      have hpos := vol_pos_of (tile i) target.isCompact.isClosed.isOpen_compl hxT hi
      apply (ne_of_gt hpos)
      refine measure_mono_null (fun y hy => ?_) hbad
      intro heq
      rw [indicator_of_notMem hy.1] at heq
      have h1 : (tile i).carrier.indicator (1 : Plane → ℝ) y = 1 :=
        indicator_of_mem (interior_subset hy.2) _
      have := Finset.single_le_sum (fun j _ => hnn y j) (Finset.mem_univ i)
      linarith
    · intro x hx
      by_contra hxU
      have hcl : IsClosed (⋃ i, (tile i).carrier) :=
        isClosed_iUnion_of_finite (fun i => (tile i).isCompact.isClosed)
      have hpos := vol_pos_of target hcl.isOpen_compl hxU hx
      apply (ne_of_gt hpos)
      refine measure_mono_null (fun y hy => ?_) hbad
      intro heq
      rw [indicator_of_mem (interior_subset hy.2)] at heq
      have : ∑ i, (tile i).carrier.indicator (1 : Plane → ℝ) y = 0 := by
        refine Finset.sum_eq_zero (fun i _ => indicator_of_notMem ?_ _)
        exact fun hi => hy.1 (mem_iUnion.mpr ⟨i, hi⟩)
      rw [this] at heq; norm_num at heq
  interiors_disjoint := by
    intro i j hij
    rw [Set.disjoint_iff]
    rintro x ⟨hxi, hxj⟩
    have hbad : volume {x | ¬ (∑ i, (tile i).carrier.indicator (1 : Plane → ℝ) x
        = target.carrier.indicator 1 x)} = 0 := ae_iff.mp h
    have hW : IsOpen (interior (tile i).carrier ∩ interior (tile j).carrier) :=
      isOpen_interior.inter isOpen_interior
    have hpos : 0 < volume (interior (tile i).carrier ∩ interior (tile j).carrier) :=
      hW.measure_pos volume ⟨x, hxi, hxj⟩
    apply (ne_of_gt hpos)
    refine measure_mono_null (fun y hy => ?_) hbad
    intro heq
    have hi1 : (tile i).carrier.indicator (1 : Plane → ℝ) y = 1 :=
      indicator_of_mem (interior_subset hy.1) _
    have hj1 : (tile j).carrier.indicator (1 : Plane → ℝ) y = 1 :=
      indicator_of_mem (interior_subset hy.2) _
    have hle : (tile i).carrier.indicator (1 : Plane → ℝ) y
        + (tile j).carrier.indicator (1 : Plane → ℝ) y
        ≤ ∑ k, (tile k).carrier.indicator (1 : Plane → ℝ) y := by
      rw [← Finset.sum_pair (f := fun k => (tile k).carrier.indicator (1 : Plane → ℝ) y) hij]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun k _ _ => indicator_nonneg (fun _ _ => zero_le_one) y)
    have hT1 : target.carrier.indicator (1 : Plane → ℝ) y ≤ 1 := by
      by_cases hy' : y ∈ target.carrier
      · rw [indicator_of_mem hy']; rfl
      · rw [indicator_of_notMem hy']; norm_num
    linarith

section Phi

include hn hσ hm4

theorem sigma_cK (T : Tri) (hT : ∀ k, toC (T.pts k) ∈ Kf n) (k : Fin 3) :
    σ (cK hn T hT k 0) = (((sw σ T hT k).re : ℝ) : ℂ) ∧
    σ (cK hn T hT k 1) = (((sw σ T hT k).im : ℝ) : ℂ) := by
  exact ⟨sigma_reK σ hσ _, sigma_imK hn σ hσ hm4 _⟩

theorem phi_det_eq (T : Tri) (hT : ∀ k, toC (T.pts k) ∈ Kf n) :
    ((det3 (sw σ T hT 0).re (sw σ T hT 0).im (sw σ T hT 1).re (sw σ T hT 1).im
      (sw σ T hT 2).re (sw σ T hT 2).im : ℝ) : ℂ) = σ (detc (cK hn T hT)) := by
  rw [show σ (detc (cK hn T hT)) = σ.toRingHom (detc (cK hn T hT)) from rfl, map_detc]
  have h := fun k => sigma_cK hn σ hσ hm4 T hT k
  simp only [detc, det3]
  change _ = (σ (cK hn T hT 1 0) - σ (cK hn T hT 0 0)) * (σ (cK hn T hT 2 1) - σ (cK hn T hT 0 1))
    - (σ (cK hn T hT 1 1) - σ (cK hn T hT 0 1)) * (σ (cK hn T hT 2 0) - σ (cK hn T hT 0 0))
  rw [(h 0).1, (h 0).2, (h 1).1, (h 1).2, (h 2).1, (h 2).2]
  push_cast; ring

theorem phi_det_ne (T : Tri) (hT : ∀ k, toC (T.pts k) ∈ Kf n) :
    det3 (sw σ T hT 0).re (sw σ T hT 0).im (sw σ T hT 1).re (sw σ T hT 1).im
      (sw σ T hT 2).re (sw σ T hT 2).im ≠ 0 := by
  intro h
  have h1 := phi_det_eq hn σ hσ hm4 T hT
  rw [h, Complex.ofReal_zero] at h1
  have h2 : detc (cK hn T hT) = 0 := σ.toRingHom.injective (by rw [map_zero]; exact h1.symm)
  have h3 := detc_cK hn T hT
  rw [h2, map_zero] at h3
  exact T.det_ne_zero (by exact_mod_cast h3.symm)

/-- **The conjugated triangle Φ(T).** -/
noncomputable def phiTri (T : Tri) (hT : ∀ k, toC (T.pts k) ∈ Kf n) : Tri :=
  mkTri (sw σ T hT 0).re (sw σ T hT 0).im (sw σ T hT 1).re (sw σ T hT 1).im
    (sw σ T hT 2).re (sw σ T hT 2).im (phi_det_ne hn σ hσ hm4 T hT)

theorem phiTri_pts (T : Tri) (hT : ∀ k, toC (T.pts k) ∈ Kf n) (k : Fin 3) :
    (phiTri hn σ hσ hm4 T hT).pts k = mkPt (sw σ T hT k).re (sw σ T hT k).im := by
  fin_cases k <;> rfl

theorem toC_phiTri (T : Tri) (hT : ∀ k, toC (T.pts k) ∈ Kf n) (k : Fin 3) :
    toC ((phiTri hn σ hσ hm4 T hT).pts k) = sw σ T hT k := by
  rw [phiTri_pts, toC_apply]; simp [Complex.re_add_im]

theorem sigma_cK_phi (T : Tri) (hT : ∀ k, toC (T.pts k) ∈ Kf n) (k : Fin 3) (v : Fin 2) :
    σ (cK hn T hT k v) = ((cT (phiTri hn σ hσ hm4 T hT) k v : ℝ) : ℂ) := by
  have h := sigma_cK hn σ hσ hm4 T hT k
  fin_cases v
  · simp only [cT, phiTri_pts]; exact h.1
  · simp only [cT, phiTri_pts]; exact h.2

theorem phi_det (T : Tri) (hT : ∀ k, toC (T.pts k) ∈ Kf n) :
    (((phiTri hn σ hσ hm4 T hT).det : ℝ) : ℂ) = σ (detc (cK hn T hT)) := by
  rw [show σ (detc (cK hn T hT)) = σ.toRingHom (detc (cK hn T hT)) from rfl, map_detc, ← detc_cT]
  have e : (fun k v => σ.toRingHom (cK hn T hT k v))
      = fun k v => ((cT (phiTri hn σ hσ hm4 T hT) k v : ℝ) : ℂ) := by
    funext k v; exact sigma_cK_phi hn σ hσ hm4 T hT k v
  rw [e, ← Complex.ofRealHom_eq_coe, map_detc]; rfl

theorem phi_Λ (T : Tri) (hT : ∀ k, toC (T.pts k) ∈ Kf n) (i j : ℕ) :
    σ (Λ (Qm (cK hn T hT) i j)) = ((Λ (Qm (cT (phiTri hn σ hσ hm4 T hT)) i j) : ℝ) : ℂ) := by
  have h1 := map_Λ σ.toRingHom (Qm (cK hn T hT) i j)
  rw [map_Qm] at h1
  have h2 := map_Λ Complex.ofRealHom (Qm (cT (phiTri hn σ hσ hm4 T hT)) i j)
  rw [map_Qm] at h2
  change σ _ = _ at h1
  rw [h1, Complex.ofRealHom_eq_coe] at *
  rw [h2]
  congr 2
  funext k v
  exact sigma_cK_phi hn σ hσ hm4 T hT k v

/-! ## The transfer -/

variable {N : ℕ} (D : Dissection N) (hK : ∀ i k, toC ((D.tile i).pts k) ∈ Kf n)
  (hKT : ∀ k, toC (D.target.pts k) ∈ Kf n) (P : ℝ) (hP : ∀ i, |(D.tile i).det| = P)
  (hPT : |D.target.det| = N * P)

/-- If `det T = c · det T'` with `c` rational, then the same holds for the conjugates. -/
theorem phi_det_mul (T T' : Tri) (hT : ∀ k, toC (T.pts k) ∈ Kf n)
    (hT' : ∀ k, toC (T'.pts k) ∈ Kf n) (c : ℚ) (h : T.det = c * T'.det) :
    (phiTri hn σ hσ hm4 T hT).det = c * (phiTri hn σ hσ hm4 T' hT').det := by
  have hK : detc (cK hn T hT) = (c : Kf n) * detc (cK hn T' hT') := by
    apply (algebraMap (Kf n) ℂ).injective
    rw [map_mul, detc_cK, detc_cK, map_ratCast, h]; push_cast; ring
  have := phi_det hn σ hσ hm4 T hT
  rw [hK, map_mul, map_ratCast, ← phi_det hn σ hσ hm4 T' hT'] at this
  exact_mod_cast this

include hP hPT in
/-- **Moment identity for the conjugated triangles.** -/
theorem phi_moment (i j : ℕ) :
    ∑ t, ∫ x in (phiTri hn σ hσ hm4 (D.tile t) (hK t)).carrier, (x 0) ^ i * (x 1) ^ j
      = ∫ x in (phiTri hn σ hσ hm4 D.target hKT).carrier, (x 0) ^ i * (x 1) ^ j := by
  have hN := D.pos
  set t0 : Fin N := ⟨0, hN⟩
  have hPpos : 0 < P := by rw [← hP t0]; exact abs_pos.mpr (D.tile t0).det_ne_zero
  -- real identity Σ Λ_t = N Λ_T
  have hreal : ∑ t, Λ (Qm (cT (D.tile t)) i j) = N * Λ (Qm (cT D.target) i j) := by
    have h := dissection_integral_sum D (h := fun x : Plane => (x 0) ^ i * (x 1) ^ j)
      (((cont_coord 0).pow i).mul ((cont_coord 1).pow j))
    simp only [integral_tri, hP, hPT] at h
    rw [← Finset.mul_sum] at h
    apply mul_left_cancel₀ hPpos.ne'
    rw [h]; ring
  -- in K
  have hK' : ∑ t, Λ (Qm (cK hn (D.tile t) (hK t)) i j) = N * Λ (Qm (cK hn D.target hKT) i j) := by
    apply (algebraMap (Kf n) ℂ).injective
    rw [map_sum, map_mul, map_natCast]
    simp only [alg_Λ]
    exact_mod_cast hreal
  -- conjugated
  have hphi : ∑ t, Λ (Qm (cT (phiTri hn σ hσ hm4 (D.tile t) (hK t))) i j)
      = N * Λ (Qm (cT (phiTri hn σ hσ hm4 D.target hKT)) i j) := by
    have := congrArg σ hK'
    rw [map_sum, map_mul, map_natCast] at this
    simp only [phi_Λ hn σ hσ hm4] at this
    exact_mod_cast this
  -- determinants
  have hdt : ∀ t, ∃ c : ℚ, (c = 1 ∨ c = -1) ∧ (D.tile t).det = c * (D.tile t0).det := by
    intro t
    have := (hP t).trans (hP t0).symm
    rcases abs_eq_abs.mp this with h | h
    · exact ⟨1, Or.inl rfl, by rw [h]; simp⟩
    · exact ⟨-1, Or.inr rfl, by rw [h]; simp⟩
  have hdT : ∃ c : ℚ, (c = N ∨ c = -N) ∧ D.target.det = c * (D.tile t0).det := by
    have : |D.target.det| = |(N : ℝ) * (D.tile t0).det| := by
      rw [hPT, abs_mul, Nat.abs_cast, hP]
    rcases abs_eq_abs.mp this with h | h
    · exact ⟨N, Or.inl rfl, by rw [h]; simp⟩
    · exact ⟨-N, Or.inr rfl, by rw [h]; push_cast; ring⟩
  set Q := |(phiTri hn σ hσ hm4 (D.tile t0) (hK t0)).det|
  have hQt : ∀ t, |(phiTri hn σ hσ hm4 (D.tile t) (hK t)).det| = Q := by
    intro t
    obtain ⟨c, hc, h⟩ := hdt t
    rw [phi_det_mul hn σ hσ hm4 _ _ (hK t) (hK t0) c h, abs_mul]
    rcases hc with rfl | rfl <;> simp [Q]
  have hQT : |(phiTri hn σ hσ hm4 D.target hKT).det| = N * Q := by
    obtain ⟨c, hc, h⟩ := hdT
    rw [phi_det_mul hn σ hσ hm4 _ _ hKT (hK t0) c h, abs_mul]
    rcases hc with rfl | rfl <;> simp [Q]
  simp only [integral_tri, hQt, hQT]
  rw [← Finset.mul_sum, hphi]; ring

include hP hPT in
/-- **The conjugated tiles' indicators sum to the conjugated target's, almost everywhere.** -/
theorem phi_ae :
    ∀ᵐ x, ∑ t, (phiTri hn σ hσ hm4 (D.tile t) (hK t)).carrier.indicator (1 : Plane → ℝ) x
      = (phiTri hn σ hσ hm4 D.target hKT).carrier.indicator 1 x := by
  let U : Option (Fin N) → Set Plane := fun o => match o with
    | none => (phiTri hn σ hσ hm4 D.target hKT).carrier
    | some t => (phiTri hn σ hσ hm4 (D.tile t) (hK t)).carrier
  let c : Option (Fin N) → ℝ := fun o => match o with
    | none => -1
    | some _ => 1
  have hU : ∀ o, IsCompact (U o) := by
    intro o; cases o <;> exact Tri.isCompact _
  have hmom : ∀ i j : ℕ, ∑ o, c o * ∫ x in U o, (x 0) ^ i * (x 1) ^ j = 0 := by
    intro i j
    rw [Fintype.sum_option]
    simp only [U, c, one_mul, neg_one_mul]
    rw [phi_moment hn σ hσ hm4 D hK hKT P hP hPT i j]; ring
  filter_upwards [ae_zero_of_moments c hU hmom] with x hx
  rw [comb, Fintype.sum_option] at hx
  simp only [U, c, one_mul, neg_one_mul] at hx
  linarith

include hP hPT in
/-- **Lemma K (iii), moment form: the conjugated triangles form a dissection of the conjugated
target.** -/
noncomputable def phiDissection : Dissection N :=
  dissectionOfAe (fun t => phiTri hn σ hσ hm4 (D.tile t) (hK t)) (phiTri hn σ hσ hm4 D.target hKT)
    D.pos (phi_ae hn σ hσ hm4 D hK hKT P hP hPT)

theorem phiDissection_tile (t : Fin N) :
    (phiDissection hn σ hσ hm4 D hK hKT P hP hPT).tile t = phiTri hn σ hσ hm4 (D.tile t) (hK t) :=
  rfl

theorem phiDissection_target :
    (phiDissection hn σ hσ hm4 D hK hKT P hP hPT).target = phiTri hn σ hσ hm4 D.target hKT :=
  rfl

end Phi

end Erdos634.KConj

#print axioms Erdos634.KConj.phi_moment
#print axioms Erdos634.KConj.phi_ae
#print axioms Erdos634.KConj.phiDissection
