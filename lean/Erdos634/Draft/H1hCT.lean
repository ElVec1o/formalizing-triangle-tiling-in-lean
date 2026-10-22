-- Draft/H1hCT.lean — ATOM H1.h (SCOPE_H1_full.md §3, Lemma CT): the Galois-conjugate dissection,
-- proved by the MOMENT method over an ARBITRARY field F with two ring homomorphisms ι, ψ : F →+* ℝ.
--
--   ι = the embedding in which the dissection lives, ψ = the conjugate embedding.
--   Hypothesis: every tile/target vertex coordinate is ι(c) for an explicit c ∈ F.
--   Conclusion: the vertexwise images ψ(c) form a Dissection N (same N) of the ψ-image of the target.
--   Equal-|det| tiles (congruent tiles) make the paper's "common sign ε" automatic: the moment
--   identity is carried by Λ (labelling independent), and the dets enter only through |·|.
--
-- Generalises `KConj.phiDissection` (Draft/KConjAe.lean: K = ℚ(ζ_{4n}), complex coordinates, σ(i)=i)
-- to any field F; reuses KMomentTri/KMomentDet/KConjAe.dissectionOfAe.
-- Formalization debt (SCOPE_H1_full H1.h); NOT /goal progress.  Imported directly by All.lean (stale "NOT imported" header corrected 2026-10-04).
import Erdos634.Draft.KConjAe

open MeasureTheory Set MvPolynomial

namespace Erdos634.H1hCT

open Erdos634.Geometry Erdos634.KMoment Erdos634.CertCoord Erdos634.KConj

variable {F : Type*} [Field F] [CharZero F]

theorem det3_eq (ψ : F →+* ℝ) (c : Fin 3 → Fin 2 → F) :
    det3 (ψ (c 0 0)) (ψ (c 0 1)) (ψ (c 1 0)) (ψ (c 1 1)) (ψ (c 2 0)) (ψ (c 2 1)) = ψ (detc c) := by
  simp only [det3, detc, map_sub, map_mul]; ring

/-- The conjugate triangle with corner coordinates `ψ ∘ c`. -/
noncomputable def conjTri (ψ : F →+* ℝ) (c : Fin 3 → Fin 2 → F) (hd : detc c ≠ 0) : Tri :=
  mkTri (ψ (c 0 0)) (ψ (c 0 1)) (ψ (c 1 0)) (ψ (c 1 1)) (ψ (c 2 0)) (ψ (c 2 1))
    (by rw [det3_eq]; exact fun h => hd (ψ.injective (by rw [h, map_zero])))

theorem conjTri_pts (ψ : F →+* ℝ) (c : Fin 3 → Fin 2 → F) (hd : detc c ≠ 0) (k : Fin 3) (v : Fin 2) :
    (conjTri ψ c hd).pts k v = ψ (c k v) := by
  fin_cases k <;> fin_cases v <;> simp [conjTri, mkPt_zero, mkPt_one]

theorem det_of_coords (φ : F →+* ℝ) (T : Tri) (c : Fin 3 → Fin 2 → F)
    (h : ∀ k v, T.pts k v = φ (c k v)) : T.det = φ (detc c) := by
  rw [← detc_cT, map_detc]
  congr 1; funext k v; exact h k v

theorem detc_ne_of_coords (φ : F →+* ℝ) (T : Tri) (c : Fin 3 → Fin 2 → F)
    (h : ∀ k v, T.pts k v = φ (c k v)) : detc c ≠ 0 := by
  intro h0
  have := det_of_coords φ T c h
  rw [h0, map_zero] at this
  exact T.det_ne_zero this

/-- Moment formula over `F`: `∫_T x₀^i x₁^j = |φ(det c)| · φ(Λ(Qm c i j))`. -/
theorem integral_of_coords (φ : F →+* ℝ) (T : Tri) (c : Fin 3 → Fin 2 → F)
    (h : ∀ k v, T.pts k v = φ (c k v)) (i j : ℕ) :
    ∫ x in T.carrier, (x 0) ^ i * (x 1) ^ j = |φ (detc c)| * φ (Λ (Qm c i j)) := by
  rw [integral_tri, ← det_of_coords φ T c h, map_Λ, map_Qm]
  congr 3
  funext k v; exact h k v

theorem coord_ne_of_conj (ψ : F →+* ℝ) (c : Fin 3 → Fin 2 → F) (hd : detc c ≠ 0) :
    (conjTri ψ c hd).det = ψ (detc c) :=
  det_of_coords ψ _ c (conjTri_pts ψ c hd)

/-- **CT (moment form).** Let `D` be a dissection whose tile and target corners are `ι(c)`.
If all tiles have `|det| = P` and the target `N·P`, then the `ψ`-conjugate corners form a
`Dissection N`. -/
theorem conj_dissection {N : ℕ} (D : Dissection N) (ι ψ : F →+* ℝ)
    (c : Fin N → Fin 3 → Fin 2 → F) (cT' : Fin 3 → Fin 2 → F)
    (hc : ∀ i k v, (D.tile i).pts k v = ι (c i k v))
    (hcT : ∀ k v, D.target.pts k v = ι (cT' k v))
    (P : ℝ) (hP : ∀ i, |(D.tile i).det| = P) (hPT : |D.target.det| = N * P) :
    ∃ D' : Dissection N, (∀ i k v, (D'.tile i).pts k v = ψ (c i k v)) ∧
      (∀ k v, D'.target.pts k v = ψ (cT' k v)) := by
  have hN := D.pos
  set t0 : Fin N := ⟨0, hN⟩
  have hd : ∀ i, detc (c i) ≠ 0 := fun i => detc_ne_of_coords ι _ _ (hc i)
  have hdT : detc cT' ≠ 0 := detc_ne_of_coords ι _ _ hcT
  have hPpos : 0 < P := by rw [← hP t0]; exact abs_pos.mpr (D.tile t0).det_ne_zero
  -- det relations in F
  have hrel : ∀ i, detc (c i) = detc (c t0) ∨ detc (c i) = -detc (c t0) := by
    intro i
    have h1 : |(D.tile i).det| = |(D.tile t0).det| := (hP i).trans (hP t0).symm
    rw [det_of_coords ι _ _ (hc i), det_of_coords ι _ _ (hc t0)] at h1
    rcases abs_eq_abs.mp h1 with h | h
    · exact Or.inl (ι.injective h)
    · exact Or.inr (ι.injective (by rw [h, map_neg]))
  have hrelT : detc cT' = N * detc (c t0) ∨ detc cT' = -(N * detc (c t0)) := by
    have h1 : |D.target.det| = |(N : ℝ) * (D.tile t0).det| := by
      rw [hPT, abs_mul, Nat.abs_cast, hP]
    rw [det_of_coords ι _ _ hcT, det_of_coords ι _ _ (hc t0)] at h1
    rw [← map_natCast ι N, ← map_mul] at h1
    rcases abs_eq_abs.mp h1 with h | h
    · exact Or.inl (ι.injective (by rw [h, map_mul, map_natCast]))
    · exact Or.inr (ι.injective (by rw [h, map_neg, map_mul, map_natCast]))
  -- the conjugate triangles
  let tile' : Fin N → Tri := fun i => conjTri ψ (c i) (hd i)
  let target' : Tri := conjTri ψ cT' hdT
  set Q := |ψ (detc (c t0))| with hQdef
  have hQi : ∀ i, |ψ (detc (c i))| = Q := by
    intro i
    rcases hrel i with h | h <;> simp [h, hQdef]
  have hQT : |ψ (detc cT')| = N * Q := by
    rcases hrelT with h | h <;> simp [h, hQdef, abs_mul]
  -- the identity over F
  have hF : ∀ i j : ℕ, ∑ t, Λ (Qm (c t) i j) = N * Λ (Qm cT' i j) := by
    intro i j
    have h := dissection_integral_sum D (h := fun x : Plane => (x 0) ^ i * (x 1) ^ j)
      (((cont_coord 0).pow i).mul ((cont_coord 1).pow j))
    simp only [integral_of_coords ι _ _ (hc _), integral_of_coords ι _ _ hcT] at h
    have hdi : ∀ t, |ι (detc (c t))| = P := fun t => by
      rw [← det_of_coords ι _ _ (hc t)]; exact hP t
    have hdT' : |ι (detc cT')| = N * P := by rw [← det_of_coords ι _ _ hcT]; exact hPT
    simp only [hdi, hdT'] at h
    rw [← Finset.mul_sum, ← map_sum] at h
    apply ι.injective
    rw [map_mul, map_natCast]
    apply mul_left_cancel₀ hPpos.ne'
    rw [h]; ring
  -- real moment identity for the conjugates
  have hmom : ∀ i j : ℕ, ∑ t, ∫ x in (tile' t).carrier, (x 0) ^ i * (x 1) ^ j
      = ∫ x in target'.carrier, (x 0) ^ i * (x 1) ^ j := by
    intro i j
    simp only [tile', target', integral_of_coords ψ _ _ (conjTri_pts ψ _ _), hQi, hQT]
    rw [← Finset.mul_sum, ← map_sum, hF i j, map_mul, map_natCast]; ring
  have hae : ∀ᵐ x, ∑ t, (tile' t).carrier.indicator (1 : Plane → ℝ) x
      = target'.carrier.indicator 1 x := by
    let U : Option (Fin N) → Set Plane := fun o => match o with
      | none => target'.carrier
      | some t => (tile' t).carrier
    let cc : Option (Fin N) → ℝ := fun o => match o with
      | none => -1
      | some _ => 1
    have hU : ∀ o, IsCompact (U o) := by
      intro o; cases o <;> exact Tri.isCompact _
    have hm : ∀ i j : ℕ, ∑ o, cc o * ∫ x in U o, (x 0) ^ i * (x 1) ^ j = 0 := by
      intro i j
      rw [Fintype.sum_option]
      simp only [U, cc, one_mul, neg_one_mul]
      rw [hmom i j]; ring
    filter_upwards [ae_zero_of_moments cc hU hm] with x hx
    rw [comb, Fintype.sum_option] at hx
    simp only [U, cc, one_mul, neg_one_mul] at hx
    linarith
  exact ⟨dissectionOfAe tile' target' hN hae, fun i k v => conjTri_pts ψ (c i) (hd i) k v,
    fun k v => conjTri_pts ψ cT' hdT k v⟩

end Erdos634.H1hCT

#print axioms Erdos634.H1hCT.conj_dissection
