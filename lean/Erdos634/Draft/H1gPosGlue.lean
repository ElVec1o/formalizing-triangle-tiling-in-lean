-- Draft/H1gPosGlue.lean — ATOM H1.g assembly: L1 (position + direction), in the hypothesis form of
-- `H1hCT.conj_congruentDissection_subfield`, plus the normal-position wrapper.
--   `L1`        : target base on the x-axis from the origin, `K` ⊇ model distances and |det|
--                 ⇒ every tile corner and every target corner has both coordinates in `K`.
--   `L1_normal` : for ANY `CongruentDissection` there is an isometric copy (same `N`, same model)
--                 with target base `pts 0 = 0`, `pts 1` on the x-axis, and the conclusion of `L1`.
-- Uses `L1_pos` (H1gPosStep) + `edges_in_K_of_horizontal_side` (H1gDir).  The target-vertex-is-a-
-- tile-vertex lemma is the pre-existing `A1Pos.target_vertex_is_tile_vertex` (extreme points).
-- Formalization debt; NOT /goal progress.  Standard axioms, no sorry.
import Erdos634.Draft.H1gPosStep
import Erdos634.Draft.H1gDir
import Erdos634.Draft.A1CornerLattice
import Erdos634.NormalPosition

namespace Erdos634.H1gPos

open Erdos634.Geometry Erdos634.H1gDir

/-! ## An isometry putting a segment on the x-axis -/

/-- Rotation by `(c, s)`. -/
noncomputable def rot (c s : ℝ) (x : Plane) : Plane :=
  WithLp.toLp 2 ![c * x 0 + s * x 1, -s * x 0 + c * x 1]

/-- Inverse rotation. -/
noncomputable def rotInv (c s : ℝ) (x : Plane) : Plane :=
  WithLp.toLp 2 ![c * x 0 - s * x 1, s * x 0 + c * x 1]

theorem rot_apply0 (c s : ℝ) (x : Plane) : rot c s x 0 = c * x 0 + s * x 1 := rfl
theorem rot_apply1 (c s : ℝ) (x : Plane) : rot c s x 1 = -s * x 0 + c * x 1 := rfl
theorem rotInv_apply0 (c s : ℝ) (x : Plane) : rotInv c s x 0 = c * x 0 - s * x 1 := rfl
theorem rotInv_apply1 (c s : ℝ) (x : Plane) : rotInv c s x 1 = s * x 0 + c * x 1 := rfl

/-- The isometry `x ↦ rot (x - A)`. -/
noncomputable def axisIso (A : Plane) (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) : Plane ≃ᵢ Plane where
  toFun x := rot c s (x - A)
  invFun y := A + rotInv c s y
  left_inv x := by
    ext i; fin_cases i
    · simp only [Fin.zero_eta, PiLp.add_apply, rotInv_apply0, rot_apply0, rot_apply1, PiLp.sub_apply]
      linear_combination (x 0 - A 0) * h
    · simp only [Fin.mk_one, PiLp.add_apply, rotInv_apply1, rot_apply0, rot_apply1, PiLp.sub_apply]
      linear_combination (x 1 - A 1) * h
  right_inv y := by
    ext i; fin_cases i
    · simp only [Fin.zero_eta, rot_apply0, PiLp.sub_apply, PiLp.add_apply, rotInv_apply0,
        rotInv_apply1]
      linear_combination (y 0) * h
    · simp only [Fin.mk_one, rot_apply1, PiLp.sub_apply, PiLp.add_apply, rotInv_apply0,
        rotInv_apply1]
      linear_combination (y 1) * h
  isometry_toFun := by
    refine Isometry.of_dist_eq fun x y => ?_
    have h1 := Erdos634.H1hCT.dist_sq_plane (rot c s (x - A)) (rot c s (y - A))
    have h2 := Erdos634.H1hCT.dist_sq_plane x y
    have h3 : dist (rot c s (x - A)) (rot c s (y - A)) ^ 2 = dist x y ^ 2 := by
      rw [h1, h2]
      simp only [rot_apply0, rot_apply1, PiLp.sub_apply]
      linear_combination ((x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2) * h
    exact (sq_eq_sq₀ dist_nonneg dist_nonneg).mp h3

theorem axisIso_apply (A : Plane) (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) (x : Plane) :
    axisIso A c s h x = rot c s (x - A) := rfl

/-- **Any segment can be carried to the x-axis, its start to the origin.** -/
theorem exists_axis_isometry (A B : Plane) (hAB : A ≠ B) :
    ∃ g : Plane ≃ᵢ Plane, g A = 0 ∧ g B 1 = 0 := by
  have hw : B - A ≠ 0 := sub_ne_zero.mpr (Ne.symm hAB)
  have hpos := dsq_pos hw
  simp only [PiLp.sub_apply] at hpos
  set q := (B 0 - A 0) ^ 2 + (B 1 - A 1) ^ 2 with hq
  have hr : 0 < Real.sqrt q := Real.sqrt_pos.mpr hpos
  have hrr : Real.sqrt q ^ 2 = q := Real.sq_sqrt hpos.le
  set r := Real.sqrt q
  have hcs : ((B 0 - A 0) / r) ^ 2 + ((B 1 - A 1) / r) ^ 2 = 1 := by
    field_simp
    rw [hrr]
  refine ⟨axisIso A ((B 0 - A 0) / r) ((B 1 - A 1) / r) hcs, ?_, ?_⟩
  · ext i; fin_cases i <;> simp [axisIso_apply, rot]
  · rw [axisIso_apply, rot_apply1]
    simp only [PiLp.sub_apply]
    field_simp
    ring

/-! ## L1 -/

/-- Coordinatewise `K`-membership as an additive subgroup. -/
def KGroup (K : Subfield ℝ) : AddSubgroup Plane where
  carrier := {v | InK K v}
  add_mem' := by
    rintro a b ⟨a0, a1⟩ ⟨b0, b1⟩
    exact ⟨by simpa using K.add_mem a0 b0, by simpa using K.add_mem a1 b1⟩
  zero_mem' := ⟨by simp, by simp⟩
  neg_mem' := by
    rintro a ⟨a0, a1⟩
    exact ⟨by simpa using K.neg_mem a0, by simpa using K.neg_mem a1⟩

theorem coord_mem_of_InK {K : Subfield ℝ} {v : Plane} (h : InK K v) (i : Fin 2) : v i ∈ K := by
  fin_cases i
  · exact h.1
  · exact h.2

/-- **L1 (H1.g), position + direction.**  With the target base on the x-axis starting at the origin,
and `K` containing all model distances and `|det model|`, every tile corner and every target corner
has both coordinates in `K`. -/
theorem L1 {N : ℕ} (D : CongruentDissection N) (K : Subfield ℝ)
    (hd : ∀ j l, dist (D.model.pts j) (D.model.pts l) ∈ K) (hdet : |D.model.det| ∈ K)
    (h0 : D.target.pts 0 = 0) (h1 : D.target.pts 1 1 = 0) :
    (∀ i k v, (D.tile i).pts k v ∈ K) ∧ (∀ k v, D.target.pts k v ∈ K) := by
  have hdir := edges_in_K_of_horizontal_side D K hd hdet (by rw [h0]; rfl) h1
  have hle : edgeGroup D.toDissection ≤ KGroup K :=
    (AddSubgroup.closure_le _).mpr (by
      rintro v ⟨i, k, rfl⟩
      exact hdir i k)
  obtain ⟨i0, c0, hc⟩ := Erdos634.Geometry.A1Pos.target_vertex_is_tile_vertex D.toDissection 0
  have hcorner : ∀ i k, InK K ((D.tile i).pts k) := by
    intro i k
    have := hle (L1_pos D.toDissection i0 c0 i k)
    rw [← hc, h0, sub_zero] at this
    exact this
  refine ⟨fun i k v => coord_mem_of_InK (hcorner i k) v, fun k v => ?_⟩
  obtain ⟨i, m, hm⟩ := Erdos634.Geometry.A1Pos.target_vertex_is_tile_vertex D.toDissection k
  rw [hm]
  exact coord_mem_of_InK (hcorner i m) v

/-- **L1 in normal position, for any `CongruentDissection`.**  An isometric copy (same `N`, same
model) with the target base on the x-axis from the origin has all corners in `K`. -/
theorem L1_normal {N : ℕ} (D : CongruentDissection N) (K : Subfield ℝ)
    (hd : ∀ j l, dist (D.model.pts j) (D.model.pts l) ∈ K) (hdet : |D.model.det| ∈ K) :
    ∃ (g : Plane ≃ᵢ Plane) (D' : CongruentDissection N),
      D'.model = D.model ∧ (∀ i m, (D'.tile i).pts m = g ((D.tile i).pts m)) ∧
      (∀ k, D'.target.pts k = g (D.target.pts k)) ∧
      D'.target.pts 0 = 0 ∧ D'.target.pts 1 1 = 0 ∧
      (∀ i k v, (D'.tile i).pts k v ∈ K) ∧ (∀ k v, D'.target.pts k v ∈ K) := by
  have hne : D.target.pts 0 ≠ D.target.pts 1 := by
    intro h
    have h3 := D.target.indep.injective h
    exact absurd h3 (by decide)
  obtain ⟨g, hg0, hg1⟩ := exists_axis_isometry _ _ hne
  let D' := Erdos634.NormalPosition.normalizeC D g 1
  have htgt : ∀ k, D'.target.pts k = g (D.target.pts k) := fun k => rfl
  have h0 : D'.target.pts 0 = 0 := by rw [htgt]; exact hg0
  have h1 : D'.target.pts 1 1 = 0 := by rw [htgt]; exact hg1
  have hmod : D'.model = D.model := rfl
  have hd' : ∀ j l, dist (D'.model.pts j) (D'.model.pts l) ∈ K := by rw [hmod]; exact hd
  have hdet' : |D'.model.det| ∈ K := by rw [hmod]; exact hdet
  obtain ⟨hA, hB⟩ := L1 D' K hd' hdet' h0 h1
  exact ⟨g, D', hmod, fun i m => rfl, htgt, h0, h1, hA, hB⟩

/-- The smallest subfield containing all model distances and `|det model|`. -/
noncomputable def modelField {N : ℕ} (D : CongruentDissection N) : Subfield ℝ :=
  Subfield.closure ({x | ∃ j l, x = dist (D.model.pts j) (D.model.pts l)} ∪ {|D.model.det|})

/-- **L1 with the minimal field** (non-vacuous instance: `modelField D` is the closure of a finite
set of reals, hence countable, hence `≠ ℝ`; the hypotheses of `L1_normal` hold by construction). -/
theorem L1_modelField {N : ℕ} (D : CongruentDissection N) :
    ∃ (g : Plane ≃ᵢ Plane) (D' : CongruentDissection N),
      D'.model = D.model ∧ (∀ i m, (D'.tile i).pts m = g ((D.tile i).pts m)) ∧
      (∀ k, D'.target.pts k = g (D.target.pts k)) ∧
      D'.target.pts 0 = 0 ∧ D'.target.pts 1 1 = 0 ∧
      (∀ i k v, (D'.tile i).pts k v ∈ modelField D) ∧ (∀ k v, D'.target.pts k v ∈ modelField D) :=
  L1_normal D (modelField D)
    (fun j l => Subfield.subset_closure (Or.inl ⟨j, l, rfl⟩))
    (Subfield.subset_closure (Or.inr rfl))

/-- **L1 feeds CT.**  For any ring hom `ψ : K →+* ℝ` (e.g. the nontrivial automorphism of a
quadratic `K`), the normal-position copy `D'` of `D` has a conjugate congruent dissection `D''`
whose corners are the `ψ`-images of those of `D'` -- the exact output form of
`H1hCT.conj_congruentDissection_subfield` with its field hypotheses discharged by `L1`. -/
theorem L1_CT {N : ℕ} (D : CongruentDissection N) (K : Subfield ℝ)
    (hd : ∀ j l, dist (D.model.pts j) (D.model.pts l) ∈ K) (hdet : |D.model.det| ∈ K)
    (ψ : K →+* ℝ) :
    ∃ (D' D'' : CongruentDissection N), D'.model = D.model ∧ D'.target.pts 0 = 0 ∧
      D'.target.pts 1 1 = 0 ∧
      ∃ (hK : ∀ i k v, (D'.tile i).pts k v ∈ K) (hKT : ∀ k v, D'.target.pts k v ∈ K),
        (∀ i k v, (D''.tile i).pts k v = ψ ⟨(D'.tile i).pts k v, hK i k v⟩) ∧
        (∀ k v, D''.target.pts k v = ψ ⟨D'.target.pts k v, hKT k v⟩) := by
  obtain ⟨g, D', hmod, -, -, h0, h1, hK, hKT⟩ := L1_normal D K hd hdet
  obtain ⟨D'', h2, h3, -⟩ := Erdos634.H1hCT.conj_congruentDissection_subfield D' K ψ hK hKT
  exact ⟨D', D'', hmod, h0, h1, hK, hKT, h2, h3⟩

end Erdos634.H1gPos

#print axioms Erdos634.H1gPos.exists_axis_isometry
#print axioms Erdos634.H1gPos.L1
#print axioms Erdos634.H1gPos.L1_normal
#print axioms Erdos634.H1gPos.L1_modelField
#print axioms Erdos634.H1gPos.L1_CT
