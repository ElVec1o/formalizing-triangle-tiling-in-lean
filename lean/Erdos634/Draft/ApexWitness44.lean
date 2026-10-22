-- Draft/ApexWitness44.lean — VACUITY WITNESSES for Draft/ApexPlacement.lean, Draft/ApexLegWord.lean.
-- Imported by All.lean (All.lean line 406: import Erdos634.Draft.ApexWitness44).
--
-- (a) The m-free apex-placement theorems (`apex_three_tiles`, `leg_tile`, and through them the
--     engines `flank_neighbour_gen`, `cover_tile_dir`) have ALL hypotheses discharged on the REAL
--     kernel-checked 44-tiling `Tiling44Bridge.dissection` (target `(16,16,22)` × 8, tile `(2,3,4)` × 8,
--     i.e. e = 1, f = 2, m = 2), with the model relabelled so that vertex `j` is opposite side `j`
--     (`relabelModel`), `α = modelAlpha 1 2`, `β = modelBeta 1 2` (`E1NormalForm.angleData_model`),
--     apex `k = 2`.  `witness44_three_tiles`, `witness44_leg_tile` are the non-vacuous instances.
-- (b) The target half of `ApexFrameReal.M1Data` (apex `3α`, base corners `β`, legs `f³`, base
--     `e(3f²−e²)`) is satisfied by the corpus' coordinate target `BaseBetaTarget.baseBetaTarget e f`
--     at apex `k = 2`, every coprime `1 ≤ e < f` (`m1_target_witness`), and the angle bundle
--     `AngleData (modelAlpha e f) (modelBeta e f) (2α+β)` holds for every coprime `1 ≤ e < f`
--     (`angleData_member`, from `BaseBetaE1.tile_alpha_irrational`).
-- NOT witnessable: `M1Data` jointly (it contains an m = 1 dissection — that such a dissection does not
-- exist is the goal); `LegFlanksC` at the 44-tiling (true there by inspection of tiles #41–43, whose
-- leg flanks are 32 = c, but not formalized here); `ModelDataE` at e ≥ 2 (a model triangle with
-- sides `(ef, f²−e², f²)`; not built here).
--
-- Build: ApexPlacement olean in $S, then
--   lake env bash -c 'LEAN_PATH=$S:$LEAN_PATH lean Erdos634/Draft/ApexWitness44.lean'
import Erdos634.Draft.ApexPlacement
import Erdos634.Tiling44Bridge
import Erdos634.E1NormalForm
import Erdos634.BaseBetaE1

namespace Erdos634.Draft.ApexWitness44

open Erdos634.Geometry Erdos634.Z15Real Erdos634.Tiling44Bridge Erdos634.BaseBetaTargetCoord
open Erdos634.Draft.ApexPlacement

/-- The cosine rule, read backwards: an angle in `[0, π]` with the right cosine is the corner. -/
theorem cornerAngle_eq_of_cos {p q r : Plane} {a b d θ : ℝ} (ha : dist p q = a)
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

theorem dist_of_sq {x y : Plane} {v s : ℝ} (hs : 0 ≤ s) (h : dist x y ^ 2 = v) (hv : v = s ^ 2) :
    dist x y = s := by
  rw [hv] at h; exact (pow_left_inj₀ dist_nonneg hs two_ne_zero).mp h

/-! ## (a) The real 44-tiling -/

/-- The relabelling `0 ↦ 2, 1 ↦ 0, 2 ↦ 1`. -/
def τ : Equiv.Perm (Fin 3) := (finRotate 3).symm

theorem τ0 : τ 0 = 2 := by decide
theorem τ1 : τ 1 = 0 := by decide
theorem τ2 : τ 2 = 1 := by decide

/-- The real 44-tiling with its model relabelled to the `sideOpp` convention. -/
noncomputable def D44 : CongruentDissection Tiling44.tiles.length := dissection.relabelModel τ

theorem piece_d01 : dist ((pieceTri headI_mem_tiles).pts 0) ((pieceTri headI_mem_tiles).pts 1)
    = 16 := by
  have e01 : Tiling44.dist2 (vertexOf Tiling44.tiles.headI 0) (vertexOf Tiling44.tiles.headI 1)
      = ((256:ℤ),(0:ℤ)) := by decide
  apply dist_of_sq (v := 256) (by norm_num) _ (by norm_num)
  rw [pieceTri_dist_sq _ headI_mem_tiles 0 1, e01]; simp [toR]

theorem piece_d12 : dist ((pieceTri headI_mem_tiles).pts 1) ((pieceTri headI_mem_tiles).pts 2)
    = 24 := by
  have e12 : Tiling44.dist2 (vertexOf Tiling44.tiles.headI 1) (vertexOf Tiling44.tiles.headI 2)
      = ((576:ℤ),(0:ℤ)) := by decide
  apply dist_of_sq (v := 576) (by norm_num) _ (by norm_num)
  rw [pieceTri_dist_sq _ headI_mem_tiles 1 2, e12]; simp [toR]

theorem piece_d20 : dist ((pieceTri headI_mem_tiles).pts 2) ((pieceTri headI_mem_tiles).pts 0)
    = 32 := by
  have e20 : Tiling44.dist2 (vertexOf Tiling44.tiles.headI 2) (vertexOf Tiling44.tiles.headI 0)
      = ((1024:ℤ),(0:ℤ)) := by decide
  apply dist_of_sq (v := 1024) (by norm_num) _ (by norm_num)
  rw [pieceTri_dist_sq _ headI_mem_tiles 2 0, e20]; simp [toR]

theorem tgt_d01 : dist (targetTri.pts 0) (targetTri.pts 1) = 176 :=
  dist_of_sq (by norm_num) targetTri_sides.1 (by norm_num)
theorem tgt_d12 : dist (targetTri.pts 1) (targetTri.pts 2) = 128 :=
  dist_of_sq (by norm_num) targetTri_sides.2.1 (by norm_num)
theorem tgt_d20 : dist (targetTri.pts 2) (targetTri.pts 0) = 128 :=
  dist_of_sq (by norm_num) targetTri_sides.2.2 (by norm_num)

theorem hf12 : (1 : ℝ) < ((2 : ℕ) : ℝ) := by norm_num

theorem alpha_bounds : 0 ≤ modelAlpha 1 ((2 : ℕ) : ℝ) ∧ modelAlpha 1 ((2 : ℕ) : ℝ) ≤ Real.pi := by
  have h0 := Erdos634.MarchKillsFan.modelAlpha_pos hf12
  have hβ := (modelBeta_mem one_pos hf12)
  have hrel := modelAngle_rel 1 ((2 : ℕ) : ℝ)
  constructor <;> linarith [Real.pi_pos]

theorem cos_alpha12 : Real.cos (modelAlpha 1 ((2 : ℕ) : ℝ)) = 7 / 8 := by
  rw [cos_modelAlpha one_pos hf12]; norm_num

theorem cos_beta12 : Real.cos (modelBeta 1 ((2 : ℕ) : ℝ)) = 11 / 16 := by
  unfold modelBeta baseLen Nq
  rw [Real.cos_arccos (by norm_num) (by norm_num)]; norm_num

theorem beta_bounds : 0 ≤ modelBeta 1 ((2 : ℕ) : ℝ) ∧ modelBeta 1 ((2 : ℕ) : ℝ) ≤ Real.pi :=
  ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩

theorem D44_hα : cornerAngle (D44.model.pts 1) (D44.model.pts 0) (D44.model.pts 2)
    = modelAlpha 1 ((2 : ℕ) : ℝ) := by
  show cornerAngle ((pieceTri headI_mem_tiles).pts (τ 1)) ((pieceTri headI_mem_tiles).pts (τ 0))
    ((pieceTri headI_mem_tiles).pts (τ 2)) = _
  rw [τ0, τ1, τ2]
  have h1 : dist ((pieceTri headI_mem_tiles).pts 0) ((pieceTri headI_mem_tiles).pts 2) = 32 := by
    rw [dist_comm]; exact piece_d20
  refine cornerAngle_eq_of_cos (a := 32) (b := 24) (d := 16) h1 piece_d12 piece_d01
    (by norm_num) (by norm_num) alpha_bounds.1 alpha_bounds.2 ?_
  rw [cos_alpha12]; norm_num

theorem D44_hβ : cornerAngle (D44.model.pts 2) (D44.model.pts 1) (D44.model.pts 0)
    = modelBeta 1 ((2 : ℕ) : ℝ) := by
  show cornerAngle ((pieceTri headI_mem_tiles).pts (τ 2)) ((pieceTri headI_mem_tiles).pts (τ 1))
    ((pieceTri headI_mem_tiles).pts (τ 0)) = _
  rw [τ0, τ1, τ2]
  have h1 : dist ((pieceTri headI_mem_tiles).pts 1) ((pieceTri headI_mem_tiles).pts 0) = 16 := by
    rw [dist_comm]; exact piece_d01
  refine cornerAngle_eq_of_cos (a := 16) (b := 32) (d := 24) h1 piece_d20 piece_d12
    (by norm_num) (by norm_num) beta_bounds.1 beta_bounds.2 ?_
  rw [cos_beta12]; norm_num

theorem D44_hγ : cornerAngle (D44.model.pts 0) (D44.model.pts 2) (D44.model.pts 1)
    = 2 * modelAlpha 1 ((2 : ℕ) : ℝ) + modelBeta 1 ((2 : ℕ) : ℝ) := by
  have hsum := Erdos634.Geometry.cornerAngle_sum D44.model
  rw [D44_hα, D44_hβ] at hsum
  have hrel := modelAngle_rel 1 ((2 : ℕ) : ℝ)
  linarith

theorem D44_angleData : MarchSlots.AngleData (modelAlpha 1 ((2 : ℕ) : ℝ))
    (modelBeta 1 ((2 : ℕ) : ℝ)) (2 * modelAlpha 1 ((2 : ℕ) : ℝ) + modelBeta 1 ((2 : ℕ) : ℝ)) :=
  Erdos634.E1NormalForm.angleData_model 2 le_rfl

/-- The apex of the 44-target is vertex `2`, with corner `3α`. -/
theorem D44_hcorner : cornerAngle (D44.target.pts (2 + 1)) (D44.target.pts 2)
    (D44.target.pts (2 + 2)) = 3 * modelAlpha 1 ((2 : ℕ) : ℝ) := by
  show cornerAngle (targetTri.pts 0) (targetTri.pts 2) (targetTri.pts 1) = _
  have hb0 : cornerAngle (targetTri.pts 1) (targetTri.pts 0) (targetTri.pts 2)
      = modelBeta 1 ((2 : ℕ) : ℝ) := by
    have h1 : dist (targetTri.pts 1) (targetTri.pts 0) = 176 := by rw [dist_comm]; exact tgt_d01
    have h2 : dist (targetTri.pts 1) (targetTri.pts 2) = 128 := tgt_d12
    refine cornerAngle_eq_of_cos (a := 176) (b := 128) (d := 128) h1 tgt_d20 h2
      (by norm_num) (by norm_num) beta_bounds.1 beta_bounds.2 ?_
    rw [cos_beta12]; norm_num
  have hb1 : cornerAngle (targetTri.pts 2) (targetTri.pts 1) (targetTri.pts 0)
      = modelBeta 1 ((2 : ℕ) : ℝ) := by
    have h1 : dist (targetTri.pts 2) (targetTri.pts 1) = 128 := by rw [dist_comm]; exact tgt_d12
    refine cornerAngle_eq_of_cos (a := 128) (b := 176) (d := 128) h1 tgt_d01 tgt_d20
      (by norm_num) (by norm_num) beta_bounds.1 beta_bounds.2 ?_
    rw [cos_beta12]; norm_num
  have hsum := Erdos634.Geometry.cornerAngle_sum targetTri
  rw [hb0, hb1] at hsum
  have hrel := modelAngle_rel 1 ((2 : ℕ) : ℝ)
  linarith

/-- **Non-vacuity of `apex_three_tiles`: the real 44-tiling satisfies every hypothesis**, and has
exactly three tiles at its apex, each presenting `α` and having the apex as a vertex. -/
theorem witness44_three_tiles :
    ∃ i₁ i₂ i₃ : Fin Tiling44.tiles.length, i₁ ≠ i₂ ∧ i₁ ≠ i₃ ∧ i₂ ≠ i₃ ∧
      (∀ i, D44.target.pts 2 ∈ (D44.tile i).carrier ↔ (i = i₁ ∨ i = i₂ ∨ i = i₃)) ∧
      (∀ i, D44.target.pts 2 ∈ (D44.tile i).carrier →
        (D44.tile i).localAngle (D44.target.pts 2) = modelAlpha 1 ((2 : ℕ) : ℝ) ∧
          ∃ j, (D44.tile i).pts j = D44.target.pts 2) :=
  apex_three_tiles D44 D44_angleData D44_hα D44_hβ D44_hγ 2 D44_hcorner

/-- **Non-vacuity of `leg_tile` (hence of `flank_neighbour_gen` and `cover_tile_dir` in the apex
setting): on the real 44-tiling, some tile has a corner at the apex with a flank along the leg to
`pts 0`.** -/
theorem witness44_leg_tile :
    ∃ i m, (D44.tile i).pts m = D44.target.pts 2 ∧ ∃ U' W' : Plane,
      CornerAdjacency.IsFlankPair (D44.tile i) m (D44.target.pts 2) U' W' ∧
      ∃ S : ℝ, 0 < S ∧ D44.target.pts (2 + 1) - D44.target.pts 2 = S • U' ∧
        cross (D44.target.pts (2 + 1) - D44.target.pts 2) W' *
          cross (D44.target.pts (2 + 1) - D44.target.pts 2)
            (-(D44.target.pts (2 + 2) - D44.target.pts 2)) < 0 := by
  obtain ⟨-, -, -, -, -, -, -, hAt⟩ := witness44_three_tiles
  exact leg_tile D44.toDissection (apexCone_target D44.target 2) (fun i hi => (hAt i hi).2)

/-! ## (b) The target data and the angle bundle, for every member -/

/-- **The target half of `M1Data` is satisfied by the corpus' coordinate target at apex `k = 2`**
(`α = modelAlpha e f`, `β = modelBeta e f`), every `0 < e < f`. -/
theorem m1_target_witness {e f : ℝ} (he : 0 < e) (hef : e < f) :
    let T := baseBetaTarget e f he hef
    cornerAngle (T.pts (2 + 1)) (T.pts 2) (T.pts (2 + 2)) = 3 * modelAlpha e f ∧
      cornerAngle (T.pts (2 + 2)) (T.pts (2 + 1)) (T.pts 2) = modelBeta e f ∧
      cornerAngle (T.pts 2) (T.pts (2 + 2)) (T.pts (2 + 1)) = modelBeta e f ∧
      dist (T.pts 2) (T.pts (2 + 1)) = f ^ 3 ∧ dist (T.pts 2) (T.pts (2 + 2)) = f ^ 3 ∧
      dist (T.pts (2 + 1)) (T.pts (2 + 2)) = e * (3 * f ^ 2 - e ^ 2) := by
  intro T
  have e1 : (2 : Fin 3) + 1 = 0 := rfl
  have e2 : (2 : Fin 3) + 2 = 1 := rfl
  rw [e1, e2]
  refine ⟨cornerAngle_apex he hef, cornerAngle_base₀ he hef, cornerAngle_base₁ he hef, ?_, ?_, ?_⟩
  · rw [dist_comm]; exact baseBetaTarget_dist_leg₀ he hef
  · rw [dist_comm]; exact baseBetaTarget_dist_leg₁ he hef
  · rw [baseBetaTarget_dist_base he hef]

/-- **The angle bundle holds at every member `1 ≤ e < f`** (irrationality from
`BaseBetaE1.tile_alpha_irrational`, Niven). -/
theorem angleData_member (e f : ℕ) (he : 1 ≤ e) (hef : e < f) :
    MarchSlots.AngleData (modelAlpha e f) (modelBeta e f)
      (2 * modelAlpha e f + modelBeta e f) := by
  have heR : (1 : ℝ) ≤ e := by exact_mod_cast he
  have hefR : (e : ℝ) < f := by exact_mod_cast hef
  have he0 : (0 : ℝ) < e := by linarith
  have hf0 : (0 : ℝ) < f := by linarith
  obtain ⟨hb0, hb2⟩ := modelBeta_mem he0 hefR
  have hrel := modelAngle_rel (e : ℝ) f
  have hα0 : 0 < modelAlpha e f := by unfold modelAlpha; linarith
  have hαπ : modelAlpha e f < Real.pi := by unfold modelAlpha; linarith [Real.pi_pos]
  -- `sin (α/2) = e/(2f)`
  have hcos := cos_modelAlpha he0 hefR
  have hsin : Real.sin (modelAlpha e f / 2) = (e : ℝ) / (2 * (f : ℝ)) := by
    have hs2 : Real.sin (modelAlpha e f / 2) ^ 2 = ((e : ℝ) / (2 * (f : ℝ))) ^ 2 := by
      have h2 := Real.cos_two_mul (modelAlpha e f / 2)
      rw [show 2 * (modelAlpha e f / 2) = modelAlpha e f by ring, hcos] at h2
      have hpy := Real.sin_sq_add_cos_sq (modelAlpha e f / 2)
      have hs : Real.sin (modelAlpha e f / 2) ^ 2 = (e : ℝ) ^ 2 / (4 * (f : ℝ) ^ 2) := by
        field_simp at h2 ⊢
        nlinarith [h2, hpy]
      rw [hs]; field_simp; ring
    have hpos : 0 < Real.sin (modelAlpha e f / 2) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
    exact (pow_left_inj₀ hpos.le (by positivity) two_ne_zero).mp hs2
  have hirr := Erdos634.BaseBetaE1.tile_alpha_irrational e f he hef _ hsin
  refine ⟨hα0, hb0, fun h => hirr ⟨1 / 5, ?_⟩, rfl, hrel, hirr⟩
  have : 5 * modelAlpha e f = Real.pi := by rw [← h] at hrel; linarith
  push_cast; linarith

end Erdos634.Draft.ApexWitness44

#print axioms Erdos634.Draft.ApexWitness44.witness44_three_tiles
#print axioms Erdos634.Draft.ApexWitness44.witness44_leg_tile
#print axioms Erdos634.Draft.ApexWitness44.m1_target_witness
#print axioms Erdos634.Draft.ApexWitness44.angleData_member
