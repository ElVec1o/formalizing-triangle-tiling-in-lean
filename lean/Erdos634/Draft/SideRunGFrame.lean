/-
Draft/SideRunGFrame.lean -- written 14 October 2026.  UNAUDITED.  In `AllThreshold`.

The frame of the side theorem for EVERY member `(e, f)`, `1 ≤ e < f`, `gcd (e, f) = 1`: the generalization of
`Draft/SideRunFrame.lean` (which has the tile `(n, n² − 1, n²)` built in) to the tile
`(a, b, c) = (e f, f² − e², f²)`.  Paper: Theorem `thm:siderunall` and its proof (section "Lattice", "Notation").

Reused by importing: `SideRunTools` (generic), `Tg`, `gA`, `gB`, `Tg_bounds`, `mem_interior_Tg`, ... of
`SideRunFrame` (generic first part), `W2E1.Ty` with `aL`, `aR`, `gR`, `gL` (they do not depend on `e`).
Copied and generalized (everything that has the tile built in):

  `rtG e f = √(4f² − e²)`, `uuG e f = e² (3f² − e²) / (2f²)` (the abscissa of the apex of a `c`-tile, from the `β` end),
  `hhG e f = e (f² − e²) rtG / (2f²)` (its height), `nuG e f = (f² − e²) / f²` (`= b / c`),
  `Ty.lenG`, `Ty.sLG`, `Ty.sRG`, `BaseTileG`, `ModelDataG`, `TileOK`, `SetupG`, `localAngle_of_oppSideG`,
  `angle_at_vertexG`, `sides_of_a_edgeG` ..., `edge_length_casesG`, `base_chain_genG`, `typed_chain`, the corners.

THE ANGLE INPUT.  `SetupG` carries `hA : AngleData α β γ` exactly as `SideRunFrame.Setup` does (`γ = 2α + β`,
`3α + 2β = π`, `α ≠ β`, `α` not a rational multiple of `π`).  This is NOT an extra assumption for a real member: for every
`1 ≤ e < f` the model angles satisfy it (`angleData_model`, below), the irrationality being `BaseBetaE1.tile_alpha_irrational`
(Niven's theorem, general in `e`, no coprimality) at `sin (α/2) = e/(2f)`.  The figure lemma (F) of the paper is `figF`.
The only hypothesis beyond the e = 1 `Setup` is `hco : Nat.Coprime e f`; it is used for one fact, `a ≠ b`
(`TileOK.hab`: `e f ≠ f² − e²`), which the angle reading `angle_at_vertexG` needs.

What replaces the e = 1 facts:  `three_alpha_lt_beta` (false for (2,3), (3,4), (5,6), (2,5)) and `alpha_lt_beta` (reversed at
(2,3)) are NOT generalized; `figF` and `AngleData.hαβ : α ≠ β` take their place.

WITNESSES.  Do real dissections satisfy the hypotheses of `SetupG`?
  * `e = 1`: YES, VERIFIED.  `SideRun.side_theorem_witness` gives a `Setup` for a normal form of the seed tiling of
    `W_f(1, f)`, every `f ≥ 2`; `setupG_one_iff` (below) turns it into a `SetupG`; this is `setupG_witness_one` in
    `SideRunGWitness.lean`.
  * `e ≥ 2`: NAMED, NOT VERIFIED.  The analogous witness is the normal form (isometry putting `QB` on the `x`-axis, model
    relabelled so that its opposite sides are `(e f, f² − e², f²)`) of the seed tiling of `W_f(e, f)` (it exists for every
    member: `CollarG.wTilable_seed e f`), or of the kernel-checked tiling of `W_4(2, 3)` by 224 tiles `(6, 5, 9)`
    (`Draft/W23.lean`, `w23_scale4`).  The passage from `HasSides` on target and model to a `SetupG` is `setup_of_sides`
    for general `e` (analogue of `SideRunMain.setup_of_sides`), which is the piece SideRunGMain, not written.
  * verified for every coprime member: `TileOK` (`tileOK_of_nat`), and `AngleData` of the model angles
    (`angleData_model`), so the field `hA` is satisfiable and carries no hypothesis the tile does not already satisfy.

No sorry, no native_decide.  Checks at `e = 1` at the end of the file (`setupG_one_iff`, `cos_gamma_e1`, `beta_eq_e1`,
`corner_left_ab_e1`, `corner_right_beta_e1`, `typed_chain_e1`).
-/
import Erdos634.Draft.SideRunFrame
import Erdos634.BaseBetaE1

open scoped Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Erdos634.Draft.SideRunG

open Erdos634.Geometry Erdos634.CertCoord Erdos634.MarchKillsFan Erdos634.MarchSlots
  Erdos634.MarchInduction Erdos634.MarchKills Erdos634.BaseBetaTargetCoord Erdos634.MarchCompose
  Erdos634.RunPartition Erdos634.E1BaseWord Erdos634.WallEndpoints Erdos634.BaseChain
  Erdos634.Placement Erdos634.OrientBridge Erdos634.ChainInstance Erdos634.TilePlacement
  Erdos634.Geometry.Dissection Erdos634.Draft.W2E1 Erdos634.Draft.SideRun Set

/-! ## 1. The constants of the tile `(e f, f² − e², f²)` -/

section consts
variable {e f : ℝ}

theorem arg_pos (he : 0 < e) (hef : e < f) : 0 < 4 * f ^ 2 - e ^ 2 := by
  nlinarith [mul_pos (sub_pos.2 hef) (add_pos he (he.trans hef)), sq_nonneg f]

/-- `r = √(4f² − e²)` -/
noncomputable def rtG (e f : ℝ) : ℝ := Real.sqrt (4 * f ^ 2 - e ^ 2)

theorem rtG_sq (he : 0 < e) (hef : e < f) : rtG e f ^ 2 = 4 * f ^ 2 - e ^ 2 :=
  Real.sq_sqrt (arg_pos he hef).le

theorem rtG_pos (he : 0 < e) (hef : e < f) : 0 < rtG e f := Real.sqrt_pos.mpr (arg_pos he hef)

/-- the abscissa of the apex of a `c`-tile, from its `β` end: `a cos β = e² (3f² − e²) / (2f²)` -/
noncomputable def uuG (e f : ℝ) : ℝ := e ^ 2 * (3 * f ^ 2 - e ^ 2) / (2 * f ^ 2)

/-- the height of the apex of a `c`-tile: `a sin β = e (f² − e²) √(4f² − e²) / (2f²)` -/
noncomputable def hhG (e f : ℝ) : ℝ := e * (f ^ 2 - e ^ 2) * rtG e f / (2 * f ^ 2)

/-- `ν = b / c` -/
noncomputable def nuG (e f : ℝ) : ℝ := (f ^ 2 - e ^ 2) / f ^ 2

theorem b_posG (he : 0 < e) (hef : e < f) : 0 < f ^ 2 - e ^ 2 := by
  nlinarith [mul_pos (sub_pos.2 hef) (add_pos he (he.trans hef))]

theorem two_f2_pos (he : 0 < e) (hef : e < f) : (0 : ℝ) < 2 * f ^ 2 := by
  have := he.trans hef; positivity

theorem uuG_spec (he : 0 < e) (hef : e < f) :
    2 * f ^ 2 * uuG e f = e ^ 2 * (3 * f ^ 2 - e ^ 2) := by
  have h0 := two_f2_pos he hef
  have := div_mul_cancel₀ (e ^ 2 * (3 * f ^ 2 - e ^ 2)) h0.ne'
  unfold uuG; linear_combination this

theorem hhG_spec (he : 0 < e) (hef : e < f) :
    2 * f ^ 2 * hhG e f = e * (f ^ 2 - e ^ 2) * rtG e f := by
  have h0 := two_f2_pos he hef
  have := div_mul_cancel₀ (e * (f ^ 2 - e ^ 2) * rtG e f) h0.ne'
  unfold hhG; linear_combination this

theorem hhG_pos (he : 0 < e) (hef : e < f) : 0 < hhG e f := by
  have hb := b_posG he hef
  unfold hhG
  exact div_pos (mul_pos (mul_pos he hb) (rtG_pos he hef)) (two_f2_pos he hef)

theorem uuG_pos (he : 0 < e) (hef : e < f) : 0 < uuG e f := by
  have h3 : 0 < 3 * f ^ 2 - e ^ 2 := by nlinarith [b_posG he hef, sq_nonneg f]
  unfold uuG
  exact div_pos (mul_pos (pow_pos he 2) h3) (two_f2_pos he hef)

theorem nuG_spec (he : 0 < e) (hef : e < f) : f ^ 2 * nuG e f = f ^ 2 - e ^ 2 := by
  have h : f ^ 2 ≠ 0 := by have := he.trans hef; positivity
  unfold nuG
  rw [mul_comm]
  exact div_mul_cancel₀ _ h

theorem nuG_pos (he : 0 < e) (hef : e < f) : 0 < nuG e f := by
  have h : (0 : ℝ) < f ^ 2 := by have := he.trans hef; positivity
  unfold nuG
  exact div_pos (b_posG he hef) h

theorem nuG_lt_one (he : 0 < e) (hef : e < f) : nuG e f < 1 := by
  have h : (0 : ℝ) < f ^ 2 := by have := he.trans hef; positivity
  unfold nuG
  rw [div_lt_one h]
  nlinarith [pow_pos he 2]

/-- the height squared: `h² = a² − u²` (the apex is at distance `a` from the `β` end) -/
theorem hhG_sq (he : 0 < e) (hef : e < f) : hhG e f ^ 2 = (e * f) ^ 2 - uuG e f ^ 2 := by
  have hu := uuG_spec he hef
  have hh' := hhG_spec he hef
  have hr := rtG_sq he hef
  have hf0 : 0 < f := he.trans hef
  have h0 : (0 : ℝ) < (2 * f ^ 2) ^ 2 := by positivity
  have key : (2 * f ^ 2) ^ 2 * (hhG e f ^ 2 - ((e * f) ^ 2 - uuG e f ^ 2)) = 0 := by
    have ee : (2 * f ^ 2) ^ 2 * (hhG e f ^ 2 - ((e * f) ^ 2 - uuG e f ^ 2))
        = (2 * f ^ 2 * hhG e f) ^ 2 - (2 * f ^ 2) ^ 2 * (e * f) ^ 2 + (2 * f ^ 2 * uuG e f) ^ 2 := by
      ring
    rw [ee, hu, hh']
    linear_combination (e ^ 2 * (f ^ 2 - e ^ 2) ^ 2) * hr
  rcases mul_eq_zero.mp key with h | h
  · exact absurd h h0.ne'
  · linarith

/-- the height squared: `h² = b² − (c − u)²` (the apex is at distance `b` from the `α` end) -/
theorem hhG_sq' (he : 0 < e) (hef : e < f) :
    hhG e f ^ 2 = (f ^ 2 - e ^ 2) ^ 2 - (f ^ 2 - uuG e f) ^ 2 := by
  have h1 := hhG_sq he hef
  have hu := uuG_spec he hef
  linear_combination h1 - hu

end consts

/-! ## 2. The tile: distinct sides, the model data -/

/-- `0 < e < f` and `a ≠ b` (the third inequality needs `gcd (e, f) = 1`: see `tileOK_of_nat`) -/
structure TileOK (e f : ℝ) : Prop where
  he : 0 < e
  hef : e < f
  hab : e * f ≠ f ^ 2 - e ^ 2

namespace TileOK

variable {e f : ℝ}

theorem f0 (T : TileOK e f) : 0 < f := T.he.trans T.hef

theorem ac (T : TileOK e f) : e * f ≠ f ^ 2 := by
  intro h
  nlinarith [mul_pos T.f0 (sub_pos.2 T.hef)]

theorem bc (T : TileOK e f) : f ^ 2 - e ^ 2 ≠ f ^ 2 := by
  intro h
  nlinarith [pow_pos T.he 2]

theorem b_pos (T : TileOK e f) : 0 < f ^ 2 - e ^ 2 := b_posG T.he T.hef

end TileOK

/-- **`a ≠ b` for a coprime member**: `e f = f² − e²` would give `e ∣ f²`, hence `e = 1`, hence `f² = f + 1`. -/
theorem tileOK_of_nat {e f : ℕ} (he : 1 ≤ e) (hef : e < f) (hco : Nat.Coprime e f) :
    TileOK (e : ℝ) (f : ℝ) := by
  refine ⟨Nat.cast_pos.mpr (by omega), by exact_mod_cast hef, ?_⟩
  intro h
  have h' : e * f + e ^ 2 = f ^ 2 := by
    have h1 : (e : ℝ) * f + (e : ℝ) ^ 2 = (f : ℝ) ^ 2 := by linarith
    exact_mod_cast h1
  have hd : e ∣ f ^ 2 := ⟨f + e, by rw [← h']; ring⟩
  have h1 : e = 1 := (Nat.Coprime.pow_right 2 hco).eq_one_of_dvd hd
  subst h1
  nlinarith

/-- **`ModelDataG D e f α β γ`**: the model of the dissection `D` is the tile with opposite sides
`(e f, f² − e², f²)` and corner angles `α, β, γ` (the generalization of `MarchKillsFan.ModelData`). -/
structure ModelDataG {N : ℕ} (D : CongruentDissection N) (e f α β γ : ℝ) : Prop where
  hs0 : sideOpp D.model 0 = e * f
  hs1 : sideOpp D.model 1 = f ^ 2 - e ^ 2
  hs2 : sideOpp D.model 2 = f ^ 2
  hα' : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α
  hβ' : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β
  hγ' : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ

/-- a tile's local angle at a vertex, read off the opposite side (general side values; the same proof as
`MarchKillsFan.localAngle_of_oppSide`) -/
theorem localAngle_of_oppSideG {N : ℕ} (D : CongruentDissection N) {a b c α β γ : ℝ}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hs0 : sideOpp D.model 0 = a) (hs1 : sideOpp D.model 1 = b) (hs2 : sideOpp D.model 2 = c)
    (hα' : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hβ' : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hγ' : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    (i : Fin N) (j : Fin 3) :
    (dist ((D.tile i).pts (j + 1)) ((D.tile i).pts (j + 2)) = a →
      (D.tile i).localAngle ((D.tile i).pts j) = α) ∧
    (dist ((D.tile i).pts (j + 1)) ((D.tile i).pts (j + 2)) = b →
      (D.tile i).localAngle ((D.tile i).pts j) = β) ∧
    (dist ((D.tile i).pts (j + 1)) ((D.tile i).pts (j + 2)) = c →
      (D.tile i).localAngle ((D.tile i).pts j) = γ) := by
  rw [Tri.localAngle_vertex]
  obtain ⟨k, hk, hd⟩ :=
    Erdos634.CornerBaseEdgesReal.congruent_opposite_side (D.tiles_congruent i).symm j
  rw [hk]
  simp only [sideOpp] at hs0 hs1 hs2
  fin_cases k <;> simp at hd hs0 hs1 hs2 ⊢
  · refine ⟨fun _ => hα', fun h => ?_, fun h => ?_⟩
    · exact absurd (hs0.symm.trans (hd.trans h)) hab
    · exact absurd (hs0.symm.trans (hd.trans h)) hac
  · refine ⟨fun h => ?_, fun _ => hβ', fun h => ?_⟩
    · exact absurd (hs1.symm.trans (hd.trans h)) hab.symm
    · exact absurd (hs1.symm.trans (hd.trans h)) hbc
  · refine ⟨fun h => ?_, fun h => ?_, fun _ => hγ'⟩
    · exact absurd (hs2.symm.trans (hd.trans h)) hac.symm
    · exact absurd (hs2.symm.trans (hd.trans h)) hbc.symm

/-- the model's three side lengths -/
theorem model_distsG {N : ℕ} (D : CongruentDissection N) {e f α β γ : ℝ}
    (hM : ModelDataG D e f α β γ) :
    dist (D.model.pts 0) (D.model.pts 1) = f ^ 2 ∧ dist (D.model.pts 1) (D.model.pts 2) = e * f ∧
    dist (D.model.pts 2) (D.model.pts 0) = f ^ 2 - e ^ 2 := by
  have h0 := hM.hs0; have h1 := hM.hs1; have h2 := hM.hs2
  simp only [sideOpp] at h0 h1 h2
  refine ⟨?_, ?_, ?_⟩
  · simpa using h2
  · simpa using h0
  · simpa using h1

/-- every edge of a tile has one of the three lengths -/
theorem edge_length_casesG {N : ℕ} (D : CongruentDissection N) {e f α β γ : ℝ}
    (hM : ModelDataG D e f α β γ) (i : Fin N) (k : Fin 3) :
    dist ((D.tile i).pts k) ((D.tile i).pts (k + 1)) = e * f ∨
    dist ((D.tile i).pts k) ((D.tile i).pts (k + 1)) = f ^ 2 - e ^ 2 ∨
    dist ((D.tile i).pts k) ((D.tile i).pts (k + 1)) = f ^ 2 := by
  obtain ⟨σ, hσ⟩ := (D.tiles_congruent i).dist_eq
  obtain ⟨m01, m12, m20⟩ := model_distsG D hM
  have m10 : dist (D.model.pts 1) (D.model.pts 0) = f ^ 2 := by rw [dist_comm]; exact m01
  have m21 : dist (D.model.pts 2) (D.model.pts 1) = e * f := by rw [dist_comm]; exact m12
  have m02 : dist (D.model.pts 0) (D.model.pts 2) = f ^ 2 - e ^ 2 := by rw [dist_comm]; exact m20
  have hk : k ≠ k + 1 := by fin_cases k <;> decide
  have hne : σ k ≠ σ (k + 1) := fun h => hk (σ.injective h)
  rw [hσ]
  generalize σ k = p at hne ⊢
  generalize σ (k + 1) = q at hne ⊢
  fin_cases p <;> fin_cases q <;> simp_all

/-- **The local angle at a vertex, read off the opposite side.** -/
theorem angle_at_vertexG {N : ℕ} (D : CongruentDissection N) {e f α β γ : ℝ} (T : TileOK e f)
    (hM : ModelDataG D e f α β γ) (i : Fin N) {k m j : Fin 3} (hkm : k ≠ m) (hkj : k ≠ j)
    (hmj : m ≠ j) :
    (dist ((D.tile i).pts m) ((D.tile i).pts j) = e * f →
      (D.tile i).localAngle ((D.tile i).pts k) = α) ∧
    (dist ((D.tile i).pts m) ((D.tile i).pts j) = f ^ 2 - e ^ 2 →
      (D.tile i).localAngle ((D.tile i).pts k) = β) ∧
    (dist ((D.tile i).pts m) ((D.tile i).pts j) = f ^ 2 →
      (D.tile i).localAngle ((D.tile i).pts k) = γ) := by
  have h := localAngle_of_oppSideG D T.hab T.ac T.bc hM.hs0 hM.hs1 hM.hs2 hM.hα' hM.hβ' hM.hγ' i k
  rcases fin3_succ k m j hkm hkj hmj with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2] at h; exact h
  · rw [h1, h2, dist_comm ((D.tile i).pts j) ((D.tile i).pts m)] at h; exact h

/-- **The sides at the third vertex of an `a`-edge**: `{c, b}` in one of the two orders. -/
theorem sides_of_a_edgeG {N : ℕ} (D : CongruentDissection N) {e f α β γ : ℝ} (T : TileOK e f)
    (hM : ModelDataG D e f α β γ) (j : Fin N) {k m n : Fin 3} (hkm : k ≠ m) (hkn : k ≠ n)
    (hmn : m ≠ n) (hd : dist ((D.tile j).pts k) ((D.tile j).pts m) = e * f) :
    (dist ((D.tile j).pts n) ((D.tile j).pts k) = f ^ 2 ∧
      dist ((D.tile j).pts n) ((D.tile j).pts m) = f ^ 2 - e ^ 2) ∨
    (dist ((D.tile j).pts n) ((D.tile j).pts k) = f ^ 2 - e ^ 2 ∧
      dist ((D.tile j).pts n) ((D.tile j).pts m) = f ^ 2) := by
  obtain ⟨σ, hσ⟩ := (D.tiles_congruent j).dist_eq
  obtain ⟨m01, m12, m20⟩ := model_distsG D hM
  have m10 : dist (D.model.pts 1) (D.model.pts 0) = f ^ 2 := by rw [dist_comm]; exact m01
  have m21 : dist (D.model.pts 2) (D.model.pts 1) = e * f := by rw [dist_comm]; exact m12
  have m02 : dist (D.model.pts 0) (D.model.pts 2) = f ^ 2 - e ^ 2 := by rw [dist_comm]; exact m20
  have hinj := σ.injective
  have hkm' : σ k ≠ σ m := fun h => hkm (hinj h)
  have hkn' : σ k ≠ σ n := fun h => hkn (hinj h)
  have hmn' : σ m ≠ σ n := fun h => hmn (hinj h)
  rw [hσ] at hd; rw [hσ, hσ]
  generalize σ k = sk at hd hkm' hkn' ⊢
  generalize σ m = sm at hd hkm' hmn' ⊢
  generalize σ n = sn at hkn' hmn' ⊢
  have hff : f ^ 2 ≠ e * f := T.ac.symm
  have hff' : f ^ 2 - e ^ 2 ≠ e * f := T.hab.symm
  fin_cases sk <;> fin_cases sm <;> fin_cases sn <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue, m01, m12, m20, m10, m21, m02,
      dist_self] at hd hkm' hkn' hmn' ⊢ <;>
    first
    | exact absurd rfl hkm'
    | exact absurd rfl hkn'
    | exact absurd rfl hmn'
    | exact absurd hd hff
    | exact absurd hd hff'
    | simp

/-- **The sides at the third vertex of a `b`-edge**: `{a, c}` in one of the two orders. -/
theorem sides_of_b_edgeG {N : ℕ} (D : CongruentDissection N) {e f α β γ : ℝ} (T : TileOK e f)
    (hM : ModelDataG D e f α β γ) (j : Fin N) {k m n : Fin 3} (hkm : k ≠ m) (hkn : k ≠ n)
    (hmn : m ≠ n) (hd : dist ((D.tile j).pts k) ((D.tile j).pts m) = f ^ 2 - e ^ 2) :
    (dist ((D.tile j).pts n) ((D.tile j).pts k) = e * f ∧
      dist ((D.tile j).pts n) ((D.tile j).pts m) = f ^ 2) ∨
    (dist ((D.tile j).pts n) ((D.tile j).pts k) = f ^ 2 ∧
      dist ((D.tile j).pts n) ((D.tile j).pts m) = e * f) := by
  obtain ⟨σ, hσ⟩ := (D.tiles_congruent j).dist_eq
  obtain ⟨m01, m12, m20⟩ := model_distsG D hM
  have m10 : dist (D.model.pts 1) (D.model.pts 0) = f ^ 2 := by rw [dist_comm]; exact m01
  have m21 : dist (D.model.pts 2) (D.model.pts 1) = e * f := by rw [dist_comm]; exact m12
  have m02 : dist (D.model.pts 0) (D.model.pts 2) = f ^ 2 - e ^ 2 := by rw [dist_comm]; exact m20
  have hinj := σ.injective
  have hkm' : σ k ≠ σ m := fun h => hkm (hinj h)
  have hkn' : σ k ≠ σ n := fun h => hkn (hinj h)
  have hmn' : σ m ≠ σ n := fun h => hmn (hinj h)
  rw [hσ] at hd; rw [hσ, hσ]
  generalize σ k = sk at hd hkm' hkn' ⊢
  generalize σ m = sm at hd hkm' hmn' ⊢
  generalize σ n = sn at hkn' hmn' ⊢
  have hff : f ^ 2 ≠ f ^ 2 - e ^ 2 := T.bc.symm
  have hff' : e * f ≠ f ^ 2 - e ^ 2 := T.hab
  fin_cases sk <;> fin_cases sm <;> fin_cases sn <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue, m01, m12, m20, m10, m21, m02,
      dist_self] at hd hkm' hkn' hmn' ⊢ <;>
    first
    | exact absurd rfl hkm'
    | exact absurd rfl hkn'
    | exact absurd rfl hmn'
    | exact absurd hd hff
    | exact absurd hd hff'
    | simp

/-- **The sides at the third vertex of a `c`-edge**: `{a, b}` in one of the two orders. -/
theorem sides_of_c_edgeG {N : ℕ} (D : CongruentDissection N) {e f α β γ : ℝ} (T : TileOK e f)
    (hM : ModelDataG D e f α β γ) (j : Fin N) {k m n : Fin 3} (hkm : k ≠ m) (hkn : k ≠ n)
    (hmn : m ≠ n) (hd : dist ((D.tile j).pts k) ((D.tile j).pts m) = f ^ 2) :
    (dist ((D.tile j).pts n) ((D.tile j).pts k) = e * f ∧
      dist ((D.tile j).pts n) ((D.tile j).pts m) = f ^ 2 - e ^ 2) ∨
    (dist ((D.tile j).pts n) ((D.tile j).pts k) = f ^ 2 - e ^ 2 ∧
      dist ((D.tile j).pts n) ((D.tile j).pts m) = e * f) := by
  obtain ⟨σ, hσ⟩ := (D.tiles_congruent j).dist_eq
  obtain ⟨m01, m12, m20⟩ := model_distsG D hM
  have m10 : dist (D.model.pts 1) (D.model.pts 0) = f ^ 2 := by rw [dist_comm]; exact m01
  have m21 : dist (D.model.pts 2) (D.model.pts 1) = e * f := by rw [dist_comm]; exact m12
  have m02 : dist (D.model.pts 0) (D.model.pts 2) = f ^ 2 - e ^ 2 := by rw [dist_comm]; exact m20
  have hinj := σ.injective
  have hkm' : σ k ≠ σ m := fun h => hkm (hinj h)
  have hkn' : σ k ≠ σ n := fun h => hkn (hinj h)
  have hmn' : σ m ≠ σ n := fun h => hmn (hinj h)
  rw [hσ] at hd; rw [hσ, hσ]
  generalize σ k = sk at hd hkm' hkn' ⊢
  generalize σ m = sm at hd hkm' hmn' ⊢
  generalize σ n = sn at hkn' hmn' ⊢
  have hff : f ^ 2 - e ^ 2 ≠ f ^ 2 := T.bc
  have hff' : e * f ≠ f ^ 2 := T.ac
  fin_cases sk <;> fin_cases sm <;> fin_cases sn <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue, m01, m12, m20, m10, m21, m02,
      dist_self] at hd hkm' hkn' hmn' ⊢ <;>
    first
    | exact absurd rfl hkm'
    | exact absurd rfl hkn'
    | exact absurd rfl hmn'
    | exact absurd hd hff
    | exact absurd hd hff'
    | simp

end Erdos634.Draft.SideRunG

/-! ## 3. The six types with the general edge lengths -/

namespace Erdos634.Draft.W2E1.Ty

/-- the length of the letter: `a = e f`, `b = f² − e²`, `c = f²` -/
noncomputable def lenG (e f : ℝ) : Ty → ℝ
  | A1 => e * f | A2 => e * f | B1 => f ^ 2 - e ^ 2 | B2 => f ^ 2 - e ^ 2 | C1 => f ^ 2 | C2 => f ^ 2

/-- the side from the apex to the left end -/
noncomputable def sLG (e f : ℝ) : Ty → ℝ
  | A1 => f ^ 2 | A2 => f ^ 2 - e ^ 2 | B1 => f ^ 2 | B2 => e * f | C1 => f ^ 2 - e ^ 2 | C2 => e * f

/-- the side from the apex to the right end -/
noncomputable def sRG (e f : ℝ) : Ty → ℝ
  | A1 => f ^ 2 - e ^ 2 | A2 => f ^ 2 | B1 => e * f | B2 => f ^ 2 | C1 => e * f | C2 => f ^ 2 - e ^ 2

theorem lenG_pos {e f : ℝ} (he : 0 < e) (hef : e < f) (t : Ty) : 0 < t.lenG e f := by
  have hf := he.trans hef
  have hb : 0 < f ^ 2 - e ^ 2 := by nlinarith [mul_pos (sub_pos.2 hef) (add_pos he hf)]
  cases t <;> simp only [lenG] <;> first | exact mul_pos he hf | exact hb | positivity

/-- at `e = 1` the general lengths are those of `W2E1.Ty` -/
theorem lenG_one (f : ℝ) (t : Ty) : t.lenG 1 f = t.lenR f := by
  cases t <;> simp [lenG, lenR]

theorem sLG_one (f : ℝ) (t : Ty) : t.sLG 1 f = t.sL f := by
  cases t <;> simp [sLG, sL]

theorem sRG_one (f : ℝ) (t : Ty) : t.sRG 1 f = t.sR f := by
  cases t <;> simp [sRG, sR]

end Erdos634.Draft.W2E1.Ty

namespace Erdos634.Draft.SideRunG

open Erdos634.Geometry Erdos634.CertCoord Erdos634.MarchKillsFan Erdos634.MarchSlots
  Erdos634.MarchInduction Erdos634.MarchKills Erdos634.BaseBetaTargetCoord Erdos634.MarchCompose
  Erdos634.RunPartition Erdos634.E1BaseWord Erdos634.WallEndpoints Erdos634.BaseChain
  Erdos634.Placement Erdos634.OrientBridge Erdos634.ChainInstance Erdos634.TilePlacement
  Erdos634.Geometry.Dissection Erdos634.Draft.W2E1 Erdos634.Draft.SideRun Set

/-- **Tile `i` is a base tile of type `t` at `x`** (general member): it has the vertices `(x, 0)` and
`(x + len t, 0)`, and its third vertex is at the distances prescribed by the type from these two. -/
def BaseTileG {N : ℕ} (D : CongruentDissection N) (e f : ℝ) (i : Fin N) (t : Ty) (x : ℝ) : Prop :=
  ∃ k m j : Fin 3, k ≠ m ∧ k ≠ j ∧ m ≠ j ∧ (D.tile i).pts k = mkPt x 0 ∧
    (D.tile i).pts m = mkPt (x + t.lenG e f) 0 ∧
    dist ((D.tile i).pts j) ((D.tile i).pts k) = t.sLG e f ∧
    dist ((D.tile i).pts j) ((D.tile i).pts m) = t.sRG e f

/-- the angles of a tile with three named vertices, read off the opposite sides -/
theorem _root_.Erdos634.Draft.SideRun.HasV.anglesG {N : ℕ} {D : CongruentDissection N} {t : Fin N}
    {A B C : Plane} {e f α β γ : ℝ} (T : TileOK e f) (hM : ModelDataG D e f α β γ)
    (h : HasV D t A B C) :
    (dist B C = e * f → (D.tile t).localAngle A = α) ∧
    (dist B C = f ^ 2 - e ^ 2 → (D.tile t).localAngle A = β) ∧
    (dist B C = f ^ 2 → (D.tile t).localAngle A = γ) := by
  obtain ⟨k, m, j, hkm, hkj, hmj, hk, hm, hj⟩ := h
  have hA := angle_at_vertexG D T hM t hkm hkj hmj
  rw [hk, hm, hj] at hA
  exact hA


/-! ## 4. The model angles, and the figure lemma (F) -/

/-- `β` is the model angle `modelBeta e f` for any model with `ModelDataG`: the law of cosines on the model's own
vertex `1` -/
theorem beta_eqG {N : ℕ} (D : CongruentDissection N) {e f α β γ : ℝ} (T : TileOK e f)
    (hM : ModelDataG D e f α β γ) : β = modelBeta e f := by
  have hf0 := T.f0
  have he := T.he
  have hef := T.hef
  have hs0 : dist (D.model.pts 1) (D.model.pts 2) = e * f := hM.hs0
  have hs1 : dist (D.model.pts 2) (D.model.pts 0) = f ^ 2 - e ^ 2 := hM.hs1
  have hs2 : dist (D.model.pts 0) (D.model.pts 1) = f ^ 2 := hM.hs2
  have hcos := Erdos634.AngleThreshold.cos_of_sides (D.model.pts 2) (D.model.pts 1) (D.model.pts 0)
    (by rw [dist_comm, hs0]; exact (mul_pos he hf0).ne') (by rw [hs2]; positivity)
  rw [hM.hβ', dist_comm (D.model.pts 2), hs0, hs2, hs1] at hcos
  have hb := cos_modelBeta he hef
  rw [← hM.hβ']
  refine cornerAngle_eq_of_cos (modelBeta_mem he hef).1.le
    (by linarith [(modelBeta_mem he hef).2, Real.pi_pos]) ?_
  rw [hM.hβ', hcos, hb]
  unfold baseLen Nq
  have hB : 2 * (e * f) * f ^ 2 ≠ 0 := by positivity
  have hD : 2 * f ^ 3 ≠ 0 := by positivity
  rw [div_eq_div_iff hB hD]
  ring

/-- `sin (α/2) = e / (2f)` for the model angle `α` (from `cos α = (2f² − e²)/(2f²)`) -/
theorem sin_half_modelAlphaG {e f : ℝ} (he : 0 < e) (hef : e < f) :
    Real.sin (modelAlpha e f / 2) = e / (2 * f) := by
  have hf0 : 0 < f := he.trans hef
  have hb := modelBeta_mem he hef
  have hα0 : 0 < modelAlpha e f := by unfold modelAlpha; linarith [hb.2, Real.pi_pos]
  have hαπ : modelAlpha e f < Real.pi / 3 := by unfold modelAlpha; linarith [hb.1, Real.pi_pos]
  have hpi := Real.pi_pos
  have hsq : Real.sin (modelAlpha e f / 2) ^ 2 = (e / (2 * f)) ^ 2 := by
    rw [Real.sin_sq_eq_half_sub, show 2 * (modelAlpha e f / 2) = modelAlpha e f by ring,
      cos_modelAlpha he hef]
    field_simp
    ring
  have hnn : 0 ≤ Real.sin (modelAlpha e f / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  exact (sq_eq_sq₀ hnn (by positivity)).mp hsq

/-- **The angle bundle holds for the model angles of EVERY member `1 ≤ e < f`** (no coprimality): `α/π` is irrational
by Niven's theorem (`BaseBetaE1.tile_alpha_irrational`, general in `e`), `α ≠ β` because `α = β` would give
`α = π/5`.  So `SetupG.hA` is a field for convenience, as in the e = 1 `Setup`, and not an extra assumption. -/
theorem angleData_model (e f : ℕ) (he : 1 ≤ e) (hef : e < f) :
    AngleData (modelAlpha (e : ℝ) (f : ℝ)) (modelBeta (e : ℝ) (f : ℝ))
      (2 * modelAlpha (e : ℝ) (f : ℝ) + modelBeta (e : ℝ) (f : ℝ)) := by
  have he0 : (0 : ℝ) < e := Nat.cast_pos.mpr (by omega)
  have hef' : (e : ℝ) < f := by exact_mod_cast hef
  have hb := modelBeta_mem he0 hef'
  have hπ := Real.pi_pos
  have hα0 : 0 < modelAlpha (e : ℝ) (f : ℝ) := by unfold modelAlpha; linarith [hb.2]
  have hirr : ¬ ∃ r : ℚ, modelAlpha (e : ℝ) (f : ℝ) = (r : ℝ) * Real.pi :=
    Erdos634.BaseBetaE1.tile_alpha_irrational e f he hef _ (sin_half_modelAlphaG he0 hef')
  refine ⟨hα0, hb.1, ?_, rfl, modelAngle_rel _ _, hirr⟩
  intro h
  apply hirr
  refine ⟨1 / 5, ?_⟩
  have hrel := modelAngle_rel (e : ℝ) (f : ℝ)
  push_cast
  linarith

/-- **(F), the figure lemma** (paper, proof of `thm:siderunall`, item (F)): for integers, a relation
`x α + y β + z γ = k π` forces `2x − 3y + z = 0` and `k = 2y − x`.  Only `AngleData` is used (`3α + 2β = π`,
`γ = 2α + β`, `α/π` irrational). -/
theorem figF {α β γ : ℝ} (hA : AngleData α β γ) (x y z k : ℤ)
    (h : (x : ℝ) * α + y * β + z * γ = k * Real.pi) : 2 * x - 3 * y + z = 0 ∧ k = 2 * y - x := by
  have hβ : β = (Real.pi - 3 * α) / 2 := by linarith [hA.hrel]
  have hγ : γ = (Real.pi + α) / 2 := by linarith [hA.hγdef, hA.hrel]
  rw [hβ, hγ] at h
  obtain ⟨m, hm⟩ : ∃ m : ℤ, m = 2 * x - 3 * y + z := ⟨_, rfl⟩
  obtain ⟨n, hn⟩ : ∃ n : ℤ, n = 2 * k - y - z := ⟨_, rfl⟩
  have key : (m : ℝ) * α = (n : ℝ) * Real.pi := by
    rw [hm, hn]
    push_cast
    linear_combination 2 * h
  have hm0 : m = 0 := by
    by_contra hne
    have hne' : (m : ℝ) ≠ 0 := by exact_mod_cast hne
    apply hA.hirr
    refine ⟨(n : ℚ) / (m : ℚ), ?_⟩
    push_cast
    field_simp
    linarith [key]
  have h1 : (n : ℝ) * Real.pi = 0 := by rw [← key, hm0]; simp
  have h2 : (n : ℝ) = 0 := (mul_eq_zero.mp h1).resolve_right Real.pi_ne_zero
  have h3 : n = 0 := by exact_mod_cast h2
  constructor <;> omega

/-- the converse of `figF` -/
theorem figF_of {α β γ : ℝ} (hA : AngleData α β γ) (x y z k : ℤ) (h1 : 2 * x - 3 * y + z = 0)
    (h2 : k = 2 * y - x) : (x : ℝ) * α + y * β + z * γ = k * Real.pi := by
  have hβ : β = (Real.pi - 3 * α) / 2 := by linarith [hA.hrel]
  have hγ : γ = (Real.pi + α) / 2 := by linarith [hA.hγdef, hA.hrel]
  have hz : z = 3 * y - 2 * x := by omega
  subst h2
  rw [hβ, hγ, hz]
  push_cast
  ring

theorem figF_iff {α β γ : ℝ} (hA : AngleData α β γ) (x y z k : ℤ) :
    (x : ℝ) * α + y * β + z * γ = k * Real.pi ↔ 2 * x - 3 * y + z = 0 ∧ k = 2 * y - x :=
  ⟨figF hA x y z k, fun h => figF_of hA x y z k h.1 h.2⟩

/-! ## 5. The standing hypotheses -/

/-- **The standing hypotheses**: a congruent dissection `D` of the triangle `Q = (0,0)`, `B = (L,0)`,
`A = (ax, ay)` with the tile `(e f, f² − e², f²)`, `1 ≤ e < f`, `gcd (e, f) = 1`, and its angles.  For `e = 1` this is
`SideRun.Setup` (`setupG_one_iff`). -/
structure SetupG {N : ℕ} (D : CongruentDissection N) (e f : ℕ) (α β γ L ax ay : ℝ) : Prop where
  he : 1 ≤ e
  hef : e < f
  hco : Nat.Coprime e f
  hM : ModelDataG D (e : ℝ) (f : ℝ) α β γ
  hA : AngleData α β γ
  hL : 0 < L
  hay : 0 < ay
  htgt : ∀ (h1 : 0 < L) (h2 : 0 < ay), D.target = Tg L ax ay h1 h2

namespace SetupG

variable {N : ℕ} {D : CongruentDissection N} {e f : ℕ} {α β γ L ax ay : ℝ}

theorem tile (S : SetupG D e f α β γ L ax ay) : TileOK (e : ℝ) (f : ℝ) :=
  tileOK_of_nat S.he S.hef S.hco

theorem e0 (S : SetupG D e f α β γ L ax ay) : (0 : ℝ) < e := S.tile.he
theorem e1 (S : SetupG D e f α β γ L ax ay) : (1 : ℝ) ≤ e := by exact_mod_cast S.he
theorem hef' (S : SetupG D e f α β γ L ax ay) : (e : ℝ) < f := S.tile.hef
theorem hf2 (S : SetupG D e f α β γ L ax ay) : 2 ≤ f := by have := S.he; have := S.hef; omega
theorem f2 (S : SetupG D e f α β γ L ax ay) : (2 : ℝ) ≤ f := by exact_mod_cast S.hf2
theorem f1 (S : SetupG D e f α β γ L ax ay) : (1 : ℝ) < f := by have := S.f2; linarith
theorem f0 (S : SetupG D e f α β γ L ax ay) : (0 : ℝ) < f := by have := S.f2; linarith
theorem b_pos (S : SetupG D e f α β γ L ax ay) : (0 : ℝ) < (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := S.tile.b_pos
theorem c_pos (S : SetupG D e f α β γ L ax ay) : (0 : ℝ) < (f : ℝ) ^ 2 := by
  have := S.f0; positivity
theorem a_pos (S : SetupG D e f α β γ L ax ay) : (0 : ℝ) < (e : ℝ) * f := mul_pos S.e0 S.f0
theorem tgt (S : SetupG D e f α β γ L ax ay) : D.target = Tg L ax ay S.hL S.hay := S.htgt S.hL S.hay

theorem mem (S : SetupG D e f α β γ L ax ay) {p : Plane} (hp : p ∈ D.target.carrier) :
    0 ≤ p 1 ∧ 0 ≤ gA ax ay p ∧ 0 ≤ gB L ax ay p := by
  rw [S.tgt] at hp; exact Tg_bounds S.hL S.hay hp

theorem pts_mem (S : SetupG D e f α β γ L ax ay) (i : Fin N) (k : Fin 3) :
    0 ≤ ((D.tile i).pts k) 1 ∧ 0 ≤ gA ax ay ((D.tile i).pts k) ∧ 0 ≤ gB L ax ay ((D.tile i).pts k) :=
  S.mem (pts_mem_target D.toDissection i k)

theorem interior_seg (S : SetupG D e f α β γ L ax ay) {P Q : Plane} (hP : P ∈ D.target.carrier)
    (hQ : Q ∈ D.target.carrier) (h1 : 0 < P 1 ∨ 0 < Q 1)
    (h2 : 0 < gA ax ay P ∨ 0 < gA ax ay Q) (h3 : 0 < gB L ax ay P ∨ 0 < gB L ax ay Q) :
    openSegment ℝ P Q ⊆ interior D.target.carrier := by
  rw [S.tgt] at hP hQ ⊢; exact openSegment_interior_Tg S.hL S.hay hP hQ h1 h2 h3

/-- a point of the target with a point of the target strictly on its left is off the side `QA` -/
theorem gA_pos_of_left (S : SetupG D e f α β γ L ax ay) {x y t : ℝ} (ht : 0 < t)
    (h : mkPt (x - t) y ∈ D.target.carrier) : 0 < gA ax ay (mkPt x y) := by
  have h1 := (S.mem h).2.1
  rw [gA_mk] at h1 ⊢
  nlinarith [mul_pos S.hay ht]

/-- a point of the target with a point of the target strictly on its right is off the side `BA` -/
theorem gB_pos_of_right (S : SetupG D e f α β γ L ax ay) {x y t : ℝ} (ht : 0 < t)
    (h : mkPt (x + t) y ∈ D.target.carrier) : 0 < gB L ax ay (mkPt x y) := by
  have h1 := (S.mem h).2.2
  rw [gB_mk] at h1 ⊢
  nlinarith [mul_pos S.hay ht]

/-- a point of the side line `y = 0` in the target lies between `Q` and `B` -/
theorem base_range (S : SetupG D e f α β γ L ax ay) {x : ℝ} (h : mkPt x 0 ∈ D.target.carrier) :
    0 ≤ x ∧ x ≤ L := by
  obtain ⟨-, h2, h3⟩ := S.mem h
  rw [gA_mk] at h2
  rw [gB_mk] at h3
  have hay := S.hay
  constructor
  · by_contra hneg
    push Not at hneg
    nlinarith [mul_pos hay (neg_pos.mpr hneg)]
  · by_contra hneg
    push Not at hneg
    nlinarith [mul_pos hay (sub_pos.mpr hneg)]

/-- a line through a base point leaves the target below the base -/
theorem below_out (S : SetupG D e f α β γ L ax ay) {V G : Plane} (hV : V 1 = 0) (hG : 0 < G 1) :
    ∀ s : ℝ, 0 < s → V + s • (V - G) ∉ D.target.carrier := by
  intro s hs hmem
  have h := (S.mem hmem).1
  simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, hV] at h
  nlinarith [mul_pos hs hG]

theorem base_frontier (S : SetupG D e f α β γ L ax ay) {x : ℝ} (hx0 : 0 < x) (hxL : x < L) :
    mkPt x 0 ∈ frontier D.target.carrier ∧ mkPt x 0 ∉ Set.range D.target.pts := by
  rw [S.tgt]
  refine ⟨base_mem_frontier_Tg S.hL S.hay hx0.le hxL.le, not_vertex_Tg S.hL S.hay ?_ ?_ ?_⟩
  · exact mkPt_ne_of_fst hx0.ne'
  · exact mkPt_ne_of_fst hxL.ne
  · exact mkPt_ne_of_snd S.hay.ne

theorem angle_base (S : SetupG D e f α β γ L ax ay) {x : ℝ} (hx0 : 0 < x) (hxL : x < L) :
    D.target.localAngle (mkPt x 0) = Real.pi :=
  Tri.localAngle_frontier _ (S.base_frontier hx0 hxL).1 (S.base_frontier hx0 hxL).2

/-- **`β` is the model angle** -/
theorem beta_eq (S : SetupG D e f α β γ L ax ay) : β = modelBeta (e : ℝ) (f : ℝ) :=
  beta_eqG D S.tile S.hM

theorem alpha_eq (S : SetupG D e f α β γ L ax ay) : α = modelAlpha (e : ℝ) (f : ℝ) := by
  have h1 := S.beta_eq
  have h2 := modelAngle_rel (e : ℝ) (f : ℝ)
  have h3 := S.hA.hrel
  rw [← h1] at h2
  linarith

/-- **`cos γ = −e/(2f)`** -/
theorem cos_gamma (S : SetupG D e f α β γ L ax ay) : Real.cos γ = -(e : ℝ) / (2 * (f : ℝ)) := by
  obtain ⟨m01, m12, m20⟩ := model_distsG D S.hM
  have d02 : dist (D.model.pts 0) (D.model.pts 2) = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
    rw [dist_comm]; exact m20
  have ha := S.a_pos
  have hb := S.b_pos
  have he := S.e0
  have hf := S.f0
  have hcos := Erdos634.AngleThreshold.cos_of_sides (D.model.pts 0) (D.model.pts 2) (D.model.pts 1)
    (by rw [d02]; exact hb.ne') (by rw [m12]; exact ha.ne')
  rw [S.hM.hγ', d02, m12, m01] at hcos
  rw [hcos]
  have hB : 2 * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) * ((e : ℝ) * f) ≠ 0 :=
    (mul_pos (mul_pos two_pos hb) ha).ne'
  have hD : 2 * (f : ℝ) ≠ 0 := (mul_pos two_pos hf).ne'
  rw [div_eq_div_iff hB hD]
  ring

end SetupG


/-! ## 6. The base chain -/

/-- **The base chain, for a target with the side `[(0,0), (L,0)]` in the upper half-plane** (general member): the
same proof as `W2E1.base_chain_gen`; the edges of the chain have the lengths `a`, `b`, `c`. -/
theorem base_chain_genG {N : ℕ} (D : CongruentDissection N) {e f α β γ : ℝ} (hM : ModelDataG D e f α β γ)
    {L : ℝ} (hL : 0 < L) (hup : ∀ y ∈ D.target.carrier, 0 ≤ y 1)
    (hbase : segment ℝ (mkPt 0 0) (mkPt L 0) ⊆ frontier D.target.carrier)
    (hface : ∀ y ∈ D.target.carrier, y 1 = 0 → 0 ≤ y 0 ∧ y 0 ≤ L) :
    ∃ (n : ℕ) (X : ℕ → ℝ), 0 < n ∧ X 0 = 0 ∧ X n = L ∧
      (∀ m, m < n → X (m + 1) - X m = e * f ∨ X (m + 1) - X m = f ^ 2 - e ^ 2 ∨
        X (m + 1) - X m = f ^ 2) ∧
      (∀ m, m < n → ∃ (i : Fin N) (k k' : Fin 3), k ≠ k' ∧
        (D.tile i).pts k = mkPt (X m) 0 ∧ (D.tile i).pts k' = mkPt (X (m + 1)) 0) := by
  classical
  have hN : 0 < N := D.toDissection.pos
  have hwall : ∀ y ∈ D.target.carrier, gY y ≤ 0 := by
    intro y hy
    have := hup y hy
    rw [gY_apply]; linarith
  have hab : (mkPt 0 0 : Plane) ≠ mkPt L 0 := mkPt_ne_of_fst hL.ne
  have hdirab : xco (mkPt 0 0) ≤ xco (mkPt L 0) := by
    simp only [xco_apply, mkPt_zero]; exact hL.le
  have hline : ∀ y ∈ segment ℝ (mkPt 0 0) (mkPt L 0), gY y = 0 := by
    intro y hy
    obtain ⟨h1, -, -⟩ := (mem_base_segment_iff hL y).mp hy
    rw [gY_apply, h1, neg_zero]
  have hface' : ∀ y ∈ D.target.carrier, gY y = 0 → y ∈ segment ℝ (mkPt 0 0) (mkPt L 0) := by
    intro y hy hgy
    rw [gY_apply, neg_eq_zero] at hgy
    obtain ⟨h0, h1⟩ := hface y hy hgy
    exact (mem_base_segment_iff hL y).mpr ⟨hgy, h0, h1⟩
  have hthird := hthird_general D.toDissection gY 0 (by rw [gY_linear]; exact negY_ne_zero) hwall
  obtain ⟨E, n, hneq, hn0, hwest, heast, hjunc, hmem, -, -, -, -, -⟩ :=
    chain_endpoints hN D.toDissection gY 0 xco hker_base hwall (mkPt 0 0) (mkPt L 0)
      hab hdirab hbase hline hface' hthird
  have hW0 : ∀ m, m < n → (edgeWest D.toDissection xco (E m)) 1 = 0 ∧
      (edgeEast D.toDissection xco (E m)) 1 = 0 := by
    intro m hm
    obtain ⟨hw1, hw2⟩ := (mem_wallList D.toDissection gY 0 (E m)).mp (hmem m hm)
    rw [gY_apply, neg_eq_zero] at hw1 hw2
    rcases edgeWest_edgeEast_pts D.toDissection xco (E m) with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]; exact ⟨hw1, hw2⟩
    · rw [h1, h2]; exact ⟨hw2, hw1⟩
  have hWeq : ∀ m, m < n → edgeWest D.toDissection xco (E m)
      = mkPt (edgePos D.toDissection xco (E m)) 0 := by
    intro m hm
    rw [← dir_edgeWest, xco_apply]
    exact eq_mkPt_of_y_zero (hW0 m hm).1
  have hEeq : ∀ m, m < n → edgeEast D.toDissection xco (E m)
      = mkPt (edgeEnd D.toDissection xco (E m)) 0 := by
    intro m hm
    rw [← dir_edgeEast, xco_apply]
    exact eq_mkPt_of_y_zero (hW0 m hm).2
  have hlen : ∀ m, m < n → edgeEnd D.toDissection xco (E m) - edgePos D.toDissection xco (E m)
      = dist ((D.tile (E m).1).pts (E m).2) ((D.tile (E m).1).pts ((E m).2 + 1)) := by
    intro m hm
    obtain ⟨hw1, hw2⟩ := (mem_wallList D.toDissection gY 0 (E m)).mp (hmem m hm)
    rw [hiso_base _ _ hw1 hw2]
    show _ = |xco ((D.tile (E m).1).pts (E m).2) - xco ((D.tile (E m).1).pts ((E m).2 + 1))|
    unfold edgeEnd edgePos
    rcases le_total (xco ((D.tile (E m).1).pts (E m).2))
        (xco ((D.tile (E m).1).pts ((E m).2 + 1))) with h | h
    · rw [min_eq_left h, max_eq_right h, abs_of_nonpos (by linarith)]; ring
    · rw [min_eq_right h, max_eq_left h, abs_of_nonneg (by linarith)]
  set X : ℕ → ℝ := fun m => if m < n then edgePos D.toDissection xco (E m) else L with hXdef
  have hXlt : ∀ m, m < n → X m = edgePos D.toDissection xco (E m) := fun m hm => if_pos hm
  have hXsucc : ∀ m, m < n → X (m + 1) = edgeEnd D.toDissection xco (E m) := by
    intro m hm
    rcases Nat.lt_or_ge (m + 1) n with h | h
    · rw [hXlt _ h, ← dir_edgeWest, ← hjunc m h, dir_edgeEast]
    · have hmn : m = n - 1 := by omega
      show (if m + 1 < n then _ else L) = _
      rw [if_neg (by omega), ← dir_edgeEast, hmn, heast, xco_apply, mkPt_zero]
  refine ⟨n, X, hn0, ?_, ?_, ?_, ?_⟩
  · rw [hXlt 0 hn0, ← dir_edgeWest, hwest, xco_apply, mkPt_zero]
  · show (if n < n then _ else L) = _
    rw [if_neg (lt_irrefl n)]
  · intro m hm
    rw [hXsucc m hm, hXlt m hm, hlen m hm]
    exact edge_length_casesG D hM (E m).1 (E m).2
  · intro m hm
    have hne := fin3_succ_ne (E m).2
    rcases edgeWest_edgeEast_pts D.toDissection xco (E m) with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · refine ⟨(E m).1, (E m).2, (E m).2 + 1, hne.2.1.symm, ?_, ?_⟩
      · rw [← h1, hWeq m hm, hXlt m hm]
      · rw [← h2, hEeq m hm, hXsucc m hm]
    · refine ⟨(E m).1, (E m).2 + 1, (E m).2, hne.2.1, ?_, ?_⟩
      · rw [← h1, hWeq m hm, hXlt m hm]
      · rw [← h2, hEeq m hm, hXsucc m hm]

/-! ## 7. Base tiles -/

namespace SetupG

variable {N : ℕ} {D : CongruentDissection N} {e f : ℕ} {α β γ L ax ay : ℝ}

/-- **The angles of a base tile at its two ends.** -/
theorem angles (S : SetupG D e f α β γ L ax ay) {i : Fin N} {t : Ty} {x : ℝ}
    (h : BaseTileG D (e : ℝ) (f : ℝ) i t x) :
    (D.tile i).localAngle (mkPt x 0) = t.aL α β γ ∧
    (D.tile i).localAngle (mkPt (x + t.lenG (e : ℝ) (f : ℝ)) 0) = t.aR α β γ := by
  obtain ⟨k, m, j, hkm, hkj, hmj, hk, hm, hsL, hsR⟩ := h
  have hL := angle_at_vertexG D S.tile S.hM i hkm hkj hmj
  have hR := angle_at_vertexG D S.tile S.hM i (Ne.symm hkm) hmj hkj
  rw [hk] at hL
  rw [hm] at hR
  rw [dist_comm] at hsL hsR
  cases t
  · exact ⟨hL.2.1 hsR, hR.2.2 hsL⟩
  · exact ⟨hL.2.2 hsR, hR.2.1 hsL⟩
  · exact ⟨hL.1 hsR, hR.2.2 hsL⟩
  · exact ⟨hL.2.2 hsR, hR.1 hsL⟩
  · exact ⟨hL.1 hsR, hR.2.1 hsL⟩
  · exact ⟨hL.2.1 hsR, hR.1 hsL⟩

/-- **The apex of a base tile**: above the side, at the two prescribed distances; it is the only vertex of the tile
off the side. -/
theorem apex (S : SetupG D e f α β γ L ax ay) {i : Fin N} {t : Ty} {x : ℝ}
    (h : BaseTileG D (e : ℝ) (f : ℝ) i t x) :
    ∃ p : Plane, p ∈ Set.range (D.tile i).pts ∧ 0 < p 1 ∧
      dist p (mkPt x 0) = t.sLG (e : ℝ) (f : ℝ) ∧
      dist p (mkPt (x + t.lenG (e : ℝ) (f : ℝ)) 0) = t.sRG (e : ℝ) (f : ℝ) ∧
      2 * t.lenG (e : ℝ) (f : ℝ) * (p 0 - x) =
        t.sLG (e : ℝ) (f : ℝ) ^ 2 - t.sRG (e : ℝ) (f : ℝ) ^ 2 + t.lenG (e : ℝ) (f : ℝ) ^ 2 ∧
      ∀ q ∈ Set.range (D.tile i).pts, q 1 ≠ 0 → q = p := by
  obtain ⟨k, m, j, hkm, hkj, hmj, hk, hm, hsL, hsR⟩ := h
  have hne : ((D.tile i).pts j) 1 ≠ 0 :=
    third_not_on_line (D.tile i) hkm hkj hmj (by rw [hk, mkPt_one]) (by rw [hm, mkPt_one])
  have hpos : 0 < ((D.tile i).pts j) 1 := lt_of_le_of_ne (S.pts_mem i j).1 (Ne.symm hne)
  rw [hk] at hsL
  rw [hm] at hsR
  have e1 := sq_of_dist hsL
  have e2 := sq_of_dist hsR
  refine ⟨(D.tile i).pts j, ⟨j, rfl⟩, hpos, hsL, hsR, by linear_combination e1 - e2, ?_⟩
  rintro q ⟨j', rfl⟩ hq
  rcases fin3_cover k m j hkm hkj hmj j' with h | h | h
  · rw [h, hk, mkPt_one] at hq; exact absurd rfl hq
  · rw [h, hm, mkPt_one] at hq; exact absurd rfl hq
  · rw [h]

/-- **A `C2` tile in coordinates**: `β` at `(x, 0)`, `α` at `(x + c, 0)`, apex `(x + u, h)`. -/
theorem c2_data (S : SetupG D e f α β γ L ax ay) {i : Fin N} {x : ℝ}
    (h : BaseTileG D (e : ℝ) (f : ℝ) i Ty.C2 x) :
    HasV D i (mkPt (x + (f : ℝ) ^ 2) 0) (mkPt x 0) (mkPt (x + uuG (e : ℝ) (f : ℝ)) (hhG (e : ℝ) (f : ℝ))) := by
  obtain ⟨k, m, j, hkm, hkj, hmj, hk, hm, hsL, hsR⟩ := h
  have hsL' : dist ((D.tile i).pts j) ((D.tile i).pts k) = (e : ℝ) * f := hsL
  have hm' : (D.tile i).pts m = mkPt (x + (f : ℝ) ^ 2) 0 := hm
  have hsR' : dist ((D.tile i).pts j) ((D.tile i).pts m) = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := hsR
  have hne : ((D.tile i).pts j) 1 ≠ 0 :=
    third_not_on_line (D.tile i) hkm hkj hmj (by rw [hk, mkPt_one]) (by rw [hm', mkPt_one])
  have hpos : 0 < ((D.tile i).pts j) 1 := lt_of_le_of_ne (S.pts_mem i j).1 (Ne.symm hne)
  rw [hk] at hsL'
  rw [hm'] at hsR'
  have e1 := sq_of_dist hsL'
  have e2 := sq_of_dist hsR'
  have hu := uuG_spec S.e0 S.hef'
  have hX : ((D.tile i).pts j) 0 - x = uuG (e : ℝ) (f : ℝ) := by
    have h1 : 2 * (f : ℝ) ^ 2 * (((D.tile i).pts j) 0 - x) = (e : ℝ) ^ 2 * (3 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) := by
      linear_combination e1 - e2
    have h2 : 2 * (f : ℝ) ^ 2 * (((D.tile i).pts j) 0 - x - uuG (e : ℝ) (f : ℝ)) = 0 := by
      linear_combination h1 - hu
    have := cancel2 S.f1 h2
    linarith
  have hY : ((D.tile i).pts j) 1 = hhG (e : ℝ) (f : ℝ) := by
    have h3 : ((D.tile i).pts j) 1 ^ 2 = hhG (e : ℝ) (f : ℝ) ^ 2 := by
      rw [hhG_sq S.e0 S.hef', ← hX]; linear_combination e1
    exact (sq_eq_sq₀ hpos.le (hhG_pos S.e0 S.hef').le).mp h3
  have hGeq : (D.tile i).pts j = mkPt (x + uuG (e : ℝ) (f : ℝ)) (hhG (e : ℝ) (f : ℝ)) :=
    plane_ext (by rw [mkPt_zero]; linarith) (by rw [mkPt_one]; exact hY)
  exact ⟨m, k, j, Ne.symm hkm, hmj, hkj, hm', hk, hGeq⟩

/-- **A `C1` tile in coordinates**: `α` at `(x, 0)`, `β` at `(x + c, 0)`, apex `(x + c − u, h)`. -/
theorem c1_data (S : SetupG D e f α β γ L ax ay) {i : Fin N} {x : ℝ}
    (h : BaseTileG D (e : ℝ) (f : ℝ) i Ty.C1 x) :
    HasV D i (mkPt x 0) (mkPt (x + (f : ℝ) ^ 2) 0)
      (mkPt (x + (f : ℝ) ^ 2 - uuG (e : ℝ) (f : ℝ)) (hhG (e : ℝ) (f : ℝ))) := by
  obtain ⟨k, m, j, hkm, hkj, hmj, hk, hm, hsL, hsR⟩ := h
  have hsL' : dist ((D.tile i).pts j) ((D.tile i).pts k) = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := hsL
  have hm' : (D.tile i).pts m = mkPt (x + (f : ℝ) ^ 2) 0 := hm
  have hsR' : dist ((D.tile i).pts j) ((D.tile i).pts m) = (e : ℝ) * f := hsR
  have hne : ((D.tile i).pts j) 1 ≠ 0 :=
    third_not_on_line (D.tile i) hkm hkj hmj (by rw [hk, mkPt_one]) (by rw [hm', mkPt_one])
  have hpos : 0 < ((D.tile i).pts j) 1 := lt_of_le_of_ne (S.pts_mem i j).1 (Ne.symm hne)
  rw [hk] at hsL'
  rw [hm'] at hsR'
  have e1 := sq_of_dist hsL'
  have e2 := sq_of_dist hsR'
  have hu := uuG_spec S.e0 S.hef'
  have hX : ((D.tile i).pts j) 0 - x = (f : ℝ) ^ 2 - uuG (e : ℝ) (f : ℝ) := by
    have h1 : 2 * (f : ℝ) ^ 2 * (((D.tile i).pts j) 0 - x) =
        2 * (f : ℝ) ^ 4 - 3 * (e : ℝ) ^ 2 * (f : ℝ) ^ 2 + (e : ℝ) ^ 4 := by
      linear_combination e1 - e2
    have h2 : 2 * (f : ℝ) ^ 2 * (((D.tile i).pts j) 0 - x - ((f : ℝ) ^ 2 - uuG (e : ℝ) (f : ℝ))) = 0 := by
      linear_combination h1 + hu
    have := cancel2 S.f1 h2
    linarith
  have hY : ((D.tile i).pts j) 1 = hhG (e : ℝ) (f : ℝ) := by
    have h3 : ((D.tile i).pts j) 1 ^ 2 = hhG (e : ℝ) (f : ℝ) ^ 2 := by
      rw [hhG_sq' S.e0 S.hef', ← hX]; linear_combination e1
    exact (sq_eq_sq₀ hpos.le (hhG_pos S.e0 S.hef').le).mp h3
  have hGeq : (D.tile i).pts j = mkPt (x + (f : ℝ) ^ 2 - uuG (e : ℝ) (f : ℝ)) (hhG (e : ℝ) (f : ℝ)) :=
    plane_ext (by rw [mkPt_zero]; linarith) (by rw [mkPt_one]; exact hY)
  exact ⟨k, m, j, hkm, hkj, hmj, hk, hm', hGeq⟩

/-- two base tiles at different places are different tiles -/
theorem baseTile_ne (S : SetupG D e f α β γ L ax ay) {i j : Fin N} {t t' : Ty} {x x' : ℝ}
    (h : BaseTileG D (e : ℝ) (f : ℝ) i t x) (h' : BaseTileG D (e : ℝ) (f : ℝ) j t' x')
    (hx : x ≠ x') : i ≠ j := by
  rintro rfl
  obtain ⟨k, m, j₁, hkm, hkj, hmj, hk, hm, -, -⟩ := h
  obtain ⟨k', m', j₁', hkm', -, -, hk', hm', -, -⟩ := h'
  have hl := Ty.lenG_pos S.e0 S.hef' t
  have hl' := Ty.lenG_pos S.e0 S.hef' t'
  have hne : ((D.tile i).pts j₁) 1 ≠ 0 :=
    third_not_on_line (D.tile i) hkm hkj hmj (by rw [hk, mkPt_one]) (by rw [hm, mkPt_one])
  have hk'j : k' ≠ j₁ := by
    intro h0
    rw [← h0, hk', mkPt_one] at hne
    exact hne rfl
  have hm'j : m' ≠ j₁ := by
    intro h0
    rw [← h0, hm', mkPt_one] at hne
    exact hne rfl
  rcases fin3_cover k m j₁ hkm hkj hmj k' with h1 | h1 | h1
  · rw [h1, hk] at hk'
    exact hx (mkPt_inj hk').1
  · rcases fin3_cover k m j₁ hkm hkj hmj m' with h2 | h2 | h2
    · rw [h1, hm] at hk'
      rw [h2, hk] at hm'
      have e1 := (mkPt_inj hk').1
      have e2 := (mkPt_inj hm').1
      linarith
    · exact absurd (h1.trans h2.symm) hkm'
    · exact absurd h2 hm'j
  · exact absurd h1 hk'j

/-- a base tile lies over the side `QB` -/
theorem baseTile_range (S : SetupG D e f α β γ L ax ay) {i : Fin N} {t : Ty} {x : ℝ}
    (h : BaseTileG D (e : ℝ) (f : ℝ) i t x) : 0 ≤ x ∧ x + t.lenG (e : ℝ) (f : ℝ) ≤ L := by
  obtain ⟨k, m, j, -, -, -, hk, hm, -, -⟩ := h
  have h1 : mkPt x 0 ∈ D.target.carrier := by rw [← hk]; exact pts_mem_target D.toDissection i k
  have h2 : mkPt (x + t.lenG (e : ℝ) (f : ℝ)) 0 ∈ D.target.carrier := by
    rw [← hm]; exact pts_mem_target D.toDissection i m
  exact ⟨(S.base_range h1).1, (S.base_range h2).2⟩

/-! ## 8. The typed chain -/

/-- **THE TYPED CHAIN ON `QB`.**  The side `QB` of the target is cut into `m ≥ 1` consecutive edges
`[X k, X (k+1)]`, `X 0 = 0`, `X m = L`, each the letter of a base tile `tile k` of type `τ k`; the edges have the
lengths `(τ k).lenG e f ∈ {e f, f² − e², f²}`. -/
theorem typed_chain (S : SetupG D e f α β γ L ax ay) :
    ∃ (m : ℕ) (X : ℕ → ℝ) (tile : ℕ → Fin N) (τ : ℕ → Ty), 0 < m ∧ X 0 = 0 ∧ X m = L ∧
      (∀ k, k < m → X (k + 1) = X k + (τ k).lenG (e : ℝ) (f : ℝ)) ∧
      (∀ k, k < m → BaseTileG D (e : ℝ) (f : ℝ) (tile k) (τ k) (X k)) := by
  have hpa := S.a_pos
  have hpb := S.b_pos
  have hpc := S.c_pos
  have hbase : segment ℝ (mkPt 0 0) (mkPt L 0) ⊆ frontier D.target.carrier := by
    intro y hy
    obtain ⟨h1, h0, hL'⟩ := (mem_base_segment_iff S.hL y).mp hy
    rw [S.tgt, eq_mkPt_of_y_zero h1]
    exact base_mem_frontier_Tg S.hL S.hay h0 hL'
  have hface : ∀ y ∈ D.target.carrier, y 1 = 0 → 0 ≤ y 0 ∧ y 0 ≤ L := by
    intro y hy h1
    rw [eq_mkPt_of_y_zero h1] at hy
    exact S.base_range hy
  obtain ⟨m, X, hm0, hX0, hXm, hℓ, htile⟩ :=
    base_chain_genG D S.hM S.hL (fun y hy => (S.mem hy).1) hbase hface
  have hN : 0 < N := D.toDissection.pos
  have key : ∀ k, ∃ (i : Fin N) (t : Ty), k < m →
      (X (k + 1) = X k + t.lenG (e : ℝ) (f : ℝ) ∧ BaseTileG D (e : ℝ) (f : ℝ) i t (X k)) := by
    intro k
    by_cases hk : k < m
    · obtain ⟨i, k₁, k₂, hne, h1, h2⟩ := htile k hk
      obtain ⟨j, hj1, hj2⟩ := fin3_third k₁ k₂ hne
      have hpos : 0 ≤ X (k + 1) - X k := by
        rcases hℓ k hk with h | h | h <;> rw [h] <;>
          first | exact hpa.le | exact hpb.le | exact hpc.le
      have hd : dist ((D.tile i).pts k₁) ((D.tile i).pts k₂) = X (k + 1) - X k := by
        have h3 := dist_mkPt_base (X k) (X (k + 1) - X k) hpos
        have e : X k + (X (k + 1) - X k) = X (k + 1) := by ring
        rw [e] at h3
        rw [h1, h2]; exact h3
      rcases hℓ k hk with ha | hb' | hc
      · have hX : X (k + 1) = X k + Ty.lenG (e : ℝ) (f : ℝ) Ty.A1 := by
          show X (k + 1) = X k + (e : ℝ) * f; linarith
        rcases sides_of_a_edgeG D S.tile S.hM i hne (Ne.symm hj1) (Ne.symm hj2) (hd.trans ha) with
          ⟨s1, s2⟩ | ⟨s1, s2⟩
        · exact ⟨i, Ty.A1, fun _ => ⟨hX, k₁, k₂, j, hne, Ne.symm hj1, Ne.symm hj2, h1,
            by rw [h2, hX], s1, s2⟩⟩
        · exact ⟨i, Ty.A2, fun _ => ⟨hX, k₁, k₂, j, hne, Ne.symm hj1, Ne.symm hj2, h1,
            by rw [h2, hX]; rfl, s1, s2⟩⟩
      · have hX : X (k + 1) = X k + Ty.lenG (e : ℝ) (f : ℝ) Ty.B1 := by
          show X (k + 1) = X k + ((f : ℝ) ^ 2 - (e : ℝ) ^ 2); linarith
        rcases sides_of_b_edgeG D S.tile S.hM i hne (Ne.symm hj1) (Ne.symm hj2) (hd.trans hb') with
          ⟨s1, s2⟩ | ⟨s1, s2⟩
        · exact ⟨i, Ty.B2, fun _ => ⟨hX, k₁, k₂, j, hne, Ne.symm hj1, Ne.symm hj2, h1,
            by rw [h2, hX]; rfl, s1, s2⟩⟩
        · exact ⟨i, Ty.B1, fun _ => ⟨hX, k₁, k₂, j, hne, Ne.symm hj1, Ne.symm hj2, h1,
            by rw [h2, hX], s1, s2⟩⟩
      · have hX : X (k + 1) = X k + Ty.lenG (e : ℝ) (f : ℝ) Ty.C1 := by
          show X (k + 1) = X k + (f : ℝ) ^ 2; linarith
        rcases sides_of_c_edgeG D S.tile S.hM i hne (Ne.symm hj1) (Ne.symm hj2) (hd.trans hc) with
          ⟨s1, s2⟩ | ⟨s1, s2⟩
        · exact ⟨i, Ty.C2, fun _ => ⟨hX, k₁, k₂, j, hne, Ne.symm hj1, Ne.symm hj2, h1,
            by rw [h2, hX]; rfl, s1, s2⟩⟩
        · exact ⟨i, Ty.C1, fun _ => ⟨hX, k₁, k₂, j, hne, Ne.symm hj1, Ne.symm hj2, h1,
            by rw [h2, hX], s1, s2⟩⟩
    · exact ⟨⟨0, hN⟩, Ty.A1, fun h => absurd h hk⟩
  choose tile τ hkey using key
  exact ⟨m, X, tile, τ, hm0, hX0, hXm, fun k hk => (hkey k hk).1, fun k hk => (hkey k hk).2⟩

/-! ## 9. The corners -/

/-- the neighbouring side at `B` runs along the `a`-edge of a `C1` tile: the angle of the target at `B` is `β` -/
theorem corner_right_beta (S : SetupG D e f α β γ L ax ay) {t : ℝ} (ht : 0 < t)
    (hax : ax = L - t * uuG (e : ℝ) (f : ℝ)) (hay' : ay = t * hhG (e : ℝ) (f : ℝ)) :
    cornerAngle (D.target.pts (1 + 1)) (D.target.pts 1) (D.target.pts (1 + 2)) = β := by
  have he := S.e0
  have hef := S.hef'
  have hf0 := S.f0
  have hL := S.hL
  have hπ := Real.pi_pos
  have hsq := hhG_sq he hef
  have hu := uuG_spec he hef
  have ha := S.a_pos
  rw [S.tgt, show ((1 : Fin 3) + 1) = 2 by decide, show ((1 : Fin 3) + 2) = 0 by decide, Tg_pts0,
    Tg_pts1, Tg_pts2]
  have h1 : dist (mkPt ax ay) (mkPt L 0) = t * ((e : ℝ) * f) := by
    refine dist_eq_of_sq_eq ?_ dist_nonneg (by positivity)
    rw [dist_sq_mkPt, hax, hay']
    linear_combination t ^ 2 * hsq
  have h2 : dist (mkPt 0 0) (mkPt L 0) = L := by
    have := dist_mkPt_base 0 L hL.le
    rwa [zero_add] at this
  have hcos := Erdos634.AngleThreshold.cos_of_sides (mkPt ax ay) (mkPt L 0) (mkPt 0 0)
    (by rw [h1]; positivity) (by rw [h2]; exact hL.ne')
  rw [h1, h2, dist_sq_mkPt] at hcos
  rw [S.beta_eq]
  have hmem := modelBeta_mem he hef
  refine cornerAngle_eq_of_cos hmem.1.le (by linarith [hmem.2]) ?_
  rw [hcos, cos_modelBeta he hef]
  unfold baseLen Nq
  have hB : 2 * (t * ((e : ℝ) * f)) * L ≠ 0 := by positivity
  have hD : 2 * (f : ℝ) ^ 3 ≠ 0 := by positivity
  rw [div_eq_div_iff hB hD, hax, hay']
  linear_combination (2 * t * (f : ℝ) * L) * hu - (2 * (f : ℝ) ^ 3 * t ^ 2) * hsq

/-- the neighbouring side at `Q` runs along the `a`-edge of a `C2` tile: the angle of the target at `Q` is `β` -/
theorem corner_left_beta (S : SetupG D e f α β γ L ax ay) {t : ℝ} (ht : 0 < t)
    (hax : ax = t * uuG (e : ℝ) (f : ℝ)) (hay' : ay = t * hhG (e : ℝ) (f : ℝ)) :
    cornerAngle (D.target.pts (0 + 1)) (D.target.pts 0) (D.target.pts (0 + 2)) = β := by
  have he := S.e0
  have hef := S.hef'
  have hf0 := S.f0
  have hL := S.hL
  have hπ := Real.pi_pos
  have hsq := hhG_sq he hef
  have hu := uuG_spec he hef
  have ha := S.a_pos
  rw [S.tgt, show ((0 : Fin 3) + 1) = 1 by decide, show ((0 : Fin 3) + 2) = 2 by decide, Tg_pts0,
    Tg_pts1, Tg_pts2]
  have h1 : dist (mkPt ax ay) (mkPt 0 0) = t * ((e : ℝ) * f) := by
    refine dist_eq_of_sq_eq ?_ dist_nonneg (by positivity)
    rw [dist_sq_mkPt, hax, hay']
    linear_combination t ^ 2 * hsq
  have h2 : dist (mkPt L 0) (mkPt 0 0) = L := by
    have := dist_mkPt_base 0 L hL.le
    rw [zero_add] at this
    rw [dist_comm]; exact this
  have hcos := Erdos634.AngleThreshold.cos_of_sides (mkPt L 0) (mkPt 0 0) (mkPt ax ay)
    (by rw [h2]; exact hL.ne') (by rw [h1]; positivity)
  rw [h1, h2, dist_sq_mkPt] at hcos
  rw [S.beta_eq]
  have hmem := modelBeta_mem he hef
  refine cornerAngle_eq_of_cos hmem.1.le (by linarith [hmem.2]) ?_
  rw [hcos, cos_modelBeta he hef]
  unfold baseLen Nq
  have hB : 2 * L * (t * ((e : ℝ) * f)) ≠ 0 := by positivity
  have hD : 2 * (f : ℝ) ^ 3 ≠ 0 := by positivity
  rw [div_eq_div_iff hB hD, hax, hay']
  linear_combination (2 * t * (f : ℝ) * L) * hu - (2 * (f : ℝ) ^ 3 * t ^ 2) * hsq

/-- the neighbouring side at `Q` has the direction `(e, √(4f² − e²))`: the angle of the target at `Q` is `α + β` -/
theorem corner_left_ab (S : SetupG D e f α β γ L ax ay) {t : ℝ} (ht : 0 < t)
    (hax : ax = t * (e : ℝ)) (hay' : ay = t * rtG (e : ℝ) (f : ℝ)) :
    D.target.localAngle (mkPt 0 0) = α + β := by
  have he := S.e0
  have hef := S.hef'
  have hf0 := S.f0
  have hL := S.hL
  have hπ := Real.pi_pos
  have hr := rtG_sq he hef
  obtain ⟨hα, hβ, hγ2, hsum, hγπ⟩ := angle_facts S.hA
  have hαβ : α + β = Real.pi - γ := by linarith
  have h0 : D.target.localAngle (mkPt 0 0)
      = cornerAngle (mkPt L 0) (mkPt 0 0) (mkPt ax ay) := by
    rw [S.tgt]
    have h := (Tg L ax ay S.hL S.hay).localAngle_vertex 0
    rw [show ((0 : Fin 3) + 1) = 1 by decide, show ((0 : Fin 3) + 2) = 2 by decide] at h
    exact h
  rw [h0]
  have h1 : dist (mkPt ax ay) (mkPt 0 0) = t * (2 * (f : ℝ)) := by
    refine dist_eq_of_sq_eq ?_ dist_nonneg (by positivity)
    rw [dist_sq_mkPt, hax, hay']
    linear_combination t ^ 2 * hr
  have h2 : dist (mkPt L 0) (mkPt 0 0) = L := by
    have := dist_mkPt_base 0 L hL.le
    rw [zero_add] at this
    rw [dist_comm]; exact this
  have hcos := Erdos634.AngleThreshold.cos_of_sides (mkPt L 0) (mkPt 0 0) (mkPt ax ay)
    (by rw [h2]; exact hL.ne') (by rw [h1]; positivity)
  rw [h1, h2, dist_sq_mkPt] at hcos
  refine cornerAngle_eq_of_cos (by linarith) (by linarith) ?_
  rw [hcos, hαβ, Real.cos_pi_sub, S.cos_gamma]
  have hB : 2 * L * (t * (2 * (f : ℝ))) ≠ 0 := by positivity
  have hD : 2 * (f : ℝ) ≠ 0 := by positivity
  have e' : -(-(e : ℝ) / (2 * (f : ℝ))) = (e : ℝ) / (2 * (f : ℝ)) := by ring
  rw [e', div_eq_div_iff hB hD, hax, hay']
  linear_combination (-(2 * (f : ℝ) * t ^ 2)) * hr

/-- **At a corner of angle `β` of the target every tile that contains the corner shows `β` there.** -/
theorem corner_tile_beta (S : SetupG D e f α β γ L ax ay) (k : Fin 3)
    (hcorner : cornerAngle (D.target.pts (k + 1)) (D.target.pts k) (D.target.pts (k + 2)) = β)
    {i : Fin N} (hi : D.target.pts k ∈ (D.tile i).carrier) :
    (D.tile i).localAngle (D.target.pts k) = β := by
  obtain ⟨hαβ, hαγ, hαπ, hα0, hβγ, hβπ, hβ0, hβ2π, hγπ, hγ0, hπ0⟩ := distinct_of_angleData S.hA
  obtain ⟨i₀, j₀, hij, hang, huniq⟩ := congruentDissection_base_corner_tile_vertex D α β γ hαβ hαγ
    hαπ hα0 hβγ hβπ hβ0 hβ2π hγπ hγ0 hπ0 S.hA.hγdef S.hA.hrel S.hA.hirr S.hM.hα' S.hM.hβ' S.hM.hγ'
    k hcorner
  rw [huniq i hi]; exact hang

theorem Q_eq (S : SetupG D e f α β γ L ax ay) : D.target.pts 0 = mkPt 0 0 := by rw [S.tgt]; rfl
theorem B_eq (S : SetupG D e f α β γ L ax ay) : D.target.pts 1 = mkPt L 0 := by rw [S.tgt]; rfl

end SetupG


/-! ## 10. Specialisation to `e = 1`: the general statements give the e = 1 statements of `SideRunFrame`

The checks below are the point of the section: each general lemma, taken at `e = 1`, is the e = 1 lemma of
`SideRunFrame` / `W2E1Frame` with the same statement (`cos_gamma`, `beta_eq`, `corner_left_ab`, `typed_chain`), and the
structures agree (`modelDataG_one_iff`, `setupG_one_iff`). -/

section e_one

theorem modelDataG_one_iff {N : ℕ} {D : CongruentDissection N} {f α β γ : ℝ} :
    ModelDataG D 1 f α β γ ↔ ModelData D f α β γ := by
  constructor
  · rintro ⟨h0, h1, h2, h3, h4, h5⟩
    exact ⟨by simpa using h0, by simpa using h1, h2, h3, h4, h5⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5⟩
    exact ⟨by simpa using h0, by simpa using h1, h2, h3, h4, h5⟩

theorem uuG_one (f : ℝ) : uuG 1 f = uu f := by unfold uuG uu; ring

theorem rtG_one (f : ℝ) : rtG 1 f = rt f := by unfold rtG rt; congr 1; ring

theorem hhG_one (f : ℝ) : hhG 1 f = hh f := by unfold hhG hh; rw [rtG_one]; ring

/-- the constants: `hhG_sq'` at `e = 1` is `W2E1.hh_sq'` -/
theorem hh_sq'_of_G {f : ℝ} (hf : 1 < f) : hh f ^ 2 = (f ^ 2 - 1) ^ 2 - (f ^ 2 - uu f) ^ 2 := by
  have h := hhG_sq' (e := 1) (f := f) one_pos hf
  rw [hhG_one, uuG_one] at h
  simpa using h

/-- the angle bundle: `angleData_model` at `e = 1` -/
theorem angleData_model_e1 (n : ℕ) (hn2 : 2 ≤ n) :
    AngleData (modelAlpha 1 (n : ℝ)) (modelBeta 1 (n : ℝ))
      (2 * modelAlpha 1 (n : ℝ) + modelBeta 1 (n : ℝ)) := by
  have h := angleData_model 1 n le_rfl (by omega)
  simpa only [Nat.cast_one] using h

/-- **`SetupG` at `e = 1` is `Setup`** -/
theorem setupG_one_iff {N : ℕ} {D : CongruentDissection N} {n : ℕ} {α β γ L ax ay : ℝ} :
    SetupG D 1 n α β γ L ax ay ↔ Setup D n α β γ L ax ay := by
  constructor
  · intro S
    refine ⟨S.hf2, ?_, S.hA, S.hL, S.hay, S.htgt⟩
    have h := S.hM
    rw [Nat.cast_one, modelDataG_one_iff] at h
    exact h
  · intro S
    refine ⟨le_refl 1, by have := S.hn2; omega, Nat.coprime_one_left n, ?_, S.hA, S.hL, S.hay, S.htgt⟩
    rw [Nat.cast_one, modelDataG_one_iff]
    exact S.hM

variable {N : ℕ} {D : CongruentDissection N} {n : ℕ} {α β γ L ax ay : ℝ}

/-- `SetupG.cos_gamma` at `e = 1` is `Setup.cos_gamma` -/
theorem cos_gamma_e1 (S : Setup D n α β γ L ax ay) : Real.cos γ = -1 / (2 * (n : ℝ)) := by
  have h := (setupG_one_iff.mpr S).cos_gamma
  simpa using h

/-- `SetupG.beta_eq` at `e = 1` is `Setup.beta_eq` -/
theorem beta_eq_e1 (S : Setup D n α β γ L ax ay) : β = modelBeta 1 (n : ℝ) := by
  have h := (setupG_one_iff.mpr S).beta_eq
  rwa [Nat.cast_one] at h

/-- `SetupG.corner_left_ab` at `e = 1` is `Setup.corner_left_ab` -/
theorem corner_left_ab_e1 (S : Setup D n α β γ L ax ay) {t : ℝ} (ht : 0 < t) (hax : ax = t)
    (hay' : ay = t * rt n) : D.target.localAngle (mkPt 0 0) = α + β :=
  (setupG_one_iff.mpr S).corner_left_ab ht (by rw [Nat.cast_one, mul_one]; exact hax)
    (by rw [Nat.cast_one, rtG_one]; exact hay')

/-- `SetupG.corner_right_beta` at `e = 1` is `Setup.corner_right_beta` -/
theorem corner_right_beta_e1 (S : Setup D n α β γ L ax ay) {t : ℝ} (ht : 0 < t)
    (hax : ax = L - t * uu n) (hay' : ay = t * hh n) :
    cornerAngle (D.target.pts (1 + 1)) (D.target.pts 1) (D.target.pts (1 + 2)) = β :=
  (setupG_one_iff.mpr S).corner_right_beta ht (by rw [Nat.cast_one, uuG_one]; exact hax)
    (by rw [Nat.cast_one, hhG_one]; exact hay')

/-- `SetupG.typed_chain` at `e = 1` is `Setup.typed_chain` -/
theorem typed_chain_e1 (S : Setup D n α β γ L ax ay) :
    ∃ (m : ℕ) (X : ℕ → ℝ) (tile : ℕ → Fin N) (τ : ℕ → Ty), 0 < m ∧ X 0 = 0 ∧ X m = L ∧
      (∀ k, k < m → X (k + 1) = X k + (τ k).lenR (n : ℝ)) ∧
      (∀ k, k < m → BaseTile D (n : ℝ) (tile k) (τ k) (X k)) := by
  obtain ⟨m, X, tile, τ, hm, h0, hmL, hstep, hbt⟩ := (setupG_one_iff.mpr S).typed_chain
  refine ⟨m, X, tile, τ, hm, h0, hmL, fun k hk => ?_, fun k hk => ?_⟩
  · have h := hstep k hk
    rwa [Nat.cast_one, Ty.lenG_one] at h
  · obtain ⟨k₁, m₁, j₁, h1, h2, h3, h4, h5, h6, h7⟩ := hbt k hk
    refine ⟨k₁, m₁, j₁, h1, h2, h3, h4, ?_, ?_, ?_⟩
    · rw [Nat.cast_one, Ty.lenG_one] at h5; exact h5
    · rw [Nat.cast_one, Ty.sLG_one] at h6; exact h6
    · rw [Nat.cast_one, Ty.sRG_one] at h7; exact h7

end e_one

end Erdos634.Draft.SideRunG

#print axioms Erdos634.Draft.SideRunG.figF
#print axioms Erdos634.Draft.SideRunG.angleData_model
#print axioms Erdos634.Draft.SideRunG.SetupG.cos_gamma
#print axioms Erdos634.Draft.SideRunG.SetupG.typed_chain
#print axioms Erdos634.Draft.SideRunG.SetupG.corner_left_ab
#print axioms Erdos634.Draft.SideRunG.SetupG.corner_right_beta
#print axioms Erdos634.Draft.SideRunG.SetupG.corner_left_beta
#print axioms Erdos634.Draft.SideRunG.SetupG.corner_tile_beta
#print axioms Erdos634.Draft.SideRunG.setupG_one_iff
#print axioms Erdos634.Draft.SideRunG.typed_chain_e1
