import Erdos634.Draft.LaczFormalMJStage2

/-!
# A bare lattice and the cell predicates without `BandSetup` (rule `M(j)`; control layer)

Erdős #634, base-`β` band.  Credit: AI assistant (item 3, band program, rule `M(j)`), Beeson–Roșu, Beeson,
Laczkovich, Paliy.  UNAUDITED.  Axiom-clean; no `sorry`.

PURPOSE.  The cell predicates `LFrame.UpCell`, `DownCell`, `Ground`, `TRule` are premises of a proof by
contradiction: a band target has no dissection, and the seed tilings (outside the band) have no standard cell at
an integer lattice point of the corner frame.  So the predicates cannot be exercised on an `LFrame` of a band
dissection.  But they only use `D.tile` and `F.pt`, and the lemmas `up_angles`, `down_angles`, `third_up`,
`third_down` use `BandSetup` only through the facts about the MODEL tile.  This file separates exactly those:

* `BLat e f`: the lattice vectors (the data of `LFrame` that is not about the target).  `LFrame.toBLat`.
* `ModelData D e f α β γ`: the facts about the model used by the lattice lemmas.  `BandSetup.toModelData`.
* `UpCellB`, `DownCellB`, `GroundB`, `TRuleB`: the predicates for a bare family of tiles; each is `Iff.rfl`
  to the corresponding `LFrame` predicate (`upCell_iff`, ... , `TRule_iff`).
* `tileVerts_angleB`, `tv_labB`, `third_upB`, `third_downB`: the proofs of `LaczFormalMJTile`/`Cell` with
  `ModelData` in place of `BandSetup`; `third_up_via_bare`, `third_down_via_bare` recover the `LFrame` statements.
-/

namespace Erdos634.LaczMJ

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.LaczJunction Erdos634.LaczJunction.Walk
  Erdos634.LaczJunction.Grammar

variable {N : ℕ}

/-- The lattice vectors of a frame, without the target. -/
structure BLat (e f : ℕ) where
  O : Plane
  e0 : Plane
  v : Plane
  he0 : ‖e0‖ = (tc e f : ℝ)
  hv : ‖v‖ = (ta e f : ℝ)
  hu : ‖v - e0‖ = (tb e f : ℝ)
  hcr : 0 < cross e0 v

namespace BLat

variable {e f : ℕ} (L : BLat e f)

/-- The lattice point `O + x e0 + y v`. -/
def pt (x y : ℝ) : Plane := L.O + x • L.e0 + y • L.v

theorem dist_pt (x y x' y' : ℝ) :
    dist (L.pt x y) (L.pt x' y') = ‖(x - x') • L.e0 + (y - y') • L.v‖ := by
  rw [dist_eq_norm]; congr 1; simp only [pt]; module

theorem dist_pt_c (x y : ℝ) : dist (L.pt x y) (L.pt (x + 1) y) = (tc e f : ℝ) := by
  rw [L.dist_pt]
  have : (x - (x + 1)) • L.e0 + (y - y) • L.v = (-1 : ℝ) • L.e0 := by module
  rw [this, norm_smul, L.he0]; simp

theorem dist_pt_a (x y : ℝ) : dist (L.pt x y) (L.pt x (y + 1)) = (ta e f : ℝ) := by
  rw [L.dist_pt]
  have : (x - x) • L.e0 + (y - (y + 1)) • L.v = (-1 : ℝ) • L.v := by module
  rw [this, norm_smul, L.hv]; simp

theorem dist_pt_b (x y : ℝ) : dist (L.pt (x + 1) y) (L.pt x (y + 1)) = (tb e f : ℝ) := by
  rw [L.dist_pt]
  have : (x + 1 - x) • L.e0 + (y - (y + 1)) • L.v = -(L.v - L.e0) := by module
  rw [this, norm_neg, L.hu]

theorem pt_sub (x1 y1 x2 y2 : ℝ) :
    L.pt x1 y1 - L.pt x2 y2 = (x1 - x2) • L.e0 + (y1 - y2) • L.v := by
  simp only [pt]; module

end BLat

/-- The lattice of a frame. -/
def LFrame.toBLat {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ} {p q r : Fin 3}
    (F : LFrame D e f α β γ p q r) : BLat e f :=
  ⟨D.target.pts p, F.e0, F.v, F.he0, F.hv, F.hu, F.hcr⟩

theorem LFrame.toBLat_pt {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ} {p q r : Fin 3}
    (F : LFrame D e f α β γ p q r) (x y : ℝ) : F.toBLat.pt x y = F.pt x y := rfl

/-- The facts about the MODEL tile used by the lattice lemmas (`tileVerts_angle`, `tv_lab`, `third_up`,
`third_down`): the corner angles read off the opposite sides, the three side lengths, and their distinctness. -/
structure ModelData (D : CongruentDissection N) (e f : ℕ) (α β γ : ℝ) : Prop where
  he : 1 ≤ e
  hef : e < f
  hα' : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α
  hβ' : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β
  hγ' : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ
  hsa : sideOpp D.model 0 = (ta e f : ℝ)
  hsb : sideOpp D.model 1 = (tb e f : ℝ)
  hsc : sideOpp D.model 2 = (tc e f : ℝ)
  hαβ : α ≠ β
  hβγ : β ≠ γ
  hαγ : α ≠ γ
  hab : (ta e f : ℝ) ≠ tb e f
  hbc : (tb e f : ℝ) ≠ tc e f
  hac : (ta e f : ℝ) ≠ tc e f

/-- `BandSetup` gives the model data. -/
theorem bandSetup_toModelData {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ} {p q r : Fin 3}
    (S : BandSetup D e f α β γ p q r) : ModelData D e f α β γ := by
  obtain ⟨hαβ, hβγ, hαγ, -, -, -⟩ := BandSetup.distinct S
  obtain ⟨hab, hbc, hac⟩ := BandSetup.dist3 S
  exact ⟨S.he, S.hef, S.hα', S.hβ', S.hγ', S.hsa, S.hsb, S.hsc, hαβ, hβγ, hαγ, hab, hbc, hac⟩

/-! ## The predicates for a bare family of tiles -/

section Preds

variable {e f : ℕ}

def UpCellB (T : Fin N → Tri) (L : BLat e f) (x y : ℝ) : Prop :=
  ∃ i : Fin N, TileVerts (T i) (L.pt x y) (L.pt (x + 1) y) (L.pt x (y + 1))

def DownCellB (T : Fin N → Tri) (L : BLat e f) (x y : ℝ) : Prop :=
  ∃ i : Fin N, TileVerts (T i) (L.pt (x + 1) y) (L.pt x (y + 1)) (L.pt (x + 1) (y + 1))

def GroundB (T : Fin N → Tri) (L : BLat e f) (ρ k : ℕ) : Prop :=
  ρ = 0 ∨ ∃ ρ' : ℕ, ρ = ρ' + 1 ∧ ∀ x : ℕ, x ≤ k → UpCellB T L (x : ℝ) (ρ' : ℝ) ∧ DownCellB T L (x : ℝ) (ρ' : ℝ)

def TRuleB (T : Fin N → Tri) (L : BLat e f) (H m : ℕ) : Prop :=
  ∀ lv : ℕ, lv + m + 1 ≤ H → m + 1 ≤ e → GroundB T L lv (m + 1) →
    (∀ x : ℕ, x ≤ m → UpCellB T L (x : ℝ) (lv : ℝ)) → DownCellB T L (m : ℝ) (lv : ℝ)

/-- `StdB`: rows `r, …, r+s` of the triangle with `m+1` up tiles on level `r` are standard. -/
def StdB (T : Fin N → Tri) (L : BLat e f) (r m s : ℕ) : Prop :=
  ∀ t : ℕ, t ≤ s →
    (∀ x : ℕ, x + t ≤ m → UpCellB T L (x : ℝ) ((r : ℝ) + t)) ∧
    (∀ x : ℕ, x + t + 1 ≤ m → DownCellB T L (x : ℝ) ((r : ℝ) + t))

variable {D : CongruentDissection N} {α β γ : ℝ} {p q r : Fin 3} (F : LFrame D e f α β γ p q r)

theorem upCell_iff (x y : ℝ) : F.UpCell x y ↔ UpCellB D.tile F.toBLat x y := Iff.rfl
theorem downCell_iff (x y : ℝ) : F.DownCell x y ↔ DownCellB D.tile F.toBLat x y := Iff.rfl
theorem ground_iff (ρ k : ℕ) : F.Ground ρ k ↔ GroundB D.tile F.toBLat ρ k := Iff.rfl
theorem TRule_iff (H m : ℕ) : F.TRule H m ↔ TRuleB D.tile F.toBLat H m := Iff.rfl
theorem Std_iff (r m s : ℕ) : F.Std r m s ↔ StdB D.tile F.toBLat r m s := Iff.rfl

end Preds

/-! ## The angle and third-vertex lemmas with `ModelData` -/

variable {D : CongruentDissection N}

theorem tileVerts_angleB {e f : ℕ} {α β γ : ℝ} (M : ModelData D e f α β γ) {i : Fin N} {A B C : Plane}
    (hv : TileVerts (D.tile i) A B C) :
    ((dist B C = (ta e f : ℝ) → (D.tile i).localAngle A = α) ∧
      (dist B C = (tb e f : ℝ) → (D.tile i).localAngle A = β) ∧
      (dist B C = (tc e f : ℝ) → (D.tile i).localAngle A = γ)) := by
  have hab : sideOpp D.model 0 ≠ sideOpp D.model 1 := by rw [M.hsa, M.hsb]; exact M.hab
  have hbc : sideOpp D.model 1 ≠ sideOpp D.model 2 := by rw [M.hsb, M.hsc]; exact M.hbc
  have hac : sideOpp D.model 0 ≠ sideOpp D.model 2 := by rw [M.hsa, M.hsc]; exact M.hac
  have F3 : ∀ j : Fin 3, j ≠ j + 1 ∧ j ≠ j + 2 ∧ j + 1 ≠ j + 2 := by decide
  obtain ⟨j, ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩⟩ := hv
  · have := angle_of_opp D α β γ M.hα' M.hβ' M.hγ' hab hbc hac i j (j + 1) (j + 2)
      (F3 j).1 (F3 j).2.1 (F3 j).2.2
    rw [h1, h2, h3, M.hsa, M.hsb, M.hsc] at this
    exact this
  · have := angle_of_opp D α β γ M.hα' M.hβ' M.hγ' hab hbc hac i j (j + 2) (j + 1)
      (F3 j).2.1 (F3 j).1 (F3 j).2.2.symm
    rw [h1, h2, h3, M.hsa, M.hsb, M.hsc] at this
    exact this

variable {e f : ℕ} {α β γ : ℝ}

theorem up_anglesB (M : ModelData D e f α β γ) (L : BLat e f) {x y : ℝ} {i : Fin N}
    (hv : TileVerts (D.tile i) (L.pt x y) (L.pt (x + 1) y) (L.pt x (y + 1))) :
    (D.tile i).localAngle (L.pt x y) = β ∧ (D.tile i).localAngle (L.pt (x + 1) y) = α ∧
      (D.tile i).localAngle (L.pt x (y + 1)) = γ := by
  refine ⟨(tileVerts_angleB M hv).2.1 (L.dist_pt_b x y), ?_, ?_⟩
  · exact (tileVerts_angleB M hv.rot).1 (by rw [dist_comm]; exact L.dist_pt_a x y)
  · exact (tileVerts_angleB M hv.rot.rot).2.2 (L.dist_pt_c x y)

theorem down_anglesB (M : ModelData D e f α β γ) (L : BLat e f) {x y : ℝ} {i : Fin N}
    (hv : TileVerts (D.tile i) (L.pt (x + 1) y) (L.pt x (y + 1)) (L.pt (x + 1) (y + 1))) :
    (D.tile i).localAngle (L.pt (x + 1) y) = γ ∧ (D.tile i).localAngle (L.pt x (y + 1)) = α ∧
      (D.tile i).localAngle (L.pt (x + 1) (y + 1)) = β := by
  refine ⟨(tileVerts_angleB M hv).2.2 (L.dist_pt_c x (y + 1)), ?_, ?_⟩
  · exact (tileVerts_angleB M hv.rot).1 (by rw [dist_comm]; exact L.dist_pt_a (x + 1) y)
  · exact (tileVerts_angleB M hv.rot.rot).2.1 (L.dist_pt_b x y)

theorem tv_labB (M : ModelData D e f α β γ) {i : Fin N} {X Y Z : Plane}
    (hv : TileVerts (D.tile i) X Y Z) :
    let a := (ta e f : ℝ); let b := (tb e f : ℝ); let c := (tc e f : ℝ)
    ((D.tile i).localAngle X = α ∧ (D.tile i).localAngle Y = β ∧ (D.tile i).localAngle Z = γ ∧
        dist Y Z = a ∧ dist X Z = b ∧ dist X Y = c) ∨
    ((D.tile i).localAngle X = α ∧ (D.tile i).localAngle Y = γ ∧ (D.tile i).localAngle Z = β ∧
        dist Y Z = a ∧ dist X Z = c ∧ dist X Y = b) ∨
    ((D.tile i).localAngle X = β ∧ (D.tile i).localAngle Y = α ∧ (D.tile i).localAngle Z = γ ∧
        dist Y Z = b ∧ dist X Z = a ∧ dist X Y = c) ∨
    ((D.tile i).localAngle X = β ∧ (D.tile i).localAngle Y = γ ∧ (D.tile i).localAngle Z = α ∧
        dist Y Z = b ∧ dist X Z = c ∧ dist X Y = a) ∨
    ((D.tile i).localAngle X = γ ∧ (D.tile i).localAngle Y = α ∧ (D.tile i).localAngle Z = β ∧
        dist Y Z = c ∧ dist X Z = a ∧ dist X Y = b) ∨
    ((D.tile i).localAngle X = γ ∧ (D.tile i).localAngle Y = β ∧ (D.tile i).localAngle Z = α ∧
        dist Y Z = c ∧ dist X Z = b ∧ dist X Y = a) := by
  intro a b c
  have hm := tv_ms hv
  have hX := tileVerts_angleB M hv
  have hY := tileVerts_angleB M hv.rot
  have hZ := tileVerts_angleB M hv.rot.rot
  rw [M.hsa, M.hsb, M.hsc] at hm
  rcases perm3 hm M.hab M.hbc M.hac with
    ⟨x1, x2, x3⟩ | ⟨x1, x2, x3⟩ | ⟨x1, x2, x3⟩ | ⟨x1, x2, x3⟩ | ⟨x1, x2, x3⟩ | ⟨x1, x2, x3⟩
  · exact Or.inl ⟨hX.1 x3, hY.2.1 ((dist_comm Z X).trans x2), hZ.2.2 x1, x3, x2, x1⟩
  · exact Or.inr (Or.inr (Or.inl ⟨hX.2.1 x3, hY.1 ((dist_comm Z X).trans x2), hZ.2.2 x1, x3, x2, x1⟩))
  · exact Or.inr (Or.inl ⟨hX.1 x3, hY.2.2 ((dist_comm Z X).trans x2), hZ.2.1 x1, x3, x2, x1⟩)
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨hX.2.2 x3, hY.1 ((dist_comm Z X).trans x2), hZ.2.1 x1, x3, x2, x1⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hX.2.1 x3, hY.2.2 ((dist_comm Z X).trans x2), hZ.1 x1, x3, x2, x1⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨hX.2.2 x3, hY.2.1 ((dist_comm Z X).trans x2), hZ.1 x1, x3, x2, x1⟩))))

theorem tc_posB (M : ModelData D e f α β γ) : (0 : ℝ) < tc e f := by
  have := b_lt_c e f M.he M.hef
  have := b_pos e f M.he M.hef
  exact_mod_cast (by omega : 0 < tc e f)

theorem third_upB (M : ModelData D e f α β γ) (L : BLat e f) {i : Fin N} {x ρ : ℝ} {Z : Plane}
    (hv : TileVerts (D.tile i) (L.pt x ρ) (L.pt (x + 1) ρ) Z)
    (hβ : (D.tile i).localAngle (L.pt x ρ) = β)
    (hup : 0 < cross L.e0 (Z - L.pt x ρ)) : Z = L.pt x (ρ + 1) := by
  have hac := M.hac
  have hXY : dist (L.pt x ρ) (L.pt (x + 1) ρ) = (tc e f : ℝ) := L.dist_pt_c x ρ
  have key : dist (L.pt x ρ) Z = (ta e f : ℝ) ∧ dist (L.pt (x + 1) ρ) Z = (tb e f : ℝ) := by
    rcases tv_labB M hv with ⟨h1, h2, h3, h4, h5, h6⟩ | ⟨h1, h2, h3, h4, h5, h6⟩ |
        ⟨h1, h2, h3, h4, h5, h6⟩ | ⟨h1, h2, h3, h4, h5, h6⟩ | ⟨h1, h2, h3, h4, h5, h6⟩ |
        ⟨h1, h2, h3, h4, h5, h6⟩
    · exact absurd (h1.symm.trans hβ) M.hαβ
    · exact absurd (h1.symm.trans hβ) M.hαβ
    · exact ⟨h5, h4⟩
    · exact absurd (hXY.symm.trans h6) hac.symm
    · exact absurd (h1.symm.trans hβ) M.hβγ.symm
    · exact absurd (h1.symm.trans hβ) M.hβγ.symm
  have hAB : L.pt x ρ ≠ L.pt (x + 1) ρ := by
    intro h; rw [h, dist_self] at hXY
    have := tc_posB M
    linarith
  refine two_circles hAB ?_ ?_ ?_ |>.symm.symm
  · rw [key.1, L.dist_pt_a]
  · rw [key.2]; exact (L.dist_pt_b x ρ).symm
  · have e1 : L.pt (x + 1) ρ - L.pt x ρ = L.e0 := by rw [L.pt_sub]; module
    have e2 : L.pt x (ρ + 1) - L.pt x ρ = L.v := by rw [L.pt_sub]; module
    rw [e1, e2]
    exact mul_pos hup L.hcr

theorem third_downB (M : ModelData D e f α β γ) (L : BLat e f) {i : Fin N} {x y : ℝ} {Z : Plane}
    (hv : TileVerts (D.tile i) (L.pt (x + 1) y) (L.pt x (y + 1)) Z)
    (hγ : (D.tile i).localAngle (L.pt (x + 1) y) = γ)
    (hside : cross (L.pt x (y + 1) - L.pt (x + 1) y) (Z - L.pt (x + 1) y) < 0) :
    Z = L.pt (x + 1) (y + 1) := by
  have hXY : dist (L.pt (x + 1) y) (L.pt x (y + 1)) = (tb e f : ℝ) := L.dist_pt_b x y
  have key : dist (L.pt (x + 1) y) Z = (ta e f : ℝ) ∧ dist (L.pt x (y + 1)) Z = (tc e f : ℝ) := by
    rcases tv_labB M hv with ⟨h1, h2, h3, h4, h5, h6⟩ | ⟨h1, h2, h3, h4, h5, h6⟩ |
        ⟨h1, h2, h3, h4, h5, h6⟩ | ⟨h1, h2, h3, h4, h5, h6⟩ | ⟨h1, h2, h3, h4, h5, h6⟩ |
        ⟨h1, h2, h3, h4, h5, h6⟩
    · exact absurd (h1.symm.trans hγ) M.hαγ
    · exact absurd (h1.symm.trans hγ) M.hαγ
    · exact absurd (h1.symm.trans hγ) M.hβγ
    · exact absurd (h1.symm.trans hγ) M.hβγ
    · exact ⟨h5, h4⟩
    · exact absurd (hXY.symm.trans h6) M.hab.symm
  have hAB : L.pt (x + 1) y ≠ L.pt x (y + 1) := by
    intro h; rw [h, dist_self] at hXY
    have : (0 : ℝ) < tb e f := by exact_mod_cast b_pos e f M.he M.hef
    linarith
  refine two_circles hAB ?_ ?_ ?_
  · rw [key.1, L.dist_pt_a]
  · rw [key.2]; exact (L.dist_pt_c x (y + 1)).symm
  · have e1 : L.pt (x + 1) (y + 1) - L.pt (x + 1) y = L.v := by rw [L.pt_sub]; module
    have e2 : L.pt x (y + 1) - L.pt (x + 1) y = L.v - L.e0 := by rw [L.pt_sub]; module
    rw [e2] at hside
    rw [e1, e2]
    have : cross (L.v - L.e0) L.v < 0 := by
      have : cross (L.v - L.e0) L.v = - cross L.e0 L.v := by
        simp only [cross, PiLp.sub_apply]; ring
      rw [this]; linarith [L.hcr]
    exact mul_pos_of_neg_of_neg hside this

/-- The real `third_up` is the bare one. -/
theorem third_up_via_bare {p q r : Fin 3} (F : LFrame D e f α β γ p q r) {i : Fin N} {x ρ : ℝ} {Z : Plane}
    (hv : TileVerts (D.tile i) (F.pt x ρ) (F.pt (x + 1) ρ) Z)
    (hβ : (D.tile i).localAngle (F.pt x ρ) = β)
    (hup : 0 < cross F.e0 (Z - F.pt x ρ)) : Z = F.pt x (ρ + 1) :=
  third_upB (bandSetup_toModelData F.S) F.toBLat hv hβ hup

theorem third_down_via_bare {p q r : Fin 3} (F : LFrame D e f α β γ p q r) {i : Fin N} {x y : ℝ} {Z : Plane}
    (hv : TileVerts (D.tile i) (F.pt (x + 1) y) (F.pt x (y + 1)) Z)
    (hγ : (D.tile i).localAngle (F.pt (x + 1) y) = γ)
    (hside : cross (F.pt x (y + 1) - F.pt (x + 1) y) (Z - F.pt (x + 1) y) < 0) :
    Z = F.pt (x + 1) (y + 1) :=
  third_downB (bandSetup_toModelData F.S) F.toBLat hv hγ hside

end Erdos634.LaczMJ
