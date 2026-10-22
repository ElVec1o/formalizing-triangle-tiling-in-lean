-- Draft/TheoremHCongruent.lean — THEOREM H, TOP-LEVEL, FOR AN ARBITRARY CONGRUENCE (EVIDENCE A20).
-- `Draft/L3MReal.theorem_H_real` closes branch (H) for `e ≥ 2` from `ApexFrameReal.M1Data`, whose
-- fields fix an exact vertex labelling and exact coordinates (`ApexNormal.m1Data_normal` derives
-- `M1Data` from `D.target = baseBetaTarget e f` LITERALLY, plus raw `sideOpp` data on `D.model`).
-- The paper's hypothesis is weaker: `D₀.target` merely *congruent* to `baseBetaTarget e f`, `D₀.model`
-- merely *congruent* to the tile `(ef, f² − e², f²)`, no vertex order at all — the gap named in
-- EVIDENCE A17/A20, "no top-level theorem taking only the natural hypotheses." This file closes it,
-- in exactly the form of `E1BaseWord.e1_family_f_ge_3_congruent` (the `e = 1` analogue).
--
-- The bridge is the one `E1NormalForm.normalFormC` already built for `e = 1`
-- (`Congruence.Tri.Congruent` supplies an isometry `g` of the *target* congruence; `normalFormC`
-- replaces `D₀`'s model outright by any tile `T` congruent to it, and carries the tiles by `g`,
-- `rfl`) plus the explicit coordinate tile `Draft.ModelWitnessE.tileTri e f`, whose three `sideOpp`
-- values are `ModelWitnessE.model_witness`'s `.hs0/.hs1/.hs2` fields. `e ≥ 2` needs no analogue of
-- `E1NormalForm.congruent_modelTri_of_sides`'s bespoke SSS lemma because that lemma already IS
-- general: `SssCongruent`'s route is `sideOpp` values, not `e = 1` specifically — `theorem_H_of_sides`
-- below reuses it via `tileTri`'s own `sideOpp` facts, proved inline (`tileTri_sides`).
--
-- Build (scratch oleans; never .lake), from `lean/`:
--   bash /(private working notes, not included) \
--     Erdos634/Draft/TheoremHCongruent.lean Erdos634/Draft/TheoremHCongruent.olean
-- Imported directly by All.lean (stale "NOT imported" header corrected 2026-10-04).
import Erdos634.Draft.ApexNormal
import Erdos634.Draft.L3MReal
import Erdos634.Draft.ModelWitnessE
import Erdos634.SssCongruent

namespace Erdos634.Draft.TheoremHCongruent

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.BaseBetaTargetCoord
open Erdos634.Draft.ApexWitness44 Erdos634.Draft.ApexNormal Erdos634.Draft.ModelWitnessE

/-! ## 1. Normal position (literal target, raw `sideOpp` model data) -/

/-- **Theorem H, normal position.** `D.target` is `baseBetaTarget e f` on the nose; the model's
`sideOpp` data is given raw. Immediate from `ApexNormal.m1Data_normal` (builds `M1Data`) and
`L3MReal.theorem_H_real` (closes `M1Data` to `False`) — no new geometry, just the composition
EVIDENCE P51 already licenses. -/
theorem theorem_H_normal {N : ℕ} (D : CongruentDissection N) {e f : ℕ}
    (hco : Nat.Coprime e f) (he : 2 ≤ e) (hef : e + 2 ≤ f)
    (he0 : (0 : ℝ) < e) (hefR : (e : ℝ) < f)
    (htgt : D.target = baseBetaTarget e f he0 hefR)
    (hs0 : sideOpp D.model 0 = (e : ℝ) * f) (hs1 : sideOpp D.model 1 = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (hs2 : sideOpp D.model 2 = (f : ℝ) ^ 2) : False :=
  Erdos634.Draft.RowWallReal.theorem_H_real
    (m1Data_normal D hco he hef he0 hefR htgt hs0 hs1 hs2)

/-! ## 2. The explicit coordinate tile's `sideOpp` values -/

/-- The coordinate tile `ModelWitnessE.tileTri e f` has `sideOpp` values `(ef, f² − e², f²)` —
`ModelWitnessE.model_witness`'s `ModelDataE` fields on the one-tile dissection, read through
`single _ .model = tileTri e f he hef` (`rfl`). -/
theorem tileTri_sides {e f : ℝ} (he : 0 < e) (hef : e < f) :
    sideOpp (tileTri e f he hef) 0 = e * f ∧
    sideOpp (tileTri e f he hef) 1 = f ^ 2 - e ^ 2 ∧
    sideOpp (tileTri e f he hef) 2 = f ^ 2 := by
  have hw := model_witness he hef
  exact ⟨hw.hs0, hw.hs1, hw.hs2⟩

/-! ## 3. Theorem H for an arbitrary congruent dissection -/

/-- **THEOREM H, TOP LEVEL — for ANY congruent dissection of a congruent copy of the base-β
target, `e ≥ 2` — PROVED.** No `CongruentDissection` `D₀` has target congruent to `baseBetaTarget
e f` and model congruent to the tile `(ef, f² − e², f²)`, at any coprime `2 ≤ e ≤ f − 2`. No vertex
correspondence, labelling, or coordinate placement is assumed — `Tri.Congruent` is congruence under
an arbitrary isometry and an arbitrary relabelling of the three vertices. This is the bridge lemma
named in EVIDENCE A17/A20, matching `E1BaseWord.e1_family_f_ge_3_congruent`'s form exactly. -/
theorem theorem_H_congruent {N : ℕ} (D₀ : CongruentDissection N) {e f : ℕ}
    (hco : Nat.Coprime e f) (he : 2 ≤ e) (hef : e + 2 ≤ f)
    (he0 : (0 : ℝ) < e) (hefR : (e : ℝ) < f)
    (htgt : D₀.target.Congruent (baseBetaTarget e f he0 hefR))
    (hmod : D₀.model.Congruent (tileTri (e : ℝ) f he0 hefR)) : False := by
  obtain ⟨g, σ, hg⟩ := htgt
  set D := Erdos634.E1NormalForm.normalFormC D₀ g σ hmod with hD
  have hDtgt : D.target = baseBetaTarget e f he0 hefR :=
    Erdos634.E1NormalForm.normalFormC_target D₀ hg hmod
  have hDmod : D.model = tileTri (e : ℝ) f he0 hefR :=
    Erdos634.E1NormalForm.normalFormC_model D₀ g σ hmod
  obtain ⟨hs0, hs1, hs2⟩ := tileTri_sides he0 hefR
  refine theorem_H_normal D hco he hef he0 hefR hDtgt ?_ ?_ ?_ <;> rw [hDmod]
  · exact hs0
  · exact hs1
  · exact hs2

/-- **The same, from raw `sideOpp` values on the model instead of a `Congruent` hypothesis
against the explicit coordinate tile** — the analogue of `E1BaseWord.e1_family_f_ge_3_of_sides`,
via `SssCongruent.congruent_of_dist_three` (the same route `E1NormalForm.congruent_modelTri_of_sides`
uses): matching `sideOpp` values (`sideOpp j = dist (pts (j+1)) (pts (j+2))`) give the three pairwise
distances, hence `Congruent` by SSS. -/
theorem theorem_H_of_sides {N : ℕ} (D₀ : CongruentDissection N) {e f : ℕ}
    (hco : Nat.Coprime e f) (he : 2 ≤ e) (hef : e + 2 ≤ f)
    (he0 : (0 : ℝ) < e) (hefR : (e : ℝ) < f)
    (htgt : D₀.target.Congruent (baseBetaTarget e f he0 hefR))
    (h0 : sideOpp D₀.model 0 = (e : ℝ) * f) (h1 : sideOpp D₀.model 1 = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (h2 : sideOpp D₀.model 2 = (f : ℝ) ^ 2) : False := by
  apply theorem_H_congruent D₀ hco he hef he0 hefR htgt
  obtain ⟨hs0, hs1, hs2⟩ := tileTri_sides he0 hefR
  simp only [sideOpp, Erdos634.E1NormalForm.fin3_two_add_one, Erdos634.E1NormalForm.fin3_two_add_two,
    Erdos634.E1NormalForm.fin3_one_add_one, Erdos634.E1NormalForm.fin3_one_add_two,
    zero_add] at h0 h1 h2 hs0 hs1 hs2
  exact Erdos634.SssCongruent.congruent_of_dist_three (T := D₀.model)
    (U := tileTri (e : ℝ) f he0 hefR)
    (by rw [h2, hs2]) (by rw [h0, hs0]) (by rw [h1, hs1])

/-! ### Non-vacuity

The conclusion is `False`: every hypothesis of `theorem_H_congruent` is individually satisfiable,
jointly they are not (that is the theorem). `hco/he/hef`: e.g. `(e, f) = (2, 5)` — **never `(3, 4)`,
hazard H59, and the coprime-2-≤-e-≤-f−2 range is exactly what excludes `(3,4)` from the domain
anyway** (`e ≤ f − 2` forces `f ≥ 4`; at `f = 4` only `e ∈ {1, 2}` and `hco`/`he` force `e = 2`,
never `3`). `he0/hefR`: `norm_num` casts of the same. `htgt`: `Tri.Congruent.refl` on
`baseBetaTarget e f he0 hefR` (any dissection whose target literally *is* the coordinate target
has it, e.g. `ModelWitnessE.single`'s one-tile dissections of a triangle by itself). `hmod`:
`Tri.Congruent.refl` on `tileTri e f he0 hefR`, matching `ModelWitnessE.model_witness`'s own
witness tile — `ModelDataE` is satisfiable there (`model_witness`), so the model side of `M1Data`
is not the obstruction; nor is the target side (`ApexWitness44.m1_target_witness`, EVIDENCE
P51's non-vacuity note); nor the angle bundle (`ApexWitness44.angleData_member`). No
`CongruentDissection` jointly satisfying `htgt` and `hmod` for the *same* `D₀` is exhibited — none
exists, and `theorem_H_congruent` is exactly that non-existence. -/

theorem hyps_25 : (2:ℝ) ≤ ((2:ℕ):ℝ) ∧ ((2:ℕ):ℝ) + 2 ≤ ((5:ℕ):ℝ) ∧ Nat.Coprime 2 5 ∧
    (0:ℝ) < ((2:ℕ):ℝ) ∧ ((2:ℕ):ℝ) < ((5:ℕ):ℝ) := by
  refine ⟨by norm_num, by norm_num, by decide, by norm_num, by norm_num⟩

end Erdos634.Draft.TheoremHCongruent

#print axioms Erdos634.Draft.TheoremHCongruent.theorem_H_normal
#print axioms Erdos634.Draft.TheoremHCongruent.tileTri_sides
#print axioms Erdos634.Draft.TheoremHCongruent.theorem_H_congruent
#print axioms Erdos634.Draft.TheoremHCongruent.theorem_H_of_sides
