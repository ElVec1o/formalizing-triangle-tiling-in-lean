import Erdos634.Draft.RWInst
import Erdos634.Refl.MC17Sound

/-!
# Beeson (arXiv 1206.2229 v4) Lemma 40, case N = 17: no tiling, by exact search certificate

The tile `(3, 8, 9)` (angles `alpha, beta, 2 alpha + beta`, `3 alpha + 2 beta = pi`, the member `(e,f) = (1,3)`, `m = 1` of the cevian
family `N = m^2 (2 f^2 - e^2)`) has `N = 17`; the target is the triangle with angles `(alpha + beta, beta, 2 alpha)` and sides
`(24, 17, 27)` (side `27 = 6 a + c`, the printed word `(6, 0, 1)`).  The kernel-checked free-branch-point certificate
`Refl.MC17.not_dissection` (33 nodes, `CheckM`, exact replay in `Q(sqrt 35)`) shows that NO `CongruentDissection` (any number of tiles, reflections
allowed) has target congruent to this triangle and model congruent to the tile.  This replaces the conditional skeleton
`l40_601_contradiction` (gaps A and B) for this instance by a proof that does not use the count at all.

Generation: (private working notes, not included) (f64 search, `3 8 9  24 17 27  17  3 1`, 33-node tree) then (private working notes, not included) (exact replay, `C17 35 "0,0; 24,0; 127/6,17/6" "3 8 9"`),
artefacts under (private working notes, not included).  The registry already held the engine verdict NO_TILING (191 nodes); this is the formal certificate.
NOTE, UNAUDITED.  Credit: Beeson (arXiv 1206.2229 v4, Lemma 40), Beeson-Rosu, Laczkovich, Beeson-Zhang.  Formalization debt, not progress on the /goal outcomes.
-/

namespace Erdos634.Draft.BeesonCol5

open Erdos634.Geometry Erdos634.Draft.NSQRW Erdos634.CertNode Erdos634.CertCoord

theorem TGT_C17 : dist (Refl.MC17.TGT.pts 0) (Refl.MC17.TGT.pts 1) = 24 ∧
    dist (Refl.MC17.TGT.pts 1) (Refl.MC17.TGT.pts 2) = 17 ∧ dist (Refl.MC17.TGT.pts 0) (Refl.MC17.TGT.pts 2) = 27 :=
  model_sides_rp Refl.MC17.hDn Refl.MC17.TGT_pos (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

/-- The S4 instance `(S', e, f) = (1, 1, 3)`: tile `(3, 8, 9)`, target sides `(17, 24, 27)`: no dissection (any number of tiles). -/
theorem s4inst_1_1_3 : S4Inst 1 1 3 :=
  s4inst_of_cert 1 1 3 Refl.MC17.TGT Refl.MC17.MODEL
    ⟨by rw [TGT_C17.1]; norm_num, by rw [TGT_C17.2.1]; norm_num, by rw [TGT_C17.2.2]; norm_num⟩
    ⟨by rw [Refl.MC17.MODEL_sides.1]; norm_num, by rw [Refl.MC17.MODEL_sides.2.1]; norm_num,
      by rw [Refl.MC17.MODEL_sides.2.2]; norm_num⟩
    (fun D hT hM => Refl.MC17.not_dissection D hT hM)

/-- **Beeson Lemma 40, N = 17**: the triangle with sides `(17, 24, 27)` is not tiled by 17 (indeed by any number of) copies of the tile `(3, 8, 9)`. -/
theorem lemma40_N17 (D : CongruentDissection 17)
    (h0 : D.target.oppLen 0 = 17) (h1 : D.target.oppLen 1 = 24) (h2 : D.target.oppLen 2 = 27)
    (hm : ∃ σ : Equiv.Perm (Fin 3), D.model.oppLen (σ 0) = 3 ∧ D.model.oppLen (σ 1) = 8 ∧ D.model.oppLen (σ 2) = 9) : False := by
  refine s4inst_1_1_3 D ?_ ?_ ?_ ?_
  · rw [h0]; norm_num
  · rw [h1]; norm_num
  · rw [h2]; norm_num
  · obtain ⟨σ, a, b, c⟩ := hm
    exact ⟨σ, by rw [a]; norm_num, by rw [b]; norm_num, by rw [c]; norm_num⟩

end Erdos634.Draft.BeesonCol5
#print axioms Erdos634.Draft.BeesonCol5.lemma40_N17
