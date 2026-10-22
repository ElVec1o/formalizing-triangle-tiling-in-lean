-- Draft/LaczFormalIIcIsoWitF.lean -- NON-VACUITY witness for `IIcIsoCore`, step F: corner counts `cnt = (1,1,0)` at the octagon vertices, `hregc`.
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012)), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcIsoWitE

open Erdos634.Geometry Erdos634.CertCoord Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Thm21 Erdos634.Draft.LaczFormal.RG

namespace Erdos634.Draft.LaczFormal.IsoWit

theorem cnt_gen (X : Plane) (l : Fin 3) : RG.cnt octDiss idx X l = (Finset.univ.filter (fun i : Fin 8 => (tile i).pts l = X)).card := by
  unfold RG.cnt
  have : (Finset.univ.filter (fun p : Fin 8 × Fin 3 => (octDiss.tile p.1).pts p.2 = X ∧ idx p.1 p.2 = l)) =
      (Finset.univ.filter (fun i : Fin 8 => (tile i).pts l = X)).image (fun i => (i, l)) := by
    ext ⟨i, k⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Prod.mk.injEq, idx, Equiv.Perm.coe_one, id_eq]
    constructor
    · rintro ⟨h1, rfl⟩; exact ⟨i, h1, rfl, rfl⟩
    · rintro ⟨j, h1, rfl, rfl⟩; exact ⟨h1, rfl⟩
  rw [this, Finset.card_image_of_injective _ (fun a b h => (Prod.mk.inj h).1)]

theorem pts0_eq (i j : Fin 8) : (tile i).pts 0 = oct.v j ↔ i = j := by
  show mkPt (cx i) (cy i) = mkPt (cx j) (cy j) ↔ _
  constructor
  · intro h; obtain ⟨h1, h2⟩ := mkPt_inj h; exact V_inj h1 h2
  · rintro rfl; rfl
theorem pts1_eq (i j : Fin 8) : (tile i).pts 1 = oct.v j ↔ i + 1 = j := by
  show mkPt (cx (i + 1)) (cy (i + 1)) = mkPt (cx j) (cy j) ↔ _
  constructor
  · intro h; obtain ⟨h1, h2⟩ := mkPt_inj h; exact V_inj h1 h2
  · rintro rfl; rfl
theorem pts2_ne (i j : Fin 8) : (tile i).pts 2 ≠ oct.v j := by
  intro h
  obtain ⟨h1, h2⟩ := mkPt_inj (show mkPt 0 0 = mkPt (cx j) (cy j) from h)
  have := cxy_sq j
  rw [← h1, ← h2] at this
  norm_num at this

theorem octDiss_cnt0 (j : Fin 8) : RG.cnt octDiss idx (oct.v j) 0 = 1 := by
  rw [cnt_gen, Finset.card_eq_one]
  exact ⟨j, by ext i; simp [pts0_eq]⟩
theorem octDiss_cnt1 (j : Fin 8) : RG.cnt octDiss idx (oct.v j) 1 = 1 := by
  rw [cnt_gen, Finset.card_eq_one]
  exact ⟨j - 1, by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, pts1_eq]
    constructor
    · intro h; exact eq_sub_of_add_eq h
    · intro h; rw [h]; exact sub_add_cancel _ _⟩
theorem octDiss_cnt2 (j : Fin 8) : RG.cnt octDiss idx (oct.v j) 2 = 0 := by
  rw [cnt_gen, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro i _; exact pts2_ne i j

theorem octDiss_hregc : ∀ X, RG.cnt octDiss idx X 0 = RG.cnt octDiss idx X 1 := by
  intro X
  rw [cnt_gen, cnt_gen]
  refine Finset.card_equiv (Equiv.subRight (1 : Fin 8)) ?_
  intro i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.subRight_apply]
  show (tile i).pts 0 = X ↔ mkPt (cx (i - 1 + 1)) (cy (i - 1 + 1)) = X
  rw [sub_add_cancel]
  rfl

end Erdos634.Draft.LaczFormal.IsoWit
