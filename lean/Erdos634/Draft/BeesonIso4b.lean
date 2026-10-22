import Erdos634.Draft.BeesonIso4a

/-!
# Beeson, "Tilings of an isosceles triangle" (arXiv 1206.1974 v7), Lemma 11.10: the chain at a base vertex (counts)

NOTE, UNAUDITED.  Credit: Michael Beeson (arXiv 1206.1974 v7, Lemma 11.10), Laczkovich (DCG 48 (2012), Sect. 4), Beeson-Zhang, Herdt, Zhang.
Formalization debt, not progress on the /goal outcomes.

* `OpenChain.first_eq`, `OpenChain.last_eq`: the sector starting along the side is `c 1`, the one ending along the opposite ray is `c (L-1)`.
* `chain_counts`: the labels of the tiles of the chain at a vertex of an open side: exactly one `beta`, and `#alpha + 2 #gamma = 3` (angle `pi`, H1), so 3 or 4 tiles; and the count.
* `c_pos_next`, `c_pos_prev`: a point of the open side `i` is strictly inside the sides `i+1`, `i-1`.
-/

open scoped Classical
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ} [NeZero M]

namespace OpenChain

variable {D : RegionDissection N} {Q : Plane} {pT : V2} (C : OpenChain D Q pT)

theorem first_eq {x : AtV D Q} (hx : 0 < crs (C.F.p x) (C.F.q x)) (hp : Par (C.F.p x) pT) : x = C.c 1 :=
  corner_start_unique C.F hx (C.hcrs 1 le_rfl (by have := C.hL2; omega)) (hp.trans C.hfirst.symm)

theorem last_eq {x : AtV D Q} (hq : Par (C.F.q x) (-pT.1, -pT.2)) : x = C.c (C.L - 1) := by
  by_contra hne
  have hcL := C.hcrs (C.L - 1) (by have := C.hL2; omega) (by have := C.hL2; omega)
  exact end_inj_sum' C.F (o := Sum.inl (C.c (C.L - 1))) (o' := Sum.inl x)
    (fun h => hne (Sum.inl_injective h).symm) (by simpa using hq.trans C.hlast.symm)

end OpenChain

/-- Labels of a chain at a vertex of an open side: exactly one beta, `#alpha + 2 #gamma = 3`, total `L - 1`. -/
theorem chain_counts (C : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3))
    (hidxA : ∀ i v, C.model.angleAt (idx i v) = (C.tile i).angleAt v)
    (hβ : C.model.angleAt 1 = Real.pi - 3 * C.model.angleAt 0) (hγ : C.model.angleAt 2 = 2 * C.model.angleAt 0)
    (hα : ¬ ∃ r : ℚ, C.model.angleAt 0 = (r : ℝ) * Real.pi) {Q : Plane} {pT : V2} (Ch : OpenChain C.toRegionDissection Q pT) :
    ∃ (l : ℕ → Fin 3) (kc : ℕ → Fin 3), (∀ j, 1 ≤ j → j < Ch.L →
      (C.tile (Ch.c j).1).pts (kc j) = Q ∧ idx (Ch.c j).1 (kc j) = l j) ∧
      ((Finset.Ico 1 Ch.L).filter (fun j => l j = 1)).card = 1 ∧
      ((Finset.Ico 1 Ch.L).filter (fun j => l j = 0)).card + 2 * ((Finset.Ico 1 Ch.L).filter (fun j => l j = 2)).card = 3 ∧
      Ch.L - 1 = ((Finset.Ico 1 Ch.L).filter (fun j => l j = 0)).card + ((Finset.Ico 1 Ch.L).filter (fun j => l j = 1)).card +
        ((Finset.Ico 1 Ch.L).filter (fun j => l j = 2)).card := by
  obtain ⟨l, kc, hl⟩ := chain_labels C idx hidxA Ch
  refine ⟨l, kc, fun j h1 h2 => ⟨(hl j h1 h2).1, (hl j h1 h2).2.1⟩, ?_⟩
  have hs : ∑ j ∈ Finset.Ico 1 Ch.L, C.model.angleAt (l j) = Real.pi := by
    rw [← Ch.hsum]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [Finset.mem_Ico] at hj
    exact ((hl j hj.1 hj.2).2.2).symm
  rw [sum_labels C.model.angleAt (Finset.Ico 1 Ch.L) l, Fin.sum_univ_three] at hs
  have key := vtype_arith (α := C.model.angleAt 0) (β := C.model.angleAt 1) hβ hα
    ((Finset.Ico 1 Ch.L).filter (fun j => l j = 0)).card ((Finset.Ico 1 Ch.L).filter (fun j => l j = 1)).card
    ((Finset.Ico 1 Ch.L).filter (fun j => l j = 2)).card 0 1 (by rw [hγ] at hs; push_cast; linarith)
  obtain ⟨k1, k2⟩ := key
  have hc := card_labels (Finset.Ico 1 Ch.L) l
  rw [Nat.card_Ico] at hc
  refine ⟨by exact_mod_cast k1, by omega, hc⟩

/-- A point of the open side `i` is strictly inside the next side. -/
theorem c_pos_next (P : ConvPoly M) (i : Fin M) {t : ℝ} (ht1 : t < 1) {X : Plane} (hX : X = (1 - t) • P.v i + t • P.v (i + 1)) :
    0 < P.c (i + 1) X := by
  have hc := crs_consecutive_pos P i
  have hcc : P.c (i + 1) X = crs (toV2 (P.e (i + 1))) (toV2 (X - P.v (i + 1))) := rfl
  have e : toV2 (X - P.v (i + 1)) = (-(1 - t) * (toV2 (P.e i)).1, -(1 - t) * (toV2 (P.e i)).2) := by
    have : X - P.v (i + 1) = (-(1 - t)) • P.e i := by
      rw [hX]; unfold ConvPoly.e; ext j; simp; ring
    rw [this]; unfold toV2; simp
  rw [hcc, e]
  have : crs (toV2 (P.e (i + 1))) (-(1 - t) * (toV2 (P.e i)).1, -(1 - t) * (toV2 (P.e i)).2) = (1 - t) * crs (toV2 (P.e i)) (toV2 (P.e (i + 1))) := by
    unfold crs; simp only; ring
  rw [this]; exact mul_pos (by linarith) hc

/-- A point of the open side `i` is strictly inside the previous side. -/
theorem c_pos_prev (P : ConvPoly M) (i : Fin M) {t : ℝ} (ht0 : 0 < t) {X : Plane} (hX : X = (1 - t) • P.v i + t • P.v (i + 1)) :
    0 < P.c (i - 1) X := by
  have hc := crs_consecutive_pos P (i - 1)
  rw [sub_add_cancel] at hc
  have hcc : P.c (i - 1) X = crs (toV2 (P.e (i - 1))) (toV2 (X - P.v (i - 1))) := rfl
  have e : toV2 (X - P.v (i - 1)) = ((toV2 (P.e (i - 1))).1 + t * (toV2 (P.e i)).1, (toV2 (P.e (i - 1))).2 + t * (toV2 (P.e i)).2) := by
    have : X - P.v (i - 1) = P.e (i - 1) + t • P.e i := by
      rw [hX]; unfold ConvPoly.e; rw [sub_add_cancel]; ext j; simp; ring
    rw [this]; unfold toV2; simp
  rw [hcc, e]
  have : crs (toV2 (P.e (i - 1))) ((toV2 (P.e (i - 1))).1 + t * (toV2 (P.e i)).1, (toV2 (P.e (i - 1))).2 + t * (toV2 (P.e i)).2) =
      t * crs (toV2 (P.e (i - 1))) (toV2 (P.e i)) := by
    unfold crs; simp only; ring
  rw [this]; exact mul_pos ht0 hc

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.chain_counts
#print axioms Erdos634.Draft.LaczFormal.RG.c_pos_prev
