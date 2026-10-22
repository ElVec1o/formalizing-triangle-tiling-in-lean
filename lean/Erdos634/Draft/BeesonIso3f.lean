import Erdos634.Draft.BeesonIso3e
import Erdos634.Draft.LaczFormalIIcWN14

/-!
# Beeson, "Tilings of an isosceles triangle" (arXiv 1206.1974 v7), Lemma 11.8: the tiles on BOTH sides of a chord (maximal segment between adjacent sides)

NOTE, UNAUDITED.  Credit: Michael Beeson (arXiv 1206.1974 v7, Lemma 11.8; arXiv 1206.2229), Laczkovich (DCG 48 (2012), Sect. 4: maximal segments, `ends_coincide`),
Beeson-Zhang, Herdt, Zhang.  Formalization debt, not progress on the /goal outcomes.

Setting: `E` in the relative interior of the side `v_i v_{i+1}`, `F` in the relative interior of the next side, `B = v_{i+1}`, `d = F - E` (`B` lies on the RIGHT of `d`).
A tile `i0` of a dissection of the polygon has the two vertices `E`, `F` (its edge `EF` is a chord).
* `exit_F`: no tile has a left step from `F` along `d` nor a right step arriving from beyond `F`.
* `tile_step`: the tile `i0` is a left step `E -> F` or a right step `F -> E`.
* `both_sides_at_E`: there is a tile starting at `E` along `d` on the left AND one on the right (the chain at `E` is cut by the ray `d`).
* `chord_walk`: there is a RIGHT walk `E -> F` along `d` and it is non-empty (the tiles on the `B`-side of the chord), by `ends_coincide`.
Witness status: the hypotheses are those of a tile with two vertices on adjacent open sides; such a tile does not exist when the lemma 11.8 holds, so the layer is exercised on
the exit/step lemmas by the geometry of the polygon only (no instantiating tiling is possible: this is the content of Lemma 11.8); the chain, `ends_coincide` and `tile_step`
are exercised by the 1125-tiling in the earlier layers (`witness_1125_thm107`).
-/

open scoped Classical
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ} [NeZero M]

theorem corner_of_crs_pos {D : RegionDissection N} {Q : Plane} {κ : Type} [Fintype κ] (F : ExtFan D Q κ) (x : AtV D Q)
    (h : 0 < crs (F.p x) (F.q x)) : ∃ k, (D.tile x.1).pts k = Q := by
  rcases F.hspec x with ⟨k, hk, -⟩ | ⟨-, m', -, -, hq, -⟩
  · exact ⟨k, hk⟩
  · exfalso
    rw [hq] at h; unfold crs at h; simp at h; linarith

/-- A point `F + kappa d` (`kappa > 0`) beyond `F` along the chord lies outside the polygon. -/
theorem outside_beyond (P : ConvPoly M) (i : Fin M) {t t' : ℝ} (ht1 : t < 1) (ht0' : 0 < t') {E F : Plane}
    (hE : E = (1 - t) • P.v i + t • P.v (i + 1)) (hF : F = (1 - t') • P.v (i + 1) + t' • P.v (i + 1 + 1))
    {U : Plane} {κ : ℝ} (hκ : 0 < κ) (hU : toV2 (U - F) = (κ * (toV2 (F - E)).1, κ * (toV2 (F - E)).2)) :
    U ∉ P.carrier := by
  intro hmem
  have h0 : 0 ≤ P.c (i + 1) U := hmem (i + 1)
  obtain ⟨-, hc2, -⟩ := chord_geo P i ht1 ht0' hE hF
  have hFv : toV2 (F - P.v (i + 1)) = (t' * (toV2 (P.e (i + 1))).1, t' * (toV2 (P.e (i + 1))).2) := by
    have : F - P.v (i + 1) = t' • P.e (i + 1) := by
      rw [hF]; unfold ConvPoly.e; ext j; simp; ring
    rw [this]; unfold toV2; simp
  have hdec : toV2 (U - P.v (i + 1)) = ((toV2 (U - F)).1 + (toV2 (F - P.v (i + 1))).1, (toV2 (U - F)).2 + (toV2 (F - P.v (i + 1))).2) := by
    unfold toV2; ext <;> simp
  have hcc : P.c (i + 1) U = crs (toV2 (P.e (i + 1))) (toV2 (U - P.v (i + 1))) := rfl
  rw [hcc, hdec, hU, hFv] at h0
  change 0 ≤ crs (toV2 (P.e (i + 1))) _ at h0
  have : crs (toV2 (P.e (i + 1))) (κ * (toV2 (F - E)).1 + t' * (toV2 (P.e (i + 1))).1, κ * (toV2 (F - E)).2 + t' * (toV2 (P.e (i + 1))).2)
      = -(κ * crs (toV2 (F - E)) (toV2 (P.e (i + 1)))) := by
    unfold crs; simp only; ring
  have h0' : 0 ≤ crs (toV2 (P.e (i + 1))) (κ * (toV2 (F - E)).1 + t' * (toV2 (P.e (i + 1))).1, κ * (toV2 (F - E)).2 + t' * (toV2 (P.e (i + 1))).2) := h0
  rw [this] at h0'
  have := mul_pos hκ hc2
  linarith

theorem tile_in_carrier (D : RegionDissection N) (P : ConvPoly M) (hreg : D.region = P.carrier) {j : Fin N} {k : Fin 3} {U : Plane}
    (h : (D.tile j).pts k = U) : U ∈ P.carrier := by
  rw [← hreg, ← D.covers]
  exact Set.mem_iUnion.mpr ⟨j, h ▸ subset_convexHull ℝ _ ⟨k, rfl⟩⟩

theorem exit_F (D : RegionDissection N) (P : ConvPoly M) (hreg : D.region = P.carrier) (i : Fin M) {t t' : ℝ} (ht1 : t < 1) (ht0' : 0 < t')
    {E F : Plane} (hE : E = (1 - t) • P.v i + t • P.v (i + 1)) (hF : F = (1 - t') • P.v (i + 1) + t' • P.v (i + 1 + 1)) :
    (∀ j U', ¬ TriStep (D.tile j) (toV2 (F - E)) F U') ∧ (∀ j U', ¬ TriStep (D.tile j) (neg2 (toV2 (F - E))) U' F) := by
  constructor
  · intro j U' hS
    obtain ⟨kk, f, g, hk, hf, -, -, -, hpar, -⟩ := hS
    obtain ⟨κ, hκ, hκe⟩ := hpar.smul
    exact outside_beyond P i ht1 ht0' hE hF hκ hκe (tile_in_carrier D P hreg hf)
  · intro j U' hS
    obtain ⟨kk, f, g, hk, hf, -, -, -, hpar, -⟩ := hS
    obtain ⟨κ, hκ, hκe⟩ := hpar.smul
    refine outside_beyond P i ht1 ht0' hE hF hκ ?_ (tile_in_carrier D P hreg hk)
    -- hκe : toV2 (F - U') = (κ * (neg2 d).1, ...)  with pts kk = U'
    have h1 := congrArg Prod.fst hκe
    have h2 := congrArg Prod.snd hκe
    unfold neg2 at h1 h2
    simp only [toV2, PiLp.sub_apply] at h1 h2 ⊢
    have hk' : (D.tile j).pts kk = U' := hk
    ext
    · simp only; linarith
    · simp only; linarith

theorem tile_step (D : RegionDissection N) {E F : Plane} (hEF : E ≠ F) {i0 : Fin N} {kE kF : Fin 3}
    (hkE : (D.tile i0).pts kE = E) (hkF : (D.tile i0).pts kF = F) :
    TriStep (D.tile i0) (toV2 (F - E)) E F ∨ TriStep (D.tile i0) (neg2 (toV2 (F - E))) F E := by
  have hne : kE ≠ kF := by
    intro h; apply hEF; rw [← hkE, ← hkF, h]
  have h3 : ∀ a b : Fin 3, a ≠ b → ∃ g : Fin 3, g ≠ a ∧ g ≠ b := by decide
  obtain ⟨g, hgE, hgF⟩ := h3 kE kF hne
  have hcr := tri_cross_ne (D.tile i0) (kk := kE) (f := kF) (g := g) (Ne.symm hne) hgE hgF
  rw [hkE, hkF] at hcr
  have hd : toV2 (F - E) ≠ 0 := toV2_ne_zero (sub_ne_zero.mpr (Ne.symm hEF))
  rcases lt_or_gt_of_ne hcr with hlt | hgt
  · right
    refine ⟨kF, kE, g, hkF, hkE, hne, hgF, hgE, ?_, ?_⟩
    · have : toV2 (E - F) = (1 * (neg2 (toV2 (F - E))).1, 1 * (neg2 (toV2 (F - E))).2) := by
        unfold neg2 toV2; ext <;> simp
      exact smul_par one_pos (by unfold neg2; intro h; apply hd; have a := congrArg Prod.fst h; have b := congrArg Prod.snd h; exact Prod.ext (by simpa using a) (by simpa using b)) this
    · have e : toV2 ((D.tile i0).pts g - F) = toV2 ((D.tile i0).pts g - E) - toV2 (F - E) := by
        unfold toV2; ext <;> simp
      rw [e]
      unfold crs at hlt
      unfold crs neg2
      simp only [Prod.fst_sub, Prod.snd_sub] at hlt ⊢
      nlinarith [hlt]
  · left
    refine ⟨kE, kF, g, hkE, hkF, Ne.symm hne, hgE, hgF, ?_, ?_⟩
    · exact par_self hd
    · exact hgt

end Erdos634.Draft.LaczFormal.RG
