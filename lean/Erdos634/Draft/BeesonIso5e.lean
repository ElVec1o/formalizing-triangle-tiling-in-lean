import Erdos634.Draft.BeesonIso5d

/-!
# Beeson, "Tilings of an isosceles triangle" (arXiv 1206.1974 v7), Lemma 11.10: at least FOUR tiles are supported by the base (polygon form)

NOTE, UNAUDITED.  Credit: Michael Beeson (arXiv 1206.1974 v7, Lemma 11.10), Laczkovich (DCG 48 (2012)), Beeson-Zhang, Herdt, Zhang.
Formalization debt, not progress on the /goal outcomes.

`four_base`: triangle `P` (a `ConvPoly 3`), tile `t (k^2, m^2-k^2, km)` with model angles `(alpha, pi - 3 alpha, 2 alpha)`, H1, base side `k+1` with `alpha` corners, apex `B` of angle
`pi - 2 alpha`, the two legs satisfy `c X = a Y` (Lemma 11.5).  Then every walk along the base has at least four steps.
Repaired proof (the print dismisses the leg case `X = a + c` by a statement about `AC`):
(1) the base has a b-edge and a c-edge (`side_len_counts_b`), so `(na,nb,nc)` is `(1,1,1)`, `(0,1,2)` or `(0,2,1)` for three tiles; `k Y' = m X'` (`base_arith`) leaves `(1,1,1)`, `X = a + c`;
(2) each leg then is `[c, a]` (resp. `[a, c]`) read from the alpha corner (`leg_structure`: a c-edge exists, `leg_arith`; the tile at an alpha corner has no a-edge, `step_ne_a`);
(3) both legs have an a-edge tile at `B`, each carrying the unique beta of `B` (`two_a_steps_at_B`): contradiction.
Witness status: all hypotheses are those of the 1125-tiling's polygon except the walk with exactly 3 steps, which is the conclusion's negation.
-/

open scoped Classical
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ} [NeZero M]

theorem fin3_add4 : ∀ k : Fin 3, k + 1 + 1 + 1 + 1 = k + 1 := by intro k; fin_cases k <;> rfl

theorem c_zero_open (P : ConvPoly M) (i : Fin M) {s : ℝ} {Z : Plane} (hZ : Z = (1 - s) • P.v i + s • P.v (i + 1)) : P.c i Z = 0 := by
  have hc : P.c i Z = crs (toV2 (P.e i)) (toV2 (Z - P.v i)) := rfl
  have e : toV2 (Z - P.v i) = (s * (toV2 (P.e i)).1, s * (toV2 (P.e i)).2) := by
    have : Z - P.v i = s • P.e i := by rw [hZ]; unfold ConvPoly.e; ext j; simp; ring
    rw [this]; unfold toV2; simp
  rw [hc, e]; unfold crs; simp only; ring

theorem nat_form (t : ℝ) (kt mt na nb nc : ℕ) (hmk : kt ^ 2 ≤ mt ^ 2) :
    (na : ℝ) * (t * (kt : ℝ) ^ 2) + nb * (t * ((mt : ℝ) ^ 2 - (kt : ℝ) ^ 2)) + nc * (t * ((kt : ℝ) * mt)) =
      t * ((na * kt ^ 2 + nb * (mt ^ 2 - kt ^ 2) + nc * (kt * mt) : ℕ) : ℝ) := by
  rw [Nat.cast_add, Nat.cast_add, Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hmk]
  push_cast; ring

theorem rel_nat (t : ℝ) (ht : 0 < t) (kt mt Y X : ℕ) (hk : 0 < kt)
    (h : (t * ((kt : ℝ) * mt)) * (t * (X : ℝ)) = (t * (kt : ℝ) ^ 2) * (t * (Y : ℝ))) : kt * Y = mt * X := by
  have hkr : (0 : ℝ) < kt := by exact_mod_cast hk
  have h2 : (t * t * kt) * ((mt : ℝ) * X - kt * Y) = 0 := by linear_combination h
  have h3 : (t * t * kt) ≠ 0 := by positivity
  have h4 : (mt : ℝ) * X - kt * Y = 0 := by
    rcases mul_eq_zero.mp h2 with h5 | h5
    · exact absurd h5 h3
    · exact h5
  have h5 : (kt : ℝ) * Y = mt * X := by linarith
  exact_mod_cast h5

theorem four_base (C : CongruentRegionDissection N) [HasFansC C.toRegionDissection] (P : ConvPoly 3) (hreg : C.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((C.tile i).pts k) ((C.tile i).pts k') = dist (C.model.pts (idx i k)) (C.model.pts (idx i k')))
    (hidxA : ∀ i v, C.model.angleAt (idx i v) = (C.tile i).angleAt v)
    (hβ : C.model.angleAt 1 = Real.pi - 3 * C.model.angleAt 0) (hγ : C.model.angleAt 2 = 2 * C.model.angleAt 0)
    (hα : ¬ ∃ r : ℚ, C.model.angleAt 0 = (r : ℝ) * Real.pi)
    (hPang : ∀ k : Fin 3, P.angle (k + 1) = C.model.angleAt 0 ∨ P.angle (k + 1) = Real.pi - 2 * C.model.angleAt 0)
    (hab : slen C 0 ≠ slen C 1) (hac : slen C 0 ≠ slen C 2) (hbc : slen C 1 ≠ slen C 2)
    {t : ℝ} (ht : 0 < t) {kt mt : ℕ} (hcop : Nat.Coprime kt mt) (hlt : kt < mt) (hm2 : mt < 2 * kt)
    (ea : slen C 0 = t * (kt : ℝ) ^ 2) (eb : slen C 1 = t * ((mt : ℝ) ^ 2 - (kt : ℝ) ^ 2)) (ec : slen C 2 = t * ((kt : ℝ) * mt))
    (k : Fin 3) (hi0 : P.angle (k + 1) = C.model.angleAt 0) (hi1 : P.angle (k + 1 + 1) = C.model.angleAt 0)
    (hBang : P.angle (k + 1 + 1 + 1) = Real.pi - 2 * C.model.angleAt 0)
    (hX1 : slen C 2 * dist (P.v (k + 1 + 1)) (P.v (k + 1 + 1 + 1)) = slen C 0 * dist (P.v (k + 1)) (P.v (k + 1 + 1)))
    (hX2 : slen C 2 * dist (P.v (k + 1 + 1 + 1)) (P.v (k + 1 + 1 + 1 + 1)) = slen C 0 * dist (P.v (k + 1)) (P.v (k + 1 + 1)))
    {L : List (Fin N × Plane × Plane)} (W : WalkT C.toRegionDissection (toV2 (P.e (k + 1))) (P.v (k + 1)) (P.v (k + 1 + 1)) L) :
    4 ≤ L.length := by
  have hkt : 2 ≤ kt := by omega
  have hmk : kt ^ 2 ≤ mt ^ 2 := by nlinarith
  have hac_lt : slen C 0 < slen C 2 := by
    rw [ea, ec]
    have : (kt : ℝ) < mt := by exact_mod_cast hlt
    have h2 : (0 : ℝ) < kt := by exact_mod_cast (by omega : 0 < kt)
    have h3 := mul_pos (mul_pos ht h2) (sub_pos.mpr this)
    nlinarith [h3]
  have h3 := base_ge_three C P hreg idx hidx hidxA hβ hγ hα hac_lt k hi0 hi1 W
  by_contra hlt4
  have hL3 : L.length = 3 := by omega
  -- the base
  obtain ⟨na, nb, nc, hl, hY, hb1, hc1⟩ := side_len_counts_b C P hreg idx hidx hidxA hβ hγ hα hPang hab hac hbc (k + 1) hi0 hi1 W
  -- the legs
  obtain ⟨L1, W1⟩ := side_walk_exists_poly C.toRegionDissection P hreg (k + 1 + 1)
  obtain ⟨u1, v1, w1, hl1, hX1', hw1⟩ := side_len_counts C P hreg idx hidx hidxA hβ hγ hα hPang hab hac hbc (k + 1 + 1) W1
  obtain ⟨L2, W2⟩ := side_walk_exists_poly C.toRegionDissection P hreg (k + 1 + 1 + 1)
  obtain ⟨u2, v2, w2, hl2, hX2', hw2⟩ := side_len_counts C P hreg idx hidx hidxA hβ hγ hα hPang hab hac hbc (k + 1 + 1 + 1) W2
  rw [ea, eb, ec, nat_form t kt mt na nb nc hmk] at hY
  rw [ea, eb, ec, nat_form t kt mt u1 v1 w1 hmk] at hX1'
  rw [ea, eb, ec, nat_form t kt mt u2 v2 w2 hmk] at hX2'
  have hrel1 : kt * (na * kt ^ 2 + nb * (mt ^ 2 - kt ^ 2) + nc * (kt * mt)) = mt * (u1 * kt ^ 2 + v1 * (mt ^ 2 - kt ^ 2) + w1 * (kt * mt)) := by
    apply rel_nat t ht _ _ _ _ (by omega)
    rw [ea, ec, hX1', hY] at hX1
    linarith
  have hrel2 : kt * (na * kt ^ 2 + nb * (mt ^ 2 - kt ^ 2) + nc * (kt * mt)) = mt * (u2 * kt ^ 2 + v2 * (mt ^ 2 - kt ^ 2) + w2 * (kt * mt)) := by
    apply rel_nat t ht _ _ _ _ (by omega)
    rw [ea, ec, hX2', hY] at hX2
    linarith
  obtain ⟨-, -, -, hX1n⟩ := Erdos634.Draft.BeesonIso5a.base_arith kt mt hcop hlt hm2 na nb nc (by omega) hb1 hc1 _ _ rfl hrel1
  obtain ⟨-, -, -, hX2n⟩ := Erdos634.Draft.BeesonIso5a.base_arith kt mt hcop hlt hm2 na nb nc (by omega) hb1 hc1 _ _ rfl hrel2
  have hleg1 : dist (P.v (k + 1 + 1)) (P.v (k + 1 + 1 + 1)) = slen C 0 + slen C 2 := by
    rw [hX1', hX1n, ea, ec]; push_cast; ring
  have hleg2 : dist (P.v (k + 1 + 1 + 1)) (P.v (k + 1 + 1 + 1 + 1)) = slen C 0 + slen C 2 := by
    rw [hX2', hX2n, ea, ec]; push_cast; ring
  obtain ⟨a1, a2, rfl, hcase1, ha10, ha12, ha22, hsa1, hsa2, s1, hs10, hs11, hs1e⟩ :=
    leg_structure C P hreg idx hidx hidxA hβ hγ hα hPang hab hac hbc ht hcop hlt hm2 ea eb ec (k + 1 + 1) W1 hleg1
  obtain ⟨b1, b2, rfl, hcase2, hb10, hb12, hb22, hsb1, hsb2, s2, hs20, hs21, hs2e⟩ :=
    leg_structure C P hreg idx hidx hidxA hβ hγ hα hPang hab hac hbc ht hcop hlt hm2 ea eb ec (k + 1 + 1 + 1) W2 hleg2
  -- the first step of leg 1 starts at an alpha corner: not an a-edge
  have hne1 : dist a1.2.1 a1.2.2 ≠ slen C 0 := by
    obtain ⟨kk, f, g, hk, hf, -⟩ := id hsa1
    have hlab := corner_label0 C P hreg idx hidxA hβ hγ hα (k + 1) hi1 (by rw [← ha10]; exact hk)
    exact step_ne_a C idx hidx hab hac hsa1 ⟨kk, Or.inl hk, hlab⟩
  -- the last step of leg 2 ends at an alpha corner: not an a-edge
  have hne2 : dist b2.2.1 b2.2.2 ≠ slen C 0 := by
    obtain ⟨kk, f, g, hk, hf, -⟩ := id hsb2
    have hf' : (C.tile b2.1).pts f = P.v (k + 1) := by rw [hf, hb22, fin3_add4]
    have hlab := corner_label0 C P hreg idx hidxA hβ hγ hα k hi0 hf'
    exact step_ne_a C idx hidx hab hac hsb2 ⟨f, Or.inr hf, hlab⟩
  have hA2 : dist a2.2.1 a2.2.2 = slen C 0 := by
    rcases hcase1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact absurd h1 hne1
    · exact h2
  have hB1 : dist b1.2.1 b1.2.2 = slen C 0 := by
    rcases hcase2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact h1
    · exact absurd h2 hne2
  -- the two a-edge tiles at B
  have hZ : a2.2.1 ≠ b1.2.2 := by
    intro hh
    have h1 : P.c (k + 1 + 1) a2.2.1 = 0 := c_zero_open P (k + 1 + 1) hs1e
    have h2 := c_pos_prev P (k + 1 + 1 + 1) hs20 (hs2e : b2.2.1 = _)
    rw [add_sub_cancel_right] at h2
    have hh' : a2.2.1 = b2.2.1 := hh.trans hb12
    rw [hh'] at h1
    linarith
  have hS1 : TriStep (C.tile a2.1) (toV2 (P.e (k + 1 + 1))) a2.2.1 (P.v (k + 1 + 1 + 1)) := by rw [← ha22]; exact hsa2
  have hS2 : TriStep (C.tile b1.1) (toV2 (P.e (k + 1 + 1 + 1))) (P.v (k + 1 + 1 + 1)) b1.2.2 := by rw [← hb10]; exact hsb1
  have hd1 : dist a2.2.1 (P.v (k + 1 + 1 + 1)) = slen C 0 := by rw [← ha22]; exact hA2
  have hd2 : dist (P.v (k + 1 + 1 + 1)) b1.2.2 = slen C 0 := by rw [← hb10]; exact hB1
  exact two_a_steps_at_B C P hreg idx hidx hidxA hβ hγ hα (k + 1 + 1) hBang hab hac hS1 hS2 hZ hd1 hd2

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.four_base
