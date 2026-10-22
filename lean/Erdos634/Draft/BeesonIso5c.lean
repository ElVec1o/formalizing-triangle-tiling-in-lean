import Erdos634.Draft.BeesonIso5b
import Erdos634.Draft.BeesonIso2b

/-!
# Beeson, "Tilings of an isosceles triangle" (arXiv 1206.1974 v7), Lemma 11.10, "at least four": edge counts along a side

NOTE, UNAUDITED.  Credit: Michael Beeson (arXiv 1206.1974 v7, Lemma 11.10, 11.13), Laczkovich (DCG 48 (2012)), Beeson-Zhang, Herdt, Zhang.
Formalization debt, not progress on the /goal outcomes.

* `side_len_counts`: along any side, the length is `na a + nb b + nc c` (`na + nb + nc` = number of steps) and `nc >= 1` (a c-edge exists: `side_has_c_step`).
* `side_len_counts_b`: along a side with two `alpha` corners also `nb >= 1` (`side_has_b_step`).
* `leg_pair`: a list of lengths in `{a,b,c}` (tile `t (k^2, m^2-k^2, km)`) with sum `a + c` and an entry `c` is `[a, c]` or `[c, a]`.
-/

open scoped Classical
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ} [NeZero M]

theorem side_len_counts (C : CongruentRegionDissection N) [HasFansC C.toRegionDissection] (P : ConvPoly M) (hreg : C.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((C.tile i).pts k) ((C.tile i).pts k') = dist (C.model.pts (idx i k)) (C.model.pts (idx i k')))
    (hidxA : ∀ i v, C.model.angleAt (idx i v) = (C.tile i).angleAt v)
    (hβ : C.model.angleAt 1 = Real.pi - 3 * C.model.angleAt 0) (hγ : C.model.angleAt 2 = 2 * C.model.angleAt 0)
    (hα : ¬ ∃ r : ℚ, C.model.angleAt 0 = (r : ℝ) * Real.pi)
    (hPang : ∀ k : Fin M, P.angle (k + 1) = C.model.angleAt 0 ∨ P.angle (k + 1) = Real.pi - 2 * C.model.angleAt 0)
    (hab : slen C 0 ≠ slen C 1) (hac : slen C 0 ≠ slen C 2) (hbc : slen C 1 ≠ slen C 2)
    (i : Fin M) {L : List (Fin N × Plane × Plane)} (W : WalkT C.toRegionDissection (toV2 (P.e i)) (P.v i) (P.v (i + 1)) L) :
    ∃ na nb nc : ℕ, na + nb + nc = L.length ∧
      dist (P.v i) (P.v (i + 1)) = na * slen C 0 + nb * slen C 1 + nc * slen C 2 ∧ 1 ≤ nc := by
  have hmem : ∀ x ∈ L.map (fun e => dist e.2.1 e.2.2), x = slen C 0 ∨ x = slen C 1 ∨ x = slen C 2 := by
    intro x hx
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
    exact side_len_mem C idx hidx (walkT_mem_step W e he)
  obtain ⟨na, nb, nc, hl, hs, -, hc⟩ := Erdos634.Draft.BeesonIso5a.sum_abc_cnt (slen C 0) (slen C 1) (slen C 2) hab hac hbc _ hmem
  refine ⟨na, nb, nc, by rw [hl, List.length_map], by rw [← hs, walkT_dist_sum W], hc ?_⟩
  obtain ⟨e, he, hno⟩ := side_has_c_step C P hreg idx hidxA hβ hγ hα hPang i W
  exact ⟨dist e.2.1 e.2.2, List.mem_map.mpr ⟨e, he, rfl⟩, cstep_dist C idx hidx (walkT_mem_step W e he) hno⟩

theorem side_len_counts_b (C : CongruentRegionDissection N) [HasFansC C.toRegionDissection] (P : ConvPoly M) (hreg : C.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((C.tile i).pts k) ((C.tile i).pts k') = dist (C.model.pts (idx i k)) (C.model.pts (idx i k')))
    (hidxA : ∀ i v, C.model.angleAt (idx i v) = (C.tile i).angleAt v)
    (hβ : C.model.angleAt 1 = Real.pi - 3 * C.model.angleAt 0) (hγ : C.model.angleAt 2 = 2 * C.model.angleAt 0)
    (hα : ¬ ∃ r : ℚ, C.model.angleAt 0 = (r : ℝ) * Real.pi)
    (hPang : ∀ k : Fin M, P.angle (k + 1) = C.model.angleAt 0 ∨ P.angle (k + 1) = Real.pi - 2 * C.model.angleAt 0)
    (hab : slen C 0 ≠ slen C 1) (hac : slen C 0 ≠ slen C 2) (hbc : slen C 1 ≠ slen C 2)
    (i : Fin M) (hi0 : P.angle i = C.model.angleAt 0) (hi1 : P.angle (i + 1) = C.model.angleAt 0)
    {L : List (Fin N × Plane × Plane)} (W : WalkT C.toRegionDissection (toV2 (P.e i)) (P.v i) (P.v (i + 1)) L) :
    ∃ na nb nc : ℕ, na + nb + nc = L.length ∧
      dist (P.v i) (P.v (i + 1)) = na * slen C 0 + nb * slen C 1 + nc * slen C 2 ∧ 1 ≤ nb ∧ 1 ≤ nc := by
  have hmem : ∀ x ∈ L.map (fun e => dist e.2.1 e.2.2), x = slen C 0 ∨ x = slen C 1 ∨ x = slen C 2 := by
    intro x hx
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
    exact side_len_mem C idx hidx (walkT_mem_step W e he)
  obtain ⟨na, nb, nc, hl, hs, hb, hc⟩ := Erdos634.Draft.BeesonIso5a.sum_abc_cnt (slen C 0) (slen C 1) (slen C 2) hab hac hbc _ hmem
  refine ⟨na, nb, nc, by rw [hl, List.length_map], by rw [← hs, walkT_dist_sum W], hb ?_, hc ?_⟩
  · obtain ⟨e, he, hno⟩ := side_has_b_step C P hreg idx hidxA hβ hγ hα hPang i hi0 hi1 W
    exact ⟨dist e.2.1 e.2.2, List.mem_map.mpr ⟨e, he, rfl⟩, bstep_dist C idx hidx (walkT_mem_step W e he) hno⟩
  · obtain ⟨e, he, hno⟩ := side_has_c_step C P hreg idx hidxA hβ hγ hα hPang i W
    exact ⟨dist e.2.1 e.2.2, List.mem_map.mpr ⟨e, he, rfl⟩, cstep_dist C idx hidx (walkT_mem_step W e he) hno⟩

/-- A list of tile edges with sum `a + c` and an entry `c` is `[a, c]` or `[c, a]` (tile `t (k^2, m^2-k^2, km)`). -/
theorem leg_pair {a b c t : ℝ} (ht : 0 < t) {k m : ℕ} (hcop : Nat.Coprime k m) (hlt : k < m) (hm2 : m < 2 * k)
    (ha : a = t * (k : ℝ) ^ 2) (hb : b = t * ((m : ℝ) ^ 2 - (k : ℝ) ^ 2)) (hc : c = t * ((k : ℝ) * m))
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (ds : List ℝ) (hds : ∀ x ∈ ds, x = a ∨ x = b ∨ x = c)
    (hsum : ds.sum = a + c) (hcx : ∃ x ∈ ds, x = c) :
    ∃ x y : ℝ, ds = [x, y] ∧ ((x = a ∧ y = c) ∨ (x = c ∧ y = a)) := by
  obtain ⟨u, v, w, hl, hs, -, hwc⟩ := Erdos634.Draft.BeesonIso5a.sum_abc_cnt a b c hab hac hbc ds hds
  have hw : 1 ≤ w := hwc hcx
  have hmk : k ^ 2 < m ^ 2 := by nlinarith
  have hcast : ((m ^ 2 - k ^ 2 : ℕ) : ℝ) = (m : ℝ) ^ 2 - (k : ℝ) ^ 2 := by
    rw [Nat.cast_sub hmk.le]; push_cast; ring
  have heq : u * k ^ 2 + v * (m ^ 2 - k ^ 2) + w * (k * m) = k * (m + k) := by
    have h1 : t * ((u : ℝ) * (k : ℝ) ^ 2 + v * ((m : ℝ) ^ 2 - (k : ℝ) ^ 2) + w * ((k : ℝ) * m)) = t * ((k : ℝ) * ((m : ℝ) + k)) := by
      have := hs.symm.trans hsum
      rw [ha, hb, hc] at this
      linarith
    have h2 := mul_left_cancel₀ ht.ne' h1
    have h3 : ((u * k ^ 2 + v * (m ^ 2 - k ^ 2) + w * (k * m) : ℕ) : ℝ) = ((k * (m + k) : ℕ) : ℝ) := by
      push_cast
      rw [Nat.cast_sub hmk.le]; push_cast
      linarith
    exact_mod_cast h3
  obtain ⟨hu, hv, hw1⟩ := Erdos634.Draft.BeesonIso5a.leg_arith k m hcop hlt hm2 u v w heq hw
  have hlen : ds.length = 2 := by omega
  obtain ⟨x, y, rfl⟩ := List.length_eq_two.mp hlen
  have hx := hds x (by simp)
  have hy := hds y (by simp)
  have hxy : x + y = a + c := by simpa using hsum
  obtain ⟨z, hz, hzc⟩ := hcx
  refine ⟨x, y, rfl, ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hx with hx | hx | hx <;> rcases hy with hy | hy | hy
  · exfalso; apply hac; linarith
  · exfalso; apply hbc; linarith
  · left; exact ⟨hx, hy⟩
  · exfalso; apply hbc; linarith
  · exfalso; rcases hz with h | h <;> exact hbc (by linarith)
  · exfalso; apply hab; linarith
  · right; exact ⟨hx, hy⟩
  · exfalso; apply hab; linarith
  · exfalso; apply hac; linarith

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.side_len_counts_b
#print axioms Erdos634.Draft.LaczFormal.RG.leg_pair
