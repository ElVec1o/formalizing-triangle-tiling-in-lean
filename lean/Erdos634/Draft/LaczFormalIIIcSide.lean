-- Draft/LaczFormalIIIcSide.lean -- Laczkovich DCG 48 (2012), Sect. 7.3 (IIIc), item (d2), part 1: the tile edges lying on the sides of A are ALL of length c or NONE is
-- (global over all sides), in the form needed for the flux count:
--   `iiic_sideEdges_all_or_none`: for a regular PolyTiling with a, b commensurable and c not commensurable with a, either every tile edge on every side of A has length c,
--   or no tile edge on any side has length c.  (Lemma 4.7 `polygon_sides_alike` + `side_len_sum` + a commensurability argument; no walk, no new geometry.)
-- Also: `iiic_edge_len_mem` (every tile edge of a placement of the tile has length a, b or c) and the small Comm calculus.
-- NOTE, UNAUDITED.  Non-vacuity: NAMED only (same hypotheses as `iiic_interior_pairs_cancel`; vTiling satisfies the Comm/RegularPQ part but not hα).
-- Credit: Laczkovich (DCG 48 (2012), Sect. 7.3, Lemmas 4.5-4.7), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIIcPair
import Erdos634.Draft.LaczFormalRG5GammaC
import Erdos634.Draft.LaczFormalFluxPolyFin

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement Erdos634.Draft.LaczFormal.RG

namespace Erdos634.Draft.LaczFormal.IIIc

theorem iiic_comm_add {x y a : ℝ} (hx : Comm x a) (hy : Comm y a) : Comm (x + y) a := by
  obtain ⟨p, q, hp, hq, h1⟩ := hx
  obtain ⟨p', q', hp', hq', h2⟩ := hy
  refine ⟨p * p', q * p' + q' * p, Nat.mul_pos hp hp', Nat.add_pos_left (Nat.mul_pos hq hp') _, ?_⟩
  push_cast
  linear_combination (p' : ℝ) * h1 + (p : ℝ) * h2

theorem iiic_comm_sub {x y a : ℝ} (ha : 0 < a) (hx : Comm x a) (hy : Comm y a) (hpos : 0 < x - y) : Comm (x - y) a := by
  obtain ⟨p, q, hp, hq, h1⟩ := hx
  obtain ⟨p', q', hp', hq', h2⟩ := hy
  have hlt : q' * p < q * p' := by
    by_contra hcon
    push Not at hcon
    have h3 : ((q * p' : ℕ) : ℝ) ≤ ((q' * p : ℕ) : ℝ) := by exact_mod_cast hcon
    push_cast at h3
    have hpp : (0 : ℝ) < p * p' := by positivity
    have h4 : (p : ℝ) * p' * (x - y) = ((q : ℝ) * p' - q' * p) * a := by linear_combination (p' : ℝ) * h1 - (p : ℝ) * h2
    have h5 : 0 < (p : ℝ) * p' * (x - y) := mul_pos hpp hpos
    rw [h4] at h5
    nlinarith
  refine ⟨p * p', q * p' - q' * p, Nat.mul_pos hp hp', Nat.sub_pos_of_lt hlt, ?_⟩
  rw [Nat.cast_sub hlt.le]
  push_cast
  linear_combination (p' : ℝ) * h1 - (p : ℝ) * h2

theorem iiic_comm_nsmul {c a : ℝ} (n : ℕ) (hn : 0 < n) (h : Comm ((n : ℝ) * c) a) : Comm c a := by
  obtain ⟨p, q, hp, hq, h1⟩ := h
  refine ⟨p * n, q, Nat.mul_pos hp hn, hq, ?_⟩
  push_cast
  linear_combination h1

/-- Decomposition of a sum of lengths each equal to `a`, `b` or `c`. -/
theorem iiic_sum_decomp {ι : Type*} (s : Finset ι) (len : ι → ℝ) {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : Comm a b)
    (hlen : ∀ e ∈ s, len e = a ∨ len e = b ∨ len e = c) :
    ∃ (nc : ℕ) (S : ℝ), ∑ e ∈ s, len e = nc * c + S ∧ (S = 0 ∨ (0 < S ∧ Comm S a)) ∧ ((∃ e ∈ s, len e = c) → 0 < nc) ∧
      ((∃ e ∈ s, len e ≠ c) → 0 < S ∧ Comm S a) := by
  classical
  have hba : Comm b a := by obtain ⟨p, q, hp, hq, h⟩ := hab; exact ⟨q, p, hq, hp, h.symm⟩
  have key : ∀ t : Finset ι, (∀ e ∈ t, len e = a ∨ len e = b) → (∑ e ∈ t, len e = 0 ∨ (0 < ∑ e ∈ t, len e ∧ Comm (∑ e ∈ t, len e) a)) := by
    intro t
    induction t using Finset.induction_on with
    | empty => intro _; left; simp
    | insert e t he ih =>
      intro h
      have hih := ih (fun x hx => h x (Finset.mem_insert_of_mem hx))
      rw [Finset.sum_insert he]
      have hle : len e = a ∨ len e = b := h e (Finset.mem_insert_self _ _)
      have hcomm : Comm (len e) a := by
        rcases hle with h' | h'
        · rw [h']; exact ⟨1, 1, one_pos, one_pos, by simp⟩
        · rw [h']; exact hba
      have hpos : 0 < len e := by rcases hle with h' | h' <;> rw [h'] <;> assumption
      right
      rcases hih with h0 | ⟨h0, h1⟩
      · rw [h0, add_zero]; exact ⟨hpos, hcomm⟩
      · exact ⟨by linarith, iiic_comm_add hcomm h1⟩
  set tc := s.filter (fun e => len e = c) with htc
  set tn := s.filter (fun e => ¬ len e = c) with htn
  have hnc : ∀ e ∈ tn, len e = a ∨ len e = b := by
    intro e he
    obtain ⟨hes, hne⟩ := Finset.mem_filter.mp he
    rcases hlen e hes with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd h hne
  have hsc : ∑ e ∈ tc, len e = tc.card * c := by
    rw [Finset.sum_congr rfl (fun e he => (Finset.mem_filter.mp he).2), Finset.sum_const, nsmul_eq_mul]
  have hsum : ∑ e ∈ s, len e = tc.card * c + ∑ e ∈ tn, len e := by
    rw [← Finset.sum_filter_add_sum_filter_not s (fun e => len e = c), hsc]
  refine ⟨tc.card, ∑ e ∈ tn, len e, hsum, key tn hnc, ?_, ?_⟩
  · rintro ⟨e, he, hec⟩
    exact Finset.card_pos.mpr ⟨e, Finset.mem_filter.mpr ⟨he, hec⟩⟩
  · rintro ⟨e, he, hec⟩
    have hmem : e ∈ tn := Finset.mem_filter.mpr ⟨he, hec⟩
    have hle : len e ≤ ∑ x ∈ tn, len x := by
      apply Finset.single_le_sum (f := len) (fun x hx => ?_) hmem
      rcases hnc x hx with h | h <;> rw [h] <;> linarith
    have hpos : 0 < len e := by rcases hnc e hmem with h | h <;> rw [h] <;> assumption
    rcases key tn hnc with h0 | h1
    · linarith
    · exact h1

/-- Every tile edge of a placement of the tile has length `a`, `b` or `c`. -/
theorem iiic_edge_len_mem {T : Tri} {α a b c : ℝ} (h : T.TwoPiThreeData α a b c) (k : Fin 3) :
    dist (T.pts k) (T.pts (k + 1)) = a ∨ dist (T.pts k) (T.pts (k + 1)) = b ∨ dist (T.pts k) (T.pts (k + 1)) = c := by
  have e : T.oppLen (k + 2) = dist (T.pts k) (T.pts (k + 1)) := by
    unfold Tri.oppLen
    have e1 : k + 2 + 1 = k := by fin_cases k <;> rfl
    have e2 : k + 2 + 2 = k + 1 := by fin_cases k <;> rfl
    rw [e1, e2]
  rw [← e]
  rcases h.cases (k + 2) with ⟨-, h1⟩ | ⟨-, h2⟩ | ⟨-, h3⟩
  · exact Or.inr (Or.inr h1)
  · exact Or.inl h2
  · exact Or.inr (Or.inl h3)

/-- **(d2) all-or-none on the boundary.**  Either every tile edge on every side of `A` has length `c`, or none has. -/
theorem iiic_sideEdges_all_or_none {N M : ℕ} [NeZero M] (T : PolyTiling N M) (hreg : RegularPQ T.C) {α : ℝ}
    (hmodel : T.C.model.TwoPiThreeData α (slen T.C 0) (slen T.C 1) (slen T.C 2))
    (hab : Comm (slen T.C 0) (slen T.C 1)) (hac : ¬ Comm (slen T.C 0) (slen T.C 2)) :
    (∀ j, ∀ e ∈ T.P.sideEdges T.C.toRegionDissection j, T.C.toRegionDissection.eLen e = slen T.C 2) ∨
    (∀ j, ∀ e ∈ T.P.sideEdges T.C.toRegionDissection j, T.C.toRegionDissection.eLen e ≠ slen T.C 2) := by
  classical
  obtain ⟨idx, hA, hcnt⟩ := hreg
  haveI : HasFansC T.C.toRegionDissection := hasFansC_poly _ T.P T.region_eq
  have hC : CaseC T.C idx := ⟨RG.idx_dist_of_angle T.C idx hA, hA, fun X => hcnt X, RG.notComb_c_of_comm (RG.slen_pos T.C 2) hab hac⟩
  have hT : ∀ i, (T.C.tile i).TwoPiThreeData α (slen T.C 0) (slen T.C 1) (slen T.C 2) :=
    fun i => Tri.TwoPiThreeData.of_congruent (T.C.tiles_congruent i) hmodel
  have ha := RG.slen_pos T.C 0
  have hb := RG.slen_pos T.C 1
  have hc := RG.slen_pos T.C 2
  have hdec : ∀ j, ∃ (nc : ℕ) (S : ℝ), T.P.side j = nc * slen T.C 2 + S ∧ (S = 0 ∨ (0 < S ∧ Comm S (slen T.C 0))) ∧
      ((∃ e ∈ T.P.sideEdges T.C.toRegionDissection j, T.C.toRegionDissection.eLen e = slen T.C 2) → 0 < nc) ∧
      ((∃ e ∈ T.P.sideEdges T.C.toRegionDissection j, T.C.toRegionDissection.eLen e ≠ slen T.C 2) → 0 < S ∧ Comm S (slen T.C 0)) := by
    intro j
    obtain ⟨nc, S, h1, h2, h3, h4⟩ := iiic_sum_decomp (T.P.sideEdges T.C.toRegionDissection j) T.C.toRegionDissection.eLen ha hb hab
      (fun e _ => iiic_edge_len_mem (hT e.1) e.2)
    exact ⟨nc, S, by rw [← T.P.side_len_sum T.C.toRegionDissection T.region_eq j]; exact h1, h2, h3, h4⟩
  rcases polygon_sides_alike T.C idx hC T.P T.region_eq with hA' | hB'
  · left
    intro j e he
    by_contra hne
    obtain ⟨m, hm, hside⟩ := hA' j
    obtain ⟨nc, S, h1, h2, h3, h4⟩ := hdec j
    obtain ⟨hSpos, hSc⟩ := h4 ⟨e, he, hne⟩
    rw [hside] at h1
    have hmn : nc < m := by
      by_contra hcon
      push Not at hcon
      have : (m : ℝ) ≤ nc := by exact_mod_cast hcon
      nlinarith
    apply hac
    have hS : S = ((m - nc : ℕ) : ℝ) * slen T.C 2 := by
      rw [Nat.cast_sub hmn.le]; linarith
    rw [hS] at hSc
    have := iiic_comm_nsmul (m - nc) (Nat.sub_pos_of_lt hmn) (a := slen T.C 0) hSc
    obtain ⟨p, q, hp, hq, h⟩ := this
    exact ⟨q, p, hq, hp, h.symm⟩
  · right
    intro j e he hec
    obtain ⟨na, nb, hpos, hside⟩ := hB' j
    obtain ⟨nc, S, h1, h2, h3, h4⟩ := hdec j
    have hncpos := h3 ⟨e, he, hec⟩
    have hZc : Comm (T.P.side j) (slen T.C 0) := by rw [hside]; exact comm_comb hab na nb hpos
    have hnc : (0 : ℝ) < nc := by exact_mod_cast hncpos
    have hxy : T.P.side j - S = nc * slen T.C 2 := by linarith
    have hpos' : 0 < T.P.side j - S := by rw [hxy]; positivity
    have hcomm : Comm ((nc : ℝ) * slen T.C 2) (slen T.C 0) := by
      rw [← hxy]
      rcases h2 with h0 | ⟨_, hSc⟩
      · rw [h0, sub_zero]; exact hZc
      · exact iiic_comm_sub ha hZc hSc hpos'
    have := iiic_comm_nsmul nc hncpos hcomm
    obtain ⟨p, q, hp, hq, h⟩ := this
    exact hac ⟨q, p, hq, hp, h.symm⟩

end Erdos634.Draft.LaczFormal.IIIc

#print axioms Erdos634.Draft.LaczFormal.IIIc.iiic_sum_decomp
#print axioms Erdos634.Draft.LaczFormal.IIIc.iiic_sideEdges_all_or_none
