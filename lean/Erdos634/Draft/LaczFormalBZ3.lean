-- Draft/LaczFormalBZ3.lean -- Beeson-Zhang (arXiv 2604.01314v1) Lemma 3.2 and the centre case of Lemma 3.5, for dissections of a convex polygon by the tile (alpha, beta, 2 pi/3), alpha not in Q pi:
--   `bz_head_analysis`  : the head H of an edge of Gamma_a has corner angle sum pi, and if its corner counts are (1,1,1) ("simple vertex") an edge of Gamma_a starts at H  (Lemma 3.2);
--   `bz_center_out`     : at an interior vertex with corner counts (0,0,3) ("centre") an edge of Gamma_a starts (Lemma 3.5, first bullet: three corners, an odd number of a-edges, so some ray carries exactly one a).
-- Hypothesis `a` not a nonnegative rational combination of `b, c` (`NotComb`).  UNAUDITED.  Credit: Beeson-Zhang (Lemmas 3.2, 3.5), Laczkovich (DCG 48 (2012), Sect. 4, 7).
import Erdos634.Draft.LaczFormalBZ2

namespace Erdos634.Draft.LaczFormal.RegFan

/-- The centre: three corners all of type `gamma`; an edge of `Gamma_a` starts along one of the three rays (pure parity: each corner has exactly one `a`-arm). -/
def centerOK (l : List ℕ) : Bool := !(cnt l 2 == 3) || (List.range 3).any (fun i => gaEdge l i)

theorem center_check : (allFans 3).all centerOK = true := by decide +kernel

theorem center_edge (l : List ℕ) (hlen : l.length = 3) (hlt : ∀ x ∈ l, x < 6) (h : cnt l 2 = 3) :
    (List.range 3).any (fun i => gaEdge l i) = true := by
  have := (List.all_eq_true.mp center_check) l (mem_allFans 3 l hlen hlt)
  simpa [centerOK, h] using this

theorem center_witness : cnt [4, 4, 4] 2 = 3 ∧ gaEdge [4, 4, 4] 1 = true ∧ cnt [4, 5, 4] 2 = 3 ∧ (List.range 3).any (fun i => gaEdge [4, 5, 4] i) = true := by decide

end Erdos634.Draft.LaczFormal.RegFan

open scoped Classical
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ} [NeZero M]

/-- The tail of an edge of `Γ_k` has two `γ` corners. -/
theorem gk_two_gamma (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) {Z X : Plane}
    (h : GkEdge D.toRegionDissection idx Z X) : 2 ≤ cnt D idx Z 2 := by
  classical
  obtain ⟨i, j, k1, k2, k1', k2', hij, a1, a2, a3, a4, a5, a6, a7, a8⟩ := h
  unfold cnt
  have : ({(i, k1), (j, k1')} : Finset (Fin N × Fin 3)) ⊆ Finset.univ.filter (fun p : Fin N × Fin 3 => (D.tile p.1).pts p.2 = Z ∧ idx p.1 p.2 = 2) := by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl <;> simp [*]
  have h3 := Finset.card_le_card this
  rw [Finset.card_pair (fun e => hij (congrArg Prod.fst e))] at h3
  exact h3

/-- **The head of an edge of `Γ_a`** has corner angle sum `π`; if its counts are `(1,1,1)` an edge of `Γ_a` starts there (Beeson-Zhang Lemma 3.2). -/
theorem bz_head_analysis (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    (hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v)
    (hnc : NotComb (slen D 0) (slen D 1) (slen D 2)) (hab : slen D 0 ≠ slen D 1) (hac : slen D 0 ≠ slen D 2)
    {X H : Plane} (hE : GaEdge D.toRegionDissection (slen D 0) X H) :
    (∑ l, (cnt D idx H l : ℝ) * D.model.angleAt l = Real.pi) ∧
      (cnt D idx H 0 = 1 → cnt D idx H 1 = 1 → cnt D idx H 2 = 1 → ∃ H', GaEdge D.toRegionDissection (slen D 0) H H') := by
  classical
  obtain ⟨κ, _, ⟨F⟩⟩ := HasFansC.fans (D := D.toRegionDissection) H (ga_edge_vertex _ _ hE)
  obtain ⟨d, hd, nb, hc⟩ := ga_edge_data D idx hidx hnc hE F
  have key : ∀ {e : V2} {u v s : AtV D.toRegionDissection H}, HeadCfg D F e u v s →
      (∑ l, (cnt D idx H l : ℝ) * D.model.angleAt l = Real.pi) ∧
      (cnt D idx H 0 = 1 → cnt D idx H 1 = 1 → cnt D idx H 2 = 1 → ∃ H', GaEdge D.toRegionDissection (slen D 0) H H') := by
    intro e u v s hc
    have hc' := hc
    obtain ⟨hc1, hc2, hc3, hc4, hc5, hc6, hc7⟩ := hc'
    have hcyc := F.head_cyc u v s hc1 hc2 hc3 hc4 hc5 hc6
    have hemp : IsEmpty κ := hcyc.1
    obtain ⟨hS1, hsum, hcard⟩ := head_counts D idx hidxA F hemp hc6 hc1
    refine ⟨hsum, fun h0 h1 h2 => ?_⟩
    have hcard4 : Fintype.card (AtV D.toRegionDissection H) = 4 := by
      rw [hcard, Fin.sum_univ_three]; omega
    have hpair : ∀ (l : Fin 3) (t1 t2 : Fin N) (k1 k2 : Fin 3), t1 ≠ t2 → (D.tile t1).pts k1 = H → (D.tile t2).pts k2 = H →
        idx t1 k1 = l → idx t2 k2 = l → 2 ≤ cnt D idx H l := by
      intro l t1 t2 k1 k2 hne h1 h2 e1 e2
      unfold cnt
      have : ({(t1, k1), (t2, k2)} : Finset (Fin N × Fin 3)) ⊆ Finset.univ.filter (fun p : Fin N × Fin 3 => (D.tile p.1).pts p.2 = H ∧ idx p.1 p.2 = l) := by
        intro p hp
        simp only [Finset.mem_insert, Finset.mem_singleton] at hp
        rcases hp with rfl | rfl <;> simp [*]
      have h3 := Finset.card_le_card this
      rw [Finset.card_pair (fun e => hne (congrArg Prod.fst e))] at h3
      exact h3
    refine (head_out_edge D idx hidx hnc hab hac F hc hcard4 (Or.inl ?_)).resolve_right ?_
    · intro t1 t2 _ _ hne k1 k2 hk1 hk2 heq
      have hl : cnt D idx H (idx t1.1 k1) ≥ 2 := hpair (idx t1.1 k1) t1.1 t2.1 k1 k2 (fun e => hne (Subtype.ext e)) hk1 hk2 rfl heq.symm
      generalize idx t1.1 k1 = z at hl
      fin_cases z <;> simp_all <;> omega
    · rintro ⟨Z, hZ⟩
      have := gk_two_gamma D idx hZ
      omega
  rcases hc with ⟨P, W, hP, a, b, s, h1, h2, h3, h4, h5, h6, h7, h8⟩ | ⟨P, W, hP, a, b, s, h1, h2, h3, h4, h5, h6, h7, h8⟩
  · exact key (HeadCfg.of_left D F a b s h1 h2 h3 h4 h5 h6 h7 h8)
  · exact key (HeadCfg.of_right D F a b s h1 h2 h3 h4 h5 h6 h7 h8)

/-- **The centre** (Beeson-Zhang Lemma 3.5, first bullet): at an interior vertex whose corner counts are `(0,0,3)` an edge of `Γ_a` starts. -/
theorem bz_center_out (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    (hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v)
    (hnc : NotComb (slen D 0) (slen D 1) (slen D 2)) (hab : slen D 0 ≠ slen D 1) (hac : slen D 0 ≠ slen D 2)
    (hγ : D.model.angleAt 2 = 2 * Real.pi / 3) {X : Plane} (hvert : ∃ j k, (D.tile j).pts k = X) (hint : X ∈ interior D.region)
    (h0 : cnt D idx X 0 = 0) (h1 : cnt D idx X 1 = 0) (h2 : cnt D idx X 2 = 3) :
    ∃ H', GaEdge D.toRegionDissection (slen D 0) X H' := by
  classical
  have hpi := Real.pi_pos
  obtain ⟨F⟩ := extFan_interior D.toRegionDissection X hvert hint
  have hemp : IsEmpty Empty := inferInstance
  have hang := head_angle_sum D idx hidxA F hemp
  have hStr : (Strn D.toRegionDissection X).card = 0 := by
    by_contra hne
    have h1' : (1 : ℝ) ≤ (Strn D.toRegionDissection X).card := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hne
    rw [Fin.sum_univ_three, h0, h1, h2, hγ] at hang
    have : (0 : ℝ) ≤ ((0 : ℕ) : ℝ) * D.model.angleAt 0 + ((0 : ℕ) : ℝ) * D.model.angleAt 1 := by simp
    push_cast at hang
    nlinarith
  have hcor : ∀ x : AtV D.toRegionDissection X, 0 < crs (F.p x) (F.q x) := by
    intro x
    rcases F.hspec x with ⟨k, hk, -⟩ | ⟨hnv, -⟩
    · exact crs_pos_of_corner (F.hok x) (F.hspec x) ⟨k, hk⟩
    · exfalso
      have : x.1 ∈ Strn D.toRegionDissection X := by
        simp only [Strn, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨x.2, hnv⟩
      have := Finset.card_pos.mpr ⟨x.1, this⟩
      omega
  have hcard : Fintype.card (AtV D.toRegionDissection X) = 3 := by
    rw [card_atV, card_corn D idx X, hStr, Fin.sum_univ_three]
    omega
  set l := lst D idx F hcor hemp 0 with hl
  have hlen : l.length = 3 := by rw [hl, lst_length, hcard]
  have hlt := lst_lt D idx F hcor hemp 0
  have hc2 : RegFan.cnt l 2 = 3 := (lst_cnt D idx F hcor hemp 0 2).trans h2
  have hconcl := RegFan.center_edge l hlen hlt hc2
  rw [List.any_eq_true] at hconcl
  obtain ⟨i, hi3, hi⟩ := hconcl
  have hi' : i < Fintype.card (AtV D.toRegionDissection X) := by rw [hcard]; exact List.mem_range.mp hi3
  set x := tl F hemp (0 + (i + Fintype.card (AtV D.toRegionDissection X) - 1) % Fintype.card (AtV D.toRegionDissection X)) with hx
  set y := tl F hemp (0 + i) with hy
  have hxy : Par (F.p y) (F.q x) := by
    have h := tl_adj F hemp (0 + (i + Fintype.card (AtV D.toRegionDissection X) - 1) % Fintype.card (AtV D.toRegionDissection X))
    rw [tl_ray F hemp 0 i hi'] at h
    exact h
  have hLc : RegFan.Lc l i = cdcode D idx F hcor x := by
    unfold RegFan.Lc; rw [hlen]
    have hlt' : (i + 3 - 1) % 3 < Fintype.card (AtV D.toRegionDissection X) := by rw [hcard]; exact Nat.mod_lt _ (by norm_num)
    rw [hl, lst_getD D idx F hcor hemp 0 _ hlt', hx, hcard]
  have hRc : RegFan.Rc l i = cdcode D idx F hcor y := by
    unfold RegFan.Rc; rw [hlen]
    have hlt' : i % 3 < Fintype.card (AtV D.toRegionDissection X) := by rw [hcard]; exact Nat.mod_lt _ (by norm_num)
    rw [hl, lst_getD D idx F hcor hemp 0 _ hlt']
    have : i % 3 = i := Nat.mod_eq_of_lt (List.mem_range.mp hi3)
    rw [this]
  obtain ⟨hkx, hpx, hqx⟩ := cd_spec D F hcor x
  obtain ⟨hky, hpy, hqy⟩ := cd_spec D F hcor y
  -- no ray is opposite to another: the corner angles are all `2π/3`
  have htyp : ∀ z : AtV D.toRegionDissection X, idx z.1 (cd D F hcor z).1 = 2 := by
    intro z
    obtain ⟨hk, -, -⟩ := cd_spec D F hcor z
    have hge : ∀ l : Fin 3, idx z.1 (cd D F hcor z).1 = l → 1 ≤ cnt D idx X l := by
      intro l hl
      unfold cnt
      exact Finset.card_pos.mpr ⟨(z.1, (cd D F hcor z).1), by simp [hk, hl]⟩
    generalize hz : idx z.1 (cd D F hcor z).1 = w
    fin_cases w
    · have := hge 0 hz; omega
    · have := hge 1 hz; omega
    · rfl
  have hp : ∀ s' : AtV D.toRegionDissection X, ¬ Par (F.p s') (neg2 (F.q x)) := by
    intro s' hs
    obtain ⟨m', hm0, hm', hπ⟩ := opp_colG_aux D F hcor hemp 0 i hi' s' hs
    have hwd : ∀ t, wd (F.p (tl F hemp (0 + i + t))) (F.q (tl F hemp (0 + i + t))) = 2 * Real.pi / 3 := by
      intro t
      rw [wd_cd' D idx F hcor hidxA, htyp, hγ]
    rw [Finset.sum_congr rfl (fun t _ => hwd t), Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hπ
    have hm2 : m' = 1 ∨ m' = 2 := by omega
    rcases hm2 with rfl | rfl <;> (push_cast at hπ; linarith)
  have hnb : NoBack D.toRegionDissection (F.q x) X := by
    apply F.noBack_of_none
    intro s
    refine ⟨hp s, fun h => ?_⟩
    obtain ⟨j0, -, hj0⟩ := tl_surj F hemp s
    have h1 := tl_adj F hemp j0
    rw [hj0] at h1
    exact hp _ (h1.trans h)
  unfold RegFan.gaEdge at hi
  rw [hLc, hRc] at hi
  exact ga_of_codes D idx hidx hnc hab hac F x y (hcor x) (hcor y) hxy hnb hkx hky hqx hpy hi

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.bz_head_analysis
#print axioms Erdos634.Draft.LaczFormal.RG.bz_center_out
