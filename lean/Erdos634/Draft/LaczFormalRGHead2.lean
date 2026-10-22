-- Draft/LaczFormalRGHead2.lean -- S4 of PLAN_THM21: the HEAD wrapper of `half_fan_edge`: if `X -> H` is an edge of `Gamma_a` and the number of tile corners at `H` of type
-- `beta` or `gamma` is even (`cnt 1 + cnt 2`), then an edge of `Gamma_a` starts at `H` (Laczkovich Lemma 4.2 / Lemma 9.1 (i), exceptional vertices included).
-- UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Lemma 4.2, Lemma 9.1 (i), Lemma 4.5), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalRGHalf
import Erdos634.Draft.LaczFormalBase

open scoped Classical
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph

namespace Erdos634.Draft.LaczFormal.RG

variable {N : ℕ}

/-- `cnt 1 + cnt 2` = number of corner pairs `(tile, vertex)` at `H` with a non-`α` type. -/
theorem cnt_nonzero (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) (H : Plane) :
    cnt D idx H 1 + cnt D idx H 2 =
      (Finset.univ.filter (fun p : Fin N × Fin 3 => (D.tile p.1).pts p.2 = H ∧ idx p.1 p.2 ≠ 0)).card := by
  unfold cnt
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    ext p
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact ⟨h1, by rw [h2]; decide⟩
      · exact ⟨h1, by rw [h2]; decide⟩
    · rintro ⟨h1, h2⟩
      have : idx p.1 p.2 = 1 ∨ idx p.1 p.2 = 2 := by
        generalize idx p.1 p.2 = z at h2
        fin_cases z <;> simp_all
      rcases this with h | h
      · exact Or.inl ⟨h1, h⟩
      · exact Or.inr ⟨h1, h⟩
  · rw [Finset.disjoint_left]
    intro p hp1 hp2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp1 hp2
    rw [hp1.2] at hp2
    exact absurd hp2.2 (by decide)

/-- Tile-count form of the number of non-`α` corners at a head. -/
theorem head_tile_count (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) {H : Plane} {κ : Type} [Fintype κ]
    (F : ExtFan D.toRegionDissection H κ) {s : AtV D.toRegionDissection H}
    (hs : F.q s = (-(F.p s).1, -(F.p s).2)) {a : AtV D.toRegionDissection H} (ha : 0 < crs (F.p a) (F.q a)) :
    (Finset.univ.filter (fun x : AtV D.toRegionDissection H => x ≠ s ∧ ∃ k : Fin 3, (D.tile x.1).pts k = H ∧ idx x.1 k ≠ 0)).card =
      cnt D idx H 1 + cnt D idx H 2 := by
  classical
  rw [cnt_nonzero]
  have hF : ∀ (t : AtV D.toRegionDissection H) (k : Fin 3), (D.tile t.1).pts k = H → t ≠ s := by
    rintro t k hk rfl
    rcases F.hspec t with ⟨k', hk', -⟩ | ⟨hnv, -⟩
    · have hcr := crs_pos_of_corner (F.hok t) (F.hspec t) ⟨k', hk'⟩
      rw [hs] at hcr; unfold crs at hcr; simp at hcr; linarith
    · exact hnv k hk
  refine Finset.card_nbij' (fun x => (x.1, if h : ∃ k, (D.tile x.1).pts k = H ∧ idx x.1 k ≠ 0 then h.choose else 0))
    (fun p => if h : (D.tile p.1).pts p.2 = H then (⟨p.1, h ▸ subset_convexHull ℝ _ ⟨p.2, rfl⟩⟩ : AtV D.toRegionDissection H)
      else s) ?_ ?_ ?_ ?_
  · intro x hx
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hx
    obtain ⟨-, hex⟩ := hx
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq, dif_pos hex]
    exact hex.choose_spec
  · intro p hp
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hp
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq, dif_pos hp.1]
    refine ⟨hF _ p.2 hp.1, p.2, hp.1, hp.2⟩
  · intro x hx
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hx
    obtain ⟨-, hex⟩ := hx
    beta_reduce
    split_ifs with h1
    · rfl
    · exact absurd (by simpa [dif_pos hex] using hex.choose_spec.1) h1
  · intro p hp
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hp
    obtain ⟨h1, h2⟩ := hp
    simp only [dif_pos h1]
    have hex : ∃ k, (D.tile p.1).pts k = H ∧ idx p.1 k ≠ 0 := ⟨p.2, h1, h2⟩
    simp only [dif_pos hex]
    have : hex.choose = p.2 := by
      have := hex.choose_spec
      exact (D.tile p.1).indep.injective (this.1.trans h1.symm)
    rw [this]

/-- **Head wrapper of the half-fan lemma.**  At a head configuration (`HeadCfg`: corner tiles `u` (end along `-e`), `v` (start along `e`), straight tile `s`),
an edge of `Γ_a` starts at `H` as soon as the number of non-`α` corners at `H` (`cnt 1 + cnt 2`) is even. -/
theorem head_cfg_edge (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    (hnc : NotComb (slen D 0) (slen D 1) (slen D 2)) (hab : slen D 0 ≠ slen D 1) (hac : slen D 0 ≠ slen D 2)
    {H : Plane} {κ : Type} [Fintype κ] (F : ExtFan D.toRegionDissection H κ) {e : V2}
    {u v s : AtV D.toRegionDissection H} (hc : HeadCfg D F e u v s)
    (hev : (cnt D idx H 1 + cnt D idx H 2) % 2 = 0) :
    ∃ H', GaEdge D.toRegionDissection (slen D 0) H H' := by
  classical
  obtain ⟨hc1, hc2, hc3, hc4, hc5, hc6, hc7⟩ := hc
  obtain ⟨hemp, hint, hus, hvs, huv, j0, hj0, hes, hev1, heu⟩ := F.head_cyc u v s hc1 hc2 hc3 hc4 hc5 hc6
  have hκ : Fintype.card κ = 0 := Fintype.card_eq_zero_iff.mpr hemp
  have hLcard : Fintype.card (AtV D.toRegionDissection H ⊕ κ) = Fintype.card (AtV D.toRegionDissection H) := by
    rw [Fintype.card_sum, hκ]; simp
  have hL3 : 3 ≤ Fintype.card (AtV D.toRegionDissection H ⊕ κ) := by
    rw [hLcard]
    have hsub : ({u, v, s} : Finset (AtV D.toRegionDissection H)) ⊆ Finset.univ := Finset.subset_univ _
    have h3 : ({u, v, s} : Finset (AtV D.toRegionDissection H)).card = 3 := by
      rw [Finset.card_insert_of_notMem (by simp [huv, hus]), Finset.card_pair hvs]
    have := Finset.card_le_card hsub
    rw [h3] at this
    simpa using this
  refine half_fan_edge D idx hidx hnc hab hac F j0 ?_ hL3 ?_ ?_ ?_
  · rw [hes]; exact hc6
  · intro m hm1 hm2
    have : ∃ x : AtV D.toRegionDissection H, F.e (j0 + m) = Sum.inl x := by
      rcases hx : F.e (j0 + m) with x | j
      · exact ⟨x, rfl⟩
      · exact (hemp.false j).elim
    obtain ⟨x, hx⟩ := this
    refine ⟨x, hx, ?_⟩
    have hxs : x ≠ s := by
      intro h
      subst h
      have h' : F.e (j0 + m) = F.e (j0 + 0) := by rw [hx]; exact hes.symm
      have := e_inj_shift F j0 hm2 (by omega) h'
      omega
    rcases F.hspec x with ⟨k, hk, -⟩ | ⟨-, m', -, -, hq, -⟩
    · exact crs_pos_of_corner (F.hok x) (F.hspec x) ⟨k, hk⟩
    · exact absurd (straight_unique F hq hc6 hc1) hxs
  · intro b a hb ha
    have hb' : b = v := by rw [hev1] at hb; exact (Sum.inl_injective hb).symm
    have ha' : a = u := by rw [heu] at ha; exact (Sum.inl_injective ha).symm
    subst hb'; subst ha'
    rcases hc7 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · intro h; exact h2 (h.mpr h1)
    · intro h; exact h1 (h.mp h2)
  · rw [hes]
    have hx := head_tile_count D idx F hc6 hc1
    simp only [ne_eq, Sum.inl.injEq]
    rw [hx]; exact hev

/-- **Parity hypothesis**: at every vertex whose corner angles add up to `π` (heads, interior points of edges) the number of non-`α` corners is even. -/
def HalfPar (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) : Prop :=
  ∀ X : Plane, ∑ l, (cnt D idx X l : ℝ) * D.model.angleAt l = Real.pi → (cnt D idx X 1 + cnt D idx X 2) % 2 = 0

/-- `γ = π/2` and regular corner counts give the parity hypothesis (`c(α+β) + rγ = π` forces `c + r = 2`). -/
theorem halfPar_of_pi2 (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3))
    (hγ : D.model.angleAt 2 = Real.pi / 2) (hregc : ∀ X, cnt D idx X 0 = cnt D idx X 1) : HalfPar D idx := by
  intro X hX
  rw [Fin.sum_univ_three] at hX
  have hang := Erdos634.Draft.LaczFormal.angleAt_sum D.model
  have hαβ : D.model.angleAt 0 + D.model.angleAt 1 = Real.pi / 2 := by linarith
  have hr : ((cnt D idx X 0 : ℕ) : ℝ) = (cnt D idx X 1 : ℕ) := by exact_mod_cast hregc X
  rw [hγ, hr] at hX
  have h2 : ((cnt D idx X 1 : ℕ) : ℝ) + (cnt D idx X 2 : ℕ) = 2 := by
    have hp := Real.pi_pos
    nlinarith [hX, hαβ]
  have h3 : cnt D idx X 1 + cnt D idx X 2 = 2 := by exact_mod_cast h2
  rw [h3]

/-- **Lemma 9.1 (i), head part**, with the parity hypothesis. -/
theorem ga_head_out_half (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    (hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v)
    (hnc : NotComb (slen D 0) (slen D 1) (slen D 2)) (hab : slen D 0 ≠ slen D 1) (hac : slen D 0 ≠ slen D 2)
    (hhp : HalfPar D idx) {X H : Plane} (hE : GaEdge D.toRegionDissection (slen D 0) X H) :
    ∃ H', GaEdge D.toRegionDissection (slen D 0) H H' := by
  classical
  obtain ⟨κ, _, ⟨F⟩⟩ := HasFansC.fans (D := D.toRegionDissection) H (ga_edge_vertex _ _ hE)
  obtain ⟨d, hd, nb, hc⟩ := ga_edge_data D idx hidx hnc hE F
  have key : ∀ {e : V2} {u v s : AtV D.toRegionDissection H}, HeadCfg D F e u v s → ∃ H', GaEdge D.toRegionDissection (slen D 0) H H' := by
    intro e u v s hc
    have hc' := hc
    obtain ⟨hc1, hc2, hc3, hc4, hc5, hc6, hc7⟩ := hc'
    have hcyc := F.head_cyc u v s hc1 hc2 hc3 hc4 hc5 hc6
    obtain ⟨hS1, hsum, hcard⟩ := head_counts D idx hidxA F hcyc.1 hc6 hc1
    exact head_cfg_edge D idx hidx hnc hab hac F hc (hhp H hsum)
  rcases hc with ⟨P, W, hP, a, b, s, h1, h2, h3, h4, h5, h6, h7, h8⟩ | ⟨P, W, hP, a, b, s, h1, h2, h3, h4, h5, h6, h7, h8⟩
  · exact key (HeadCfg.of_left D F a b s h1 h2 h3 h4 h5 h6 h7 h8)
  · exact key (HeadCfg.of_right D F a b s h1 h2 h3 h4 h5 h6 h7 h8)

end Erdos634.Draft.LaczFormal.RG
