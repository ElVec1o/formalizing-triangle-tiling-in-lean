-- Draft/LaczFormalRG5GammaC.lean -- Laczkovich DCG 48 (2012), Sect. 4: the graph `Gamma_c` (the graph `Gamma_a` of the model relabeled `alpha <-> gamma`), for a congruent dissection of a convex polygon.
-- Hypotheses `CaseC`: angle-/distance-matching `idx`, REGULAR counts (`#alpha = #beta` at every point), and `c` not a nonnegative rational combination of `a, b`.  No hypothesis on `gamma`.
--  * Lemma 4.5 / balance: the head of a `Gamma_c` edge has an outgoing `Gamma_c` edge (free: the number of corners of type `alpha, beta` is even at every vertex, `HalfPar` for the relabeled model);
--    out-degree = in-degree at every vertex; no edge starts at a point that is not an interior point of the polygon.
--  * Lemma 4.7: at every vertex of the polygon the `c`-status of the first tile along the outgoing side equals that of the last tile along the incoming side; hence all sides of the polygon
--    are integer multiples of `c`, or all are combinations of `a, b`.  When `a, b` are commensurable the polygon is rational.
-- UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Lemmas 4.4-4.7), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalRGCaseVgen
import Erdos634.Draft.LaczFormalRG4IVa
import Erdos634.Draft.LaczFormalRG4Comm

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ} [NeZero M]

/-- Standing hypotheses of the `Γ_c` theory. -/
structure CaseC (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) : Prop where
  hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k'))
  hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v
  hregc : ∀ X, cnt D idx X 0 = cnt D idx X 1
  hnc : NotComb (slen D 2) (slen D 1) (slen D 0)

/-- The relabeled model `α ↔ γ`: `Γ_c` of `D` is `Γ_a` of `D'`. -/
noncomputable def relabelC (D : CongruentRegionDissection N) : CongruentRegionDissection N := relabel D (Equiv.swap 0 2)

noncomputable def relabelCIdx (idx : Fin N → Equiv.Perm (Fin 3)) : Fin N → Equiv.Perm (Fin 3) := relabelIdx idx (Equiv.swap 0 2)

theorem swap02_0 : (Equiv.swap (0 : Fin 3) 2) 0 = 2 := by simp
theorem swap02_1 : (Equiv.swap (0 : Fin 3) 2) 1 = 1 := Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)
theorem swap02_2 : (Equiv.swap (0 : Fin 3) 2) 2 = 0 := by simp

theorem relabelC_slen0 (D : CongruentRegionDissection N) : slen (relabelC D) 0 = slen D 2 := by
  unfold relabelC; rw [relabel_slen, swap02_0]

theorem CaseC.halfPar {D : CongruentRegionDissection N} {idx : Fin N → Equiv.Perm (Fin 3)} (h : CaseC D idx) : HalfPar (relabelC D) (relabelCIdx idx) := by
  intro X _
  have e1 := relabel_cnt D idx (Equiv.swap 0 2) X 1
  have e2 := relabel_cnt D idx (Equiv.swap 0 2) X 2
  rw [swap02_1] at e1; rw [swap02_2] at e2
  show (cnt (relabelC D) (relabelCIdx idx) X 1 + cnt (relabelC D) (relabelCIdx idx) X 2) % 2 = 0
  unfold relabelC relabelCIdx
  rw [e1, e2, ← h.hregc X]
  omega

theorem CaseC.caseG {D : CongruentRegionDissection N} {idx : Fin N → Equiv.Perm (Fin 3)} (h : CaseC D idx) : CaseG (relabelC D) (relabelCIdx idx) := by
  refine ⟨relabel_hidx D idx _ h.hidx, relabel_hidxA D idx _ h.hidxA, ?_, h.halfPar⟩
  unfold relabelC
  rw [relabel_slen, relabel_slen, relabel_slen, swap02_0, swap02_1, swap02_2]
  exact h.hnc

/-- `Γ_c`: the graph `Γ_a` with `a` replaced by `c`. -/
def GcEdge (D : CongruentRegionDissection N) (X H : Plane) : Prop := GaEdge D.toRegionDissection (slen D 2) X H

theorem gcEdge_iff (D : CongruentRegionDissection N) (X H : Plane) : GcEdge D X H ↔ GaEdge (relabelC D).toRegionDissection (slen (relabelC D) 0) X H := by
  unfold GcEdge; rw [relabelC_slen0]; rfl

/-- **Lemma 4.5 (head of a `Γ_c` edge starts an edge), real version.** -/
theorem gc_head_out (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (idx : Fin N → Equiv.Perm (Fin 3)) (h : CaseC D idx)
    {X H : Plane} (hE : GcEdge D X H) : ∃ H', GcEdge D H H' := by
  have hG := h.caseG
  haveI : HasFansC (relabelC D).toRegionDissection := (inferInstance : HasFansC D.toRegionDissection)
  rw [gcEdge_iff] at hE
  obtain ⟨H', hH'⟩ := ga_head_out_half (relabelC D) (relabelCIdx idx) hG.hidx hG.hidxA hG.hnc hG.hab hG.hac hG.hhp hE
  exact ⟨H', (gcEdge_iff D H H').mpr hH'⟩

/-- **Balance**: at every vertex the out-degree of `Γ_c` equals the in-degree. -/
theorem gc_balance (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (h : CaseC D idx) :
    ∀ v : ↥(vtxSet (relabelC D).toRegionDissection),
      ((GAset (relabelC D)).filter fun e => e.1 = v).card = ((GAset (relabelC D)).filter fun e => e.2 = v).card := by
  have hG := h.caseG
  haveI : HasFansC (relabelC D).toRegionDissection := (inferInstance : HasFansC D.toRegionDissection)
  exact lemma91_i (relabelC D) (relabelCIdx idx) hG.hidx hG.hidxA hG.hnc hG.hab hG.hac hG.hhp

/-- **No edge of `Γ_c` starts at a point that is not an interior point of the polygon.** -/
theorem gc_no_boundary (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (idx : Fin N → Equiv.Perm (Fin 3)) (h : CaseC D idx)
    {X H : Plane} (hX : X ∉ interior D.region) : ¬ GcEdge D X H := by
  have hG := h.caseG
  haveI : HasFansC (relabelC D).toRegionDissection := (inferInstance : HasFansC D.toRegionDissection)
  rw [gcEdge_iff]
  exact lemma91_ii (relabelC D) (relabelCIdx idx) hG.hidx hG.hidxA hG.hnc hG.hab hG.hac hG.hhp hX

set_option maxHeartbeats 3200000 in
/-- **Lemma 4.7, vertex step.**  At every vertex `v_{k+1}` of the polygon the `c`-status of the first tile of the walk along the outgoing edge equals the `c`-status of the last tile of the walk along the
incoming edge (no edge of `Γ_c` starts on the boundary, and the number of `α, β` corners is even). -/
theorem corner_c_status (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (idx : Fin N → Equiv.Perm (Fin 3)) (h : CaseC D idx)
    (P : ConvPoly M) (hreg : D.region = P.carrier) (k : Fin M) :
    ∀ (jo : Fin N) (Uo : Plane) (ji : Fin N) (Ui : Plane),
      TriStep (D.tile jo) (toV2 (P.e (k + 1))) (P.v (k + 1)) Uo → TriStep (D.tile ji) (toV2 (P.e k)) Ui (P.v (k + 1)) →
      (dist (P.v (k + 1)) Uo = slen D 2 ↔ dist Ui (P.v (k + 1)) = slen D 2) := by
  classical
  intro jo Uo ji Ui hSo hSi
  have hG := h.caseG
  set D' := relabelC D with hD'
  set idx' := relabelCIdx idx with hidx'
  haveI : HasFansC D'.toRegionDissection := (inferInstance : HasFansC D.toRegionDissection)
  have hreg' : D'.region = P.carrier := hreg
  have hD'0 : slen D' 0 = slen D 2 := relabelC_slen0 D
  set V := P.v (k + 1) with hVdef
  have hvert : ∃ j k', (D'.tile j).pts k' = V := poly_vertex_is_tile_vertex D'.toRegionDissection P hreg' (k + 1)
  obtain ⟨pT, qT, F, hpd, hqd, hcr, h1, h2, h3, h4, h5⟩ := fan_vertex_poly D'.toRegionDissection P hreg' k hvert
  have hqT : qT ≠ 0 := by intro h; rw [h] at hcr; unfold crs at hcr; simp at hcr
  have hpT : pT ≠ 0 := hpd.ne_left
  obtain ⟨i0, k0, hk0⟩ := hvert
  have hmem0 : V ∈ (D'.tile i0).carrier := hk0 ▸ subset_convexHull ℝ _ ⟨k0, rfl⟩
  have hAt : 0 < Fintype.card (AtV D'.toRegionDissection V) := Fintype.card_pos_iff.mpr ⟨⟨i0, hmem0⟩⟩
  obtain ⟨c, hc1, hcn, hadj, hsurjc, hinjc⟩ := corner_chain F hcr h1 h2 h3 h4 h5 hAt
  set n := Fintype.card (AtV D'.toRegionDissection V) with hn
  have hsumT := corner_tile_sum D'.toRegionDissection F hcr h1 h2 h3 h4
  have hwlt := wd_lt_pi_of_crs_pos hcr
  have hwpos := wd_pos (Or.inl hcr : SecOK pT qT)
  have hnostr : ∀ x : AtV D'.toRegionDissection V, ∃ k, (D'.tile x.1).pts k = V := by
    intro x
    rcases F.hspec x with ⟨k, hk, -⟩ | ⟨hnv, m', -, -, hq, -⟩
    · exact ⟨k, hk⟩
    · exfalso
      have hw : wd (F.p x) (F.q x) = Real.pi := by rw [hq]; exact wd_straight (F.hok x).ne_p
      have hle : wd (F.p x) (F.q x) ≤ ∑ y : AtV D'.toRegionDissection V, wd (F.p y) (F.q y) :=
        Finset.single_le_sum (f := fun y => wd (F.p y) (F.q y)) (fun y _ => (wd_pos (F.hok y)).le) (Finset.mem_univ x)
      linarith
  have hcrall : ∀ x : AtV D'.toRegionDissection V, 0 < crs (F.p x) (F.q x) :=
    fun x => crs_pos_of_corner (F.hok x) (F.hspec x) (hnostr x)
  have hcpos : ∀ l, 1 ≤ l → l ≤ n → 0 < crs (F.p (c l)) (F.q (c l)) := fun l _ _ => hcrall _
  have hnb : ∀ l, 1 ≤ l → l < n → NoBack D'.toRegionDissection (F.q (c l)) V := by
    intro l _ _
    exact noBack_corner F hcr h5 (tile_ray_mem F (c l)).2 (F.hok (c l)).ne_q
  have hcore := chain_core D' idx' hG.hidx hG.hnc hG.hab hG.hac F n hAt c hcpos hadj hnb
  have hci : P.c (k + 1) V = 0 := by rw [hVdef]; exact P.c_self _
  rcases hcore with ⟨H', hH'⟩ | hpar
  · exact absurd hH' (lemma91_ii D' idx' hG.hidx hG.hidxA hG.hnc hG.hab hG.hac hG.hhp
      (by rw [hreg']; exact not_interior_of_c_zero P hci))
  · -- parity: the number of `α, β` corners is even
    have heven : (∑ l ∈ Finset.Icc 1 n, (if ∃ k' : Fin 3, (D'.tile (c l).1).pts k' = V ∧ idx' (c l).1 k' ≠ 0 then 1 else 0)) % 2 = 0 := by
      have hs := chain_sum c hsurjc hinjc (fun x => if ∃ k' : Fin 3, (D'.tile x.1).pts k' = V ∧ idx' x.1 k' ≠ 0 then 1 else 0)
      rw [hs, Finset.sum_boole]
      have := corner_tile_count D' idx' V ⟨i0, hmem0⟩
      simp only [Nat.cast_id]
      rw [this]
      have e1 := relabel_cnt D idx (Equiv.swap 0 2) V 1
      have e2 := relabel_cnt D idx (Equiv.swap 0 2) V 2
      rw [swap02_1] at e1; rw [swap02_2] at e2
      have e1' : cnt D' idx' V 1 = cnt D idx V 1 := e1
      have e2' : cnt D' idx' V 2 = cnt D idx V 0 := e2
      rw [e1', e2', ← h.hregc V]
      omega
    have hiff : (nsq (F.p (c 1)) = slen D' 0 ^ 2 ↔ nsq (F.q (c n)) = slen D' 0 ^ 2) := hpar.mpr heven
    -- identify the steps
    have hdis := tiles_disjoint D'.toRegionDissection V F.p F.q F.hloc
    have hd1 : Par (toV2 (P.e (k + 1))) pT := hpd.symm
    have hqe' : Par qT (neg2 (toV2 (P.e k))) := by
      have e : toV2 (P.v k - P.v (k + 1)) = neg2 (toV2 (P.e k)) := by
        unfold neg2 toV2 ConvPoly.e; ext <;> simp
      rw [e] at hqd; exact hqd
    have hsl : 0 ≤ slen D' 0 := (slen_pos D' 0).le
    -- out tile
    have hOut : nsq (F.p (c 1)) = dist V Uo ^ 2 := by
      obtain ⟨kk, f, g, hk, hf, hfk, hgk, hgf, hpar2, hleft⟩ := id hSo
      have hmem : V ∈ (D'.tile jo).carrier := hk ▸ subset_convexHull ℝ _ ⟨kk, rfl⟩
      set x : AtV D'.toRegionDissection V := ⟨jo, hmem⟩
      obtain ⟨kk', fl, hk', hp, hq⟩ := spec_corner_data (F.hspec x) ⟨kk, hk⟩
      have hkk : kk' = kk := (D'.tile jo).indep.injective (hk'.trans hk.symm)
      have hPx : Par (F.p x) (toV2 (P.e (k + 1))) := triStep_start hSo kk' fl hk' hp hq (F.hok x)
      have hx1 : x = c 1 := by
        by_contra hne
        exact start_inj F.p F.q F.hok hdis (Ne.symm hne) (hPx.trans (hd1.trans hc1.symm))
      have hq' : Par (toV2 ((D'.tile jo).pts (armP kk' fl) - V)) (toV2 (P.e (k + 1))) := hp ▸ hPx
      have harm := parm_eq (T := D'.tile jo) fl hk' (W := Uo) (w := f) hf (by rw [hkk]; exact hfk) hq' hpar2
      rw [← hx1, hp, nsq_toV2_sub, harm, dist_comm]
    have hIn : nsq (F.q (c n)) = dist Ui V ^ 2 := by
      obtain ⟨kk, f, g, hk, hf, hfk, hgk, hgf, hpar2, hleft⟩ := id hSi
      have hmem : V ∈ (D'.tile ji).carrier := hf ▸ subset_convexHull ℝ _ ⟨f, rfl⟩
      set x : AtV D'.toRegionDissection V := ⟨ji, hmem⟩
      obtain ⟨kk', fl, hk', hp, hq⟩ := spec_corner_data (F.hspec x) ⟨f, hf⟩
      have hkk : kk' = f := (D'.tile ji).indep.injective (hk'.trans hf.symm)
      have hQx : Par (F.q x) (neg2 (toV2 (P.e k))) := triStep_end hSi kk' fl hk' hp hq (F.hok x)
      have hx1 : x = c n := by
        by_contra hne
        exact end_inj' F.p F.q F.hok hdis (Ne.symm hne) (hQx.trans (hqe'.symm.trans hcn))
      have hq' : Par (toV2 ((D'.tile ji).pts (armQ kk' fl) - V)) (neg2 (toV2 (P.e k))) := hq ▸ hQx
      have hW : Par (toV2 (Ui - V)) (neg2 (toV2 (P.e k))) := par_neg_arm hpar2
      have harm := qarm_eq (T := D'.tile ji) fl hk' (W := Ui) (w := kk) hk (by rw [hkk]; exact hfk.symm) hq' hW
      rw [← hx1, hq, nsq_toV2_sub, harm]
    rw [hOut, hIn] at hiff
    rw [hD'0] at hiff hsl
    have e1 : dist V Uo ^ 2 = slen D 2 ^ 2 ↔ dist V Uo = slen D 2 := (pow_left_inj₀ dist_nonneg hsl two_ne_zero)
    have e2 : dist Ui V ^ 2 = slen D 2 ^ 2 ↔ dist Ui V = slen D 2 := (pow_left_inj₀ dist_nonneg hsl two_ne_zero)
    rw [e1, e2] at hiff
    exact hiff

/-- **Lemma 4.7: all sides of the polygon are alike.**  Either every side is a positive integer multiple of `c`, or every side is a (nonzero) combination `na a + nb b`. -/
theorem polygon_sides_alike (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (idx : Fin N → Equiv.Perm (Fin 3)) (h : CaseC D idx)
    (P : ConvPoly M) (hreg : D.region = P.carrier) :
    (∀ i : Fin M, ∃ m : ℕ, 0 < m ∧ P.side i = m * slen D 2) ∨
    (∀ i : Fin M, ∃ na nb : ℕ, 0 < na + nb ∧ P.side i = na * slen D 0 + nb * slen D 1) := by
  classical
  have hG := h.caseG
  set D' := relabelC D with hD'
  set idx' := relabelCIdx idx with hidx'
  haveI : HasFansC D'.toRegionDissection := (inferInstance : HasFansC D.toRegionDissection)
  have hD'0 : slen D' 0 = slen D 2 := relabelC_slen0 D
  have hed := edge_data D P hreg
  choose L e0 el hW hh hl hs1 hs2 hT0 hT1 using hed
  -- statuses along each edge
  have hU : ∀ i, ∃ s : ℝ, 0 ≤ s ∧ toV2 (P.v i - P.v i) = (s * (toV2 (P.e i)).1, s * (toV2 (P.e i)).2) :=
    fun i => ⟨0, le_rfl, by unfold toV2; ext <;> simp⟩
  have hchain : ∀ i, ∀ e ∈ L i, (dist e.2.1 e.2.2 = slen D 2 ↔ dist (e0 i).2.1 (e0 i).2.2 = slen D 2) := by
    intro i e he
    have := walk_status_chain D' idx' hG P hreg i rfl (hW i) (hU i) (e0 i) (hh i) e he
    rwa [hD'0] at this
  have hlast : ∀ i, (dist (el i).2.1 (el i).2.2 = slen D 2 ↔ dist (e0 i).2.1 (e0 i).2.2 = slen D 2) := by
    intro i
    exact hchain i (el i) (List.mem_of_getLast? (hl i))
  -- the status at consecutive edges agrees
  have hstep : ∀ k : Fin M, (dist (e0 (k + 1)).2.1 (e0 (k + 1)).2.2 = slen D 2 ↔ dist (e0 k).2.1 (e0 k).2.2 = slen D 2) := by
    intro k
    have hSo : TriStep (D.tile (e0 (k + 1)).1) (toV2 (P.e (k + 1))) (P.v (k + 1)) (e0 (k + 1)).2.2 := by
      have := hT0 (k + 1); rwa [hs1 (k + 1)] at this
    have hSi : TriStep (D.tile (el k).1) (toV2 (P.e k)) (el k).2.1 (P.v (k + 1)) := by
      have := hT1 k; rwa [hs2 k] at this
    have := corner_c_status D idx h P hreg k _ _ _ _ hSo hSi
    have hA : dist (e0 (k + 1)).2.1 (e0 (k + 1)).2.2 = dist (P.v (k + 1)) (e0 (k + 1)).2.2 := by rw [hs1]
    have hB : dist (el k).2.1 (el k).2.2 = dist (el k).2.1 (P.v (k + 1)) := by rw [hs2]
    rw [hA]
    exact this.trans (by rw [← hB]; exact hlast k)
  have hall : ∀ n : ℕ, (dist (e0 (n : Fin M)).2.1 (e0 (n : Fin M)).2.2 = slen D 2 ↔ dist (e0 0).2.1 (e0 0).2.2 = slen D 2) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have := hstep (n : Fin M)
      rw [Nat.cast_succ]
      exact this.trans ih
  have hall' : ∀ i : Fin M, (dist (e0 i).2.1 (e0 i).2.2 = slen D 2 ↔ dist (e0 0).2.1 (e0 0).2.2 = slen D 2) := by
    intro i
    have := hall i.val
    rwa [Fin.cast_val_eq_self] at this
  have hmem := fun i => walkT_mem_step (hW i)
  have hsum := fun i => walkT_dist_sum (hW i)
  have hLne : ∀ i, L i ≠ [] := by
    intro i hL0
    have := hh i
    rw [hL0] at this; simp at this
  by_cases hc0 : dist (e0 0).2.1 (e0 0).2.2 = slen D 2
  · left
    intro i
    have hall2 : ∀ e ∈ L i, dist e.2.1 e.2.2 = slen D 2 := fun e he => ((hchain i e he).mpr ((hall' i).mpr hc0))
    have hsumA : ((L i).map fun e => dist e.2.1 e.2.2).sum = ((L i).map fun e => dist e.2.1 e.2.2).length • slen D 2 :=
      List.sum_eq_card_nsmul _ _ (fun x hx => by
        obtain ⟨e', he', rfl⟩ := List.mem_map.mp hx
        exact hall2 e' he')
    rw [List.length_map, nsmul_eq_mul] at hsumA
    exact ⟨(L i).length, List.length_pos_of_ne_nil (hLne i), by rw [ConvPoly.side, ← hsum i, hsumA]⟩
  · right
    intro i
    have hall2 : ∀ e ∈ L i, dist e.2.1 e.2.2 ≠ slen D 2 := fun e he hh' => hc0 ((hall' i).mp ((hchain i e he).mp hh'))
    obtain ⟨na, nb, h1, h2⟩ := list_sum_decomp2 (slen D 0) (slen D 1) ((L i).map fun e => dist e.2.1 e.2.2) (by
      intro x hx
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
      rcases side_len_mem D idx h.hidx (hmem i e he) with h' | h' | h'
      · exact Or.inl h'
      · exact Or.inr h'
      · exact absurd h' (hall2 e he))
    refine ⟨na, nb, ?_, ?_⟩
    · rw [h2, List.length_map]; exact List.length_pos_of_ne_nil (hLne i)
    · rw [ConvPoly.side, ← hsum i, h1]

/-- `Comm (na a + nb b) a` when `a, b` are commensurable and `na + nb > 0`. -/
theorem comm_comb {a b : ℝ} (hab : Comm a b) (na nb : ℕ) (hpos : 0 < na + nb) : Comm (na * a + nb * b) a := by
  obtain ⟨m, n, hm, hn, e⟩ := hab
  refine ⟨n, n * na + nb * m, hn, ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos na with h | h
    · have : 0 < nb := by omega
      have := Nat.mul_pos this hm
      omega
    · have := Nat.mul_pos hn h
      omega
  · push_cast
    have : (n : ℝ) * b = m * a := by linarith
    calc (n : ℝ) * (na * a + nb * b) = n * na * a + nb * (n * b) := by ring
      _ = n * na * a + nb * (m * a) := by rw [this]
      _ = ((n : ℝ) * na + nb * m) * a := by ring

/-- **Lemma 4.7 (rationality of the polygon).**  `a, b` commensurable and `c` not a rational multiple of `a`: all sides of the polygon are pairwise commensurable. -/
theorem rational_of_caseC (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (idx : Fin N → Equiv.Perm (Fin 3)) (h : CaseC D idx)
    (hab : Comm (slen D 0) (slen D 1)) (P : ConvPoly M) (hreg : D.region = P.carrier) : RationalPoly P := by
  rcases polygon_sides_alike D idx h P hreg with hc | hab'
  · intro i j
    obtain ⟨m, hm, e1⟩ := hc i
    obtain ⟨m', hm', e2⟩ := hc j
    refine ⟨m', m, hm', hm, ?_⟩
    rw [e1, e2]; ring
  · have key : ∀ i : Fin M, Comm (P.side i) (slen D 0) := by
      intro i
      obtain ⟨na, nb, hpos, e⟩ := hab' i
      rw [e]; exact comm_comb hab na nb hpos
    intro i j
    exact comm_trans' (key i) (comm_symm' (key j))

/-- `c` not a rational multiple of `a`, `a, b` commensurable: `c` is not a nonnegative rational combination of `a, b`. -/
theorem notComb_c_of_comm {a b c : ℝ} (hc : 0 < c) (hab : Comm a b) (hac : ¬ Comm a c) : NotComb c b a := by
  intro r p q hr h
  obtain ⟨m, n, hm, hn, e⟩ := hab
  -- n r c = (p m + q n) a
  apply hac
  have hpos : 0 < p * m + q * n ∨ (p = 0 ∧ q = 0) := by
    rcases Nat.eq_zero_or_pos p with h0 | h0
    · rcases Nat.eq_zero_or_pos q with h1 | h1
      · exact Or.inr ⟨h0, h1⟩
      · exact Or.inl (by have := Nat.mul_pos h1 hn; omega)
    · exact Or.inl (by have := Nat.mul_pos h0 hm; omega)
  rcases hpos with hpos | ⟨rfl, rfl⟩
  · refine ⟨p * m + q * n, n * r, hpos, Nat.mul_pos hn hr, ?_⟩
    push_cast
    have : (n : ℝ) * (r * c) = n * (p * b + q * a) := by rw [h]
    have hnb : (n : ℝ) * b = m * a := by linarith
    nlinarith [this, hnb]
  · exfalso
    have : (r : ℝ) * c = 0 := by rw [h]; simp
    have : 0 < (r : ℝ) * c := mul_pos (by exact_mod_cast hr) hc
    linarith

/-- **Lemma 4.7 for a polygon tiling** (any `γ`): `a, b` commensurable and `c` not commensurable with `a` imply that the polygon is rational. -/
theorem polytiling_rational {N M : ℕ} [NeZero M] (T : PolyTiling N M) (hreg : RegularPQ T.C) (hab : Comm (slen T.C 0) (slen T.C 1))
    (hac : ¬ Comm (slen T.C 0) (slen T.C 2)) : RationalPoly T.P := by
  classical
  obtain ⟨idx, hA, hcnt⟩ := hreg
  haveI : HasFansC T.C.toRegionDissection := hasFansC_poly _ T.P T.region_eq
  have hC : CaseC T.C idx := ⟨idx_dist_of_angle T.C idx hA, hA, fun X => hcnt X, notComb_c_of_comm (slen_pos T.C 2) hab hac⟩
  exact rational_of_caseC T.C idx hC hab T.P T.region_eq

end Erdos634.Draft.LaczFormal.RG
