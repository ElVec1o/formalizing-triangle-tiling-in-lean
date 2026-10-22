-- Draft/LaczFormalRGCnt.lean -- S3 of PLAN_THM21: port of LaczFormalGraphCnt to `RegionDissection` (dissection-dependent declarations only; the rest is used
-- from the original module).  UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 4), Beeson, Beeson-Zhang; port of the project's LaczFormalGraphCnt.
import Erdos634.Draft.LaczFormalRGIn
import Erdos634.Draft.LaczFormalGraphCnt


open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph

namespace Erdos634.Draft.LaczFormal.RG

variable {N : ℕ}


open scoped Classical

open Erdos634.Geometry Erdos634.KConj

/-- Tiles having `H` in the relative interior of a side. -/
noncomputable def Strn (D : RegionDissection N) (H : Plane) : Finset (Fin N) :=
  Finset.univ.filter (fun i => H ∈ (D.tile i).carrier ∧ ∀ k, (D.tile i).pts k ≠ H)


/-- Tiles having `H` as a vertex. -/
noncomputable def Corn (D : RegionDissection N) (H : Plane) : Finset (Fin N) :=
  Finset.univ.filter (fun i => ∃ k, (D.tile i).pts k = H)


theorem sum_vc_eq (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3))
    (hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v) (P : Plane) :
    ∑ l, (cnt D idx P l : ℝ) * D.model.angleAt l = ∑ i, vc (D.tile i) P := by
  rw [← fiber_sum_P D idx P D.model.angleAt]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  unfold vc
  refine Finset.sum_congr rfl (fun v _ => ?_)
  split_ifs
  · exact hidxA i v
  · rfl


theorem card_corn (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) (H : Plane) :
    (Corn D.toRegionDissection H).card = ∑ l, cnt D idx H l := by
  classical
  let P : Finset (Fin N × Fin 3) := Finset.univ.filter (fun p => (D.tile p.1).pts p.2 = H)
  have h1 : (Corn D.toRegionDissection H).card = P.card := by
    have himg : P.image Prod.fst = Corn D.toRegionDissection H := by
      ext i
      simp only [Finset.mem_image, P, Corn, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨⟨j, k⟩, hk, rfl⟩; exact ⟨k, hk⟩
      · rintro ⟨k, hk⟩; exact ⟨(i, k), hk, rfl⟩
    rw [← himg, Finset.card_image_of_injOn]
    rintro ⟨i, k⟩ hp ⟨i', k'⟩ hp' he
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq, P] at hp hp'
    simp only at he
    subst he
    have : k = k' := (D.tile i).indep.injective (hp.trans hp'.symm)
    rw [this]
  have h2 : P.card = ∑ l, cnt D idx H l := by
    have := Finset.card_eq_sum_card_fiberwise (s := P) (t := Finset.univ) (f := fun p : Fin N × Fin 3 => idx p.1 p.2)
      (fun _ _ => Finset.mem_univ _)
    rw [this]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    unfold cnt
    congr 1
    ext p
    simp [P, and_comm]
  rw [h1, h2]


theorem card_atV (D : RegionDissection N) (H : Plane) :
    Fintype.card (AtV D H) = (Corn D H).card + (Strn D H).card := by
  classical
  have h0 : Fintype.card (AtV D H) = (Finset.univ.filter (fun i => H ∈ (D.tile i).carrier)).card := by
    unfold AtV; rw [Fintype.card_subtype]
  rw [h0, ← Finset.filter_card_add_filter_neg_card_eq_card (s := Finset.univ.filter (fun i => H ∈ (D.tile i).carrier))
    (fun i => ∃ k, (D.tile i).pts k = H)]
  congr 2
  · ext i
    simp only [Corn, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨-, h⟩; exact h
    · rintro ⟨k, hk⟩; exact ⟨vertex_mem hk, k, hk⟩
  · ext i
    simp only [Strn, Finset.mem_filter, Finset.mem_univ, true_and, not_exists]


/-- **Angle equation at a vertex (general fan)**: corner angles, `π` per tile having `H` inside a side, and the virtual sectors add up to `2π`. -/
theorem head_angle_sum_gen (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3))
    (hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v) {H : Plane} {κ : Type} [Fintype κ]
    (F : ExtFan D.toRegionDissection H κ) :
    ∑ l, (cnt D idx H l : ℝ) * D.model.angleAt l + Real.pi * (Strn D.toRegionDissection H).card +
      ∑ j, wd (F.pe j) (F.qe j) = 2 * Real.pi := by
  classical
  have hsum := F.hsum
  set g : Fin N → ℝ := fun i => vc (D.tile i) H + if i ∈ Strn D.toRegionDissection H then Real.pi else 0 with hg
  have per : ∀ x : AtV D.toRegionDissection H, wd (F.p x) (F.q x) = g x.1 := by
    intro x
    rcases F.hspec x with ⟨k, hk, -⟩ | ⟨hnv, m, -, -, hq, -⟩
    · have hloc : (D.tile x.1).localAngle H = vc (D.tile x.1) H := by
        have e := vc_of_vertex (D.tile x.1) k
        rw [hk] at e; exact e.symm
      have hnS : x.1 ∉ Strn D.toRegionDissection H := by
        simp only [Strn, Finset.mem_filter, Finset.mem_univ, true_and, not_and, not_forall, not_not]
        intro _; exact ⟨k, hk⟩
      rw [F.hwd x, hloc, hg]
      simp [hnS]
    · have hvc : vc (D.tile x.1) H = 0 := vc_of_nonvertex _ _ (fun v h => hnv v h.symm)
      have hS : x.1 ∈ Strn D.toRegionDissection H := by
        simp only [Strn, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨x.2, hnv⟩
      have hw : wd (F.p x) (F.q x) = Real.pi := by rw [hq]; exact wd_straight (F.hok x).ne_p
      rw [hw, hg]
      simp [hvc, hS]
  have h1 : ∑ x : AtV D.toRegionDissection H, wd (F.p x) (F.q x) = ∑ i, g i := by
    calc ∑ x : AtV D.toRegionDissection H, wd (F.p x) (F.q x) = ∑ x : AtV D.toRegionDissection H, g x.1 :=
          Finset.sum_congr rfl (fun x _ => per x)
      _ = ∑ i ∈ Finset.univ.filter (fun i => H ∈ (D.tile i).carrier), g i := by
          symm
          exact Finset.sum_subtype (Finset.univ.filter (fun i => H ∈ (D.tile i).carrier)) (by simp)
            (fun i => g i)
      _ = ∑ i, g i := by
          rw [Finset.sum_filter_of_ne]
          intro i _ hne
          by_contra hnm
          apply hne
          have hvc : vc (D.tile i) H = 0 := vc_of_nonvertex _ _ (fun v h => hnm (vertex_mem h.symm))
          have hS : i ∉ Strn D.toRegionDissection H := fun h => hnm (by simp [Strn] at h; exact h.1)
          simp [hg, hvc, hS]
  have h2 : ∑ i, g i = ∑ i, vc (D.tile i) H + Real.pi * (Strn D.toRegionDissection H).card := by
    rw [hg]; simp only
    rw [Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  rw [sum_vc_eq D idx hidxA H, ← h2, ← h1]
  exact hsum


/-- **Angle equation at a vertex with a complete fan**: corner angles plus `π` per tile having `H` inside a side give `2π`. -/
theorem head_angle_sum (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3))
    (hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v) {H : Plane} {κ : Type} [Fintype κ]
    (F : ExtFan D.toRegionDissection H κ) (hemp : IsEmpty κ) :
    ∑ l, (cnt D idx H l : ℝ) * D.model.angleAt l + Real.pi * (Strn D.toRegionDissection H).card = 2 * Real.pi := by
  have h := head_angle_sum_gen D idx hidxA F
  have hv : ∑ j, wd (F.pe j) (F.qe j) = 0 := by haveI := hemp; simp
  rw [hv, add_zero] at h
  exact h


/-- **Head counts**: at a head (one straight sector, one corner) there is exactly one tile with `H` inside a side, the corner angles sum to `π`, and the
tiles at `H` are the straight one and the `∑ cnt` corners. -/
theorem head_counts (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3))
    (hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v) {H : Plane} {κ : Type} [Fintype κ]
    (F : ExtFan D.toRegionDissection H κ) (hemp : IsEmpty κ) {s a : AtV D.toRegionDissection H}
    (hs : F.q s = (-(F.p s).1, -(F.p s).2)) (ha : 0 < crs (F.p a) (F.q a)) :
    (Strn D.toRegionDissection H).card = 1 ∧ ∑ l, (cnt D idx H l : ℝ) * D.model.angleAt l = Real.pi ∧
      Fintype.card (AtV D.toRegionDissection H) = 1 + ∑ l, cnt D idx H l := by
  classical
  have hsmem : s.1 ∈ Strn D.toRegionDissection H := by
    rcases F.hspec s with ⟨k, hk, -⟩ | ⟨hnv, m, -⟩
    · exfalso
      have hc := crs_pos_of_corner (F.hok s) (F.hspec s) ⟨k, hk⟩
      rw [hs] at hc; unfold crs at hc; simp at hc; linarith
    · simp only [Strn, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨s.2, hnv⟩
  have hcard1 : (Strn D.toRegionDissection H).card = 1 := by
    rw [Finset.card_eq_one]
    refine ⟨s.1, ?_⟩
    ext j
    simp only [Finset.mem_singleton]
    constructor
    · intro hj
      simp only [Strn, Finset.mem_filter, Finset.mem_univ, true_and] at hj
      obtain ⟨hjm, hnv⟩ := hj
      rcases F.hspec ⟨j, hjm⟩ with ⟨k, hk, -⟩ | ⟨-, m, -, -, hq, -⟩
      · exact absurd hk (hnv k)
      · exact congrArg Subtype.val (straight_unique F hq hs ha)
    · rintro rfl; exact hsmem
  have hsum := head_angle_sum D idx hidxA F hemp
  rw [hcard1] at hsum
  refine ⟨hcard1, by push_cast at hsum; linarith, ?_⟩
  rw [card_atV, card_corn D idx H, hcard1]; ring


/-- Angle arithmetic of a model with types `0, 1, 2` = `(α, β, γ)`: the half-plane equations compatible with regularity (`#α = #β`). -/
def HalfPlaneArith (D : CongruentRegionDissection N) : Prop :=
  ∀ n0 n1 n2 : ℕ, (n0 : ℝ) * D.model.angleAt 0 + n1 * D.model.angleAt 1 + n2 * D.model.angleAt 2 = Real.pi →
    n0 = n1 → (n0 = 0 ∧ n2 = 3) ∨ (n0 = 1 ∧ n2 = 1)


/-- **Head classification**: a head of a `Γ_a` edge with a regular corner count has either three `γ` corners or one corner of each type; in both cases
the tiles at `H` are four and the hypotheses of `head_out_edge` hold. -/
theorem head_out_of_cfg (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    (hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v)
    (hnc : NotComb (slen D 0) (slen D 1) (slen D 2)) (hab : slen D 0 ≠ slen D 1) (hac : slen D 0 ≠ slen D 2)
    (harith : HalfPlaneArith D) {H : Plane} {κ : Type} [Fintype κ] (F : ExtFan D.toRegionDissection H κ) {e : V2}
    {u v s : AtV D.toRegionDissection H} (hc : HeadCfg D F e u v s) (hreg : cnt D idx H 0 = cnt D idx H 1) :
    (∃ H', GaEdge D.toRegionDissection (slen D 0) H H') ∨ ∃ Z, GkEdge D.toRegionDissection idx H Z := by
  classical
  have hc' := hc
  obtain ⟨hc1, hc2, hc3, hc4, hc5, hc6, hc7⟩ := hc'
  have hcyc := F.head_cyc u v s hc1 hc2 hc3 hc4 hc5 hc6
  have hemp : IsEmpty κ := hcyc.1
  obtain ⟨hS1, hsum, hcard⟩ := head_counts D idx hidxA F hemp hc6 hc1
  rw [Fin.sum_univ_three] at hsum
  have hsum' : ((cnt D idx H 0 : ℕ) : ℝ) * D.model.angleAt 0 + (cnt D idx H 1 : ℕ) * D.model.angleAt 1 + (cnt D idx H 2 : ℕ) * D.model.angleAt 2 = Real.pi := by
    simpa using hsum
  have hcls := harith _ _ _ hsum' hreg
  rw [Fin.sum_univ_three] at hcard
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
  have hmem : ∀ (l : Fin 3) (t : Fin N) (k : Fin 3), (D.tile t).pts k = H → idx t k = l → 1 ≤ cnt D idx H l := by
    intro l t k h1 e1
    unfold cnt
    apply Finset.card_pos.mpr
    exact ⟨(t, k), by simp [h1, e1]⟩
  have hF : ∀ (t : AtV D.toRegionDissection H) (k : Fin 3), (D.tile t.1).pts k = H → t ≠ s := by
    rintro t k hk rfl
    rcases F.hspec t with ⟨k', hk', -⟩ | ⟨hnv, -⟩
    · have hcr := crs_pos_of_corner (F.hok t) (F.hspec t) ⟨k', hk'⟩
      rw [hc6] at hcr; unfold crs at hcr; simp at hcr; linarith
    · exact hnv k hk
  rcases hcls with ⟨h0, h2⟩ | ⟨h0, h2⟩
  · -- three gammas
    have c0 : cnt D idx H 0 = 0 := h0
    have c1 : cnt D idx H 1 = 0 := by omega
    have c2 : cnt D idx H 2 = 3 := h2
    have hcard4 : Fintype.card (AtV D.toRegionDissection H) = 4 := by omega
    refine head_out_edge D idx hidx hnc hab hac F hc hcard4 (Or.inr ?_)
    intro t _ k hk
    have := (idx t.1 k)
    by_contra hne
    have hl : idx t.1 k = 0 ∨ idx t.1 k = 1 := by
      generalize idx t.1 k = z at hne
      fin_cases z <;> simp_all
    rcases hl with hl | hl
    · have := hmem 0 t.1 k hk hl; omega
    · have := hmem 1 t.1 k hk hl; omega
  · have c0 : cnt D idx H 0 = 1 := h0
    have c1 : cnt D idx H 1 = 1 := by omega
    have c2 : cnt D idx H 2 = 1 := h2
    have hcard4 : Fintype.card (AtV D.toRegionDissection H) = 4 := by omega
    refine head_out_edge D idx hidx hnc hab hac F hc hcard4 (Or.inl ?_)
    intro t1 t2 _ _ hne k1 k2 hk1 hk2 heq
    have hl : cnt D idx H (idx t1.1 k1) ≥ 2 := hpair (idx t1.1 k1) t1.1 t2.1 k1 k2 (fun e => hne (Subtype.ext e)) hk1 hk2 rfl heq.symm
    generalize idx t1.1 k1 = z at hl
    fin_cases z <;> simp_all <;> omega


/-- **Lemma 8.1(i), `Γ_a` part (and Lemma 4.2 for real tilings)**: the head `H` of an edge of `Γ_a` is the tail of an edge of `Γ_a` or of `Γ_k`,
provided the tile corner counts at `H` are regular (`#α = #β`) and the half-plane equation `n₀α + n₁β + n₂γ = π` forces `(0,0,3)` or `(1,1,1)`. -/
theorem ga_head_out (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    (hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v)
    (hnc : NotComb (slen D 0) (slen D 1) (slen D 2)) (hab : slen D 0 ≠ slen D 1) (hac : slen D 0 ≠ slen D 2)
    (harith : HalfPlaneArith D) {X H : Plane} (hE : GaEdge D.toRegionDissection (slen D 0) X H)
    (hreg : cnt D idx H 0 = cnt D idx H 1) :
    (∃ H', GaEdge D.toRegionDissection (slen D 0) H H') ∨ ∃ Z, GkEdge D.toRegionDissection idx H Z := by
  classical
  obtain ⟨κ, _, ⟨F⟩⟩ := HasFansC.fans (D := D.toRegionDissection) H (ga_edge_vertex _ _ hE)
  obtain ⟨d, hd, nb, hc⟩ := ga_edge_data D idx hidx hnc hE F
  rcases hc with ⟨P, W, hP, a, b, s, h1, h2, h3, h4, h5, h6, h7, h8⟩ | ⟨P, W, hP, a, b, s, h1, h2, h3, h4, h5, h6, h7, h8⟩
  · exact head_out_of_cfg D idx hidx hidxA hnc hab hac harith F (HeadCfg.of_left D F a b s h1 h2 h3 h4 h5 h6 h7 h8) hreg
  · exact head_out_of_cfg D idx hidx hidxA hnc hab hac harith F (HeadCfg.of_right D F a b s h1 h2 h3 h4 h5 h6 h7 h8) hreg


/-- Counts at the head of a `Γ_a` edge: `(0,0,3)` or `(1,1,1)`. -/
theorem ga_head_cls (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    (hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v)
    (hnc : NotComb (slen D 0) (slen D 1) (slen D 2)) (harith : HalfPlaneArith D) {X H : Plane}
    (hE : GaEdge D.toRegionDissection (slen D 0) X H) (hreg : cnt D idx H 0 = cnt D idx H 1) :
    (cnt D idx H 0 = 0 ∧ cnt D idx H 1 = 0 ∧ cnt D idx H 2 = 3) ∨ (cnt D idx H 0 = 1 ∧ cnt D idx H 1 = 1 ∧ cnt D idx H 2 = 1) := by
  classical
  obtain ⟨κ, _, ⟨F⟩⟩ := HasFansC.fans (D := D.toRegionDissection) H (ga_edge_vertex _ _ hE)
  obtain ⟨d, hd, nb, hc⟩ := ga_edge_data D idx hidx hnc hE F
  have key : ∀ {e : V2} {u v s : AtV D.toRegionDissection H}, HeadCfg D F e u v s →
      (cnt D idx H 0 = 0 ∧ cnt D idx H 1 = 0 ∧ cnt D idx H 2 = 3) ∨ (cnt D idx H 0 = 1 ∧ cnt D idx H 1 = 1 ∧ cnt D idx H 2 = 1) := by
    intro e u v s hc
    obtain ⟨hc1, hc2, hc3, hc4, hc5, hc6, hc7⟩ := hc
    have hcyc := F.head_cyc u v s hc1 hc2 hc3 hc4 hc5 hc6
    obtain ⟨hS1, hsum, hcard⟩ := head_counts D idx hidxA F hcyc.1 hc6 hc1
    rw [Fin.sum_univ_three] at hsum
    have hsum' : ((cnt D idx H 0 : ℕ) : ℝ) * D.model.angleAt 0 + (cnt D idx H 1 : ℕ) * D.model.angleAt 1 + (cnt D idx H 2 : ℕ) * D.model.angleAt 2 = Real.pi := by
      simpa using hsum
    rcases harith _ _ _ hsum' hreg with ⟨h0, h2⟩ | ⟨h0, h2⟩
    · left; exact ⟨h0, by omega, h2⟩
    · right; exact ⟨h0, by omega, h2⟩
  rcases hc with ⟨P, W, hP, a, b, s, h1, h2, h3, h4, h5, h6, h7, h8⟩ | ⟨P, W, hP, a, b, s, h1, h2, h3, h4, h5, h6, h7, h8⟩
  · exact key (HeadCfg.of_left D F a b s h1 h2 h3 h4 h5 h6 h7 h8)
  · exact key (HeadCfg.of_right D F a b s h1 h2 h3 h4 h5 h6 h7 h8)


/-- An edge of `Γ_k` into `X` gives two tiles with `β` at `X`. -/
theorem gk_two_beta (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) {Z X : Plane}
    (h : GkEdge D.toRegionDissection idx Z X) : 2 ≤ cnt D idx X 1 := by
  classical
  obtain ⟨i, j, k1, k2, k1', k2', hij, a1, a2, a3, a4, a5, a6, a7, a8⟩ := h
  unfold cnt
  have : ({(i, k2), (j, k2')} : Finset (Fin N × Fin 3)) ⊆ Finset.univ.filter (fun p : Fin N × Fin 3 => (D.tile p.1).pts p.2 = X ∧ idx p.1 p.2 = 1) := by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl <;> simp [*]
  have h3 := Finset.card_le_card this
  rw [Finset.card_pair (fun e => hij (congrArg Prod.fst e))] at h3
  exact h3


/-- The edge set `Γ_a ∪ Γ_k`. -/
def GE (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) (X H : Plane) : Prop :=
  GaEdge D.toRegionDissection (slen D 0) X H ∨ GkEdge D.toRegionDissection idx X H


/-- **In-degree of `Γ_a ∪ Γ_k` is at most one** (Laczkovich, Sect. 8.1): `Γ_a` and `Γ_k` heads are disjoint (a `Γ_a` head has at most one `β`, a `Γ_k` head two),
`Γ_a` by `ga_indegree`, `Γ_k` by `gk_indegree` given at most three `β` at every vertex (`hβ3`). -/
theorem GE_indegree (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    (hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v)
    (hnc : NotComb (slen D 0) (slen D 1) (slen D 2)) (harith : HalfPlaneArith D)
    (hreg : ∀ P, cnt D idx P 0 = cnt D idx P 1) (hβ3 : ∀ P, cnt D idx P 1 ≤ 3) {X X' H : Plane}
    (h1 : GE D idx X H) (h2 : GE D idx X' H) : X = X' := by
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact ga_indegree D idx hidx hnc h1 h2
  · exfalso
    have hc := gk_two_beta D idx h2
    rcases ga_head_cls D idx hidx hidxA hnc harith h1 (hreg H) with ⟨-, h, -⟩ | ⟨-, h, -⟩ <;> omega
  · exfalso
    have hc := gk_two_beta D idx h1
    rcases ga_head_cls D idx hidx hidxA hnc harith h2 (hreg H) with ⟨-, h, -⟩ | ⟨-, h, -⟩ <;> omega
  · exact gk_indegree D idx (hβ3 H) h1 h2


end Erdos634.Draft.LaczFormal.RG
