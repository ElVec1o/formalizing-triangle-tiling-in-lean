-- Draft/LaczFormalGraphBal.lean -- D5 (part 5): Lemma 8.1 (i), (ii) for real tilings.
-- (i) at every vertex the out-degree of `Gamma_a u Gamma_k` equals the in-degree (finite digraph balance); (ii) no edge starts on the boundary of the target.
-- UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Lemma 8.1), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalGraphGk
import Erdos634.Draft.LaczFormalRegArith

open scoped Classical
open Erdos634.Geometry Erdos634.KConj

namespace Erdos634.Draft.LaczFormal.Graph

variable {N : ℕ}

theorem localAngle_two_pi_interior (T : Tri) {p : Plane} (h : T.localAngle p = 2 * Real.pi) : p ∈ interior T.carrier := by
  classical
  rw [Tri.mem_interior_iff_coord_pos]
  unfold Tri.localAngle at h
  split_ifs at h with h1 h2 h3
  · exfalso
    have := Erdos634.RouteOneVertexKill.cornerAngle_lt_pi T h1.choose
    have hp := Real.pi_pos
    linarith
  · exact h2
  · exfalso; have := Real.pi_pos; linarith
  · exfalso; have := Real.pi_pos; linarith

/-- A vertex whose fan has no virtual sector lies in the interior of the target. -/
theorem interior_of_complete_fan (D : CongruentDissection N) {X : Plane} {κ : Type} [Fintype κ] (F : ExtFan D.toDissection X κ)
    (hemp : IsEmpty κ) : X ∈ interior D.target.carrier := by
  classical
  have hsum := F.hsum
  have hvirt : ∑ j, wd (F.pe j) (F.qe j) = 0 := by haveI := hemp; simp
  rw [hvirt, add_zero] at hsum
  have h1 : ∑ x : AtV D.toDissection X, (D.tile x.1).localAngle X = 2 * Real.pi := by
    rw [← hsum]; exact Finset.sum_congr rfl (fun x _ => (F.hwd x).symm)
  have h2 : ∑ i, (D.tile i).localAngle X = ∑ x : AtV D.toDissection X, (D.tile x.1).localAngle X := by
    calc ∑ i, (D.tile i).localAngle X = ∑ i ∈ Finset.univ.filter (fun i => X ∈ (D.tile i).carrier), (D.tile i).localAngle X := by
          symm
          rw [Finset.sum_filter_of_ne]
          intro i _ hne
          by_contra hnm
          exact hne (Tri.localAngle_eq_zero_of_not_mem _ hnm)
      _ = ∑ x : AtV D.toDissection X, (D.tile x.1).localAngle X := by
          exact Finset.sum_subtype (Finset.univ.filter (fun i => X ∈ (D.tile i).carrier)) (by simp) (fun i => (D.tile i).localAngle X)
  have h3 := D.toDissection.sum_localAngle_eq X
  rw [h2, h1] at h3
  exact localAngle_two_pi_interior D.target h3.symm

theorem cnt_zero_of_not_vertex (D : CongruentDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) {P : Plane}
    (hP : ¬ ∃ i k, (D.tile i).pts k = P) (l : Fin 3) : cnt D idx P l = 0 := by
  unfold cnt
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro ⟨i, k⟩ _ ⟨h, -⟩
  exact hP ⟨i, k, h⟩

/-- Regularity at every point (non-vertices have no corners). -/
theorem reg_all (D : CongruentDissection N) (idx : Fin N → Equiv.Perm (Fin 3))
    (hreg : ∀ P, (∃ i k, (D.tile i).pts k = P) → cnt D idx P 0 = cnt D idx P 1) (P : Plane) : cnt D idx P 0 = cnt D idx P 1 := by
  by_cases h : ∃ i k, (D.tile i).pts k = P
  · exact hreg P h
  · rw [cnt_zero_of_not_vertex D idx h, cnt_zero_of_not_vertex D idx h]

/-- At most three `β` at a vertex (regular counts, `α+β = 2γ`, angle sum at most `2π`). -/
theorem beta_le_three (D : CongruentDissection N) (idx : Fin N → Equiv.Perm (Fin 3))
    (hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v) {w0 w1 w2 : ℕ} {u : ℝ} (W : WtData D w0 w1 w2 u)
    (hreg : ∀ P, (∃ i k, (D.tile i).pts k = P) → cnt D idx P 0 = cnt D idx P 1) (P : Plane) : cnt D idx P 1 ≤ 3 := by
  classical
  by_cases hP : ∃ i k, (D.tile i).pts k = P
  · have hS : ∑ l, (cnt D idx P l : ℝ) * D.model.angleAt l ≤ 2 * Real.pi := by
      rcases vertex_group D idx hidxA P (by obtain ⟨i, k, hk⟩ := hP; exact ⟨(i, k), hk⟩) with ⟨j, -, hj⟩ | ⟨-, hj | hj⟩
      · have hlt : D.target.angleAt j < Real.pi := Erdos634.RouteOneVertexKill.cornerAngle_lt_pi D.target j
        have := Real.pi_pos
        rw [hj]; linarith
      · have := Real.pi_pos; rw [hj]; linarith
      · rw [hj]
    rw [Fin.sum_univ_three] at hS
    have hr := hreg P hP
    have hw2 := W.hw2
    have hu := W.hu
    have hpi : Real.pi = 3 * (w2 : ℝ) * u := by
      have := W.hsum
      have hw : ((w0 + w1 + w2 : ℕ) : ℝ) = 3 * w2 := by
        have : w0 + w1 + w2 = 3 * w2 := by have := W.hw; omega
        rw [this]; push_cast; ring
      rw [← this, hw]
    have hA01 : D.model.angleAt 0 + D.model.angleAt 1 = 2 * w2 * u := by
      rw [W.h0, W.h1]
      have : (w0 : ℝ) + w1 = 2 * w2 := by exact_mod_cast W.hw
      linear_combination u * this
    have hA2 := model_angle_pos D 2
    have hc : ((cnt D idx P 0 : ℕ) : ℝ) = (cnt D idx P 1 : ℕ) := by exact_mod_cast hr
    rw [hc] at hS
    have hnn : (0 : ℝ) ≤ (cnt D idx P 2 : ℕ) * D.model.angleAt 2 := mul_nonneg (Nat.cast_nonneg _) hA2.le
    have h1 : (cnt D idx P 1 : ℝ) * (2 * w2 * u) ≤ 2 * Real.pi := by
      have : (cnt D idx P 1 : ℝ) * (D.model.angleAt 0 + D.model.angleAt 1) ≤ 2 * Real.pi := by nlinarith
      rwa [hA01] at this
    rw [hpi] at h1
    have hwu : 0 < (w2 : ℝ) * u := mul_pos (by exact_mod_cast hw2) hu
    have h2 : (cnt D idx P 1 : ℝ) ≤ 3 := by nlinarith
    exact_mod_cast h2
  · rw [cnt_zero_of_not_vertex D idx hP]; omega

/-- The finite set of tile vertices. -/
noncomputable def vtxFin (D : Dissection N) : Finset Plane :=
  Finset.univ.image (fun p : Fin N × Fin 3 => (D.tile p.1).pts p.2)

theorem mem_vtxFin {D : Dissection N} {P : Plane} : P ∈ vtxFin D ↔ ∃ i k, (D.tile i).pts k = P := by
  unfold vtxFin
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Prod.exists]

theorem ga_edge_endpoints (D : Dissection N) (a : ℝ) {X H : Plane} (h : GaEdge D a X H) :
    (∃ i k, (D.tile i).pts k = X) ∧ (∃ i k, (D.tile i).pts k = H) := by
  refine ⟨?_, ga_edge_vertex D a h⟩
  obtain ⟨d, Y, L1, L2, hd, hnb, W1, W2, hL1, hL2, -⟩ := h
  cases W1 with
  | nil => exact absurd rfl hL1
  | cons hS _ =>
    obtain ⟨kk, f, g, hk, -⟩ := hS
    exact ⟨_, kk, hk⟩

theorem GE_endpoints (D : CongruentDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) {X H : Plane} (h : GE D idx X H) :
    (∃ i k, (D.tile i).pts k = X) ∧ (∃ i k, (D.tile i).pts k = H) := by
  rcases h with h | ⟨i, j, k1, k2, k1', k2', -, a1, a2, -⟩
  · exact ga_edge_endpoints _ _ h
  · exact ⟨⟨i, k1, a1⟩, ⟨i, k2, a2⟩⟩

/-- The edge set of `Γ_a ∪ Γ_k` on the finite vertex set. -/
noncomputable def GEset (D : CongruentDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) :
    Finset (↥(vtxFin D.toDissection) × ↥(vtxFin D.toDissection)) :=
  Finset.univ.filter (fun e => GE D idx e.1.1 e.2.1)

/-- **Lemma 8.1 (i)**: at every vertex the out-degree of `Γ_a ∪ Γ_k` equals its in-degree. -/
theorem lemma81_i (D : CongruentDissection N) (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    (hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v)
    (hnc : NotComb (slen D 0) (slen D 1) (slen D 2)) (hab : slen D 0 ≠ slen D 1) (hac : slen D 0 ≠ slen D 2)
    {w0 w1 w2 : ℕ} {u : ℝ} (W : WtData D w0 w1 w2 u)
    (hw3 : (w0, w1, w2) = (1, 7, 4) ∨ (w0, w1, w2) = (1, 19, 10) ∨ (w0, w1, w2) = (7, 13, 10))
    (hreg : ∀ P, (∃ i k, (D.tile i).pts k = P) → cnt D idx P 0 = cnt D idx P 1) :
    ∀ v : ↥(vtxFin D.toDissection), ((GEset D idx).filter fun e => e.1 = v).card = ((GEset D idx).filter fun e => e.2 = v).card := by
  classical
  have hreg' := reg_all D idx hreg
  have hβ3 := beta_le_three D idx hidxA W hreg
  have harith := halfPlaneArith_of_wt W
  apply digraph_balance
  · intro v
    rw [Finset.card_le_one]
    intro a ha b hb
    simp only [GEset, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    have hb1 : GE D idx b.1.1 a.2.1 := by rw [show a.2 = b.2 from ha.2.trans hb.2.symm]; exact hb.1
    have := GE_indegree D idx hidx hidxA hnc harith hreg' hβ3 ha.1 hb1
    exact Prod.ext (Subtype.ext this) (ha.2.trans hb.2.symm)
  · intro v hv
    obtain ⟨e, he⟩ := Finset.card_pos.mp hv
    simp only [GEset, Finset.mem_filter, Finset.mem_univ, true_and] at he
    obtain ⟨hE, hev⟩ := he
    have hvv : v.1 = e.2.1 := by rw [hev]
    have hvert : ∃ i k, (D.tile i).pts k = v.1 := mem_vtxFin.mp v.2
    have hout : (∃ H', GaEdge D.toDissection (slen D 0) v.1 H') ∨ ∃ Z', GkEdge D.toDissection idx v.1 Z' := by
      rcases hE with hE | hE
      · rw [hvv]
        exact ga_head_out D idx hidx hidxA hnc hab hac harith hE (hreg' _)
      · rw [hvv]
        exact gk_head_out D idx hidx hidxA hnc hab hac W hw3 hE (hreg' _)
    apply Finset.card_pos.mpr
    rcases hout with ⟨H', hH'⟩ | ⟨Z', hZ'⟩
    · have hv' : H' ∈ vtxFin D.toDissection := mem_vtxFin.mpr (ga_edge_endpoints _ _ hH').2
      exact ⟨(v, ⟨H', hv'⟩), by simp [GEset, GE, hH']⟩
    · have hv' : Z' ∈ vtxFin D.toDissection := mem_vtxFin.mpr (GE_endpoints D idx (Or.inr hZ')).2
      exact ⟨(v, ⟨Z', hv'⟩), by simp [GEset, GE, hZ']⟩

/-- The head of a `Γ_a` edge is an interior point of the target. -/
theorem ga_head_interior (D : CongruentDissection N) (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    (hnc : NotComb (slen D 0) (slen D 1) (slen D 2)) {X H : Plane} (hE : GaEdge D.toDissection (slen D 0) X H) :
    H ∈ interior D.target.carrier := by
  classical
  obtain ⟨κ, _, ⟨F⟩⟩ := extFan_exists D.toDissection H (ga_edge_vertex _ _ hE)
  obtain ⟨d, hd, nb, hc⟩ := ga_edge_data D idx hidx hnc hE F
  rcases hc with ⟨P, W, hP, a, b, s, h1, h2, h3, h4, h5, h6, h7, h8⟩ | ⟨P, W, hP, a, b, s, h1, h2, h3, h4, h5, h6, h7, h8⟩
  · exact (F.head_cyc a b s h1 h2 h3 h4 h5 h6).2.1
  · obtain ⟨c1, c2, c3, c4, c5, c6, -⟩ := HeadCfg.of_right D F a b s h1 h2 h3 h4 h5 h6 h7 h8
    exact (F.head_cyc b a s c1 c2 c3 c4 c5 c6).2.1

theorem gk_head_interior (D : CongruentDissection N) (idx : Fin N → Equiv.Perm (Fin 3))
    (hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v) {w0 w1 w2 : ℕ} {u : ℝ} (W : WtData D w0 w1 w2 u)
    {Z X : Plane} (hE : GkEdge D.toDissection idx Z X) (hreg : cnt D idx X 0 = cnt D idx X 1) :
    X ∈ interior D.target.carrier := by
  obtain ⟨κ, _, F, hemp, -⟩ := gk_fan_full D idx hidxA W hE hreg
  exact interior_of_complete_fan D F hemp

/-- **Lemma 8.1 (ii)**: no edge of `Γ_a ∪ Γ_k` starts on the boundary of the target. -/
theorem lemma81_ii (D : CongruentDissection N) (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    (hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v)
    (hnc : NotComb (slen D 0) (slen D 1) (slen D 2)) (hab : slen D 0 ≠ slen D 1) (hac : slen D 0 ≠ slen D 2)
    {w0 w1 w2 : ℕ} {u : ℝ} (W : WtData D w0 w1 w2 u)
    (hw3 : (w0, w1, w2) = (1, 7, 4) ∨ (w0, w1, w2) = (1, 19, 10) ∨ (w0, w1, w2) = (7, 13, 10))
    (hreg : ∀ P, (∃ i k, (D.tile i).pts k = P) → cnt D idx P 0 = cnt D idx P 1)
    {X H : Plane} (hX : X ∉ interior D.target.carrier) : ¬ GE D idx X H := by
  classical
  intro hGE
  have hreg' := reg_all D idx hreg
  have hXv : X ∈ vtxFin D.toDissection := mem_vtxFin.mpr (GE_endpoints D idx hGE).1
  have hHv : H ∈ vtxFin D.toDissection := mem_vtxFin.mpr (GE_endpoints D idx hGE).2
  have hbal := lemma81_i D idx hidx hidxA hnc hab hac W hw3 hreg ⟨X, hXv⟩
  have hout : 0 < ((GEset D idx).filter fun e => e.1 = (⟨X, hXv⟩ : ↥(vtxFin D.toDissection))).card :=
    Finset.card_pos.mpr ⟨(⟨X, hXv⟩, ⟨H, hHv⟩), by simp [GEset, hGE]⟩
  rw [hbal] at hout
  obtain ⟨e, he⟩ := Finset.card_pos.mp hout
  simp only [GEset, Finset.mem_filter, Finset.mem_univ, true_and] at he
  obtain ⟨hE, hev⟩ := he
  have hvv : e.2.1 = X := by rw [hev]
  apply hX
  rw [← hvv]
  rcases hE with hE | hE
  · exact ga_head_interior D idx hidx hnc hE
  · exact gk_head_interior D idx hidxA W hE (hreg' _)

end Erdos634.Draft.LaczFormal.Graph
