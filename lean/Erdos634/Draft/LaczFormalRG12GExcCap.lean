-- Draft/LaczFormalRG12GExcCap.lean -- Laczkovich (DCG 48 (2012)), Sect. 6.2, Gamma_except, lemma L9 `exc_capacity` (blueprint A.2, capacity of an exceptional point): at an exceptional point `E` (`p < r`) at which NO tile has `E` inside one of its sides
-- (`Strn E = empty`) the number of edges of Gamma_except arriving at `E` is at most `r - p` (`r = cnt gamma`, `p = cnt alpha`).
-- Route: an arriving edge gives two ADJACENT `gamma` corner sectors at `E` with common ray `-d` (`arrData_exists`, from `gexc_end_split_full`; the paper's "two triangles having E as a vertex"); distinct edges give distinct sectors (`align_same`); the right sectors of the
-- arrivals form a subset of the `gamma` sectors; if they were ALL of them then, the left neighbour of a right sector being a `gamma` sector too, the set of `gamma` sectors would be closed under predecessor, hence (the fan is cyclic) every sector would be a `gamma` corner,
-- contradicting `p = 1` (`fan_closed`).  `p <= 1` at an exceptional point is the equation `p (pi - gamma) + r gamma = v pi`, `v <= 2` (`exc_cnt0_le_one`).
-- NOTE, UNAUDITED.  PRINT GAP (named): for an exceptional point with a straight tile (an INTERIOR T-junction of type (0,0,N/2)) an edge may arrive along the line of the straight tile (one side of the end is an inner point of a side, not a corner), so the paper's
-- "if an edge arrives at E then there are two triangles having E as a vertex" (l. 1409-1411) is not justified there; the capacity bound is proved only under `Strn E = empty` (boundary and interior points without straight tile).
-- Credit: Laczkovich (DCG 48 (2012), Sect. 6.2), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalRG12GExcEnd

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ}

/-- The start of an edge of Gamma_except is a tile vertex. -/
theorem gexc_start_vertex (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) {X Y : Plane} (h : GExc D idx X Y) :
    ∃ j k, (D.tile j).pts k = X := by
  obtain ⟨d, Z, L1, L2, H1, H2, hd, hnb, W1, W2, hL1, -⟩ := h
  cases W1 with
  | nil => exact absurd rfl hL1
  | cons hS W' => obtain ⟨kk, f, g, hk, -⟩ := hS; exact ⟨_, kk, hk⟩

/-- A tile with `Y` as an inner point of one of its sides has `Y` inside a side (`Strn`). -/
theorem strn_of_inner {D : RegionDissection N} {i : Fin N} {d : V2} {A B Y : Plane} (hS : TriStep (D.tile i) d A B) (hY : Y ∈ openSegment ℝ A B) :
    i ∈ Strn D Y := by
  obtain ⟨σ, h0, h1, hYσ⟩ := openSegment_param hY
  obtain ⟨hmem, hnv, -⟩ := step_interior_pt hS h0 h1
  rw [← hYσ] at hmem hnv
  simp only [Strn, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨hmem, hnv⟩

/-- `p <= 1` at an exceptional point. -/
theorem exc_cnt0_le_one [NeZero M] (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v) (hregc : ∀ X, cnt D idx X 0 = cnt D idx X 1)
    (h1 : D.model.angleAt 2 < Real.pi / 2) (h3 : D.model.angleAt 2 ≠ Real.pi / 3) {X : Plane}
    (hvert : ∃ j k, (D.tile j).pts k = X) (hnc : ∀ k : Fin M, X ≠ P.v (k + 1)) (hlt : cnt D idx X 0 < cnt D idx X 2) : cnt D idx X 0 ≤ 1 := by
  have hpi := Real.pi_pos
  have hγ0 := model_angle_pos' D 2
  have hv : ∃ v : ℕ, (v = 1 ∨ (v = 2 ∧ X ∈ interior D.region)) ∧ Asum D idx X = v * Real.pi := by
    rcases vertex_A D P hreg idx hidxA hvert with ⟨hi, h2 | h1'⟩ | ⟨hni, h1' | ⟨k, hXk, -⟩⟩
    · exact ⟨2, Or.inr ⟨rfl, hi⟩, by rw [h2]; push_cast; ring⟩
    · exact ⟨1, Or.inl rfl, by rw [h1']; push_cast; ring⟩
    · exact ⟨1, Or.inl rfl, by rw [h1']; push_cast; ring⟩
    · exact absurd hXk (hnc k)
  obtain ⟨v, hv12, hAv⟩ := hv
  rw [Asum_eq D idx hregc] at hAv
  have hv2 : v ≤ 2 := by rcases hv12 with h | ⟨h, -⟩ <;> omega
  have hA : ((cnt D idx X 2 : ℝ) - cnt D idx X 0) * D.model.angleAt 2 = ((v : ℝ) - cnt D idx X 0) * Real.pi := by linarith
  have hd : (0 : ℝ) < (cnt D idx X 2 : ℝ) - cnt D idx X 0 := by
    have : (cnt D idx X 0 : ℝ) < cnt D idx X 2 := by exact_mod_cast hlt
    linarith
  have hvr : (0 : ℝ) < (v : ℝ) - cnt D idx X 0 := by
    have h0 : 0 < ((cnt D idx X 2 : ℝ) - cnt D idx X 0) * D.model.angleAt 2 := mul_pos hd hγ0
    rw [hA] at h0
    exact (mul_pos_iff_of_pos_right hpi).mp h0
  have h5 : (cnt D idx X 0 : ℝ) < v := by linarith
  have h6 : cnt D idx X 0 < v := by exact_mod_cast h5
  omega

/-- The left and right `gamma` corner sectors of an arriving edge. -/
def IsGam (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) {E : Plane} (a : AtV D.toRegionDissection E) : Prop :=
  ∃ k, (D.tile a.1).pts k = E ∧ idx a.1 k = 2

def ArrData (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) {E : Plane} {κ : Type} [Fintype κ] (F : ExtFan D.toRegionDissection E κ)
    (X : Plane) (aL aR : AtV D.toRegionDissection E) : Prop :=
  ∃ d : V2, d ≠ 0 ∧ NoBack D.toRegionDissection d X ∧ (∃ (b : Bool) (P : List (Fin N × Plane × Plane)), WalkU D.toRegionDissection b d X E P ∧ P ≠ []) ∧
    Par (F.q aL) (neg2 d) ∧ Par (F.p aR) (neg2 d) ∧ IsGam D idx aL ∧ IsGam D idx aR

theorem arrData_exists (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (idx : Fin N → Equiv.Perm (Fin 3)) {E : Plane} {κ : Type} [Fintype κ]
    (F : ExtFan D.toRegionDissection E κ) (hStrn : Strn D.toRegionDissection E = ∅) {X : Plane} (h : GExc D idx X E) :
    ∃ aL aR : AtV D.toRegionDissection E, ArrData D idx F X aL aR := by
  obtain ⟨d, hd, hnb, hw, ⟨iL, A, B, hL, hcL⟩, ⟨iR, A', B', hR, hcR⟩, -⟩ := gexc_end_split_full D idx h
  rcases hcL with ⟨hYB, hLg⟩ | hin
  swap
  · have := strn_of_inner hL hin
    rw [hStrn] at this
    exact absurd this (Finset.notMem_empty _)
  rcases hcR with ⟨hYB', hRg⟩ | hin'
  swap
  · have := strn_of_inner hR (by rw [openSegment_symm]; exact hin')
    rw [hStrn] at this
    exact absurd this (Finset.notMem_empty _)
  rw [← hYB] at hL
  rw [← hYB'] at hR
  obtain ⟨x, hxi, hxq⟩ := sec_end F hL
  obtain ⟨x2, hx2i, hx2p⟩ := sec_start F hR
  obtain ⟨kL, hkL, hkL2⟩ := hLg
  obtain ⟨kR, hkR, hkR2⟩ := hRg
  exact ⟨x, x2, d, hd, hnb, hw, hxq, hx2p, ⟨kL, by rw [hxi]; exact hkL, by rw [hxi]; exact hkL2⟩, ⟨kR, by rw [hx2i]; exact hkR, by rw [hx2i]; exact hkR2⟩⟩

theorem arrData_inj_R (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) {E : Plane} {κ : Type} [Fintype κ]
    (F : ExtFan D.toRegionDissection E κ) {X X' : Plane} {aL aR aL' aR' : AtV D.toRegionDissection E} (h : ArrData D idx F X aL aR)
    (h' : ArrData D idx F X' aL' aR') (hR : aR = aR') : X' = X := by
  obtain ⟨d, hd, hnb, ⟨b, P, w, hP⟩, hq, hp, -, -⟩ := h
  obtain ⟨d', hd', hnb', ⟨b', P', w', hP'⟩, hq', hp', -, -⟩ := h'
  subst hR
  have hdd : Par (neg2 d') (neg2 d) := hp'.symm.trans hp
  exact align_same D.toRegionDissection hd (par_neg2 hdd) w hP w' hP' hnb hnb'

/-- Uniqueness of the sector with a given start ray, over the whole fan. -/
theorem start_inj_sum {D : RegionDissection N} {V : Plane} {κ : Type} [Fintype κ] (F : ExtFan D V κ) {o o' : AtV D V ⊕ κ} (h : o ≠ o') :
    ¬ Par (Sum.elim F.p F.pe o') (Sum.elim F.p F.pe o) :=
  start_inj (Sum.elim F.p F.pe) (Sum.elim F.q F.qe) (fun o => by rcases o with s | j; exact F.hok s; exact F.hokE j)
    (fun s t hst z => F.disj_all hst z) h

theorem end_inj_sum {D : RegionDissection N} {V : Plane} {κ : Type} [Fintype κ] (F : ExtFan D V κ) {o o' : AtV D V ⊕ κ} (h : o ≠ o') :
    ¬ Par (Sum.elim F.q F.qe o') (Sum.elim F.q F.qe o) :=
  end_inj' (Sum.elim F.p F.pe) (Sum.elim F.q F.qe) (fun o => by rcases o with s | j; exact F.hok s; exact F.hokE j)
    (fun s t hst z => F.disj_all hst z) h

/-- **A set of corner sectors closed under predecessor and nonempty contains every sector of the (cyclic) fan.** -/
theorem fan_closed {D : RegionDissection N} {V : Plane} {κ : Type} [Fintype κ] (F : ExtFan D V κ) (Γ : Set (AtV D V)) {g0 : AtV D V} (hg0 : g0 ∈ Γ)
    (hcl : ∀ g ∈ Γ, ∃ a ∈ Γ, Par (F.q a) (F.p g)) : ∀ o : AtV D V ⊕ κ, ∃ a ∈ Γ, o = Sum.inl a := by
  classical
  have hLpos : 0 < Fintype.card (AtV D V ⊕ κ) := Fintype.card_pos_iff.mpr ⟨Sum.inl g0⟩
  set L := Fintype.card (AtV D V ⊕ κ) with hL
  have pred : ∀ n g, g ∈ Γ → F.e (n + 1) = Sum.inl g → ∃ a ∈ Γ, F.e n = Sum.inl a := by
    intro n g hg hen
    obtain ⟨a, ha, hqa⟩ := hcl g hg
    refine ⟨a, ha, ?_⟩
    by_contra hne
    have h1 := F.hP n
    rw [hen] at h1
    simp only [Sum.elim_inl] at h1
    exact end_inj_sum F (o := Sum.inl a) (o' := F.e n) (fun h => hne h.symm) (by simp only [Sum.elim_inl]; exact h1.symm.trans hqa.symm)
  have per : ∀ n k, F.e (n + L * k) = F.e n := by
    intro n k
    induction k with
    | zero => simp
    | succ k ih => rw [show n + L * (k + 1) = (n + L * k) + L by ring, hL, F.hper, ← hL, ih]
  obtain ⟨j0, -, hj0⟩ := F.hsurj (Sum.inl g0)
  intro o
  obtain ⟨j, -, hj⟩ := F.hsurj o
  set m := j0 + L * (j + 1) with hm
  have hmj : j ≤ m := by nlinarith
  have hdown : ∀ t, t ≤ m → ∃ a ∈ Γ, F.e (m - t) = Sum.inl a := by
    intro t
    induction t with
    | zero => intro _; exact ⟨g0, hg0, by rw [Nat.sub_zero, hm, per, hj0]⟩
    | succ t ih =>
      intro ht
      obtain ⟨a, ha, hea⟩ := ih (by omega)
      have : m - t = (m - (t + 1)) + 1 := by omega
      rw [this] at hea
      exact pred _ a ha hea
  obtain ⟨a, ha, hea⟩ := hdown (m - j) (by omega)
  rw [show m - (m - j) = j by omega, hj] at hea
  exact ⟨a, ha, hea⟩

end Erdos634.Draft.LaczFormal.RG
