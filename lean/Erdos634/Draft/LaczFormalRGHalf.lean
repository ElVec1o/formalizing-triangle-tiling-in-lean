-- Draft/LaczFormalRGHalf.lean -- S4 of PLAN_THM21: the HALF-FAN lemma (parity form of Laczkovich Lemma 4.2 / 4.5).
-- At a vertex `H` whose fan has a STRAIGHT sector (a tile `s` with `H` inside one of its sides -- the head of a `Gamma_a` edge -- or a virtual sector --
-- `H` on a side of the polygon) and `n >= 2` corner tiles filling the other half-plane, exactly one of the two corner arms on the boundary line has length `a`
-- (`slen D 0`).  Each corner tile of type `alpha` has no arm `a`; a tile of type `beta` or `gamma` has exactly one.  If the number of non-`alpha`
-- corners is EVEN, two consecutive corners disagree on their common ray, and (the ray is a start of a maximal segment) an edge of `Gamma_a` starts at `H`.
-- This replaces the case inspection ("Fig. 2") of the paper for every vertex equation `p(alpha+beta) + r gamma = pi` with `p + r` even.
-- UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Lemmas 4.2, 4.5, proofs "considering all possible positions of the angle alpha"), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalRGCnt
import Erdos634.Draft.LaczFormalRGFull

open scoped Classical
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph

namespace Erdos634.Draft.LaczFormal.RG

variable {N : ℕ}

/-- **Parity core.**  A chain of `n` corner tiles `1..n`; `P m` / `Q m` = "the `p`-arm / `q`-arm of tile `m` has length `a`".  A tile with `f m = false`
(type `α`) has neither arm `a`; with `f m = true` (type `β`, `γ`) exactly one.  If the two arms on the boundary line differ in being `a` and the number of
`true` tiles is even, then two consecutive tiles disagree on their common ray. -/
theorem parity_core (n : ℕ) (hn : 1 ≤ n) (P Q f : ℕ → Bool)
    (htile : ∀ m, 1 ≤ m → m ≤ n → ((f m = false → P m = false ∧ Q m = false) ∧ (f m = true → P m ≠ Q m)))
    (hline : P 1 ≠ Q n) (hpar : (∑ j ∈ Finset.Icc 1 n, (if f j = true then 1 else 0)) % 2 = 0) :
    ∃ m, 1 ≤ m ∧ m < n ∧ Q m ≠ P (m + 1) := by
  by_contra hcon
  have hcon' : ∀ m, 1 ≤ m → m < n → Q m = P (m + 1) := by
    intro m h1 h2
    by_contra h
    exact hcon ⟨m, h1, h2, h⟩
  have key : ∀ m, 1 ≤ m → m ≤ n → (Q m = P 1 ↔ (∑ j ∈ Finset.Icc 1 m, (if f j = true then 1 else 0)) % 2 = 0) := by
    intro m hm1 hmn
    induction m, hm1 using Nat.le_induction with
    | base =>
      have h1 := htile 1 le_rfl hn
      rw [Finset.Icc_self, Finset.sum_singleton]
      generalize hx : P 1 = x at *
      generalize hy : Q 1 = y at *
      cases hf : f 1
      · obtain ⟨h2, h3⟩ := h1.1 hf
        rw [h2, h3]; simp
      · have h2 := h1.2 hf
        cases x <;> cases y <;> simp_all
    | succ m hm ih =>
      have ih' := ih (by omega)
      have hnext := hcon' m hm (by omega)
      have h1 := htile (m + 1) (by omega) hmn
      rw [Finset.sum_Icc_succ_top (by omega)]
      generalize hx : P 1 = x at *
      generalize hq : Q m = q at *
      generalize hq' : Q (m + 1) = q' at *
      generalize hp : P (m + 1) = p' at *
      cases hf : f (m + 1)
      · obtain ⟨h2, h3⟩ := h1.1 hf
        rw [h3]
        rw [hnext, h2] at ih'
        simpa using ih'
      · have h2 := h1.2 hf
        subst hnext
        cases q <;> cases q' <;> cases x <;> simp_all <;> omega
  have := (key n hn le_rfl).mpr hpar
  exact hline this.symm

/-! ## Bits of a corner tile -/

theorem fin3_bits : ∀ x y z : Fin 3, x ≠ y → x ≠ z → y ≠ z → (x = 0 → y ≠ 0 ∧ z ≠ 0) ∧ (x ≠ 0 → (y = 0 ↔ ¬ z = 0)) := by decide

/-- **The arms of a corner tile.**  For a tile corner at `H` (vertex `kk`, orientation `fl`), the `p`-arm has length `a` iff the `armQ`-vertex has type `α`, the `q`-arm
iff the `armP`-vertex has type `α`.  Hence a corner of type `α` has no arm of length `a`, and a corner of type `β` or `γ` exactly one. -/
theorem corner_bits (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    (hab : slen D 0 ≠ slen D 1) (hac : slen D 0 ≠ slen D 2) {H : Plane} {i : Fin N} {kk : Fin 3} (fl : Bool)
    (hk : (D.tile i).pts kk = H) {p q : V2} (hp : p = toV2 ((D.tile i).pts (armP kk fl) - H))
    (hq : q = toV2 ((D.tile i).pts (armQ kk fl) - H)) :
    (idx i kk = 0 → ¬ nsq p = slen D 0 ^ 2 ∧ ¬ nsq q = slen D 0 ^ 2) ∧
    (idx i kk ≠ 0 → (nsq p = slen D 0 ^ 2 ↔ ¬ nsq q = slen D 0 ^ 2)) := by
  have e1 := nsq_p_iff D idx hidx hab hac fl hk hp
  have e2 := nsq_q_iff D idx hidx hab hac fl hk hq
  have hP := armP_ne kk fl
  have hQ := armQ_ne kk fl
  have hPQ := armPQ_ne kk fl
  have d1 : idx i kk ≠ idx i (armP kk fl) := fun h => hP ((idx i).injective h).symm
  have d2 : idx i kk ≠ idx i (armQ kk fl) := fun h => hQ ((idx i).injective h).symm
  have d3 : idx i (armP kk fl) ≠ idx i (armQ kk fl) := fun h => hPQ ((idx i).injective h)
  obtain ⟨b1, b2⟩ := fin3_bits _ _ _ d1 d2 d3
  rw [e1, e2]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨c1, c2⟩ := b1 h
    exact ⟨c2, c1⟩
  · have := b2 h
    constructor
    · intro h1 h2; exact (this.mp h2) h1
    · intro h1
      by_contra h3
      exact h1 (this.mpr h3)

/-! ## The fan around a straight sector -/

section Fan

variable {D : RegionDissection N} {H : Plane} {κ : Type} [Fintype κ]

/-- Position injectivity with a shift. -/
theorem e_inj_shift (F : ExtFan D H κ) (j0 : ℕ) {x y : ℕ} (hx : x < Fintype.card (AtV D H ⊕ κ)) (hy : y < Fintype.card (AtV D H ⊕ κ))
    (h : F.e (j0 + x) = F.e (j0 + y)) : x = y := by
  set L := Fintype.card (AtV D H ⊕ κ) with hL
  have hL0 : 0 < L := by omega
  have h1 : F.e ((j0 + x) % L) = F.e ((j0 + y) % L) := by
    rw [← cyc_mod F.e L F.hper, ← cyc_mod F.e L F.hper]; exact h
  have h2 := F.hinj (Set.mem_Iio.mpr (Nat.mod_lt _ hL0)) (Set.mem_Iio.mpr (Nat.mod_lt _ hL0)) h1
  have h3 : j0 + x ≡ j0 + y [MOD L] := h2
  exact Nat.ModEq.eq_of_lt_of_lt (Nat.ModEq.add_left_cancel' j0 h3) hx hy

/-- Surjectivity with a shift. -/
theorem e_surj_shift (F : ExtFan D H κ) (j0 : ℕ) (o : AtV D H ⊕ κ) :
    ∃ m < Fintype.card (AtV D H ⊕ κ), F.e (j0 + m) = o := by
  classical
  set L := Fintype.card (AtV D H ⊕ κ) with hL
  have hinjn : Set.InjOn (fun m => F.e (j0 + m)) (↑(Finset.range L) : Set ℕ) := by
    intro x hx y hy h
    simp only [Finset.coe_range, Set.mem_Iio] at hx hy
    exact e_inj_shift F j0 hx hy h
  have himg : (Finset.range L).image (fun m => F.e (j0 + m)) = Finset.univ :=
    Finset.eq_univ_of_card _ (by rw [Finset.card_image_of_injOn hinjn, Finset.card_range])
  have : o ∈ (Finset.range L).image (fun m => F.e (j0 + m)) := by rw [himg]; exact Finset.mem_univ _
  obtain ⟨m, hm, hem⟩ := Finset.mem_image.mp this
  exact ⟨m, Finset.mem_range.mp hm, hem⟩

end Fan


/-! ## Rays of the corners lie in the closed half-plane opposite to a straight sector -/

/-- A point of the open cone `(p,q)` arbitrarily close to the ray `p` (resp. `q`) lies on the positive side of any `u` that is positive on that ray. -/
theorem cone_witness_p (u px qx : V2) (hc : 0 < crs px qx) (hpos : 0 < crs u px) :
    ∃ z : V2, inInt px qx z ∧ 0 < crs u z := by
  set c := crs u qx with hcdef
  set δ : ℝ := crs u px / (2 * (|c| + 1)) with hδ
  have hδpos : 0 < δ := by positivity
  refine ⟨(px.1 + δ * qx.1, px.2 + δ * qx.2), ⟨?_, ?_⟩, ?_⟩
  · have : crs px (px.1 + δ * qx.1, px.2 + δ * qx.2) = δ * crs px qx := by unfold crs; simp only; ring
    rw [this]; positivity
  · have : crs (px.1 + δ * qx.1, px.2 + δ * qx.2) qx = crs px qx := by unfold crs; simp only; ring
    rw [this]; exact hc
  · have : crs u (px.1 + δ * qx.1, px.2 + δ * qx.2) = crs u px + δ * c := by rw [hcdef]; unfold crs; simp only; ring
    rw [this]
    have h1 : δ * c ≥ - (δ * |c|) := by nlinarith [neg_abs_le c]
    have h2 : δ * |c| < crs u px / 2 := by
      rw [hδ, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith [abs_nonneg c]
    linarith

theorem cone_witness_q (u px qx : V2) (hc : 0 < crs px qx) (hpos : 0 < crs u qx) :
    ∃ z : V2, inInt px qx z ∧ 0 < crs u z := by
  set c := crs u px with hcdef
  set δ : ℝ := crs u qx / (2 * (|c| + 1)) with hδ
  have hδpos : 0 < δ := by positivity
  refine ⟨(qx.1 + δ * px.1, qx.2 + δ * px.2), ⟨?_, ?_⟩, ?_⟩
  · have : crs px (qx.1 + δ * px.1, qx.2 + δ * px.2) = crs px qx := by unfold crs; simp only; ring
    rw [this]; exact hc
  · have : crs (qx.1 + δ * px.1, qx.2 + δ * px.2) qx = δ * crs px qx := by unfold crs; simp only; ring
    rw [this]; positivity
  · have : crs u (qx.1 + δ * px.1, qx.2 + δ * px.2) = crs u qx + δ * c := by rw [hcdef]; unfold crs; simp only; ring
    rw [this]
    have h1 : δ * c ≥ - (δ * |c|) := by nlinarith [neg_abs_le c]
    have h2 : δ * |c| < crs u qx / 2 := by
      rw [hδ, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith [abs_nonneg c]
    linarith

section Fan2

variable {D : RegionDissection N} {H : Plane} {κ : Type} [Fintype κ]

/-- Sector start / end ray of a member of the full family. -/
abbrev sp (F : ExtFan D H κ) (o : AtV D H ⊕ κ) : V2 := Sum.elim F.p F.pe o
abbrev sq' (F : ExtFan D H κ) (o : AtV D H ⊕ κ) : V2 := Sum.elim F.q F.qe o

theorem inInt_straight {u z : V2} : inInt u (-u.1, -u.2) z ↔ 0 < crs u z := by
  unfold inInt crs
  simp only
  constructor
  · rintro ⟨h, -⟩; exact h
  · intro h; exact ⟨h, by linarith⟩

/-- **Every corner tile other than the straight sector lies in the closed half-plane `crs u · ≤ 0`** (`u` = start ray of the straight sector). -/
theorem rays_closed (F : ExtFan D H κ) {o : AtV D H ⊕ κ} (hstr : sq' F o = (-(sp F o).1, -(sp F o).2))
    {x : AtV D H} (hx : (Sum.inl x : AtV D H ⊕ κ) ≠ o) (hc : 0 < crs (F.p x) (F.q x)) :
    crs (sp F o) (F.p x) ≤ 0 ∧ crs (sp F o) (F.q x) ≤ 0 := by
  constructor
  · by_contra h
    replace h := not_le.mp h
    obtain ⟨z, hz1, hz2⟩ := cone_witness_p (sp F o) (F.p x) (F.q x) hc h
    apply F.disj_all hx z
    refine ⟨hz1, ?_⟩
    show inInt (sp F o) (sq' F o) z
    rw [hstr]; exact inInt_straight.mpr hz2
  · by_contra h
    replace h := not_le.mp h
    obtain ⟨z, hz1, hz2⟩ := cone_witness_q (sp F o) (F.p x) (F.q x) hc h
    apply F.disj_all hx z
    refine ⟨hz1, ?_⟩
    show inInt (sp F o) (sq' F o) z
    rw [hstr]; exact inInt_straight.mpr hz2

theorem sectorOK (F : ExtFan D H κ) (o : AtV D H ⊕ κ) : SecOK (sp F o) (sq' F o) := by
  rcases o with s | j
  · exact F.hok s
  · exact F.hokE j

theorem par_or_par_neg_of_crs_zero {u w : V2} (hu : u ≠ 0) (hw : w ≠ 0) (h : crs u w = 0) :
    Par w u ∨ Par w (-u.1, -u.2) := by
  have hdt : dt u w ≠ 0 := fun h2 => hu (eq_zero_of_crs_dt hw h h2)
  rcases lt_or_gt_of_ne hdt with hlt | hgt
  · right
    refine ⟨?_, ?_⟩
    · unfold crs at h ⊢; linarith
    · unfold dt at hlt ⊢; linarith
  · left
    refine ⟨?_, ?_⟩
    · unfold crs at h ⊢; linarith
    · unfold dt at hgt ⊢; linarith

theorem crs_pos_of_par_neg {u w r : V2} (hw : crs u w < 0) (hr : Par r (-w.1, -w.2)) : 0 < crs u r := by
  obtain ⟨c, hc, hcr⟩ := hr.smul
  rw [hcr]
  unfold crs at hw ⊢
  simp only at hw ⊢
  nlinarith [mul_pos hc (neg_pos.mpr hw)]

/-- A tile sector with positive `crs` is a genuine corner of the tile at `H`. -/
theorem corner_vertex (F : ExtFan D H κ) (x : AtV D H) (hc : 0 < crs (F.p x) (F.q x)) : ∃ k, (D.tile x.1).pts k = H := by
  rcases F.hspec x with ⟨k, hk, -⟩ | ⟨-, m', -, -, hq, -⟩
  · exact ⟨k, hk⟩
  · exfalso; rw [hq] at hc; unfold crs at hc; try simp only at hc; nlinarith

end Fan2

set_option maxHeartbeats 1600000 in
/-- **The half-fan lemma.**  Let `F` be the fan at `H` and let the sector at position `j0` be straight; the other `L - 1` sectors are tile corners in order
`c 1, .., c (L-1)`.  The arms of `c 1` (start) and of `c (L-1)` (end) on the boundary line: exactly one has length `a`.  If the number of corners having a vertex of type
`β` or `γ` at `H` is even, then an edge of `Γ_a` starts at `H`. -/
theorem half_fan_edge (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    (hnc : NotComb (slen D 0) (slen D 1) (slen D 2)) (hab : slen D 0 ≠ slen D 1) (hac : slen D 0 ≠ slen D 2)
    {H : Plane} {κ : Type} [Fintype κ] (F : ExtFan D.toRegionDissection H κ) (j0 : ℕ)
    (hstr : sq' F (F.e j0) = (-(sp F (F.e j0)).1, -(sp F (F.e j0)).2))
    (hL : 3 ≤ Fintype.card (AtV D.toRegionDissection H ⊕ κ))
    (hcorn : ∀ m, 1 ≤ m → m < Fintype.card (AtV D.toRegionDissection H ⊕ κ) →
      ∃ x : AtV D.toRegionDissection H, F.e (j0 + m) = Sum.inl x ∧ 0 < crs (F.p x) (F.q x))
    (hxor : ∀ b a : AtV D.toRegionDissection H, F.e (j0 + 1) = Sum.inl b →
      F.e (j0 + (Fintype.card (AtV D.toRegionDissection H ⊕ κ) - 1)) = Sum.inl a →
      ¬ (nsq (F.p b) = slen D 0 ^ 2 ↔ nsq (F.q a) = slen D 0 ^ 2))
    (hpar : (Finset.univ.filter (fun x : AtV D.toRegionDissection H =>
        (Sum.inl x : AtV D.toRegionDissection H ⊕ κ) ≠ F.e j0 ∧ ∃ k : Fin 3, (D.tile x.1).pts k = H ∧ idx x.1 k ≠ 0)).card % 2 = 0) :
    ∃ H', GaEdge D.toRegionDissection (slen D 0) H H' := by
  classical
  set L := Fintype.card (AtV D.toRegionDissection H ⊕ κ) with hLdef
  haveI hne : Nonempty (AtV D.toRegionDissection H) := ⟨(hcorn 1 le_rfl (by omega)).choose⟩
  let c : ℕ → AtV D.toRegionDissection H := fun m =>
    if h : 1 ≤ m ∧ m < L then (hcorn m h.1 h.2).choose else Classical.arbitrary _
  have hc_e : ∀ m, 1 ≤ m → m < L → F.e (j0 + m) = Sum.inl (c m) := by
    intro m h1 h2
    simp only [c, dif_pos (And.intro h1 h2)]
    exact (hcorn m h1 h2).choose_spec.1
  have hc_pos : ∀ m, 1 ≤ m → m < L → 0 < crs (F.p (c m)) (F.q (c m)) := by
    intro m h1 h2
    simp only [c, dif_pos (And.intro h1 h2)]
    exact (hcorn m h1 h2).choose_spec.2
  have hc_inj : ∀ m m', 1 ≤ m → m < L → 1 ≤ m' → m' < L → c m = c m' → m = m' := by
    intro m m' h1 h2 h1' h2' h
    apply e_inj_shift F j0 h2 h2'
    rw [hc_e m h1 h2, hc_e m' h1' h2', h]
  have hdis := tiles_disjoint D.toRegionDissection H F.p F.q F.hloc
  set u := sp F (F.e j0) with hu
  have hu0 : u ≠ 0 := (sectorOK F _).ne_p
  have hadj : ∀ m, 1 ≤ m → m + 1 < L → Par (F.p (c (m + 1))) (F.q (c m)) := by
    intro m h1 h2
    have := F.hP (j0 + m)
    rw [show j0 + m + 1 = j0 + (m + 1) by ring, hc_e (m + 1) (by omega) h2, hc_e m h1 (by omega)] at this
    simpa using this
  have hfirst : Par (F.p (c 1)) (-u.1, -u.2) := by
    have := F.hP j0
    rw [hc_e 1 le_rfl (by omega)] at this
    simp only [Sum.elim_inl] at this
    have h2 : Sum.elim F.q F.qe (F.e j0) = (-u.1, -u.2) := hstr
    rw [h2] at this
    exact this
  have hlast : Par u (F.q (c (L - 1))) := by
    have := F.hP (j0 + (L - 1))
    rw [show j0 + (L - 1) + 1 = j0 + L by omega, F.hper j0, hc_e (L - 1) (by omega) (by omega)] at this
    simpa using this
  have hclosed : ∀ m, 1 ≤ m → m < L → crs u (F.p (c m)) ≤ 0 ∧ crs u (F.q (c m)) ≤ 0 := by
    intro m h1 h2
    refine rays_closed F hstr ?_ (hc_pos m h1 h2)
    intro h
    have h' : F.e (j0 + m) = F.e (j0 + 0) := by rw [hc_e m h1 h2, h]; rfl
    have := e_inj_shift F j0 h2 (by omega : 0 < L) h'
    omega
  have hinner : ∀ m, 1 ≤ m → m + 1 < L → crs u (F.q (c m)) < 0 := by
    intro m h1 h2
    rcases (hclosed m h1 (by omega)).2.lt_or_eq with hlt | heq
    · exact hlt
    · exfalso
      have hw0 : F.q (c m) ≠ 0 := (F.hok (c m)).ne_q
      rcases par_or_par_neg_of_crs_zero hu0 hw0 heq with hp | hp
      · have hP1 : Par (F.q (c (L - 1))) (F.q (c m)) := hlast.symm.trans hp.symm
        have hne1 : c m ≠ c (L - 1) := fun h => by
          have := hc_inj m (L - 1) h1 (by omega) (by omega) (by omega) h
          omega
        exact end_inj' F.p F.q F.hok hdis hne1 hP1
      · have hP2 : Par (F.p (c (m + 1))) (F.p (c 1)) := (hadj m h1 h2).trans (hp.trans hfirst.symm)
        have hne1 : c 1 ≠ c (m + 1) := fun h => by
          have := hc_inj 1 (m + 1) le_rfl (by omega) (by omega) h2 h
          omega
        exact start_inj F.p F.q F.hok hdis hne1 hP2
  have hnb : ∀ m, 1 ≤ m → m + 1 < L → NoBack D.toRegionDissection (F.q (c m)) H := by
    intro m h1 h2
    apply ExtFan.noBack_of_none F
    intro s'
    have hneg : ∀ r : V2, crs u r ≤ 0 → ¬ Par r (neg2 (F.q (c m))) := by
      intro r hr hpar'
      have := crs_pos_of_par_neg (hinner m h1 h2) hpar'
      linarith
    obtain ⟨m', hm', hem'⟩ := e_surj_shift F j0 (Sum.inl s')
    by_cases h0 : m' = 0
    · subst h0
      have hs : F.e j0 = Sum.inl s' := by simpa using hem'
      have hp : u = F.p s' := by simp [hu, hs, sp]
      have hq : F.q s' = (-u.1, -u.2) := by
        have h3 : Sum.elim F.q F.qe (F.e j0) = (-u.1, -u.2) := hstr
        rw [hs] at h3; simpa using h3
      constructor
      · apply hneg; rw [← hp]; unfold crs; ring_nf; exact le_rfl
      · apply hneg; rw [hq]; unfold crs; simp only; ring_nf; exact le_rfl
    · have h1' : 1 ≤ m' := by omega
      have hs' : s' = c m' := by
        have := hc_e m' h1' hm'
        rw [hem'] at this
        exact Sum.inl_injective this
      rw [hs']
      exact ⟨hneg _ (hclosed m' h1' hm').1, hneg _ (hclosed m' h1' hm').2⟩
  have hcd : ∀ m, 1 ≤ m → m < L → ∃ (kk : Fin 3) (fl : Bool), (D.tile (c m).1).pts kk = H ∧
      F.p (c m) = toV2 ((D.tile (c m).1).pts (armP kk fl) - H) ∧ F.q (c m) = toV2 ((D.tile (c m).1).pts (armQ kk fl) - H) :=
    fun m h1 h2 => spec_corner_data (F.hspec (c m)) (corner_vertex F (c m) (hc_pos m h1 h2))
  let P : ℕ → Bool := fun m => decide (nsq (F.p (c m)) = slen D 0 ^ 2)
  let Q : ℕ → Bool := fun m => decide (nsq (F.q (c m)) = slen D 0 ^ 2)
  let f : ℕ → Bool := fun m => decide (∃ k, (D.tile (c m).1).pts k = H ∧ idx (c m).1 k ≠ 0)
  have htile : ∀ m, 1 ≤ m → m ≤ L - 1 → ((f m = false → P m = false ∧ Q m = false) ∧ (f m = true → P m ≠ Q m)) := by
    intro m h1 h2
    obtain ⟨kk, fl, hk, hp, hq⟩ := hcd m h1 (by omega)
    have hb := corner_bits D idx hidx hab hac fl hk hp hq
    have hf : (∃ k, (D.tile (c m).1).pts k = H ∧ idx (c m).1 k ≠ 0) ↔ idx (c m).1 kk ≠ 0 := by
      constructor
      · rintro ⟨k, hk', hne'⟩
        have : k = kk := (D.tile (c m).1).indep.injective (hk'.trans hk.symm)
        rw [← this]; exact hne'
      · intro h; exact ⟨kk, hk, h⟩
    constructor
    · intro hfm
      have hfm' : ¬ (∃ k, (D.tile (c m).1).pts k = H ∧ idx (c m).1 k ≠ 0) := by simpa [f] using hfm
      have h0 : idx (c m).1 kk = 0 := by
        by_contra hh; exact hfm' (hf.mpr hh)
      have := hb.1 h0
      simp [P, Q, this.1, this.2]
    · intro hfm
      have hfm' : ∃ k, (D.tile (c m).1).pts k = H ∧ idx (c m).1 k ≠ 0 := by simpa [f] using hfm
      have h0 := hf.mp hfm'
      have := hb.2 h0
      simp only [P, Q, ne_eq, decide_eq_decide]
      tauto
  have hline : P 1 ≠ Q (L - 1) := by
    have := hxor (c 1) (c (L - 1)) (hc_e 1 le_rfl (by omega)) (hc_e (L - 1) (by omega) (by omega))
    simp only [P, Q, ne_eq, decide_eq_decide]
    exact this
  have hsumeq : (∑ j ∈ Finset.Icc 1 (L - 1), (if f j = true then 1 else 0)) =
      (Finset.univ.filter (fun x : AtV D.toRegionDissection H =>
        (Sum.inl x : AtV D.toRegionDissection H ⊕ κ) ≠ F.e j0 ∧ ∃ k : Fin 3, (D.tile x.1).pts k = H ∧ idx x.1 k ≠ 0)).card := by
    rw [Finset.sum_boole]
    simp only [Nat.cast_id]
    refine Finset.card_nbij' c (fun x => (e_surj_shift F j0 (Sum.inl x)).choose) ?_ ?_ ?_ ?_
    · intro j hj
      simp only [Finset.coe_filter, Finset.mem_Icc, Set.mem_setOf_eq, decide_eq_true_eq] at hj
      obtain ⟨⟨hj1, hj2⟩, hjf⟩ := hj
      have hjL : j < L := by omega
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
      have hjf' : ∃ k, (D.tile (c j).1).pts k = H ∧ idx (c j).1 k ≠ 0 := by simpa [f] using hjf
      refine ⟨?_, hjf'⟩
      rw [← hc_e j hj1 hjL]
      intro h
      have h' : F.e (j0 + j) = F.e (j0 + 0) := h
      have := e_inj_shift F j0 hjL (by omega : 0 < L) h'
      omega
    · intro x hx
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hx
      obtain ⟨hxs, hxf⟩ := hx
      have hsp := (e_surj_shift F j0 (Sum.inl x)).choose_spec
      set m := (e_surj_shift F j0 (Sum.inl x)).choose with hm
      have hmL : m < L := hsp.1
      have hm0 : m ≠ 0 := by
        intro h0; apply hxs; rw [← hsp.2, h0]; rfl
      simp only [Finset.coe_filter, Finset.mem_Icc, Set.mem_setOf_eq]
      refine ⟨⟨by omega, by omega⟩, ?_⟩
      have : c m = x := by
        have := hc_e m (by omega) hmL
        rw [hsp.2] at this; exact (Sum.inl_injective this).symm
      simp only [f, decide_eq_true_eq]
      rw [this]; exact hxf
    · intro j hj
      simp only [Finset.coe_filter, Finset.mem_Icc, Set.mem_setOf_eq] at hj
      have hjL : j < L := by omega
      have hsp := (e_surj_shift F j0 (Sum.inl (c j))).choose_spec
      apply e_inj_shift F j0 hsp.1 hjL
      rw [hsp.2, hc_e j hj.1.1 hjL]
    · intro x hx
      have hsp := (e_surj_shift F j0 (Sum.inl x)).choose_spec
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hx
      obtain ⟨hxs, hxf⟩ := hx
      have hm0 : (e_surj_shift F j0 (Sum.inl x)).choose ≠ 0 := by
        intro h0; apply hxs; rw [← hsp.2, h0]; rfl
      have := hc_e _ (by omega) hsp.1
      rw [hsp.2] at this
      exact (Sum.inl_injective this).symm
  have hpar' : (∑ j ∈ Finset.Icc 1 (L - 1), (if f j = true then 1 else 0)) % 2 = 0 := by
    rw [hsumeq]; exact hpar
  obtain ⟨m, hm1, hm2, hmne⟩ := parity_core (L - 1) (by omega) P Q f htile hline hpar'
  have hcx := hc_pos m hm1 (by omega)
  have hcy := hc_pos (m + 1) (by omega) (by omega)
  refine ga_edge_of_ray D idx hidx hnc F (c m) (c (m + 1)) hcx hcy (hadj m hm1 (by omega)) (hnb m hm1 (by omega)) ?_
  simp only [P, Q, ne_eq, decide_eq_decide] at hmne
  by_cases h1 : nsq (F.q (c m)) = slen D 0 ^ 2
  · left
    refine ⟨h1, fun h2 => hmne ⟨fun _ => h2, fun _ => h1⟩⟩
  · right
    refine ⟨h1, ?_⟩
    by_contra h2
    exact hmne ⟨fun h => absurd h h1, fun h => absurd h h2⟩

end Erdos634.Draft.LaczFormal.RG
