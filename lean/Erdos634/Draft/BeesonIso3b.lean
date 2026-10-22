import Erdos634.Draft.LaczFormalBZL7h7
import Erdos634.Draft.LaczFormalIIcSpoke2

/-!
# Beeson, "Tilings of an isosceles triangle" (arXiv 1206.1974 v7), Sect. 11: the CHORD LAYER, part 1 (fan chain at a side vertex)

NOTE, UNAUDITED.  Credit: Michael Beeson (arXiv 1206.1974 v7, Lemmas 11.8-11.10; arXiv 1206.2229), Laczkovich (DCG 48 (2012), Sect. 4: fans, half-fan lemma,
maximal segments), Beeson-Zhang, Herdt, Zhang.  Formalization debt, not progress on the /goal outcomes.

Lemmas 11.8, 11.9, 11.10 argue about tiles on BOTH sides of a segment (a chord `EF` of the triangle, the ray `PS` of a tile edge).  The minimal geometric notion chosen:
the fan of tile sectors at a vertex `Q` in the relative interior of a side of the polygon, with ONE virtual straight sector (the exterior).  Its tiles form a linear
chain `c 1, ..., c (L-1)` from the ray along the side (direction `pT`) counterclockwise to the ray `-pT`, consecutive sectors share a ray, and the widths add up to `pi`.
* `wd_add`: two consecutive sectors of total width at most `pi` add their widths (`Complex.arg_mul`).
* `OpenChain`, `open_chain`: the chain at a tile vertex `Q` on an open side (fan with `kappa = Unit`, as in `junction_edge`).
* `OpenChain.wd_partial`: the widths of `c 1 .. c m` add up to `wd pT (q (c m))`.
Witness status: the lemmas are proved for every dissection of a convex polygon; no hypothesis beyond a tile vertex on an open side (satisfied e.g. by the 1125-tiling).
-/

open scoped Classical
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ}

/-- The Hermitian product `conj p * q` as a complex number: `wd p q` is its argument. -/
noncomputable def hz (p q : V2) : ℂ := ⟨dt p q, crs p q⟩

theorem wd_eq_arg_hz (p q : V2) : wd p q = Complex.arg (hz p q) := rfl

theorem hz_mul (p q r : V2) : hz p q * hz q r = ((nsq q : ℝ) : ℂ) * hz p r := by
  apply Complex.ext
  · simp only [hz, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]; unfold dt crs nsq; ring
  · simp only [hz, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]; unfold dt crs nsq; ring

theorem hz_ne {p q : V2} (hp : p ≠ 0) (hq : q ≠ 0) (hc : 0 ≤ crs p q) : hz p q ≠ 0 := by
  intro h
  have h1 : dt p q = 0 := congrArg Complex.re h
  have h2 : crs p q = 0 := congrArg Complex.im h
  exact hp (eq_zero_of_crs_dt hq h2 h1)

theorem arg_hz_nonneg {p q : V2} (hc : 0 ≤ crs p q) : 0 ≤ wd p q := by
  rw [wd_eq_arg_hz, Complex.arg_nonneg_iff]; exact hc

/-- Two consecutive sectors `(p,q)`, `(q,r)` with total width at most `pi` have the width of `(p,r)` equal to the sum. -/
theorem wd_add {p q r : V2} (hp : p ≠ 0) (hq : q ≠ 0) (hr : r ≠ 0) (hc1 : 0 ≤ crs p q) (hc2 : 0 ≤ crs q r)
    (h : wd p q + wd q r ≤ Real.pi) : wd p r = wd p q + wd q r := by
  have hn : 0 < nsq q := nsq_pos hq
  have h1 := hz_ne hp hq hc1
  have h2 := hz_ne hq hr hc2
  have hmul : Complex.arg (hz p q * hz q r) = Complex.arg (hz p q) + Complex.arg (hz q r) := by
    apply Complex.arg_mul h1 h2
    constructor
    · have a1 := arg_hz_nonneg hc1
      have a2 := arg_hz_nonneg hc2
      rw [wd_eq_arg_hz] at a1 a2
      linarith [Real.pi_pos]
    · rw [← wd_eq_arg_hz, ← wd_eq_arg_hz]; exact h
  rw [hz_mul, Complex.arg_real_mul _ hn] at hmul
  rw [wd_eq_arg_hz, wd_eq_arg_hz, wd_eq_arg_hz]
  exact hmul

theorem par_self {p : V2} (hp : p ≠ 0) : Par p p := by
  refine ⟨by unfold crs; ring, ?_⟩
  have := nsq_pos hp
  unfold dt nsq at *; nlinarith

/-- The chain of tile sectors at a vertex `Q` of a polygon side (one virtual straight sector `(-pT, pT)`). -/
structure OpenChain (D : RegionDissection N) (Q : Plane) (pT : V2) where
  F : ExtFan D Q Unit
  L : ℕ
  c : ℕ → AtV D Q
  hL2 : 2 ≤ L
  hpe : F.pe () = (-pT.1, -pT.2)
  hqe : F.qe () = pT
  hcrs : ∀ m, 1 ≤ m → m < L → 0 < crs (F.p (c m)) (F.q (c m))
  hadj : ∀ m, 1 ≤ m → m + 1 < L → Par (F.p (c (m + 1))) (F.q (c m))
  hfirst : Par (F.p (c 1)) pT
  hlast : Par (F.q (c (L - 1))) (-pT.1, -pT.2)
  hinj : ∀ m m', 1 ≤ m → m < L → 1 ≤ m' → m' < L → c m = c m' → m = m'
  hsurj : ∀ x : AtV D Q, ∃ m, 1 ≤ m ∧ m < L ∧ c m = x
  hsum : ∑ m ∈ Finset.Ico 1 L, wd (F.p (c m)) (F.q (c m)) = Real.pi

/-- **The chain of tiles at a tile vertex on an open side.** -/
theorem open_chain (D : RegionDissection N) {Q : Plane} (F : ExtFan D Q Unit) {pT : V2} (hpT : pT ≠ 0)
    (hpe : F.pe () = (-pT.1, -pT.2)) (hqe : F.qe () = pT) (hvert : ∃ i k, (D.tile i).pts k = Q) :
    Nonempty (OpenChain D Q pT) := by
  classical
  obtain ⟨i0, k0, hk0⟩ := hvert
  have hmem0 : Q ∈ (D.tile i0).carrier := hk0 ▸ subset_convexHull ℝ _ ⟨k0, rfl⟩
  set s0 : AtV D Q := ⟨i0, hmem0⟩ with hs0
  obtain ⟨j0, hj0, hej0⟩ := F.hsurj (Sum.inr ())
  set L := Fintype.card (AtV D Q ⊕ Unit) with hLdef
  have hLcard : L = Fintype.card (AtV D Q) + 1 := by rw [hLdef, Fintype.card_sum]; simp
  have hAt1 : 1 ≤ Fintype.card (AtV D Q) := Fintype.card_pos_iff.mpr ⟨s0⟩
  have hL2 : 2 ≤ L := by omega
  have hvirt : ∑ j : Unit, wd (F.pe j) (F.qe j) = Real.pi := by
    rw [Fintype.sum_unique]
    show wd (F.pe ()) (F.qe ()) = Real.pi
    rw [hpe, hqe, wd_ext hpT]
  have hreal : ∑ s : AtV D Q, wd (F.p s) (F.q s) = Real.pi := by
    have := F.hsum
    linarith
  have hcorner0 : ∃ k, (D.tile s0.1).pts k = Q := ⟨k0, hk0⟩
  have hcrs : ∀ x : AtV D Q, 0 < crs (F.p x) (F.q x) := by
    intro x
    rcases F.hspec x with ⟨k, hk, -⟩ | ⟨-, m', -, -, hq, -⟩
    · exact crs_pos_of_corner (F.hok x) (F.hspec x) ⟨k, hk⟩
    · exfalso
      have hxw : wd (F.p x) (F.q x) = Real.pi := by rw [hq]; exact wd_straight (F.hok x).ne_p
      have hx_ne : x ≠ s0 := by
        intro h
        subst h
        have := crs_pos_of_corner (F.hok s0) (F.hspec s0) hcorner0
        rw [hq] at this; unfold crs at this; simp at this; linarith
      have hpair : ∑ s ∈ ({x, s0} : Finset (AtV D Q)), wd (F.p s) (F.q s) ≤ ∑ s : AtV D Q, wd (F.p s) (F.q s) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun s _ _ => (wd_pos (F.hok s)).le)
      rw [Finset.sum_pair hx_ne, hxw, hreal] at hpair
      have := wd_pos (F.hok s0)
      linarith
  have hcorn : ∀ m, 1 ≤ m → m < L → ∃ x : AtV D Q, F.e (j0 + m) = Sum.inl x := by
    intro m h1 h2
    rcases hm : F.e (j0 + m) with x | j
    · exact ⟨x, rfl⟩
    · exfalso
      have h' : F.e (j0 + m) = F.e (j0 + 0) := by rw [hm, add_zero, hej0]
      have := e_inj_shift F j0 h2 (by omega : 0 < L) h'
      omega
  let c : ℕ → AtV D Q := fun m => if h : 1 ≤ m ∧ m < L then (hcorn m h.1 h.2).choose else s0
  have hc_e : ∀ m, 1 ≤ m → m < L → F.e (j0 + m) = Sum.inl (c m) := by
    intro m h1 h2
    simp only [c, dif_pos (And.intro h1 h2)]
    exact (hcorn m h1 h2).choose_spec
  have hpT0 := hpT
  have hinj_aux : ∀ m m', 1 ≤ m → m < L → 1 ≤ m' → m' < L → c m = c m' → m = m' := by
    intro m m' h1 h2 h1' h2' h
    apply e_inj_shift F j0 h2 h2'
    rw [hc_e m h1 h2, hc_e m' h1' h2', h]
  have hsurj_aux : ∀ x : AtV D Q, ∃ m, 1 ≤ m ∧ m < L ∧ c m = x := by
    intro x
    obtain ⟨m, hm, hem⟩ := e_surj_shift F j0 (Sum.inl x)
    have hm1 : 1 ≤ m := by
      rcases Nat.eq_zero_or_pos m with h | h
      · subst h
        rw [add_zero, hej0] at hem
        exact absurd hem (by simp)
      · exact h
    refine ⟨m, hm1, hm, ?_⟩
    have := hc_e m hm1 hm
    rw [hem] at this
    exact (Sum.inl_injective this).symm
  refine ⟨{ F := F, L := L, c := c, hL2 := hL2, hpe := hpe, hqe := hqe,
            hcrs := fun m h1 h2 => ?_, hadj := fun m h1 h2 => ?_, hfirst := ?_, hlast := ?_,
            hinj := fun m m' h1 h2 h1' h2' h => ?_, hsurj := fun x => ?_, hsum := ?_ }⟩
  · exact hcrs (c m)
  · have := F.hP (j0 + m)
    rw [show j0 + m + 1 = j0 + (m + 1) by ring, hc_e (m + 1) (by omega) h2, hc_e m h1 (by omega)] at this
    simpa using this
  · have := F.hP j0
    rw [hc_e 1 le_rfl (by omega)] at this
    simp only [Sum.elim_inl] at this
    rw [hej0] at this
    simp only [Sum.elim_inr] at this
    rw [hqe] at this
    exact this
  · have := F.hP (j0 + (L - 1))
    have hE : F.e (j0 + L) = Sum.inr () := (F.hper j0).trans hej0
    rw [show j0 + (L - 1) + 1 = j0 + L by omega, hE, hc_e (L - 1) (by omega) (by omega)] at this
    simp only [Sum.elim_inl, Sum.elim_inr] at this
    rw [hpe] at this
    exact this.symm.trans (par_neg_neg (par_self hpT0))
  · exact hinj_aux m m' h1 h2 h1' h2' h
  · exact hsurj_aux x
  · -- the widths add up to pi
    rw [← hreal]
    refine Finset.sum_bij (fun m _ => c m) (fun m _ => Finset.mem_univ _) ?_ ?_ (fun m _ => rfl)
    · intro m hm m' hm' h
      simp only [Finset.mem_Ico] at hm hm'
      exact (hinj_aux m m' hm.1 hm.2 hm'.1 hm'.2 h)
    · intro x _
      obtain ⟨m, hm1, hm2, hmx⟩ := hsurj_aux x
      exact ⟨m, Finset.mem_Ico.mpr ⟨hm1, hm2⟩, hmx⟩

end Erdos634.Draft.LaczFormal.RG
