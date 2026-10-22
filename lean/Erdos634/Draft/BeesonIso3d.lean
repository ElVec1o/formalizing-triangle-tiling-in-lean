import Erdos634.Draft.BeesonIso3c

/-!
# Beeson, "Tilings of an isosceles triangle" (arXiv 1206.1974 v7), Sect. 11: the CHORD LAYER, part 3 (the chain at a side vertex)

NOTE, UNAUDITED.  Credit: Michael Beeson (arXiv 1206.1974 v7, Lemma 11.8; arXiv 1206.2229), Laczkovich (DCG 48 (2012), Sect. 4), Beeson-Zhang, Herdt, Zhang.
Formalization debt, not progress on the /goal outcomes.

* `OpenChain.wd_partial`: the widths of `c 1 .. c m` add up to `wd pT (q (c m))`.
* `OpenChain.split_q`, `OpenChain.split_p`: a ray `d` strictly inside the half-plane (`0 < crs pT d`) that is the end ray of one chain sector is the start ray of the next
  (and conversely): both sides of a chord have tiles at a vertex of the side.
* `sector_angle`: the width of a corner sector is the model angle of the corner label.
* `north_arith`: two non-empty families of corner labels whose model angles add up to `2 alpha` consist of one label `alpha` each (irrationality of `alpha / pi`).
-/

open scoped Classical
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ}

theorem par_par_crs {a u v : V2} (h1 : Par a u) (h2 : Par a v) : crs u v = 0 := by
  obtain ⟨c1, hc1, e1⟩ := h1.smul
  obtain ⟨c2, hc2, e2⟩ := h2.smul
  -- a = c1 u = c2 v  hmm: Par a u gives a = c1 * u
  have h1' : a.1 = c1 * u.1 := congrArg Prod.fst e1
  have h2' : a.2 = c1 * u.2 := congrArg Prod.snd e1
  have h3' : a.1 = c2 * v.1 := congrArg Prod.fst e2
  have h4' : a.2 = c2 * v.2 := congrArg Prod.snd e2
  have : c1 * c2 * crs u v = 0 := by
    unfold crs
    have : c1 * c2 * (u.1 * v.2 - u.2 * v.1) = (c1 * u.1) * (c2 * v.2) - (c1 * u.2) * (c2 * v.1) := by ring
    rw [this, ← h1', ← h2', ← h3', ← h4']; ring
  rcases mul_eq_zero.mp this with h | h
  · exact absurd h (mul_pos hc1 hc2).ne'
  · exact h

theorem wd_neg_neg (p q : V2) : wd (-p.1, -p.2) (-q.1, -q.2) = wd p q := by
  unfold wd
  have : (⟨dt (-p.1, -p.2) (-q.1, -q.2), crs (-p.1, -p.2) (-q.1, -q.2)⟩ : ℂ) = ⟨dt p q, crs p q⟩ := by
    apply Complex.ext <;> simp [dt, crs]
  rw [this]

namespace OpenChain

variable {D : RegionDissection N} {Q : Plane} {pT : V2} (C : OpenChain D Q pT)

theorem wd_nonneg_all (m : ℕ) (hm1 : 1 ≤ m) (hmL : m < C.L) : 0 < wd (C.F.p (C.c m)) (C.F.q (C.c m)) :=
  wd_pos (C.F.hok _)

/-- The widths of `c 1 .. c m` add up to `wd pT (q (c m))`. -/
theorem wd_partial (hpT : pT ≠ 0) : ∀ m, 1 ≤ m → m < C.L →
    wd pT (C.F.q (C.c m)) = ∑ j ∈ Finset.Ico 1 (m + 1), wd (C.F.p (C.c j)) (C.F.q (C.c j)) := by
  intro m hm1 hmL
  induction m, hm1 using Nat.le_induction with
  | base =>
    have : Finset.Ico 1 (1 + 1) = {1} := by decide
    rw [this, Finset.sum_singleton]
    exact (wd_par_left C.hfirst _).symm
  | succ m hm ih =>
    have ih' := ih (by omega)
    have hq1 : C.F.q (C.c m) ≠ 0 := (C.F.hok _).ne_q
    have hq2 : C.F.q (C.c (m + 1)) ≠ 0 := (C.F.hok _).ne_q
    have hsub : ∑ j ∈ Finset.Ico 1 (m + 1 + 1), wd (C.F.p (C.c j)) (C.F.q (C.c j)) ≤ Real.pi := by
      rw [← C.hsum]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ico_subset_Ico_right (by omega))
        (fun j _ _ => (wd_pos (C.F.hok _)).le)
    have hsplit : ∑ j ∈ Finset.Ico 1 (m + 1 + 1), wd (C.F.p (C.c j)) (C.F.q (C.c j)) =
        ∑ j ∈ Finset.Ico 1 (m + 1), wd (C.F.p (C.c j)) (C.F.q (C.c j)) + wd (C.F.p (C.c (m + 1))) (C.F.q (C.c (m + 1))) :=
      Finset.sum_Ico_succ_top (by omega) _
    have hadj := C.hadj m hm (by omega)
    have hw2 : wd (C.F.q (C.c m)) (C.F.q (C.c (m + 1))) = wd (C.F.p (C.c (m + 1))) (C.F.q (C.c (m + 1))) :=
      (wd_par_left hadj _).symm
    have hc1 : 0 ≤ crs pT (C.F.q (C.c m)) := by
      have : 0 ≤ wd pT (C.F.q (C.c m)) := by
        rw [ih']
        exact Finset.sum_nonneg (fun j _ => (wd_pos (C.F.hok _)).le)
      rw [wd_eq_arg_hz, Complex.arg_nonneg_iff] at this
      exact this
    have hc2 : 0 ≤ crs (C.F.q (C.c m)) (C.F.q (C.c (m + 1))) :=
      (crs_pos_par_left hadj (C.hcrs (m + 1) (by omega) hmL)).le
    have := wd_add hpT hq1 hq2 hc1 hc2 (by rw [hw2, ih', ← hsplit]; exact hsub)
    rw [this, hw2, ih', hsplit]

/-- Both sides of a ray `d` strictly inside the half-plane: an end ray of a chain sector is the start ray of the next sector. -/
theorem split_q (hpT : pT ≠ 0) {d : V2} (hd : 0 < crs pT d) {x : AtV D Q} (hx : Par (C.F.q x) d) :
    ∃ m, 1 ≤ m ∧ m + 1 < C.L ∧ C.c m = x ∧ Par (C.F.p (C.c (m + 1))) d := by
  obtain ⟨m, hm1, hmL, hmx⟩ := C.hsurj x
  have hlt : m + 1 < C.L := by
    by_contra hh
    have hm : m = C.L - 1 := by omega
    have h1 : Par (C.F.q (C.c m)) (-pT.1, -pT.2) := by rw [hm]; exact C.hlast
    rw [hmx] at h1
    have := par_par_crs h1 hx
    -- crs (-pT) d = 0
    unfold crs at this hd
    try simp only at this hd
    nlinarith
  refine ⟨m, hm1, hlt, hmx, ?_⟩
  have := C.hadj m hm1 hlt
  rw [hmx] at this
  exact this.trans hx

theorem split_p (hpT : pT ≠ 0) {d : V2} (hd : 0 < crs pT d) {x : AtV D Q} (hx : Par (C.F.p x) d) :
    ∃ m, 2 ≤ m ∧ m < C.L ∧ C.c m = x ∧ Par (C.F.q (C.c (m - 1))) d := by
  obtain ⟨m, hm1, hmL, hmx⟩ := C.hsurj x
  have hge : 2 ≤ m := by
    by_contra hh
    have hm : m = 1 := by omega
    have h1 : Par (C.F.p (C.c m)) pT := by rw [hm]; exact C.hfirst
    rw [hmx] at h1
    have := par_par_crs h1 hx
    unfold crs at this hd
    try simp only at this hd
    nlinarith
  refine ⟨m, hge, hmL, hmx, ?_⟩
  have h := C.hadj (m - 1) (by omega) (by omega)
  rw [show m - 1 + 1 = m by omega, hmx] at h
  -- h : Par (p x) (q (c (m-1))), hx : Par (p x) d
  -- so q (c (m-1)) ~ p x ~ d
  exact h.symm.trans hx

end OpenChain

/-- The width of a corner sector is the model angle of the corner label. -/
theorem sector_angle (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3))
    (hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v) {Q : Plane} {κ : Type} [Fintype κ]
    (F : ExtFan D.toRegionDissection Q κ) (x : AtV D.toRegionDissection Q) {k : Fin 3} (hk : (D.tile x.1).pts k = Q) :
    wd (F.p x) (F.q x) = D.model.angleAt (idx x.1 k) := by
  have e := Tri.localAngle_vertex (D.tile x.1) k
  rw [hk] at e
  have e2 : (D.tile x.1).angleAt k = cornerAngle ((D.tile x.1).pts (k + 1)) Q ((D.tile x.1).pts (k + 2)) := by
    unfold Tri.angleAt; rw [hk]
  rw [F.hwd x, hidxA, e, e2]

end Erdos634.Draft.LaczFormal.RG
