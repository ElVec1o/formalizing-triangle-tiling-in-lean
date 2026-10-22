-- Draft/LaczFormalIIcWN18.lean -- Laczkovich (DCG 48 (2012)), Sect. 6.2, step (a) (first half, "each cycle of Gamma_kite is a SIMPLE polygon"):
--   `gkite_edges_meet`: two distinct edges of Gamma_kite meet only in common endpoints;
--   `gkite_cycle_simple`: a closed chain C_0 -> C_1 -> ... of Gamma_kite edges with distinct vertices has length >= 3 and is a `SimplePolyP` polygon of the plane.
-- NOT here (second half of (a)): the angles alpha+beta / alpha+beta+2 gamma of the cycle at its vertices.  NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.2), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcWN17
import Erdos634.Draft.LaczFormalIIcWN13

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement Erdos634.CertCoord Filter Topology

namespace Erdos634.Draft.LaczFormal.RG

variable {N : ℕ}

theorem gkite_edges_meet [NeZero N] (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) {X Y X' Y' : Plane}
    (h : GKite D idx X Y) (h' : GKite D idx X' Y') (hne : ¬ (X = X' ∧ Y = Y')) {z : Plane}
    (hz : z ∈ segment ℝ X Y) (hz' : z ∈ segment ℝ X' Y') : (z = X ∨ z = Y) ∧ (z = X' ∨ z = Y') := by
  have key : ∀ {A B A' B' : Plane}, GKite D idx A B → GKite D idx A' B' → ¬ (A = A' ∧ B = B') →
      ∀ {w : Plane}, w ∈ segment ℝ A B → w ∈ segment ℝ A' B' → (w = A ∨ w = B) := by
    intro A B A' B' g g' gne w hw hw'
    by_contra hcon
    push Not at hcon
    rw [segment_eq_image'] at hw
    obtain ⟨t, ⟨ht0, ht1⟩, rfl⟩ := hw
    have ht0' : 0 < t := by
      rcases ht0.lt_or_eq with h0 | h0
      · exact h0
      · exfalso; apply hcon.1; rw [← h0]; simp
    have ht1' : t < 1 := by
      rcases ht1.lt_or_eq with h0 | h0
      · exact h0
      · exfalso; apply hcon.2; rw [h0]; ext m; simp
    exact gkite_open_not_meet D idx g g' gne ht0' ht1' hw'
  exact ⟨key h h' hne hz hz', key h' h (fun hh => hne ⟨hh.1.symm, hh.2.symm⟩) hz' hz⟩

theorem gkite_ne [NeZero N] (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) {X Y : Plane}
    (h : GKite D idx X Y) : X ≠ Y := by
  obtain ⟨i, j, d, kk, f, kk2, f2, hij, hi, hj, hk, hf, hl1, hl2, hk2, hf2, hl3, hl4⟩ := h
  obtain ⟨kk', f', g', hk', hf', hfk', -, -, hpar, -⟩ := hi
  intro hXY
  have hinj := (D.tile i).indep.injective
  have : f' = kk' := hinj (hf'.trans (hXY.symm.trans hk'.symm))
  exact hfk' this


theorem gkite_not_symm [NeZero N] (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) {X Y : Plane}
    (h : GKite D idx X Y) (h2 : GKite D idx Y X) : False := by
  obtain ⟨i, j, d, kk, f, kk2, f2, hij, hi, hj, hk, hf, hl1, hl2, hk2, hf2, hl3, hl4⟩ := h
  obtain ⟨i2, j2, d2, kka, fa, kkb, fb, hij2, hi2, hj2, hka, hfa, hl1a, hl2a, hkb, hfb, hl3b, hl4b⟩ := h2
  have hd0 : d ≠ 0 := by
    obtain ⟨kk, f, g, hk, hf, hfk, hgk, hgf, hpar, -⟩ := hi
    exact hpar.ne_right
  have hpar1 : Par (toV2 (Y - X)) d := by
    obtain ⟨kk, f, g, hk, hf, hfk, hgk, hgf, hpar, -⟩ := hi
    exact hpar
  have hpar2 : Par (toV2 (Y - X)) (neg2 d2) := by
    obtain ⟨kk, f, g, hk, hf, hfk, hgk, hgf, hpar, -⟩ := hj2
    exact hpar
  have hp : Par d (neg2 d2) := hpar1.symm.trans hpar2
  obtain ⟨r1, hr1, h1⟩ := halfdisc (D.tile i) hi (t := 1 / 2) (by norm_num) (by norm_num)
  obtain ⟨r2, hr2, h2'⟩ := halfdisc (D.tile j2) hj2 (t := 1 / 2) (by norm_num) (by norm_num)
  set z : Plane := X + (1 / 2 : ℝ) • (Y - X) with hz
  obtain ⟨ε, hε0, hεd⟩ := exists_eps z (mkPt (-d.2) d.1) (lt_min hr1 hr2)
  have hrot : 0 < crs d (-d.2, d.1) := by
    have : crs d (-d.2, d.1) = d.1 ^ 2 + d.2 ^ 2 := by unfold crs; ring
    rw [this]; exact v2_sq_pos hd0
  have hrot2 : 0 < crs (neg2 d2) (-d.2, d.1) := by
    have e : crs (neg2 d2) (-d.2, d.1) = dt d (neg2 d2) := by unfold crs dt neg2; ring
    rw [e]; exact hp.2
  have wi : z + ε • mkPt (-d.2) d.1 ∈ interior (D.tile i).carrier := by
    refine h1 _ (lt_of_lt_of_le hεd (min_le_left _ _)) ?_
    rw [crs_shift d z ε (-d.2, d.1)]; exact mul_pos hε0 hrot
  have wj : z + ε • mkPt (-d.2) d.1 ∈ interior (D.tile j2).carrier := by
    refine h2' _ (lt_of_lt_of_le hεd (min_le_right _ _)) ?_
    rw [crs_shift (neg2 d2) z ε (-d.2, d.1)]; exact mul_pos hε0 hrot2
  have hij3 : i = j2 := by
    by_contra hh
    exact Set.disjoint_left.1 (D.interiors_disjoint hh) wi wj
  subst hij3
  have hinj := (D.tile i).indep.injective
  have : kk = kkb := hinj (by rw [hk, hkb])
  rw [this] at hl1
  rw [hl1] at hl3b
  exact absurd hl3b (by decide)

theorem gkite_cycle_simple [NeZero N] (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) {m : ℕ} [NeZero m]
    (C : Fin m → Plane) (hC : ∀ k : Fin m, GKite D idx (C k) (C (k + 1))) (hinj : Function.Injective C) :
    3 ≤ m ∧ Erdos634.Draft.LaczFormal.WN.SimplePolyP C := by
  have hm : 3 ≤ m := by
    by_contra hlt
    have hm0 : m ≠ 0 := NeZero.ne m
    have : m = 1 ∨ m = 2 := by omega
    rcases this with rfl | rfl
    · exact gkite_ne D idx (hC 0) (by congr 1)
    · have h0 := hC 0
      have h1 := hC 1
      have e0 : (0 : Fin 2) + 1 = 1 := by decide
      have e1 : (1 : Fin 2) + 1 = 0 := by decide
      rw [e0] at h0
      rw [e1] at h1
      exact gkite_not_symm D idx h0 h1
  refine ⟨hm, ?_⟩
  intro i j hij z hz
  have hne : ¬ (C i = C j ∧ C (i + 1) = C (j + 1)) := fun hh => hij (hinj hh.1)
  exact gkite_edges_meet D idx (hC i) (hC j) hne hz.1 hz.2

#print axioms gkite_cycle_simple

end Erdos634.Draft.LaczFormal.RG
