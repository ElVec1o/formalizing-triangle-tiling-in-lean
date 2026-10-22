import Erdos634.Draft.BeesonIso4b

/-!
# Beeson, "Tilings of an isosceles triangle" (arXiv 1206.1974 v7), Lemma 11.10, "at least three tiles on the base": the two-tile case is impossible

NOTE, UNAUDITED.  Credit: Michael Beeson (arXiv 1206.1974 v7, Lemma 11.10), Laczkovich (DCG 48 (2012), Sect. 4), Beeson-Zhang, Herdt, Zhang.
Formalization debt, not progress on the /goal outcomes.

Printed: "Suppose only two tiles are supported [by AC].  Those two tiles have their alpha angles at A and C ... Tile 1 has its beta angle at P, Tile 2 its gamma angle at P, so the remaining angle at P
is alpha ... Tile 3 with its alpha angle at P.  Then Tile 3 has its c side either against Tile 1 or Tile 2, but that is impossible since those edges are of length a and terminate at the boundary, and c > a."
(The print says the corner tiles have "their a edges ... end at P"; the edges on AC are b or c, the edges `PS`, `PR` that Tile 3 sits against are the `a` sides.)
`two_tile_contra`: a base walk `A -> P -> C` with two steps (corner angles `alpha` at `A`, `C`, `c > a`) is impossible.  Proof: the chain at `P` has exactly three tiles (`chain_counts`: one beta,
`#alpha + 2 #gamma = 3`, and the corner tiles have beta/gamma at `P`), the middle one has label `alpha` at `P`; its arms are `b` and `c`, along the sides `PS`, `PR` of the corner tiles (length `a`, ending on `AB`,
`BC`): `ray_bound` gives arm `<= a`, but one arm is `c > a`.
Witness status: the hypotheses (an `alpha` corner at both ends, the tile `c > a`, a base walk) hold for the 1125-tiling; the conclusion `False` is for the two-step shape, which does not occur there
(the base of the 1125-tiling is covered by more tiles; this is the lemma).
-/

open scoped Classical
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ} [NeZero M]

theorem fin3_third_eq : ∀ a b c x : Fin 3, a ≠ b → a ≠ c → b ≠ c → x ≠ a → x ≠ c → x = b := by
  intro a b c x; fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases x <;> simp

theorem eq_of_toV2_sub {X Y Q : Plane} (h : toV2 (X - Q) = toV2 (Y - Q)) : X = Y := by
  have := toV2_inj' h
  exact sub_left_injective this

/-- Corner data of a sector with positive cross. -/
theorem corner_arm_vertices {D : RegionDissection N} {Q : Plane} {κ : Type} [Fintype κ] (F : ExtFan D Q κ) (x : AtV D Q)
    (h : 0 < crs (F.p x) (F.q x)) :
    ∃ kk : Fin 3, (D.tile x.1).pts kk = Q ∧ ∃ fl : Bool, F.p x = toV2 ((D.tile x.1).pts (armP kk fl) - Q) ∧
      F.q x = toV2 ((D.tile x.1).pts (armQ kk fl) - Q) := by
  obtain ⟨k, hk⟩ := corner_of_crs_pos F x h
  obtain ⟨kk, fl, hk', hp, hq⟩ := spec_corner_data (F.hspec x) ⟨k, hk⟩
  exact ⟨kk, hk', fl, hp, hq⟩

theorem chain_three (L : ℕ) (l : ℕ → Fin 3)
    (hn1 : ((Finset.Ico 1 L).filter (fun j => l j = 1)).card = 1)
    (hn02 : ((Finset.Ico 1 L).filter (fun j => l j = 0)).card + 2 * ((Finset.Ico 1 L).filter (fun j => l j = 2)).card = 3)
    (hL : L - 1 = ((Finset.Ico 1 L).filter (fun j => l j = 0)).card + ((Finset.Ico 1 L).filter (fun j => l j = 1)).card +
        ((Finset.Ico 1 L).filter (fun j => l j = 2)).card)
    (h1 : l 1 ≠ 0) (h3 : l (L - 1) ≠ 0) (hL2 : 2 ≤ L) : L = 4 ∧ l 2 = 0 := by
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hn1
  have hc2 : ((Finset.Ico 1 L).filter (fun j => l j = 2)).card ≤ 1 := by omega
  have hone : ∀ x y, x ∈ Finset.Ico 1 L → y ∈ Finset.Ico 1 L → l x = 1 → l y = 1 → x = y := by
    intro x y hx hy hlx hly
    have hx' : x ∈ (Finset.Ico 1 L).filter (fun j => l j = 1) := Finset.mem_filter.mpr ⟨hx, hlx⟩
    have hy' : y ∈ (Finset.Ico 1 L).filter (fun j => l j = 1) := Finset.mem_filter.mpr ⟨hy, hly⟩
    rw [ha] at hx' hy'
    simp at hx' hy'
    omega
  have htwo : ∀ x y, x ∈ Finset.Ico 1 L → y ∈ Finset.Ico 1 L → l x = 2 → l y = 2 → x = y := by
    intro x y hx hy hlx hly
    have hx' : x ∈ (Finset.Ico 1 L).filter (fun j => l j = 2) := Finset.mem_filter.mpr ⟨hx, hlx⟩
    have hy' : y ∈ (Finset.Ico 1 L).filter (fun j => l j = 2) := Finset.mem_filter.mpr ⟨hy, hly⟩
    exact Finset.card_le_one.mp hc2 x hx' y hy'
  have hm3 : 3 ≤ L - 1 := by omega
  have hmem1 : 1 ∈ Finset.Ico 1 L := by simp; omega
  have hmemm : L - 1 ∈ Finset.Ico 1 L := by simp; omega
  have hne : (1 : ℕ) ≠ L - 1 := by omega
  have h2pos : 1 ≤ ((Finset.Ico 1 L).filter (fun j => l j = 2)).card := by
    apply Finset.card_pos.mpr
    -- one of l 1, l (L-1) is 2
    have c1 : l 1 = 1 ∨ l 1 = 2 := by revert h1; generalize l 1 = x; revert x; decide
    have c3 : l (L - 1) = 1 ∨ l (L - 1) = 2 := by revert h3; generalize l (L - 1) = x; revert x; decide
    rcases c1 with c1 | c1
    · rcases c3 with c3 | c3
      · exact absurd (hone 1 (L - 1) hmem1 hmemm c1 c3) hne
      · exact ⟨L - 1, Finset.mem_filter.mpr ⟨hmemm, c3⟩⟩
    · exact ⟨1, Finset.mem_filter.mpr ⟨hmem1, c1⟩⟩
  have hc2' : ((Finset.Ico 1 L).filter (fun j => l j = 2)).card = 1 := by omega
  have hL4 : L = 4 := by omega
  refine ⟨hL4, ?_⟩
  subst hL4
  have hmem2 : 2 ∈ Finset.Ico 1 4 := by simp
  have c1 : l 1 = 1 ∨ l 1 = 2 := by revert h1; generalize l 1 = x; revert x; decide
  have c3 : l 3 = 1 ∨ l 3 = 2 := by
    have : (4 : ℕ) - 1 = 3 := rfl
    rw [this] at h3
    revert h3; generalize l 3 = x; revert x; decide
  by_contra hl2
  have c2 : l 2 = 1 ∨ l 2 = 2 := by revert hl2; generalize l 2 = x; revert x; decide
  have m1 : 1 ∈ Finset.Ico 1 4 := by simp
  have m3 : 3 ∈ Finset.Ico 1 4 := by simp
  rcases c2 with c2 | c2
  · rcases c1 with c1 | c1
    · have := hone 1 2 m1 hmem2 c1 c2; omega
    · rcases c3 with c3 | c3
      · have := hone 3 2 m3 hmem2 c3 c2; omega
      · have := htwo 1 3 m1 m3 c1 c3; omega
  · rcases c1 with c1 | c1
    · rcases c3 with c3 | c3
      · have := hone 1 3 m1 m3 c1 c3; omega
      · have := htwo 3 2 m3 hmem2 c3 c2; omega
    · have := htwo 1 2 m1 hmem2 c1 c2; omega

theorem c_zero_of_par {P : ConvPoly M} (j : Fin M) {Y : Plane} (h : Par (toV2 (Y - P.v j)) (toV2 (P.e j))) : P.c j Y = 0 := by
  obtain ⟨c, hc, he⟩ := h.smul
  have hcc : P.c j Y = crs (toV2 (P.e j)) (toV2 (Y - P.v j)) := rfl
  rw [hcc, he]; unfold crs; simp only; ring

theorem c_zero_of_par_in {P : ConvPoly M} (j : Fin M) {X : Plane} (h : Par (toV2 (P.v (j + 1) - X)) (toV2 (P.e j))) : P.c j X = 0 := by
  obtain ⟨c, hc, he⟩ := h.smul
  have hcc : P.c j X = crs (toV2 (P.e j)) (toV2 (X - P.v j)) := rfl
  have hd : toV2 (X - P.v j) = (-(toV2 (P.v (j + 1) - X)).1 + (toV2 (P.e j)).1, -(toV2 (P.v (j + 1) - X)).2 + (toV2 (P.e j)).2) := by
    unfold toV2 ConvPoly.e; ext <;> simp
  rw [hcc, hd, he]; unfold crs; simp only; ring

theorem two_tile_contra (C : CongruentRegionDissection N) [HasFansC C.toRegionDissection] (P : ConvPoly M) (hreg : C.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((C.tile i).pts k) ((C.tile i).pts k') = dist (C.model.pts (idx i k)) (C.model.pts (idx i k')))
    (hidxA : ∀ i v, C.model.angleAt (idx i v) = (C.tile i).angleAt v)
    (hβ : C.model.angleAt 1 = Real.pi - 3 * C.model.angleAt 0) (hγ : C.model.angleAt 2 = 2 * C.model.angleAt 0)
    (hα : ¬ ∃ r : ℚ, C.model.angleAt 0 = (r : ℝ) * Real.pi) (hac : slen C 0 < slen C 2)
    (k : Fin M) (hi0 : P.angle (k + 1) = C.model.angleAt 0) (hi1 : P.angle (k + 1 + 1) = C.model.angleAt 0)
    {j1 j2 : Fin N} {Pm : Plane}
    (hS1 : TriStep (C.tile j1) (toV2 (P.e (k + 1))) (P.v (k + 1)) Pm) (hS2 : TriStep (C.tile j2) (toV2 (P.e (k + 1))) Pm (P.v (k + 1 + 1)))
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (hPm : Pm = (1 - t) • P.v (k + 1) + t • P.v (k + 1 + 1)) : False := by
  have hvPm : ∃ j kk, (C.tile j).pts kk = Pm := by
    obtain ⟨kk, f, g, hk, hf, -⟩ := hS2
    exact ⟨j2, kk, hk⟩
  -- the outgoing step at C and the incoming step at A
  obtain ⟨Lo, Wo⟩ := side_walk_exists_poly C.toRegionDissection P hreg (k + 1 + 1)
  obtain ⟨eo, Lo', -, heo, hSo⟩ := walkT_head_h10 Wo (walk_ne_nil _ P _ Wo)
  rw [heo] at hSo
  obtain ⟨Li, Wi⟩ := side_walk_exists_poly C.toRegionDissection P hreg k
  obtain ⟨ji, Ui, -, hSi⟩ := walkT_last Wi (walk_ne_nil _ P _ Wi)
  -- corner tiles
  obtain ⟨hjA, kA0, kA1, kA2, dA10, dA20, dA21, pA0, pA1, pA2, lA0⟩ :=
    corner_tile_vertices C P hreg idx hidxA hβ hγ hα k hi0 hS1 hSi
  obtain ⟨hjC, kC0, kC1, kC2, dC10, dC20, dC21, pC0, pC1, pC2, lC0⟩ :=
    corner_tile_vertices C P hreg idx hidxA hβ hγ hα (k + 1) hi1 hSo hS2
  have hjC' : eo.1 = j2 := hjC
  rw [hjC'] at pC0 pC1 pC2 lC0 hSo
  -- chain at Pm
  obtain ⟨pT, hpd, ⟨Ch⟩⟩ := chain_at C.toRegionDissection P hreg (k + 1) ht0 ht1 hPm hvPm
  have hpT : pT ≠ 0 := hpd.ne_left
  obtain ⟨s2, hs2j, hs2p, hs2c, hs2e⟩ := step_start_sector Ch.F hS2
  obtain ⟨s1, hs1j, hs1q, hs1c, hs1e⟩ := step_end_sector Ch.F hS1
  have hc1 : s2 = Ch.c 1 := Ch.first_eq hs2c (hs2p.trans hpd.symm)
  have hc3 : s1 = Ch.c (Ch.L - 1) := Ch.last_eq (hs1q.trans (par_neg_neg hpd.symm))
  obtain ⟨l, kc, hmem, hn1, hn02, hL⟩ := chain_counts C idx hidxA hβ hγ hα Ch
  have hL2 := Ch.hL2
  have hge3 : 4 ≤ Ch.L := by omega
  -- labels of c 1 and c (L-1) are not 0
  have hl1 : l 1 ≠ 0 := by
    have h := hmem 1 le_rfl (by omega)
    have hj : (Ch.c 1).1 = j2 := by rw [← hc1]; exact hs2j
    rw [hj] at h
    obtain ⟨hk1, hl⟩ := h
    have : kc 1 = kC2 := (C.tile j2).indep.injective (hk1.trans pC2.symm)
    rw [this] at hl
    intro h0
    rw [← hl] at h0
    exact dC20 ((idx j2).injective (h0.trans lC0.symm))
  have hl3 : l (Ch.L - 1) ≠ 0 := by
    have h := hmem (Ch.L - 1) (by omega) (by omega)
    have hj : (Ch.c (Ch.L - 1)).1 = j1 := by rw [← hc3]; exact hs1j
    rw [hj] at h
    obtain ⟨hk1, hl⟩ := h
    have : kc (Ch.L - 1) = kA1 := (C.tile j1).indep.injective (hk1.trans pA1.symm)
    rw [this] at hl
    intro h0
    rw [← hl] at h0
    exact dA10 ((idx j1).injective (h0.trans lA0.symm))
  obtain ⟨hL4, hl2⟩ := chain_three Ch.L l hn1 hn02 hL hl1 hl3 hL2
  have hc3' : s1 = Ch.c 3 := by rw [hc3]; congr 1; omega
  have hcr1 := Ch.hcrs 1 (by omega) (by omega)
  have hcr2 := Ch.hcrs 2 (by omega) (by omega)
  have hcr3 := Ch.hcrs 3 (by omega) (by omega)
  have hadj1 := Ch.hadj 1 le_rfl (by omega)
  have hadj2 := Ch.hadj 2 (by omega) (by omega)
  -- the middle tile
  obtain ⟨kk, hkk, fl, hp2, hq2⟩ := corner_arm_vertices Ch.F (Ch.c 2) hcr2
  have hmem2 := hmem 2 (by omega) (by omega)
  have hkk' : kk = kc 2 := (C.tile (Ch.c 2).1).indep.injective (hkk.trans hmem2.1.symm)
  have hid0 : idx (Ch.c 2).1 kk = 0 := by rw [hkk', hmem2.2, hl2]
  -- the east tile j2: its sector s2 = c 1
  obtain ⟨kkb, hkb, flb, hpb, hqb⟩ := corner_arm_vertices Ch.F s2 hs2c
  rw [hs2j] at hkb hpb hqb
  have hkb2 : kkb = kC2 := (C.tile j2).indep.injective (hkb.trans pC2.symm)
  have harmP : (C.tile j2).pts (armP kkb flb) = P.v (k + 1 + 1) := by
    have h1 : toV2 ((C.tile j2).pts (armP kkb flb) - Pm) = toV2 (P.v (k + 1 + 1) - Pm) := by
      rw [← hpb, hs2e]
    exact eq_of_toV2_sub h1
  have harmP' : armP kkb flb = kC0 := (C.tile j2).indep.injective (harmP.trans pC0.symm)
  have harmQ : armQ kkb flb = kC1 := by
    refine fin3_third_eq kC0 kC1 kC2 (armQ kkb flb) (Ne.symm dC10) (Ne.symm dC20) (Ne.symm dC21) ?_ ?_
    · rw [← harmP']; exact Ne.symm (armPQ_ne kkb flb)
    · rw [← hkb2]; exact armQ_ne kkb flb
  -- R = third vertex of the east tile, on the line of the outgoing side
  have hRline : P.c (k + 1 + 1) ((C.tile j2).pts kC1) = 0 := by
    apply c_zero_of_par
    rw [pC1]
    obtain ⟨-, -, -, -, -, -, -, -, hpar, -⟩ := id hSo
    exact hpar
  have hqs2 : Ch.F.q s2 = toV2 ((C.tile j2).pts kC1 - Pm) := by rw [hqb, harmQ]
  -- the west tile j1: its sector s1 = c 3
  obtain ⟨kka, hka, fla, hpa, hqa⟩ := corner_arm_vertices Ch.F s1 hs1c
  rw [hs1j] at hka hpa hqa
  have hka1 : kka = kA1 := (C.tile j1).indep.injective (hka.trans pA1.symm)
  have harmQa : (C.tile j1).pts (armQ kka fla) = P.v (k + 1) := by
    have h1 : toV2 ((C.tile j1).pts (armQ kka fla) - Pm) = toV2 (P.v (k + 1) - Pm) := by
      rw [← hqa, hs1e]
    exact eq_of_toV2_sub h1
  have harmQa' : armQ kka fla = kA0 := (C.tile j1).indep.injective (harmQa.trans pA0.symm)
  have harmPa : armP kka fla = kA2 := by
    refine fin3_third_eq kA0 kA2 kA1 (armP kka fla) (Ne.symm dA20) (Ne.symm dA10) dA21 ?_ ?_
    · rw [← harmQa']; exact armPQ_ne kka fla
    · rw [← hka1]; exact armP_ne kka fla
  have hSline : P.c k ((C.tile j1).pts kA2) = 0 := by
    apply c_zero_of_par_in
    rw [pA2]
    obtain ⟨-, -, -, -, -, -, -, -, hpar, -⟩ := id hSi
    exact hpar
  have hps1 : Ch.F.p s1 = toV2 ((C.tile j1).pts kA2 - Pm) := by rw [hpa, harmPa]
  -- bounds on the arms of the middle tile
  have hQe : 0 < P.c (k + 1 + 1) Pm := c_pos_next P (k + 1) ht1 hPm
  have hQw : 0 < P.c k Pm := by
    have := c_pos_prev P (k + 1) ht0 hPm
    rwa [add_sub_cancel_right] at this
  -- east arm: p (c 2) is parallel to q (c 1) = q s2 = R - Pm
  have hpar_e : Par (toV2 ((C.tile (Ch.c 2).1).pts (armP kk fl) - Pm)) (toV2 ((C.tile j2).pts kC1 - Pm)) := by
    rw [← hp2, ← hqs2, hc1]; exact hadj1
  obtain ⟨lam, hlam, hZe⟩ := hpar_e.smul
  obtain ⟨hlam1, hdistE⟩ := ray_bound P (k + 1 + 1) hQe hRline (tile_in_carrier C.toRegionDissection P hreg rfl) hlam hZe
  -- west arm: q (c 2) is parallel to p (c 3) = p s1 = S - Pm
  have hpar_w : Par (toV2 ((C.tile (Ch.c 2).1).pts (armQ kk fl) - Pm)) (toV2 ((C.tile j1).pts kA2 - Pm)) := by
    rw [← hq2, ← hps1, hc3']; exact hadj2.symm
  obtain ⟨mu, hmu, hZe'⟩ := hpar_w.smul
  obtain ⟨hmu1, hdistW⟩ := ray_bound P k hQw hSline (tile_in_carrier C.toRegionDissection P hreg rfl) hmu hZe'
  -- lengths
  have hRd : dist ((C.tile j2).pts kC1) Pm = slen C 0 := by
    rw [dist_comm, ← pC2]
    have := tile_dist_third C idx hidx j2 (u := kC2) (v := kC1) (w := kC0) (Ne.symm dC21) (Ne.symm dC20) (Ne.symm dC10)
    rw [this, lC0]
  have hSd : dist ((C.tile j1).pts kA2) Pm = slen C 0 := by
    rw [dist_comm, ← pA1]
    have := tile_dist_third C idx hidx j1 (u := kA1) (v := kA2) (w := kA0) dA21 (Ne.symm dA10) (Ne.symm dA20)
    rw [this, lA0]
  set j3 := (Ch.c 2).1 with hj3
  have hdE : dist ((C.tile j3).pts kk) ((C.tile j3).pts (armP kk fl)) = slen C (idx j3 (armQ kk fl)) :=
    tile_dist_third C idx hidx j3 (armP_ne kk fl) (armQ_ne kk fl) (Ne.symm (armPQ_ne kk fl))
  have hdW : dist ((C.tile j3).pts kk) ((C.tile j3).pts (armQ kk fl)) = slen C (idx j3 (armP kk fl)) :=
    tile_dist_third C idx hidx j3 (armQ_ne kk fl) (armP_ne kk fl) (armPQ_ne kk fl)
  rw [hkk] at hdE hdW
  have hE1 : slen C (idx j3 (armQ kk fl)) ≤ slen C 0 := by
    rw [← hdE, dist_comm, hdistE, ← hRd]
    exact mul_le_of_le_one_left dist_nonneg hlam1
  have hW1 : slen C (idx j3 (armP kk fl)) ≤ slen C 0 := by
    rw [← hdW, dist_comm, hdistW, ← hSd]
    exact mul_le_of_le_one_left dist_nonneg hmu1
  -- one of the arms of the label-alpha corner has length c
  have hP0 : idx j3 (armP kk fl) ≠ 0 := fun h => armP_ne kk fl ((idx j3).injective (h.trans hid0.symm))
  have hQ0 : idx j3 (armQ kk fl) ≠ 0 := fun h => armQ_ne kk fl ((idx j3).injective (h.trans hid0.symm))
  have hPQ : idx j3 (armP kk fl) ≠ idx j3 (armQ kk fl) := fun h => armPQ_ne kk fl ((idx j3).injective h)
  have h2 : idx j3 (armP kk fl) = 2 ∨ idx j3 (armQ kk fl) = 2 := by
    revert hP0 hQ0 hPQ; generalize idx j3 (armP kk fl) = x; generalize idx j3 (armQ kk fl) = y; revert x y; decide
  rcases h2 with h2 | h2
  · rw [h2] at hW1; linarith
  · rw [h2] at hE1; linarith

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.chain_three
#print axioms Erdos634.Draft.LaczFormal.RG.two_tile_contra
