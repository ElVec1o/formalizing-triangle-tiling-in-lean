import Erdos634.Draft.LaczFormalW2Tri
import Erdos634.Draft.LaczFormalJunctionChord

/-!
# Rule W2, interface lemma I4: the wedge at `G₁`

Erdős #634, band program, rule W2 (`PROOF_W2.md`).  Credit: AI assistant (item 3, band program), Laczkovich (DCG 48
(2012), Sect. 4: the fan of angular domains at a vertex), Beeson–Roșu, Beeson, Paliy.  UNAUDITED.

`w2_wedge_G1`: `G₁` is a point of the open left leg `(A_p, A_r)` of the target, `T₀ = (A_p, P₁, G₁)` presents `γ`
at `G₁`, `T' = (P₁, G₁, G₂)` presents `α` at `G₁` (the three vectors `A_p − G₁`, `P₁ − G₁`, `G₂ − G₁` turn
counterclockwise and `G₂ − G₁` is clockwise of the leg).  Then the tiles through `G₁` are exactly `T₀, T', U'` with
`U'` presenting `β`, and `U'` has an edge along the ray `G₁ → G₂` and an edge along the leg, of lengths `{a, c}` in
some order.  Proof: boundary figure `{α,β,γ}` (`boundary_three_tiles`), the side fan (`extFan_side'`), the
successor lemma `ExtFan.fill_side`.
-/

namespace Erdos634.LaczJunction.Walk

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.LaczJunction Erdos634.LaczJunction.Grammar
open Erdos634.Draft.LaczFormal.Graph Erdos634.Geometry.Dissection Erdos634.VertexFigureReal

variable {N : ℕ}

theorem w2_fin3_succ : ∀ k m n : Fin 3, k ≠ m → k ≠ n → m ≠ n →
    (k + 1 = m ∧ k + 2 = n) ∨ (k + 1 = n ∧ k + 2 = m) := by decide

theorem w2_fin3_cov : ∀ x y z : Fin 3, x ≠ y → x ≠ z → y ≠ z → ∀ m : Fin 3, m = x ∨ m = y ∨ m = z := by
  decide

theorem smul_of_par_toV2 {x y : Plane} (h : Par (toV2 x) (toV2 y)) : ∃ c : ℝ, 0 < c ∧ x = c • y := by
  obtain ⟨c, hc, he⟩ := h.smul
  refine ⟨c, hc, ?_⟩
  have h0 : x 0 = c * y 0 := congrArg Prod.fst he
  have h1 : x 1 = c * y 1 := congrArg Prod.snd he
  ext i; fin_cases i
  · simpa using h0
  · simpa using h1

theorem par_toV2_smul {c : ℝ} (hc : 0 < c) {y : Plane} (hy : y ≠ 0) : Par (toV2 (c • y)) (toV2 y) := by
  refine smul_par hc (toV2_ne_zero hy) ?_
  simp [toV2]

theorem toV2_neg (x : Plane) : toV2 (-x) = (-(toV2 x).1, -(toV2 x).2) := by
  simp [toV2]

theorem par_self' {v : V2} (hv : v ≠ 0) : Par v v := by
  refine smul_par one_pos hv ?_
  ext <;> simp

theorem neg2_toV2 (x : Plane) : ((-(toV2 x).1, -(toV2 x).2) : V2) = toV2 (-x) := by
  simp [toV2]

theorem crs_eq_cross (u v : Plane) : crs (toV2 u) (toV2 v) = cross u v := rfl

/-- **I4.** -/
theorem w2_wedge_G1 {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ} {p q r : Fin 3}
    (S : BandSetup D e f α β γ p q r)
    (hori : 0 < cross (D.target.pts q - D.target.pts p) (D.target.pts r - D.target.pts p))
    {G1 G2 P1 : Plane} (hG1 : G1 ∈ openSegment ℝ (D.target.pts p) (D.target.pts r))
    (i0 i' : Fin N) (ka kb kc : Fin 3) (hab : ka ≠ kb) (hac : ka ≠ kc) (hbc : kb ≠ kc)
    (hka : (D.tile i0).pts ka = D.target.pts p) (hkb : (D.tile i0).pts kb = P1)
    (hkc : (D.tile i0).pts kc = G1) (hγ0 : (D.tile i0).localAngle G1 = γ)
    (ja jb jc : Fin 3) (jab : ja ≠ jb) (jac : ja ≠ jc) (jbc : jb ≠ jc)
    (hja : (D.tile i').pts ja = P1) (hjb : (D.tile i').pts jb = G1) (hjc : (D.tile i').pts jc = G2)
    (hα' : (D.tile i').localAngle G1 = α)
    (hc1 : 0 < cross (D.target.pts p - G1) (P1 - G1)) (hc2 : 0 < cross (P1 - G1) (G2 - G1))
    (hc3 : 0 < cross (G2 - G1) (D.target.pts r - D.target.pts p)) :
    ∃ iU : Fin N, iU ≠ i0 ∧ iU ≠ i' ∧ (D.tile iU).localAngle G1 = β ∧
      (∀ j, G1 ∈ (D.tile j).carrier → j = i0 ∨ j = i' ∨ j = iU) ∧
      ∃ ku kb' kc' : Fin 3, ku ≠ kb' ∧ ku ≠ kc' ∧ kb' ≠ kc' ∧ (D.tile iU).pts ku = G1 ∧
        (∃ s : ℝ, 0 < s ∧ (D.tile iU).pts kb' = G1 + s • (G2 - G1)) ∧
        (∃ s : ℝ, 0 < s ∧ (D.tile iU).pts kc' = G1 + s • (D.target.pts r - D.target.pts p)) ∧
        ((dist G1 ((D.tile iU).pts kb') = (ta e f : ℝ) ∧ dist G1 ((D.tile iU).pts kc') = (tc e f : ℝ)) ∨
         (dist G1 ((D.tile iU).pts kb') = (tc e f : ℝ) ∧ dist G1 ((D.tile iU).pts kc') = (ta e f : ℝ))) ∧
        0 < cross ((D.tile iU).pts kb' - G1) ((D.tile iU).pts kc' - G1) := by
  classical
  set T := D.target with hT
  set LC := T.pts p with hLC
  set RC := T.pts q with hRC
  set AP := T.pts r with hAP
  obtain ⟨hfront, hnv⟩ := side_frontier T S.hpr S.hpq S.hqr.symm hG1
  obtain ⟨b0, hb00, hb01, cp, cr, cq⟩ := coords_side T S.hpr S.hpq S.hqr.symm hG1
  -- G1 = LC + b (AP - LC)
  obtain ⟨b, hb0, hGv⟩ : ∃ b : ℝ, 0 < b ∧ G1 - LC = b • (AP - LC) := by
    obtain ⟨a', b', ha', hb', hab', hG⟩ := hG1
    refine ⟨b', hb', ?_⟩
    rw [← hG]
    have : a' = 1 - b' := by linarith
    rw [this]; module
  have hpos : ∀ j, j ≠ q → 0 < T.basis.coord j G1 := by
    intro j hj
    rcases w2_fin3_cov p r q S.hpr S.hpq S.hqr.symm j with rfl | rfl | rfl
    · rw [cp]; linarith
    · rw [cr]; exact hb00
    · exact absurd rfl hj
  have hvert : ∃ i k, (D.tile i).pts k = G1 := ⟨i0, kc, hkc⟩
  obtain ⟨F, pT, hpe, hqe, hTgt, hdir, hcr⟩ :=
    extFan_side' D.toDissection G1 q cq hpos hvert
  -- the direction of the side
  have hsucc := w2_fin3_succ q p r S.hpq.symm S.hqr S.hpr
  have hcrAP : cross (AP - LC) (RC - G1) < 0 := by
    have : cross (AP - LC) (RC - G1) = - cross (RC - LC) (AP - LC) := by
      have e1 : RC - G1 = (RC - LC) - (G1 - LC) := by abel
      rw [e1, hGv, cross_sub_right, cross_smul_right, Erdos634.Geometry.cross_self, cross_swap (AP - LC) (RC - LC)]
      ring
    rw [this]; linarith
  have hpT : pT = toV2 (LC - AP) := by
    have hg : (D.target.pts (q + 2) - D.target.pts (q + 1) = AP - LC ∧
        D.target.pts (q + 1) - D.target.pts (q + 2) = LC - AP) ∨
        (D.target.pts (q + 2) - D.target.pts (q + 1) = LC - AP ∧
        D.target.pts (q + 1) - D.target.pts (q + 2) = AP - LC) := by
      rcases hsucc with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · left; exact ⟨by rw [h1, h2], by rw [h1, h2]⟩
      · right; exact ⟨by rw [h1, h2], by rw [h1, h2]⟩
    rcases hdir with h | h <;> rcases hg with ⟨g1, g2⟩ | ⟨g1, g2⟩
    · exfalso; rw [h, g1] at hcr; rw [crs_eq_cross] at hcr; linarith
    · rw [h, g1]
    · rw [h, g2]
    · exfalso; rw [h, g2] at hcr; rw [crs_eq_cross] at hcr; linarith
  have hLG : LC - G1 = b • (LC - AP) := by
    have : LC - G1 = -(G1 - LC) := by abel
    rw [this, hGv]; module
  have hAPLC : AP - LC ≠ 0 := by
    intro h
    have : cross (RC - LC) (AP - LC) = 0 := by rw [h]; simp [cross]
    linarith
  have hLCAP : LC - AP ≠ 0 := by
    intro h; apply hAPLC; have : AP - LC = -(LC - AP) := by abel
    rw [this, h]; simp
  -- tiles through G1
  have hi0mem : G1 ∈ (D.tile i0).carrier := by
    rw [← hkc]; exact subset_convexHull ℝ _ (Set.mem_range_self _)
  have hi'mem : G1 ∈ (D.tile i').carrier := by
    rw [← hjb]; exact subset_convexHull ℝ _ (Set.mem_range_self _)
  obtain ⟨iU, hUang, hU0, hU1, h01, hall⟩ := boundary_three_tiles S hfront hnv i0 i' hγ0 hα'
  have hiUmem : G1 ∈ (D.tile iU).carrier := mem_of_angle_ne_zero _ (by rw [hUang]; exact S.hβ0.ne')
  set s0 : AtV D.toDissection G1 := ⟨i0, hi0mem⟩ with hs0
  set s1 : AtV D.toDissection G1 := ⟨i', hi'mem⟩ with hs1
  set u : AtV D.toDissection G1 := ⟨iU, hiUmem⟩ with hu
  -- arms of s0 and s1
  have ha0 : F.p s0 = toV2 (LC - G1) ∧ F.q s0 = toV2 (P1 - G1) := by
    have := arms_of_cross (F.hok s0) (F.hspec s0) (kk := kc) (k1 := ka) (k2 := kb) hkc hac hbc hab
      (by rw [hka, hkb]; exact hc1)
    rw [hka, hkb] at this; exact this
  have ha1 : F.p s1 = toV2 (P1 - G1) ∧ F.q s1 = toV2 (G2 - G1) := by
    have := arms_of_cross (F.hok s1) (F.hspec s1) (kk := jb) (k1 := ja) (k2 := jc) hjb jab jbc.symm jac
      (by rw [hja, hjc]; exact hc2)
    rw [hja, hjc] at this; exact this
  have hP1G : P1 - G1 ≠ 0 := by
    intro h; rw [h] at hc2; simp [cross] at hc2
  have hG2G : G2 - G1 ≠ 0 := by
    intro h; rw [h] at hc2; simp [cross] at hc2
  have hall' : ∀ x : AtV D.toDissection G1, x = s0 ∨ x = s1 ∨ x = u := by
    intro x
    rcases hall x.1 x.2 with h | h | h
    · left; exact Subtype.ext h
    · right; left; exact Subtype.ext h
    · right; right; exact Subtype.ext h
  have hstart : Par (F.p s0) (F.qe ()) := by
    rw [ha0.1, hqe, hpT, hLG]
    exact par_toV2_smul hb0 hLCAP
  have h10 : Par (F.p s1) (F.q s0) := by
    rw [ha1.1, ha0.2]; exact par_self' (toV2_ne_zero hP1G)
  have hpe' : F.pe () = toV2 (AP - LC) := by
    rw [hpe, hpT, neg2_toV2]; congr 1; abel
  have hnot : ¬ Par (F.pe ()) (F.q s1) := by
    rintro ⟨hx, -⟩
    rw [hpe', ha1.2] at hx
    have : cross (AP - LC) (G2 - G1) = 0 := hx
    rw [cross_swap] at this; linarith
  have hns0u : s0 ≠ u := by
    intro h; apply hU0; have := congrArg Subtype.val h; simpa [hs0, hu] using this.symm
  have hns1u : s1 ≠ u := by
    intro h; apply hU1; have := congrArg Subtype.val h; simpa [hs1, hu] using this.symm
  obtain ⟨hpu, hpeu⟩ := F.fill_side hall' hns0u hns1u hstart h10 hnot
  -- the vertex of U' at G1
  have hbne : β ≠ 0 := S.hβ0.ne'
  have hbpi : β ≠ Real.pi := by intro h; have := S.hrel; have := S.hα0; linarith [Real.pi_pos]
  have hb2pi : β ≠ 2 * Real.pi := by intro h; have := S.hrel; have := S.hα0; linarith [Real.pi_pos]
  obtain ⟨kv, hkv⟩ := exists_vertex_of_angle (D.tile iU) hUang hbne hbpi hb2pi
  obtain ⟨kk', fl, hk', hpU, hqU⟩ := spec_corner_data (F.hspec u) ⟨kv, hkv⟩
  rw [hpU, ha1.2] at hpu
  rw [hqU, hpe'] at hpeu
  obtain ⟨s, hs, hse⟩ := smul_of_par_toV2 hpu
  obtain ⟨s', hs', hse'⟩ := smul_of_par_toV2 hpeu.symm
  have hang : (D.tile iU).localAngle ((D.tile iU).pts kk') = β := by rw [hk']; exact hUang
  have hne1 := armP_ne kk' fl
  have hne2 := armQ_ne kk' fl
  have hne3 := armPQ_ne kk' fl
  refine ⟨iU, hU0, hU1, hUang, hall, kk', armP kk' fl, armQ kk' fl, hne1.symm, hne2.symm, hne3, hk',
    ⟨s, hs, ?_⟩, ⟨s', hs', ?_⟩, ?_, ?_⟩
  · rw [← hse]; abel
  · rw [← hse']; abel
  · have hadj := tile_adj_B S iU kk' (armP kk' fl) (armQ kk' fl) hne1.symm hne2.symm hne3 hang
    rw [S.hsa, S.hsc] at hadj
    rw [hk'] at hadj
    rcases hadj with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left; exact ⟨h1, h2⟩
    · right; exact ⟨h1, h2⟩
  · rw [hse, hse', cross_smul_left, cross_smul_right]
    exact mul_pos hs (mul_pos hs' hc3)

end Erdos634.LaczJunction.Walk
