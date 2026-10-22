-- Draft/LaczFormalRGCorner.lean -- S4 of PLAN_THM21: the fan at a CORNER of the polygon: the tiles at the corner form a chain `c 1, .., c n` between the two virtual sectors, the first starts along the
-- outgoing edge and the last ends along the incoming edge; inner rays are starts of maximal segments (the target cone contains no line).
-- UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 4, proof of Lemma 4.3 (iii) and Lemma 9.1), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalRGChain
import Erdos634.Draft.LaczFormalRGBdy5

open scoped Classical
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ} [NeZero M]

theorem crs_mul_nsq (a b w : V2) : crs a b * nsq w = crs a w * dt w b + dt a w * crs w b := by
  unfold crs dt nsq; ring

/-- A cone with `crs pT qT > 0` contains no line. -/
theorem cone_no_line {pT qT z : V2} (hcr : 0 < crs pT qT) (h1 : inCone pT qT z) (h2 : inCone pT qT (-z.1, -z.2)) : z = 0 := by
  obtain ⟨a1, a2⟩ := h1
  obtain ⟨b1, b2⟩ := h2
  have c1 : crs pT z = 0 := by unfold crs at a1 b1 ⊢; simp only at b1; linarith
  have c2 : crs z qT = 0 := by unfold crs at a2 b2 ⊢; simp only at b2; linarith
  have := crs_mul_nsq pT qT z
  rw [c1, c2] at this
  have hn : nsq z = 0 := by
    have : crs pT qT * nsq z = 0 := by rw [this]; ring
    exact (mul_eq_zero.mp this).resolve_left hcr.ne'
  by_contra hz
  exact (nsq_pos hz).ne' hn

theorem tile_ray_mem {D : RegionDissection N} {V : Plane} {κ : Type} [Fintype κ] (F : ExtFan D V κ) (s : AtV D V) :
    F.p s ∈ F.Tgt ∧ F.q s ∈ F.Tgt := by
  have hok := F.hok s
  have hc : 0 ≤ crs (F.p s) (F.q s) := by rcases hok with h | ⟨h, -⟩ <;> linarith
  constructor
  · exact F.tile_cone_sub s ⟨by unfold crs; ring_nf; exact le_rfl, hc⟩
  · exact F.tile_cone_sub s ⟨hc, by unfold crs; ring_nf; exact le_rfl⟩

/-- At a corner fan (target cone `inCone pT qT` without a line) every tile ray starts a maximal segment: `NoBack`. -/
theorem noBack_corner {D : RegionDissection N} {V : Plane} (F : ExtFan D V Bool) {pT qT : V2} (hcr : 0 < crs pT qT)
    (hT : F.Tgt = {z | inCone pT qT z}) {w : V2} (hw : w ∈ F.Tgt) (hw0 : w ≠ 0) : NoBack D w V := by
  apply ExtFan.noBack_of_none F
  intro s
  have key : ∀ r : V2, r ∈ F.Tgt → ¬ Par r (neg2 w) := by
    intro r hr hpar
    obtain ⟨c, hc, hcr'⟩ := hpar.smul
    have hmw : neg2 w ∈ F.Tgt := F.Tgt_inv hc (hcr' ▸ hr)
    rw [hT] at hw hmw
    exact hw0 (cone_no_line hcr hw hmw)
  exact ⟨key _ (tile_ray_mem F s).1, key _ (tile_ray_mem F s).2⟩

set_option maxHeartbeats 1600000 in
/-- **The tiles at a corner form a chain** between the two virtual sectors. -/
theorem corner_chain {D : RegionDissection N} {V : Plane} (F : ExtFan D V Bool) {pT qT : V2} (hcr : 0 < crs pT qT)
    (h1 : F.pe true = (-qT.1, -qT.2)) (h2 : F.qe true = pT) (h3 : F.pe false = qT) (h4 : F.qe false = (-qT.1, -qT.2))
    (hT : F.Tgt = {z | inCone pT qT z}) (hAt : 0 < Fintype.card (AtV D V)) :
    ∃ (c : ℕ → AtV D V), Par (F.p (c 1)) pT ∧ Par qT (F.q (c (Fintype.card (AtV D V)))) ∧
      (∀ l, 1 ≤ l → l < Fintype.card (AtV D V) → Par (F.p (c (l + 1))) (F.q (c l))) ∧
      (∀ x : AtV D V, ∃ l, 1 ≤ l ∧ l ≤ Fintype.card (AtV D V) ∧ c l = x) ∧
      (∀ l l', 1 ≤ l → l ≤ Fintype.card (AtV D V) → 1 ≤ l' → l' ≤ Fintype.card (AtV D V) → c l = c l' → l = l') := by
  classical
  have hqT : qT ≠ 0 := by intro h; rw [h] at hcr; unfold crs at hcr; simp at hcr
  set n := Fintype.card (AtV D V) with hn
  set L := Fintype.card (AtV D V ⊕ Bool) with hL
  have hLn : L = n + 2 := by rw [hL, Fintype.card_sum]; simp [hn]
  obtain ⟨j0, hj0, hej0⟩ := F.hsurj (Sum.inr true)
  have hqTmem : qT ∈ F.Tgt := by
    rw [hT]
    show inCone pT qT qT
    exact ⟨hcr.le, by unfold crs; ring_nf; exact le_rfl⟩
  -- Claim A: the position of `inr false`
  have hA : ∀ m, 1 ≤ m → m < L → F.e (j0 + m) = Sum.inr false → m = L - 1 := by
    intro m hm1 hmL hmf
    by_contra hne
    have hP0 := F.hP (j0 + m)
    rw [hmf] at hP0
    simp only [Sum.elim_inr] at hP0
    rw [h4] at hP0
    rcases hnx : F.e (j0 + m + 1) with s | b
    · rw [hnx] at hP0
      simp only [Sum.elim_inl] at hP0
      obtain ⟨c, hc, hcs⟩ := hP0.smul
      have hmem : (-qT.1, -qT.2) ∈ F.Tgt := F.Tgt_inv hc (hcs ▸ (tile_ray_mem F s).1)
      rw [hT] at hmem hqTmem
      exact hqT (cone_no_line hcr hqTmem hmem)
    · rw [hnx] at hP0
      cases b
      · have h5 : F.e (j0 + (m + 1)) = F.e (j0 + m) := by rw [← add_assoc, hnx, hmf]
        have := e_inj_shift F j0 (by omega) hmL h5
        omega
      · have h5 : F.e (j0 + (m + 1)) = F.e (j0 + 0) := by
          rw [← add_assoc, hnx]; show _ = F.e j0; rw [hej0]
        have := e_inj_shift F j0 (by omega) (by omega) h5
        omega
  obtain ⟨mf, hmf, hemf⟩ := e_surj_shift F j0 (Sum.inr false)
  have hmfpos : 1 ≤ mf := by
    by_contra h0
    have : mf = 0 := by omega
    subst this
    have : F.e (j0 + 0) = Sum.inr true := hej0
    rw [this] at hemf
    simp at hemf
  have hmfL : mf = L - 1 := hA mf hmfpos hmf hemf
  -- Claim B: positions 1 .. n are tiles
  have hB : ∀ m, 1 ≤ m → m ≤ n → ∃ x : AtV D V, F.e (j0 + m) = Sum.inl x := by
    intro m hm1 hmn
    rcases hx : F.e (j0 + m) with x | b
    · exact ⟨x, rfl⟩
    · exfalso
      cases b
      · have := hA m hm1 (by omega) hx
        omega
      · have h5 : F.e (j0 + m) = F.e (j0 + 0) := by rw [hx]; show _ = F.e j0; rw [hej0]
        have := e_inj_shift F j0 (by omega) (by omega) h5
        omega
  haveI : Nonempty (AtV D V) := Fintype.card_pos_iff.mp hAt
  let c : ℕ → AtV D V := fun m => if h : 1 ≤ m ∧ m ≤ n then (hB m h.1 h.2).choose else Classical.arbitrary _
  have hc_e : ∀ m, 1 ≤ m → m ≤ n → F.e (j0 + m) = Sum.inl (c m) := by
    intro m h1 h2
    simp only [c, dif_pos (And.intro h1 h2)]
    exact (hB m h1 h2).choose_spec
  refine ⟨c, ?_, ?_, ?_, ?_, ?_⟩
  · have := F.hP j0
    rw [hej0, hc_e 1 le_rfl (by omega)] at this
    simpa [h2] using this
  · have := F.hP (j0 + n)
    have e1 : j0 + n + 1 = j0 + (L - 1) := by omega
    have hLast : F.e (j0 + (L - 1)) = Sum.inr false := by rw [← hmfL]; exact hemf
    rw [e1, hLast, hc_e n (by omega) le_rfl] at this
    simpa [h3] using this
  · intro l hl1 hl2
    have := F.hP (j0 + l)
    rw [show j0 + l + 1 = j0 + (l + 1) by ring, hc_e (l + 1) (by omega) (by omega), hc_e l hl1 (by omega)] at this
    simpa using this
  · intro x
    obtain ⟨m, hm, hem⟩ := e_surj_shift F j0 (Sum.inl x)
    have hm0 : m ≠ 0 := by
      rintro rfl
      have : F.e (j0 + 0) = Sum.inr true := hej0
      rw [this] at hem; simp at hem
    have hmL : m ≠ L - 1 := by
      intro h
      rw [h] at hem
      rw [← hmfL, hemf] at hem
      simp at hem
    refine ⟨m, by omega, by omega, ?_⟩
    have := hc_e m (by omega) (by omega)
    rw [hem] at this
    exact (Sum.inl_injective this).symm
  · intro l l' hl1 hl2 hl1' hl2' h
    apply e_inj_shift F j0 (by omega) (by omega)
    rw [hc_e l hl1 hl2, hc_e l' hl1' hl2', h]

/-- Sum over the chain positions equals the sum over the tiles. -/
theorem chain_sum {D : RegionDissection N} {V : Plane} (c : ℕ → AtV D V)
    (hsurj : ∀ x : AtV D V, ∃ l, 1 ≤ l ∧ l ≤ Fintype.card (AtV D V) ∧ c l = x)
    (hinj : ∀ l l', 1 ≤ l → l ≤ Fintype.card (AtV D V) → 1 ≤ l' → l' ≤ Fintype.card (AtV D V) → c l = c l' → l = l')
    (g : AtV D V → ℕ) : ∑ l ∈ Finset.Icc 1 (Fintype.card (AtV D V)), g (c l) = ∑ x : AtV D V, g x := by
  classical
  refine Finset.sum_bij (fun l _ => c l) (fun l _ => Finset.mem_univ _) ?_ ?_ (fun l _ => rfl)
  · intro l hl l' hl' h
    rw [Finset.mem_Icc] at hl hl'
    exact hinj l l' hl.1 hl.2 hl'.1 hl'.2 h
  · intro x _
    obtain ⟨l, h1, h2, hl⟩ := hsurj x
    exact ⟨l, Finset.mem_Icc.mpr ⟨h1, h2⟩, hl⟩

set_option maxHeartbeats 3200000 in
/-- **Every angle of the polygon is `π/2`** (`γ = π/2`, regular corner counts): at a polygon vertex the corner angles sum to the polygon angle, and `(c + r)(π/2)` with
`0 < c + r < 2` forces `c + r = 1`.  (No irrationality hypothesis.) -/
theorem polygon_angle_pi2 (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (idx : Fin N → Equiv.Perm (Fin 3))
    (hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v) (hγ : D.model.angleAt 2 = Real.pi / 2)
    (hregc : ∀ X, cnt D idx X 0 = cnt D idx X 1) (P : ConvPoly M) (hreg : D.region = P.carrier) (k : Fin M) :
    P.angle (k + 1) = Real.pi / 2 := by
  classical
  set V := P.v (k + 1) with hVdef
  have hvert : ∃ j k', (D.tile j).pts k' = V := poly_vertex_is_tile_vertex D.toRegionDissection P hreg (k + 1)
  obtain ⟨pT, qT, F, hpd, hqd, hcr, h1, h2, h3, h4, h5⟩ := fan_vertex_poly D.toRegionDissection P hreg k hvert
  have hqT : qT ≠ 0 := by intro h; rw [h] at hcr; unfold crs at hcr; simp at hcr
  have hpT : pT ≠ 0 := hpd.ne_left
  obtain ⟨i0, k0, hk0⟩ := hvert
  have hmem0 : V ∈ (D.tile i0).carrier := hk0 ▸ subset_convexHull ℝ _ ⟨k0, rfl⟩
  have hAt : 0 < Fintype.card (AtV D.toRegionDissection V) := Fintype.card_pos_iff.mpr ⟨⟨i0, hmem0⟩⟩
  obtain ⟨c, hc1, hcn, hadj, hsurjc, hinjc⟩ := corner_chain F hcr h1 h2 h3 h4 h5 hAt
  set n := Fintype.card (AtV D.toRegionDissection V) with hn
  have hsumT := corner_tile_sum D.toRegionDissection F hcr h1 h2 h3 h4
  have hwlt := wd_lt_pi_of_crs_pos hcr
  have hwpos := wd_pos (Or.inl hcr : SecOK pT qT)
  -- no straight tile
  have hnostr : ∀ x : AtV D.toRegionDissection V, ∃ k, (D.tile x.1).pts k = V := by
    intro x
    rcases F.hspec x with ⟨k, hk, -⟩ | ⟨hnv, m', -, -, hq, -⟩
    · exact ⟨k, hk⟩
    · exfalso
      have hw : wd (F.p x) (F.q x) = Real.pi := by rw [hq]; exact wd_straight (F.hok x).ne_p
      have hle : wd (F.p x) (F.q x) ≤ ∑ y : AtV D.toRegionDissection V, wd (F.p y) (F.q y) :=
        Finset.single_le_sum (f := fun y => wd (F.p y) (F.q y)) (fun y _ => (wd_pos (F.hok y)).le) (Finset.mem_univ x)
      linarith
  have hcrall : ∀ x : AtV D.toRegionDissection V, 0 < crs (F.p x) (F.q x) :=
    fun x => crs_pos_of_corner (F.hok x) (F.hspec x) (hnostr x)
  -- counts
  have hStrn : Strn D.toRegionDissection V = ∅ := by
    ext j
    simp only [Strn, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false, not_and, not_forall, not_not]
    intro hj
    exact hnostr ⟨j, hj⟩
  have hang := head_angle_sum_gen D idx hidxA F
  have hvirt : ∑ j : Bool, wd (F.pe j) (F.qe j) = Real.pi + (Real.pi - wd pT qT) := by
    rw [Fintype.sum_bool, h1, h2, h3, h4, wd_straight hqT, wd_neg_left hcr]; ring
  rw [hStrn, hvirt] at hang
  simp only [Finset.card_empty, Nat.cast_zero, mul_zero, add_zero] at hang
  rw [Fin.sum_univ_three] at hang
  have hsum' : ((cnt D idx V 0 : ℕ) : ℝ) * D.model.angleAt 0 + (cnt D idx V 1 : ℕ) * D.model.angleAt 1 + (cnt D idx V 2 : ℕ) * D.model.angleAt 2 = wd pT qT := by
    linarith
  have hangs := Erdos634.Draft.LaczFormal.angleAt_sum D.model
  have hαβ : D.model.angleAt 0 + D.model.angleAt 1 = Real.pi / 2 := by have := hγ; linarith
  have hr : ((cnt D idx V 0 : ℕ) : ℝ) = (cnt D idx V 1 : ℕ) := by exact_mod_cast hregc V
  rw [hγ, hr] at hsum'
  have hc12 : ((cnt D idx V 1 : ℕ) : ℝ) + (cnt D idx V 2 : ℕ) = 1 := by
    have hp := Real.pi_pos
    have e1 : (((cnt D idx V 1 : ℕ) : ℝ) + (cnt D idx V 2 : ℕ)) * (Real.pi / 2) = wd pT qT := by nlinarith [hsum', hαβ]
    have h0 : 0 < ((cnt D idx V 1 : ℕ) : ℝ) + (cnt D idx V 2 : ℕ) := by
      by_contra hh
      have : ((cnt D idx V 1 : ℕ) : ℝ) + (cnt D idx V 2 : ℕ) = 0 := by
        have := Nat.cast_nonneg (α := ℝ) (cnt D idx V 1)
        have := Nat.cast_nonneg (α := ℝ) (cnt D idx V 2)
        linarith
      rw [this] at e1; linarith
    have h2' : ((cnt D idx V 1 : ℕ) : ℝ) + (cnt D idx V 2 : ℕ) < 2 := by
      by_contra hh
      push Not at hh
      nlinarith
    have h3' : cnt D idx V 1 + cnt D idx V 2 = 1 := by
      have : 0 < cnt D idx V 1 + cnt D idx V 2 := by exact_mod_cast h0
      have : cnt D idx V 1 + cnt D idx V 2 < 2 := by exact_mod_cast h2'
      omega
    exact_mod_cast h3'
  have hc12' : cnt D idx V 1 + cnt D idx V 2 = 1 := by exact_mod_cast hc12
  have hangle : P.angle (k + 1) = Real.pi / 2 := by
    obtain ⟨ρ, hρ, hiff⟩ := P.vertex_local_T P.three_le k
    have hN : 0 < N := Fin.pos i0
    have hT1 : (P.locTri P.three_le k).pts 1 = V := rfl
    have hiffD : ∀ y, dist y ((P.locTri P.three_le k).pts 1) < ρ → (y ∈ D.region ↔ y ∈ (P.locTri P.three_le k).carrier) := by
      intro y hy; rw [hreg]; exact hiff y hy
    have hs := sum_localAngle_tri D.toRegionDissection hN (P.locTri P.three_le k) hρ hiffD
    have hwdt := tiles_angle_sum D.toRegionDissection V F.p F.q F.hwd
    have hwdT : wd pT qT = (P.locTri P.three_le k).localAngle V := by
      rw [← hsumT, hwdt]; exact hs
    have hloc : (P.locTri P.three_le k).localAngle V = P.angle (k + 1) := by
      have := Tri.localAngle_vertex (P.locTri P.three_le k) 1
      rw [hT1] at this
      rw [this]
      unfold ConvPoly.angle cornerAngle
      have e1 : k + 1 - 1 = k := by simp
      have e2 : k + 1 + 1 = k + 2 := (ConvPoly.fin_facts P.three_le k).2.2.2.2.2
      rw [e1, e2, EuclideanGeometry.angle_comm (P.v k)]
      rfl
    have e1 : (((cnt D idx V 1 : ℕ) : ℝ) + (cnt D idx V 2 : ℕ)) * (Real.pi / 2) = wd pT qT := by
      have hp := Real.pi_pos
      nlinarith [hsum', hαβ]
    rw [← hloc, ← hwdT, ← e1, hc12]; ring
  exact hangle

set_option maxHeartbeats 3200000 in
/-- **Arms at a polygon corner** (`γ = π/2`).  At the vertex `v_{k+1}` either every left tile step along the outgoing edge `e_{k+1}` from it has length `a`, or every left tile
step along the incoming edge `e_k` into it has length `a`.  (The parity of the non-`α` corners is `1`, so exactly one of the two outer arms is `a`, as no edge of `Γ_a` starts at a boundary vertex.) -/
theorem corner_arms (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (idx : Fin N → Equiv.Perm (Fin 3))
    (hV : CaseV D idx) (P : ConvPoly M) (hreg : D.region = P.carrier) (k : Fin M) :
    P.angle (k + 1) = Real.pi / 2 ∧
    ((∀ j U', TriStep (D.tile j) (toV2 (P.e (k + 1))) (P.v (k + 1)) U' → dist (P.v (k + 1)) U' = slen D 0) ∨
    (∀ j U'', TriStep (D.tile j) (toV2 (P.e k)) U'' (P.v (k + 1)) → dist U'' (P.v (k + 1)) = slen D 0)) := by
  classical
  set V := P.v (k + 1) with hVdef
  have hvert : ∃ j k', (D.tile j).pts k' = V := poly_vertex_is_tile_vertex D.toRegionDissection P hreg (k + 1)
  obtain ⟨pT, qT, F, hpd, hqd, hcr, h1, h2, h3, h4, h5⟩ := fan_vertex_poly D.toRegionDissection P hreg k hvert
  have hqT : qT ≠ 0 := by intro h; rw [h] at hcr; unfold crs at hcr; simp at hcr
  have hpT : pT ≠ 0 := hpd.ne_left
  obtain ⟨i0, k0, hk0⟩ := hvert
  have hmem0 : V ∈ (D.tile i0).carrier := hk0 ▸ subset_convexHull ℝ _ ⟨k0, rfl⟩
  have hAt : 0 < Fintype.card (AtV D.toRegionDissection V) := Fintype.card_pos_iff.mpr ⟨⟨i0, hmem0⟩⟩
  obtain ⟨c, hc1, hcn, hadj, hsurjc, hinjc⟩ := corner_chain F hcr h1 h2 h3 h4 h5 hAt
  set n := Fintype.card (AtV D.toRegionDissection V) with hn
  have hsumT := corner_tile_sum D.toRegionDissection F hcr h1 h2 h3 h4
  have hwlt := wd_lt_pi_of_crs_pos hcr
  have hwpos := wd_pos (Or.inl hcr : SecOK pT qT)
  -- no straight tile
  have hnostr : ∀ x : AtV D.toRegionDissection V, ∃ k, (D.tile x.1).pts k = V := by
    intro x
    rcases F.hspec x with ⟨k, hk, -⟩ | ⟨hnv, m', -, -, hq, -⟩
    · exact ⟨k, hk⟩
    · exfalso
      have hw : wd (F.p x) (F.q x) = Real.pi := by rw [hq]; exact wd_straight (F.hok x).ne_p
      have hle : wd (F.p x) (F.q x) ≤ ∑ y : AtV D.toRegionDissection V, wd (F.p y) (F.q y) :=
        Finset.single_le_sum (f := fun y => wd (F.p y) (F.q y)) (fun y _ => (wd_pos (F.hok y)).le) (Finset.mem_univ x)
      linarith
  have hcrall : ∀ x : AtV D.toRegionDissection V, 0 < crs (F.p x) (F.q x) :=
    fun x => crs_pos_of_corner (F.hok x) (F.hspec x) (hnostr x)
  -- counts
  have hStrn : Strn D.toRegionDissection V = ∅ := by
    ext j
    simp only [Strn, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false, not_and, not_forall, not_not]
    intro hj
    exact hnostr ⟨j, hj⟩
  have hang := head_angle_sum_gen D idx hV.hidxA F
  have hvirt : ∑ j : Bool, wd (F.pe j) (F.qe j) = Real.pi + (Real.pi - wd pT qT) := by
    rw [Fintype.sum_bool, h1, h2, h3, h4, wd_straight hqT, wd_neg_left hcr]; ring
  rw [hStrn, hvirt] at hang
  simp only [Finset.card_empty, Nat.cast_zero, mul_zero, add_zero] at hang
  rw [Fin.sum_univ_three] at hang
  have hsum' : ((cnt D idx V 0 : ℕ) : ℝ) * D.model.angleAt 0 + (cnt D idx V 1 : ℕ) * D.model.angleAt 1 + (cnt D idx V 2 : ℕ) * D.model.angleAt 2 = wd pT qT := by
    linarith
  have hangs := Erdos634.Draft.LaczFormal.angleAt_sum D.model
  have hαβ : D.model.angleAt 0 + D.model.angleAt 1 = Real.pi / 2 := by have := hV.hγ; linarith
  have hr : ((cnt D idx V 0 : ℕ) : ℝ) = (cnt D idx V 1 : ℕ) := by exact_mod_cast hV.hregc V
  rw [hV.hγ, hr] at hsum'
  have hc12 : ((cnt D idx V 1 : ℕ) : ℝ) + (cnt D idx V 2 : ℕ) = 1 := by
    have hp := Real.pi_pos
    have e1 : (((cnt D idx V 1 : ℕ) : ℝ) + (cnt D idx V 2 : ℕ)) * (Real.pi / 2) = wd pT qT := by nlinarith [hsum', hαβ]
    have h0 : 0 < ((cnt D idx V 1 : ℕ) : ℝ) + (cnt D idx V 2 : ℕ) := by
      by_contra hh
      have : ((cnt D idx V 1 : ℕ) : ℝ) + (cnt D idx V 2 : ℕ) = 0 := by
        have := Nat.cast_nonneg (α := ℝ) (cnt D idx V 1)
        have := Nat.cast_nonneg (α := ℝ) (cnt D idx V 2)
        linarith
      rw [this] at e1; linarith
    have h2' : ((cnt D idx V 1 : ℕ) : ℝ) + (cnt D idx V 2 : ℕ) < 2 := by
      by_contra hh
      push Not at hh
      nlinarith
    have h3' : cnt D idx V 1 + cnt D idx V 2 = 1 := by
      have : 0 < cnt D idx V 1 + cnt D idx V 2 := by exact_mod_cast h0
      have : cnt D idx V 1 + cnt D idx V 2 < 2 := by exact_mod_cast h2'
      omega
    exact_mod_cast h3'
  have hc12' : cnt D idx V 1 + cnt D idx V 2 = 1 := by exact_mod_cast hc12
  have hangle : P.angle (k + 1) = Real.pi / 2 := by
    obtain ⟨ρ, hρ, hiff⟩ := P.vertex_local_T P.three_le k
    have hN : 0 < N := Fin.pos i0
    have hT1 : (P.locTri P.three_le k).pts 1 = V := rfl
    have hiffD : ∀ y, dist y ((P.locTri P.three_le k).pts 1) < ρ → (y ∈ D.region ↔ y ∈ (P.locTri P.three_le k).carrier) := by
      intro y hy; rw [hreg]; exact hiff y hy
    have hs := sum_localAngle_tri D.toRegionDissection hN (P.locTri P.three_le k) hρ hiffD
    have hwdt := tiles_angle_sum D.toRegionDissection V F.p F.q F.hwd
    have hwdT : wd pT qT = (P.locTri P.three_le k).localAngle V := by
      rw [← hsumT, hwdt]; exact hs
    have hloc : (P.locTri P.three_le k).localAngle V = P.angle (k + 1) := by
      have := Tri.localAngle_vertex (P.locTri P.three_le k) 1
      rw [hT1] at this
      rw [this]
      unfold ConvPoly.angle cornerAngle
      have e1 : k + 1 - 1 = k := by simp
      have e2 : k + 1 + 1 = k + 2 := (ConvPoly.fin_facts P.three_le k).2.2.2.2.2
      rw [e1, e2, EuclideanGeometry.angle_comm (P.v k)]
      rfl
    have e1 : (((cnt D idx V 1 : ℕ) : ℝ) + (cnt D idx V 2 : ℕ)) * (Real.pi / 2) = wd pT qT := by
      have hp := Real.pi_pos
      nlinarith [hsum', hαβ]
    rw [← hloc, ← hwdT, ← e1, hc12]; ring
  -- the chain
  have hcpos : ∀ l, 1 ≤ l → l ≤ n → 0 < crs (F.p (c l)) (F.q (c l)) := fun l _ _ => hcrall _
  have hnb : ∀ l, 1 ≤ l → l < n → NoBack D.toRegionDissection (F.q (c l)) V := by
    intro l _ _
    exact noBack_corner F hcr h5 (tile_ray_mem F (c l)).2 (F.hok (c l)).ne_q
  have hcore := chain_core D idx hV.hidx hV.hnc hV.hab hV.hac F n hAt c hcpos hadj hnb
  have hci : P.c (k + 1) V = 0 := by rw [hVdef]; exact P.c_self _
  refine ⟨hangle, ?_⟩
  rcases hcore with ⟨H', hH'⟩ | hpar
  · exact absurd hH' (lemma91_ii D idx hV.hidx hV.hidxA hV.hnc hV.hab hV.hac hV.toG.hhp
      (by rw [hreg]; exact not_interior_of_c_zero P hci))
  · have hodd : (∑ l ∈ Finset.Icc 1 n, (if ∃ k' : Fin 3, (D.tile (c l).1).pts k' = V ∧ idx (c l).1 k' ≠ 0 then 1 else 0)) % 2 = 1 := by
      have hs := chain_sum c hsurjc hinjc (fun x => if ∃ k' : Fin 3, (D.tile x.1).pts k' = V ∧ idx x.1 k' ≠ 0 then 1 else 0)
      rw [hs, Finset.sum_boole]
      have := corner_tile_count D idx V ⟨i0, hmem0⟩
      simp only [Nat.cast_id]
      rw [this, hc12']
    have hnot : ¬ (nsq (F.p (c 1)) = slen D 0 ^ 2 ↔ nsq (F.q (c n)) = slen D 0 ^ 2) := by
      intro h
      have h0 := hpar.mp h
      have hodd' : (∑ l ∈ Finset.Icc 1 n, (if ∃ k' : Fin 3, (D.tile (c l).1).pts k' = P.v (k + 1) ∧ idx (c l).1 k' ≠ 0 then 1 else 0)) % 2 = 1 := hodd
      omega
    -- identify the steps
    have hdis := tiles_disjoint D.toRegionDissection V F.p F.q F.hloc
    have hd1 : Par (toV2 (P.e (k + 1))) pT := hpd.symm
    have hqe' : Par qT (neg2 (toV2 (P.e k))) := by
      have e : toV2 (P.v k - P.v (k + 1)) = neg2 (toV2 (P.e k)) := by
        unfold neg2 toV2 ConvPoly.e; ext <;> simp
      rw [e] at hqd; exact hqd
    have hsl : 0 ≤ slen D 0 := (slen_pos D 0).le
    by_cases hP : nsq (F.p (c 1)) = slen D 0 ^ 2
    · left
      intro j U' hS
      obtain ⟨kk, f, g, hk, hf, hfk, hgk, hgf, hpar2, hleft⟩ := id hS
      have hmem : V ∈ (D.tile j).carrier := hk ▸ subset_convexHull ℝ _ ⟨kk, rfl⟩
      set x : AtV D.toRegionDissection V := ⟨j, hmem⟩
      obtain ⟨kk', fl, hk', hp, hq⟩ := spec_corner_data (F.hspec x) ⟨kk, hk⟩
      have hkk : kk' = kk := (D.tile j).indep.injective (hk'.trans hk.symm)
      have hPx : Par (F.p x) (toV2 (P.e (k + 1))) := triStep_start hS kk' fl hk' hp hq (F.hok x)
      have hx1 : x = c 1 := by
        by_contra hne
        exact start_inj F.p F.q F.hok hdis (Ne.symm hne) (hPx.trans (hd1.trans hc1.symm))
      have hq' : Par (toV2 ((D.tile j).pts (armP kk' fl) - V)) (toV2 (P.e (k + 1))) := hp ▸ hPx
      have harm := parm_eq (T := D.tile j) fl hk' (W := U') (w := f) hf (by rw [hkk]; exact hfk) hq' hpar2
      have hn2 : nsq (F.p x) = dist V U' ^ 2 := by rw [hp, nsq_toV2_sub, harm, dist_comm]
      rw [hx1] at hn2
      rw [hn2] at hP
      exact (pow_left_inj₀ dist_nonneg hsl two_ne_zero).mp hP
    · right
      have hQ : nsq (F.q (c n)) = slen D 0 ^ 2 := by
        by_contra hQ
        exact hnot ⟨fun h => absurd h hP, fun h => absurd h hQ⟩
      intro j U'' hS
      obtain ⟨kk, f, g, hk, hf, hfk, hgk, hgf, hpar2, hleft⟩ := id hS
      have hmem : V ∈ (D.tile j).carrier := hf ▸ subset_convexHull ℝ _ ⟨f, rfl⟩
      set x : AtV D.toRegionDissection V := ⟨j, hmem⟩
      obtain ⟨kk', fl, hk', hp, hq⟩ := spec_corner_data (F.hspec x) ⟨f, hf⟩
      have hkk : kk' = f := (D.tile j).indep.injective (hk'.trans hf.symm)
      have hQx : Par (F.q x) (neg2 (toV2 (P.e k))) := triStep_end hS kk' fl hk' hp hq (F.hok x)
      have hx1 : x = c n := by
        by_contra hne
        exact end_inj' F.p F.q F.hok hdis (Ne.symm hne) (hQx.trans (hqe'.symm.trans hcn))
      have hq' : Par (toV2 ((D.tile j).pts (armQ kk' fl) - V)) (neg2 (toV2 (P.e k))) := hq ▸ hQx
      have hW : Par (toV2 (U'' - V)) (neg2 (toV2 (P.e k))) := par_neg_arm hpar2
      have harm := qarm_eq (T := D.tile j) fl hk' (W := U'') (w := kk) hk (by rw [hkk]; exact hfk.symm) hq' hW
      have hn1 : nsq (F.q x) = dist U'' V ^ 2 := by rw [hq, nsq_toV2_sub, harm]
      rw [hx1] at hn1
      rw [hn1] at hQ
      exact (pow_left_inj₀ dist_nonneg hsl two_ne_zero).mp hQ

theorem walkT_nil_eq {D : RegionDissection N} {d : V2} {X Y : Plane} (W : WalkT D d X Y []) : X = Y := by
  cases W; rfl

theorem walkT_head {D : RegionDissection N} {d : V2} {X Y : Plane} {e : Fin N × Plane × Plane} {L' : List (Fin N × Plane × Plane)}
    (W : WalkT D d X Y (e :: L')) : e.2.1 = X ∧ TriStep (D.tile e.1) d e.2.1 e.2.2 := by
  cases W with
  | cons hS _ => exact ⟨rfl, hS⟩

/-- **Lemma 9.1 (iii) for an edge:** if the first tile side from `v_i` (or the last tile side into `v_{i+1}`) has length `a`, the edge is `m · a`, `m ≥ 1`. -/
theorem edge_side_multiple (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (idx : Fin N → Equiv.Perm (Fin 3))
    (hV : CaseV D idx) (P : ConvPoly M) (hreg : D.region = P.carrier) (i : Fin M)
    (h : (∀ j U', TriStep (D.tile j) (toV2 (P.e i)) (P.v i) U' → dist (P.v i) U' = slen D 0) ∨
      (∀ j U'', TriStep (D.tile j) (toV2 (P.e i)) U'' (P.v (i + 1)) → dist U'' (P.v (i + 1)) = slen D 0)) :
    ∃ m : ℕ, 0 < m ∧ P.side i = m * slen D 0 := by
  classical
  obtain ⟨L, W⟩ := side_walk_exists_poly D.toRegionDissection P hreg i
  have hne : P.v i ≠ P.v (i + 1) := by
    intro he
    apply P.e_ne_zero P.three_le i
    unfold ConvPoly.e; rw [← he]; simp
  have hL : L ≠ [] := by
    rintro rfl
    exact hne (walkT_nil_eq W)
  have hU : ∃ s : ℝ, 0 ≤ s ∧ toV2 (P.v i - P.v i) = (s * (toV2 (P.e i)).1, s * (toV2 (P.e i)).2) :=
    ⟨0, le_rfl, by unfold toV2; ext <;> simp⟩
  have hchain := walk_status_chain D idx hV.toG P hreg i rfl W hU
  -- the first element
  obtain ⟨e0, L0, hL0⟩ : ∃ e0 L0, L = e0 :: L0 := by
    cases L with
    | nil => exact absurd rfl hL
    | cons e0 L0 => exact ⟨e0, L0, rfl⟩
  have hstat0 : dist e0.2.1 e0.2.2 = slen D 0 := by
    rcases h with hout | hin
    · -- e0 is a left step from v_i
      subst hL0
      obtain ⟨hX, hS⟩ := walkT_head W
      have := hout _ _ (hX ▸ hS)
      rw [hX]; exact this
    · obtain ⟨j, U, hmem, hS⟩ := walkT_last W hL
      have hel := hin j U hS
      have hall := hchain e0 (by rw [hL0]; simp) (j, U, P.v (i + 1)) hmem
      exact hall.mp hel
  have hallA : ∀ e ∈ L, dist e.2.1 e.2.2 = slen D 0 := by
    intro e he
    exact ((hchain e0 (by rw [hL0]; simp) e he).mpr hstat0)
  have hsum := walkT_dist_sum W
  have hsumA : (L.map fun e => dist e.2.1 e.2.2).sum = (L.map fun e => dist e.2.1 e.2.2).length • slen D 0 :=
    List.sum_eq_card_nsmul _ _ (fun x hx => by
      obtain ⟨e', he', rfl⟩ := List.mem_map.mp hx
      exact hallA e' he')
  rw [List.length_map, nsmul_eq_mul] at hsumA
  refine ⟨L.length, List.length_pos_of_ne_nil hL, ?_⟩
  rw [ConvPoly.side, ← hsum, hsumA]

/-- **Case V, Va: some side of the polygon is an integer multiple of `a`.** -/
theorem some_side_multiple (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (idx : Fin N → Equiv.Perm (Fin 3))
    (hV : CaseV D idx) (P : ConvPoly M) (hreg : D.region = P.carrier) :
    ∃ i : Fin M, ∃ m : ℕ, 0 < m ∧ P.side i = m * slen D 0 := by
  rcases (corner_arms D idx hV P hreg 0).2 with h | h
  · exact ⟨0 + 1, edge_side_multiple D idx hV P hreg (0 + 1) (Or.inl h)⟩
  · exact ⟨0, edge_side_multiple D idx hV P hreg 0 (Or.inr h)⟩

end Erdos634.Draft.LaczFormal.RG
