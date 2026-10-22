-- Draft/ConvergingWallsReal.lean — CW(ℓ_j, m_k), THE CONVERGING WALLS, for REAL `m = 1`
-- dissections in the apex frame, in every regime (no relation between `j` and `k`; c-seed at `kV`):
-- the statement of (private working notes, not included) §1.1 (review record R1–R3; proof_H_empty.md §5.9),
-- proved by its nested induction (outer strong induction on `j`, inner march over the levels),
-- from the local steps of Draft/ConvergingWallsLocal.lean.  Imported directly by All.lean (stale "NOT imported" header corrected 2026-10-04).
--
-- Build (scratch oleans; never .lake): ConvergingWallsLocal olean in $S, then
--   lake env bash -c 'LEAN_PATH=$S:$LEAN_PATH lean Erdos634/Draft/ConvergingWallsReal.lean'
--
-- Formal route vs. the paper (proof_CW_P2.md §4): identical steps, two simplifications of the
-- ORDER, both sound and both stated where used:
-- (i) (B4) PROP is not used: the half-turns across `σ_{N+1}` are found by marching FROM the `ℓ_j`
--     end (as RW's `row_step` marches from the `L_j` end): at `Y` the band straddle leaves `β`, at
--     each later junction the previous half-turn's `γ` leaves no room for the mirror's `γ`
--     (`interior_card_eqs`).  This is the contrapositive of the paper's "mirrors drift to the ℓ_j
--     end, where only β is left".
-- (ii) The exit terminal (T2, level `L*(k)`) needs no separate proof: a present tile has its
--     vertices in the target (`mem_of_present`), and `O2` makes every such lattice vertex interior,
--     so the march always reaches the apex `Z = kV + jP′` and dies there by the double straddle (T1).
--     (At an exit level the half-turn found by the march would have a vertex outside the target, so
--     in a genuine dissection the hypotheses are already contradictory there; formally no branch is
--     needed.)
import Erdos634.Draft.ConvergingWallsLocal

namespace Erdos634.Draft.RowWallReal

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.Draft.HalfTurnR3R4
open Erdos634.Draft.HalfTurnR3R4Glue Erdos634.Draft.CornerAdjacency
open Erdos634.Draft.HalfTurnR3R4Order Erdos634.Draft.MirrorStripR2Real
open Erdos634.Draft.HalfTurnR4Real

variable {N : ℕ} {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ}
variable (F : HFrame D e f α β γ)

/-! ## §1 (B3) The far word of `σ` -/

set_option maxHeartbeats 1000000 in
/-- **(B3) The far word on `AD_n`** (proof_CW_P2.md §4.3 (B3)).  The segment `σ` of `AD_n` from
`Y = i₀V + (n−i₀)P′` to `W = (i₀+q)V + (n−i₀−q)P′`, interior, lined above by the `a`-edges of the up
cells `U(i, n−1−i)`, `i₀ ≤ i < i₀+q`, with neither end straddled from the far side, has far side a
whole-edge word of value `q·a` (`TraceCovering.wall_sum`), all `a` by **m = 1**
(`Inflation.a_side_no_b`, `a_side_rigid`: `q < f`; at N = 44, `2a = c`): every far edge leaving a
point of `[Y, W)` along `V − P′` is an `a`-edge. -/
theorem far_word (L : LFrame F) (Nl i0 q : ℕ) (hq : 1 ≤ q) (hqf : q + 1 ≤ f) (hiN : i0 + q ≤ Nl)
    (hint : ∀ s : ℝ, 0 < s → s < q →
      Q2 F ((i0 : ℝ) + s) ((Nl : ℝ) - i0 - s) ∈ interior D.target.carrier)
    (hUp : ∀ i t, i0 ≤ i → i < i0 + q → i + t + 1 = Nl → Present D (T2c F i t))
    (hs0 : ¬ AStr F Nl (Q2 F i0 ((Nl : ℝ) - i0)))
    (hs1 : ¬ AStr F Nl (Q2 F ((i0 : ℝ) + q) ((Nl : ℝ) - i0 - q))) :
    ∀ ε ∈ adChain F (Nl : ℝ), ∀ s ℓ : ℝ, 0 < ℓ → 0 ≤ s → s < q →
      EdgeIs D ε (Q2 F ((i0 : ℝ) + s) ((Nl : ℝ) - i0 - s))
        (Q2 F ((i0 : ℝ) + s + ℓ / ((e : ℝ) * f)) ((Nl : ℝ) - i0 - s - ℓ / ((e : ℝ) * f))) →
      ℓ = (e : ℝ) * f := by
  classical
  have FC := L.FC
  obtain ⟨ha0, hb0, hc0, hbc, hac⟩ := consts F
  have hu1 : ‖uA F‖ = 1 := uA_norm F
  have hu0 : uA F ≠ 0 := TraceCovering.ne_zero_of_norm hu1
  have hg : adF F ≠ 0 := adF_ne F FC
  have hg' : (-(adF F) : Plane →ₗ[ℝ] ℝ) ≠ 0 := fun h => hg (neg_eq_zero.mp h)
  have hgd : ∀ y, (-(adF F)) y = -(adF F F.A + (Nl : ℝ)) ↔ adF F y = adF F F.A + (Nl : ℝ) :=
    TraceCovering.neg_iff
  have hgu : adF F (uA F) = 0 := adF_uA F FC
  have hXg : adF F (Q2 F i0 ((Nl : ℝ) - i0)) = adF F F.A + (Nl : ℝ) := by
    rw [adF_Q2 F FC]; ring
  have hpt : ∀ x : ℝ, Q2 F i0 ((Nl : ℝ) - i0) + x • uA F
      = Q2 F ((i0 : ℝ) + x / ((e : ℝ) * f)) ((Nl : ℝ) - i0 - x / ((e : ℝ) * f)) := by
    intro x; rw [Q2_uA]
  have hqa : (0 : ℝ) ≤ (q : ℝ) * ((e : ℝ) * f) := by positivity
  have hintA : ∀ x ∈ Set.Ioo 0 ((q : ℝ) * ((e : ℝ) * f)),
      Q2 F i0 ((Nl : ℝ) - i0) + x • uA F ∈ interior D.target.carrier := by
    intro x hx
    rw [hpt]
    exact hint _ (div_pos hx.1 ha0) (by rw [div_lt_iff₀ ha0]; exact hx.2)
  have hwall := wall_lattice (D := D) hu0 ha0 q (X := Q2 F i0 ((Nl : ℝ) - i0)) (fun k hk => by
    obtain ⟨t, ht⟩ : ∃ t, i0 + k + t + 1 = Nl := ⟨Nl - (i0 + k) - 1, by omega⟩
    obtain ⟨iz, hiz⟩ := hUp (i0 + k) t (by omega) (by omega) ht
    have htR : (t : ℝ) = (Nl : ℝ) - i0 - k - 1 := by
      have : ((i0 + k + t + 1 : ℕ) : ℝ) = Nl := by exact_mod_cast ht
      push_cast at this; linarith
    refine ⟨iz, ?_, ?_⟩ <;> rw [hiz, U_eq F FC, hpt]
    · have : Q2 F ((i0 : ℝ) + (k : ℝ) * ((e : ℝ) * f) / ((e : ℝ) * f))
          ((Nl : ℝ) - i0 - (k : ℝ) * ((e : ℝ) * f) / ((e : ℝ) * f))
          = Q2 F ((i0 + k : ℕ) : ℝ) ((t : ℝ) + 1) := by
        rw [mul_div_cancel_right₀ _ ha0.ne', htR]; push_cast; congr 1 <;> ring
      rw [this]; exact mem3_3
    · have : Q2 F ((i0 : ℝ) + ((k : ℝ) + 1) * ((e : ℝ) * f) / ((e : ℝ) * f))
          ((Nl : ℝ) - i0 - ((k : ℝ) + 1) * ((e : ℝ) * f) / ((e : ℝ) * f))
          = Q2 F (((i0 + k : ℕ) : ℝ) + 1) (t : ℝ) := by
        rw [mul_div_cancel_right₀ _ ha0.ne', htR]; push_cast; congr 1 <;> ring
      rw [this]; exact mem3_2)
  have hs : ¬ TraceCovering.Straddled D.toDissection (-(adF F)) (-(adF F F.A + (Nl : ℝ)))
      (Q2 F i0 ((Nl : ℝ) - i0) + (0 : ℝ) • uA F) := by
    rw [zero_smul, add_zero]; exact hs0
  have hQe : Q2 F i0 ((Nl : ℝ) - i0) + ((q : ℝ) * ((e : ℝ) * f)) • uA F
      = Q2 F ((i0 : ℝ) + q) ((Nl : ℝ) - i0 - q) := by
    rw [hpt, mul_div_cancel_right₀ _ ha0.ne']
  have ht : ¬ TraceCovering.Straddled D.toDissection (-(adF F)) (-(adF F F.A + (Nl : ℝ)))
      (Q2 F i0 ((Nl : ℝ) - i0) + ((q : ℝ) * ((e : ℝ) * f)) • uA F) := by
    rw [hQe]; exact hs1
  have hsum := TraceCovering.wall_sum (D := D.toDissection) hg' hgd hg hXg hgu hu1 hqa hintA hwall
    hs ht
  intro ε hε s ℓ hℓ hs0' hsq hE
  have hpq' := pts_ne (D.tile ε.1) (TraceCovering.fin3_succ_ne ε.2)
  have hPe : Q2 F ((i0 : ℝ) + s) ((Nl : ℝ) - i0 - s)
      = Q2 F i0 ((Nl : ℝ) - i0) + (s * ((e : ℝ) * f)) • uA F := by
    rw [hpt, mul_div_cancel_right₀ _ ha0.ne']
  have hQe' : Q2 F ((i0 : ℝ) + s + ℓ / ((e : ℝ) * f)) ((Nl : ℝ) - i0 - s - ℓ / ((e : ℝ) * f))
      = Q2 F i0 ((Nl : ℝ) - i0) + (s * ((e : ℝ) * f) + ℓ) • uA F := by
    rw [hpt, add_div, mul_div_cancel_right₀ _ ha0.ne']; congr 1 <;> ring
  rw [hPe, hQe'] at hE
  have hx0 : 0 ≤ s * ((e : ℝ) * f) := mul_nonneg hs0' ha0.le
  have hxK : s * ((e : ℝ) * f) < (q : ℝ) * ((e : ℝ) * f) := mul_lt_mul_of_pos_right hsq ha0
  by_cases hin : s * ((e : ℝ) * f) + ℓ ≤ (q : ℝ) * ((e : ℝ) * f)
  · have hseg : ∀ x, 0 ≤ x → x ≤ (q : ℝ) * ((e : ℝ) * f) →
        Q2 F i0 ((Nl : ℝ) - i0) + x • uA F ∈ segment ℝ (Q2 F i0 ((Nl : ℝ) - i0) + (0 : ℝ) • uA F)
          (Q2 F i0 ((Nl : ℝ) - i0) + ((q : ℝ) * ((e : ℝ) * f)) • uA F) := by
      intro x hx0 hx1
      rw [TraceCovering.segment_param, min_eq_left hqa, max_eq_right hqa]
      exact ⟨x, ⟨hx0, hx1⟩, rfl⟩
    have hb1 := hseg _ hx0 hxK.le
    have hb2 := hseg _ (by linarith) hin
    have hsub : (D.tile ε.1).edge ε.2 ⊆ segment ℝ (Q2 F i0 ((Nl : ℝ) - i0) + (0 : ℝ) • uA F)
        (Q2 F i0 ((Nl : ℝ) - i0) + ((q : ℝ) * ((e : ℝ) * f)) • uA F) := by
      rw [Tri.edge]
      rcases pair_cases hE hpq' with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
      · exact (convex_segment _ _).segment_subset hb1 hb2
      · exact (convex_segment _ _).segment_subset hb2 hb1
    have hd : dist (Q2 F i0 ((Nl : ℝ) - i0) + (s * ((e : ℝ) * f)) • uA F)
        (Q2 F i0 ((Nl : ℝ) - i0) + (s * ((e : ℝ) * f) + ℓ) • uA F) = ℓ := by
      rw [TraceCovering.dist_param hu1, max_eq_right (by linarith), min_eq_left (by linarith)]; ring
    have hdM : dist ((D.tile ε.1).pts ε.2) ((D.tile ε.1).pts (ε.2 + 1)) = ℓ := by
      rcases pair_cases hE hpq' with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2]; exact hd
      · rw [h1, h2, dist_comm]; exact hd
    set sF := (D.toDissection.lineChain (-(adF F)) (-(adF F F.A + (Nl : ℝ)))).filter
      (fun ε' => (D.tile ε'.1).edge ε'.2 ⊆ segment ℝ (Q2 F i0 ((Nl : ℝ) - i0) + (0 : ℝ) • uA F)
        (Q2 F i0 ((Nl : ℝ) - i0) + ((q : ℝ) * ((e : ℝ) * f)) • uA F)) with hsF
    have hmemS : ε ∈ sF := Finset.mem_filter.mpr ⟨hε, hsub⟩
    rw [← Finset.add_sum_erase sF _ hmemS] at hsum
    obtain ⟨P', Q', R', hPQR, -⟩ := Erdos634.Geometry.sum_three_values (sF.erase ε)
      (fun ε' => dist ((D.tile ε'.1).pts ε'.2) ((D.tile ε'.1).pts (ε'.2 + 1)))
      ((e : ℝ) * f) ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ((f : ℝ) ^ 2)
      (fun ε _ => edge_len_mem D F.hM.hs0 F.hM.hs1 F.hM.hs2 ε.1 ε.2)
    simp only at hsum hdM
    rw [hdM] at hsum
    have hee : e ^ 2 ≤ f ^ 2 := Nat.pow_le_pow_left (by have := F.hef; omega) 2
    have hb' : f ^ 2 - e ^ 2 + e ^ 2 = f ^ 2 := Nat.sub_add_cancel hee
    rcases edge_len_mem D F.hM.hs0 F.hM.hs1 F.hM.hs2 ε.1 ε.2 with h | h | h <;> rw [hdM] at h
    · exact h
    · exfalso
      have hreal : ((P' * (e * f) + (Q' + 1) * (f ^ 2 - e ^ 2) + R' * f ^ 2 : ℕ) : ℝ)
          = ((q * (e * f) : ℕ) : ℝ) := by
        push_cast [Nat.cast_sub hee]; rw [h] at hsum; linarith
      have hnat : P' * (e * f) + (Q' + 1) * (f ^ 2 - e ^ 2) + R' * f ^ 2 = q * (e * f) := by
        exact_mod_cast hreal
      have := Inflation.a_side_no_b e f (f ^ 2 - e ^ 2) q P' (Q' + 1) R'
        (by have := F.he; omega) (by have := F.hef; omega) F.hco hb' (by omega) hnat
      omega
    · exfalso
      have hreal : ((P' * (e * f) + Q' * (f ^ 2 - e ^ 2) + (R' + 1) * f ^ 2 : ℕ) : ℝ)
          = ((q * (e * f) : ℕ) : ℝ) := by
        push_cast [Nat.cast_sub hee]; rw [h] at hsum; linarith
      have hnat : P' * (e * f) + Q' * (f ^ 2 - e ^ 2) + (R' + 1) * f ^ 2 = q * (e * f) := by
        exact_mod_cast hreal
      have hQ0 := Inflation.a_side_no_b e f (f ^ 2 - e ^ 2) q P' Q' (R' + 1)
        (by have := F.he; omega) (by have := F.hef; omega) F.hco hb' (by omega) hnat
      rw [hQ0, zero_mul, add_zero] at hnat
      have := Inflation.a_side_rigid e f q P' (R' + 1) (by have := F.he; omega)
        (by have := F.hef; omega) F.hco (by omega) hnat
      omega
  · -- the edge would straddle `W`
    exfalso
    push Not at hin
    unfold AStr at hs1
    apply hs1
    refine ⟨ε, hε, ?_⟩
    have hopen : Q2 F i0 ((Nl : ℝ) - i0) + ((q : ℝ) * ((e : ℝ) * f)) • uA F ∈
        openSegment ℝ (Q2 F i0 ((Nl : ℝ) - i0) + (s * ((e : ℝ) * f)) • uA F)
          (Q2 F i0 ((Nl : ℝ) - i0) + (s * ((e : ℝ) * f) + ℓ) • uA F) := by
      rw [TraceCovering.openSegment_param (by linarith), min_eq_left (by linarith),
        max_eq_right (by linarith)]
      exact ⟨_, ⟨hxK, hin⟩, rfl⟩
    rw [hQe] at hopen
    rcases pair_cases hE hpq' with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
    · exact hopen
    · rw [openSegment_symm]; exact hopen

/-! ## §2 (B4) The half-turns across `σ`, marching from the `ℓ_j` end -/

theorem card_three {x : Plane} {θ : ℝ} {i1 i2 i3 : Fin N} (h12 : i1 ≠ i2) (h13 : i1 ≠ i3)
    (h23 : i2 ≠ i3) (g1 : (D.tile i1).localAngle x = θ) (g2 : (D.tile i2).localAngle x = θ)
    (g3 : (D.tile i3).localAngle x = θ) :
    3 ≤ ({i | (D.tile i).localAngle x = θ} : Finset (Fin N)).card := by
  classical
  have hsub : ({i1, i2, i3} : Finset (Fin N)) ⊆
      ({i | (D.tile i).localAngle x = θ} : Finset (Fin N)) := by
    intro y hy; simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl
    · exact mem_filter_of g1
    · exact mem_filter_of g2
    · exact mem_filter_of g3
  have h3 : ({i1, i2, i3} : Finset (Fin N)).card = 3 :=
    Finset.card_eq_three.mpr ⟨i1, i2, i3, h12, h13, h23, rfl⟩
  have := Finset.card_le_card hsub
  omega

set_option maxHeartbeats 2000000 in
/-- **(B4) One junction of `σ` on `AD_n`.**  At `X = (i+1)V + (t+1)P′` (`n = i + t + 2`), the up cell
`U(i+1, t)` presents `γ` with its `a`-flank along `V − P′` on `AD_n`, and `D(i, t)` presents `α`.
Given a *blocker* — a straight tile through `X` on a line not parallel to `AD_n` (the band straddle,
at the `ℓ_j` end) or the half-turn `D(i, t+1)` found at the previous junction (`γ`) — the tile across
that flank is the half-turn `D(i+1, t)`: it has an edge on `AD_n` (no straight tile fits), that edge
is an `a`-edge (the far word `hall`), so it presents `β` or `γ` (not `α`: flanks `b, c`), and `γ` would
make three `γ`'s (or two `γ`'s and a straight angle) beside the `α` (`interior_card_eqs`).
No `m = 1` input beyond `hall`. -/
theorem junction (L : LFrame F) (Nl i' t : ℕ) (hit : i' + 1 + t + 1 = Nl)
    (hXint : Q2 F ((i' : ℝ) + 1) ((t : ℝ) + 1) ∈ interior D.target.carrier)
    (hall : ∀ ε ∈ adChain F (Nl : ℝ), ∀ ℓ : ℝ, 0 < ℓ →
      EdgeIs D ε (Q2 F ((i' : ℝ) + 1) ((t : ℝ) + 1))
        (Q2 F ((i' : ℝ) + 1 + ℓ / ((e : ℝ) * f)) ((t : ℝ) + 1 - ℓ / ((e : ℝ) * f))) →
      ℓ = (e : ℝ) * f)
    (hγ : Present D (T2c F (i' + 1) t)) (hα : Present D (Kc F i' t))
    (hcase : (∃ g : Plane →ₗ[ℝ] ℝ, ∃ d : ℝ,
        TraceCovering.Straddled D.toDissection g d (Q2 F ((i' : ℝ) + 1) ((t : ℝ) + 1)) ∧
          g (vec F (cb e f) (-1)) ≠ 0) ∨ Present D (Kc F i' (t + 1))) :
    Present D (Kc F (i' + 1) t) := by
  classical
  have FC := L.FC
  obtain ⟨ha0, hb0, hc0, hbc, hac⟩ := consts F
  obtain ⟨hab, hac', hbc'⟩ := sides_distinct F.hco F.he (by have := F.hef; omega)
  obtain ⟨hcb0, hcb1⟩ := cb_pos F
  have hK := K_ne F FC
  have hK2 := mul_self_pos.mpr hK
  have hitR : (i' : ℝ) + 1 + t + 1 = Nl := by exact_mod_cast hit
  obtain ⟨iG, hrG⟩ := hγ
  obtain ⟨iA, hrA⟩ := hα
  have gG : (D.tile iG).localAngle (Q2 F ((i' : ℝ) + 1) ((t : ℝ) + 1)) = γ := by
    have := (U_angles F FC hrG).2.2; push_cast at this; exact this
  have gA : (D.tile iA).localAngle (Q2 F ((i' : ℝ) + 1) ((t : ℝ) + 1)) = α := (D_angles F FC hrA).2.2
  have rG : Set.range (D.tile iG).pts = {Q2 F ((i' : ℝ) + 1) ((t : ℝ) + 1),
      Q2 F ((i' : ℝ) + 1 + 1) t, Q2 F ((i' : ℝ) + 1) t} := by
    rw [hrG, U_eq F FC]; push_cast
    ext p; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  obtain ⟨mG, hmG, hflG⟩ := flank_of_range rG
  rw [Q2_sub_eq F (p := cb e f) (q := -1) (by ring) (by ring),
    Q2_sub_eq F (p := -1) (q := 0) (by ring) (by ring)] at hflG
  obtain ⟨z, hzG, hXz, hcz⟩ := flank_neighbour_dissection D.toDissection hXint hmG hflG
  obtain ⟨E1, E2⟩ := interior_card_eqs D F.hAng F.hM.hα' F.hM.hβ' F.hM.hγ' hXint
  have cA := card_one gA
  have cG := card_one gG
  -- the previous half-turn, if that is the blocker
  have hHdata : ∀ iH : Fin N, Set.range (D.tile iH).pts = Kc F i' (t + 1) →
      (D.tile iH).localAngle (Q2 F ((i' : ℝ) + 1) ((t : ℝ) + 1)) = γ ∧ iG ≠ iH ∧
      Set.range (D.tile iH).pts = {Q2 F ((i' : ℝ) + 1) ((t : ℝ) + 1),
        Q2 F (i' : ℝ) ((t : ℝ) + 1 + 1), Q2 F ((i' : ℝ) + 1) ((t : ℝ) + 1 + 1)} := by
    intro iH hrH
    have gH : (D.tile iH).localAngle (Q2 F ((i' : ℝ) + 1) ((t : ℝ) + 1)) = γ := by
      have := (D_angles F FC hrH).1; push_cast at this; exact this
    have rH : Set.range (D.tile iH).pts = {Q2 F ((i' : ℝ) + 1) ((t : ℝ) + 1),
        Q2 F (i' : ℝ) ((t : ℝ) + 1 + 1), Q2 F ((i' : ℝ) + 1) ((t : ℝ) + 1 + 1)} := by
      rw [hrH, D_eq F FC]; push_cast; rfl
    refine ⟨gH, ne_of_range rG rH (p := Q2 F ((i' : ℝ) + 1) t) mem3_3 ?_, rH⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    refine ⟨Q2_ne F FC (Or.inr (by intro h; linarith)), Q2_ne F FC (Or.inl (by intro h; linarith)),
      Q2_ne F FC (Or.inr (by intro h; linarith))⟩
  rcases hcz with ⟨mz, hmz, U, W, hUW, S, hS, hU0, hside⟩ | ⟨m', -, hmpos, hcr, -⟩
  swap
  · -- a straight tile through `X` along `AD_n`
    exfalso
    have hznv : ∀ q, (D.tile z).pts q ≠ Q2 F ((i' : ℝ) + 1) ((t : ℝ) + 1) := fun q hq =>
      NearBaseVertex.vertex_not_edge _ q hq m' hmpos
    have hzs := localAngle_mem_pi_of_mem (D.tile z) hXz hznv
    rcases hcase with ⟨g, d, ⟨ε', hε', hxε'⟩, hgU⟩ | ⟨iH, hrH⟩
    · have sε := straight_count hxε'
      by_cases hze : z = ε'.1
      · obtain ⟨h0, h1, -⟩ := Dissection.mem_lineChain.mp hε'
        rw [← hze] at hxε' h0 h1
        obtain ⟨c2, -, -⟩ := openSeg_coords (D.tile z) ε'.2 hxε'
        have hm : m' = ε'.2 + 2 := by
          by_contra hne
          have := hmpos (ε'.2 + 2) (Ne.symm hne)
          linarith
        subst hm
        rw [fin3_add_two_add_two, fin3_add_two_add_one] at hcr
        have hd0 := sub_ne_zero.mpr (pts_ne (D.tile z) (TraceCovering.fin3_succ_ne ε'.2)).symm
        have hgd : g ((D.tile z).pts (ε'.2 + 1) - (D.tile z).pts ε'.2) = 0 := by
          rw [map_sub, h0, h1, sub_self]
        exact cross_ne_of_g g hd0 hgd hgU hcr
      · have := Level2LemmaGReal.two_straight hze hzs sε
        omega
    · obtain ⟨gH, hGH, -⟩ := hHdata iH hrH
      have := card_two hGH gG gH
      rcases hzs with h | h <;> (have := card_one h; omega)
  -- the corner tile `z` across the `a`-flank
  have hU0n : ‖vec F (cb e f) (-1)‖ = (e : ℝ) * f := norm_VP F
  have hUne : U ≠ 0 := by
    intro h; rw [h, smul_zero] at hU0; rw [hU0, norm_zero] at hU0n; linarith
  obtain ⟨ℓ, hℓdef⟩ : ∃ ℓ : ℝ, ‖U‖ = ℓ := ⟨_, rfl⟩
  have hℓ : 0 < ℓ := hℓdef ▸ norm_pos_iff.mpr hUne
  have hUe : U = (ℓ / ((e : ℝ) * f)) • vec F (cb e f) (-1) := flank_eq hS hU0 hℓdef hU0n ha0
  have hadU : adF F U = 0 := by
    have h1 := congrArg (adF F) hU0
    rw [map_smul, adF_vec F FC, smul_eq_mul] at h1
    have h2 : S * adF F U = 0 := by rw [← h1]; ring
    rcases mul_eq_zero.mp h2 with h | h
    · linarith
    · exact h
  have hadW : 0 < adF F W := by
    have hW := vec_coords F FC W
    rw [hW, cross_vec, cross_vec] at hside
    rw [hW, adF_vec F FC]
    nlinarith
  have hXad : adF F (Q2 F ((i' : ℝ) + 1) ((t : ℝ) + 1)) = adF F F.A + (Nl : ℝ) := by
    rw [adF_Q2 F FC]; linarith
  have hall3 : ∀ k, adF F F.A + (Nl : ℝ) ≤ adF F ((D.tile z).pts k) := by
    intro k
    have hk : (D.tile z).pts k ∈ Set.range (D.tile z).pts := ⟨k, rfl⟩
    rw [ApexPlacement.range_of_flank hmz hUW] at hk
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hk
    rcases hk with h | h | h <;> rw [h]
    · rw [hXad]
    · rw [map_add, hXad, hadU, add_zero]
    · rw [map_add, hXad]; linarith
  obtain ⟨idx, hidx, hE⟩ : ∃ idx : Fin 3, (z, idx) ∈ adChain F (Nl : ℝ) ∧
      EdgeIs D (z, idx) (Q2 F ((i' : ℝ) + 1) ((t : ℝ) + 1))
        (Q2 F ((i' : ℝ) + 1) ((t : ℝ) + 1) + U) := by
    rcases hUW with ⟨h1, -⟩ | ⟨h1, -⟩
    · have e1 : (D.tile z).pts (mz + 1) = Q2 F ((i' : ℝ) + 1) ((t : ℝ) + 1) + U := by
        rw [h1]; abel
      refine ⟨mz, mem_adChain F (by rw [hmz, hXad]) (by rw [e1, map_add, hXad, hadU, add_zero])
        hall3, ?_⟩
      simp only [EdgeIs]; rw [hmz, e1]
    · have e1 : (D.tile z).pts (mz + 2) = Q2 F ((i' : ℝ) + 1) ((t : ℝ) + 1) + U := by
        rw [h1]; abel
      have e2 : (D.tile z).pts (mz + 2 + 1) = Q2 F ((i' : ℝ) + 1) ((t : ℝ) + 1) := by
        rw [fin3_add_two_add_one]; exact hmz
      refine ⟨mz + 2, mem_adChain F (by rw [e1, map_add, hXad, hadU, add_zero])
        (by rw [e2, hXad]) hall3, ?_⟩
      simp only [EdgeIs]; rw [e1, e2, Set.pair_comm]
  have hUq : Q2 F ((i' : ℝ) + 1) ((t : ℝ) + 1) + U
      = Q2 F ((i' : ℝ) + 1 + ℓ / ((e : ℝ) * f)) ((t : ℝ) + 1 - ℓ / ((e : ℝ) * f)) := by
    rw [hUe, vec_smul, Q2_add_eq F (di := ℓ / ((e : ℝ) * f)) (dt := -(ℓ / ((e : ℝ) * f)))
      (by ring) (by ring)]
    congr 1
    try ring
  rw [hUq] at hE
  have hla := hall (z, idx) hidx ℓ hℓ hE
  have hU1 : U = vec F (cb e f) (-1) := by rw [hUe, hla, div_self ha0.ne', one_smul]
  have hang := localAngle_at_own_vertex_mem D α β γ F.hM.hα' F.hM.hβ' F.hM.hγ' z mz
  rw [hmz] at hang
  rcases hang with hz | hz | hz
  · exfalso
    obtain ⟨hn, -⟩ := (corner_dataH F hmz hUW).2 hz
    rcases hn with ⟨h1, -⟩ | ⟨h1, -⟩
    · rw [hℓdef, hla] at h1; exact hab h1
    · rw [hℓdef, hla] at h1; exact hac' h1
  · obtain ⟨hn, hopp⟩ := (corner_dataH F hmz hUW).1 hz
    have hWc : ‖W‖ = (f : ℝ) ^ 2 := by
      rcases hn with ⟨-, h2⟩ | ⟨h1, -⟩
      · exact h2
      · rw [hℓdef, hla] at h1; exact absurd h1 hac'
    have hs2 : cross (vec F (cb e f) (-1)) (vec F (1 + cb e f) (-1)) *
        cross (vec F (cb e f) (-1)) (vec F (-1) 0) < 0 := by
      rw [cross_vec, cross_vec]; nlinarith
    have hr := ident hmz hUW hU1 (by intro h; rw [h, norm_zero] at hU0n; linarith)
      (by have := side_of_across hS hU0 hside hs2; rwa [hU1] at this)
      (by rw [hWc, norm_V])
      (by rw [hopp, dist_add_vec, show cb e f - (1 + cb e f) = -1 by ring,
        show (-1 : ℝ) - (-1) = 0 by ring, norm_vec_m10])
    have e1 : Q2 F ((i' : ℝ) + 1) ((t : ℝ) + 1) + vec F (cb e f) (-1) = Q2 F ((i' : ℝ) + 1 + 1) t := by
      rw [Q2_add_eq F (di := 1) (dt := -1) (by ring) (by ring)]; congr 1; ring
    have e2 : Q2 F ((i' : ℝ) + 1) ((t : ℝ) + 1) + vec F (1 + cb e f) (-1)
        = Q2 F ((i' : ℝ) + 1 + 1) ((t : ℝ) + 1) := by
      rw [Q2_add_eq F (di := 1) (dt := 0) (by ring) (by ring), add_zero]
    refine ⟨z, ?_⟩
    rw [hr, e1, e2, D_eq F FC]; push_cast
    ext p; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  · exfalso
    rcases hcase with ⟨g, d, ⟨ε', hε', hxε'⟩, -⟩ | ⟨iH, hrH⟩
    · have sε := straight_count hxε'
      have := card_two hzG hz gG
      rcases sε with h | h <;> (have := card_one h; omega)
    · obtain ⟨gH, hGH, rH⟩ := hHdata iH hrH
      have hzH : z ≠ iH := ne_of_flank_Q2 F FC hmz hUW hS hU0 rH (d1 := -cb e f) (e1 := 1) (d2 := 1)
        (e2 := 0) (by ring) (by ring) (by ring) (by ring)
        (fun S' hS' h1 h2 => by linarith) (fun S' hS' h1 h2 => by linarith)
      have := card_three hzG hzH hGH hz gG gH
      omega

/-- **(B4) The whole of `σ`**: descending the junctions from the `ℓ_j` end `Y = i₀V + (n−i₀)P′`
(blocker: the band straddle), each junction's half-turn is the next one's blocker. -/
theorem ad_march (L : LFrame F) (Nl i0 q : ℕ) (hi0 : 1 ≤ i0) (hiN : i0 + q ≤ Nl)
    (hall : ∀ ε ∈ adChain F (Nl : ℝ), ∀ s ℓ : ℝ, 0 < ℓ → 0 ≤ s → s < q →
      EdgeIs D ε (Q2 F ((i0 : ℝ) + s) ((Nl : ℝ) - i0 - s))
        (Q2 F ((i0 : ℝ) + s + ℓ / ((e : ℝ) * f)) ((Nl : ℝ) - i0 - s - ℓ / ((e : ℝ) * f))) →
      ℓ = (e : ℝ) * f)
    (hint : ∀ i t, i0 ≤ i → i < i0 + q → i + t + 1 = Nl →
      Q2 F (i : ℝ) ((t : ℝ) + 1) ∈ interior D.target.carrier)
    (hUp : ∀ i t, i0 ≤ i → i < i0 + q → i + t + 1 = Nl → Present D (T2c F i t))
    (hDn : ∀ i t, i0 ≤ i + 1 → i + 1 < i0 + q → i + t + 2 = Nl → Present D (Kc F i t))
    (hY : ∃ g : Plane →ₗ[ℝ] ℝ, ∃ d : ℝ,
      TraceCovering.Straddled D.toDissection g d (Q2 F (i0 : ℝ) ((Nl : ℝ) - i0)) ∧
        g (vec F (cb e f) (-1)) ≠ 0) :
    ∀ i t, i0 ≤ i → i < i0 + q → i + t + 1 = Nl → Present D (Kc F i t) := by
  have key : ∀ n, ∀ i t, i = i0 + n → i < i0 + q → i + t + 1 = Nl → Present D (Kc F i t) := by
    intro n
    induction n with
    | zero =>
      intro i t hi hiq hit
      obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
      have hi0R : ((i0 : ℕ) : ℝ) = (i' : ℝ) + 1 := by exact_mod_cast (show i0 = i' + 1 by omega)
      have hitR : (i' : ℝ) + 1 + t + 1 = Nl := by
        exact_mod_cast (show i' + 1 + t + 1 = Nl by omega)
      have hXint : Q2 F ((i' : ℝ) + 1) ((t : ℝ) + 1) ∈ interior D.target.carrier := by
        have := hint (i' + 1) t (by omega) hiq hit
        push_cast at this; exact this
      have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
      have hall' : ∀ ε ∈ adChain F (Nl : ℝ), ∀ ℓ : ℝ, 0 < ℓ →
          EdgeIs D ε (Q2 F ((i' : ℝ) + 1) ((t : ℝ) + 1))
            (Q2 F ((i' : ℝ) + 1 + ℓ / ((e : ℝ) * f)) ((t : ℝ) + 1 - ℓ / ((e : ℝ) * f))) →
          ℓ = (e : ℝ) * f := by
        intro ε hε ℓ hℓ hE
        apply hall ε hε 0 ℓ hℓ le_rfl hq0
        have e1 : Q2 F ((i0 : ℝ) + 0) ((Nl : ℝ) - i0 - 0) = Q2 F ((i' : ℝ) + 1) ((t : ℝ) + 1) := by
          congr 1 <;> linarith
        have e2 : Q2 F ((i0 : ℝ) + 0 + ℓ / ((e : ℝ) * f)) ((Nl : ℝ) - i0 - 0 - ℓ / ((e : ℝ) * f))
            = Q2 F ((i' : ℝ) + 1 + ℓ / ((e : ℝ) * f)) ((t : ℝ) + 1 - ℓ / ((e : ℝ) * f)) := by
          congr 1 <;> linarith
        rw [e1, e2]; exact hE
      have hY' : ∃ g : Plane →ₗ[ℝ] ℝ, ∃ d : ℝ,
          TraceCovering.Straddled D.toDissection g d (Q2 F ((i' : ℝ) + 1) ((t : ℝ) + 1)) ∧
            g (vec F (cb e f) (-1)) ≠ 0 := by
        obtain ⟨g, d, hs, hg⟩ := hY
        have e1 : Q2 F (i0 : ℝ) ((Nl : ℝ) - i0) = Q2 F ((i' : ℝ) + 1) ((t : ℝ) + 1) := by
          congr 1 <;> linarith
        rw [e1] at hs; exact ⟨g, d, hs, hg⟩
      exact junction F L Nl i' t (by omega) hXint hall' (hUp (i' + 1) t (by omega) hiq hit)
        (hDn i' t (by omega) (by omega) (by omega)) (Or.inl hY')
    | succ n ih =>
      intro i t hi hiq hit
      obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
      have hitR : (i' : ℝ) + 1 + t + 1 = Nl := by
        exact_mod_cast (show i' + 1 + t + 1 = Nl by omega)
      have hsR : (i' : ℝ) + 1 = (i0 : ℝ) + ((n : ℝ) + 1) := by
        have : i' + 1 = i0 + (n + 1) := hi
        exact_mod_cast this
      have hXint : Q2 F ((i' : ℝ) + 1) ((t : ℝ) + 1) ∈ interior D.target.carrier := by
        have := hint (i' + 1) t (by omega) hiq hit
        push_cast at this; exact this
      have hnq : (n : ℝ) + 1 < q := by exact_mod_cast (show n + 1 < q by omega)
      have hall' : ∀ ε ∈ adChain F (Nl : ℝ), ∀ ℓ : ℝ, 0 < ℓ →
          EdgeIs D ε (Q2 F ((i' : ℝ) + 1) ((t : ℝ) + 1))
            (Q2 F ((i' : ℝ) + 1 + ℓ / ((e : ℝ) * f)) ((t : ℝ) + 1 - ℓ / ((e : ℝ) * f))) →
          ℓ = (e : ℝ) * f := by
        intro ε hε ℓ hℓ hE
        apply hall ε hε ((n : ℝ) + 1) ℓ hℓ (by positivity) hnq
        have e1 : Q2 F ((i0 : ℝ) + ((n : ℝ) + 1)) ((Nl : ℝ) - i0 - ((n : ℝ) + 1))
            = Q2 F ((i' : ℝ) + 1) ((t : ℝ) + 1) := by
          congr 1 <;> linarith
        have e2 : Q2 F ((i0 : ℝ) + ((n : ℝ) + 1) + ℓ / ((e : ℝ) * f))
            ((Nl : ℝ) - i0 - ((n : ℝ) + 1) - ℓ / ((e : ℝ) * f))
            = Q2 F ((i' : ℝ) + 1 + ℓ / ((e : ℝ) * f)) ((t : ℝ) + 1 - ℓ / ((e : ℝ) * f)) := by
          congr 1 <;> linarith
        rw [e1, e2]; exact hE
      exact junction F L Nl i' t (by omega) hXint hall' (hUp (i' + 1) t (by omega) hiq hit)
        (hDn i' t (by omega) (by omega) (by omega))
        (Or.inr (ih i' (t + 1) (by omega) (by omega) (by omega)))
  intro i t hi hiq hit
  exact key (i - i0) i t (by omega) hiq hit

/-! ## §3 CW: the hypotheses, the invariant, the two steps, the apex -/

/-- **The march invariant `I(M)`**: every cell of `Q_{j,k}` of level `≤ M` is a tile. -/
def CWInv (F : HFrame D e f α β γ) (j k M : ℕ) : Prop :=
  ∀ i t, i < k → t < j → i + t + 1 ≤ M → Present D (T2c F i t) ∧ Present D (Kc F i t)

/-- **The hypotheses of CW(ℓ_j, m_k)** (proof_CW_P2.md §1.1; review A's restatement specialised to
the c-seed at `kV`, which every call site has — record correction, review_CW R1), with
`X = (n_X − j)V + jP′`:
* range: `1 ≤ j`, `1 ≤ k`, `j ≤ n_X ≤ n₀`, `k ≤ n₀ ≤ k + j − 1` (no relation between `j` and `k`);
* (CW-a) b-seed: a band-side edge of `ℓ_j` from `X` to `X + b·u_r`;
* (CW-b) c-seed: an r-side edge of `m_k` from `kV` to `kV + c·u_l`;
* (CW-c) every cell `U(i,t)`, `D(i,t)` (`i < k`, `t < j`) of level `≤ n₀` is a tile. -/
structure CWH (F : HFrame D e f α β γ) (j k nX n0 : ℕ) : Prop where
  hj : 1 ≤ j
  hk : 1 ≤ k
  hjX : j ≤ nX
  hX0 : nX ≤ n0
  hk0 : k ≤ n0
  h0k : n0 + 1 ≤ k + j
  seedA : ∃ ε ∈ bandChain F (j : ℝ),
    EdgeIs D ε (Q2 F ((nX : ℝ) - j) j) (Q2 F ((nX : ℝ) - j + bcr e f) j)
  seedB : ∃ ε ∈ rsChain F (k : ℝ), EdgeIs D ε (Q2 F k 0) (Q2 F k (cb e f))
  cells : CWInv F j k n0

/-- A vertex of a present `D(i,t)`: `(i+1)V + (t+1)P′` is interior (`O2`). -/
theorem D_vertex_int (L : LFrame F) {i t : ℕ} (h : Present D (Kc F i t)) :
    Q2 F ((i : ℝ) + 1) ((t : ℝ) + 1) ∈ interior D.target.carrier := by
  have FC := L.FC
  have hm : Q2 F ((i : ℝ) + 1) ((t : ℝ) + 1) ∈ D.target.carrier := by
    apply mem_of_present h; rw [D_eq F FC]; exact mem3_3
  have := Q2_int_of_mem F FC (i + 1) (t + 1) (by omega) (by push_cast; exact hm)
  push_cast at this; exact this

set_option maxHeartbeats 1000000 in
/-- **Step A(M)** (proof_CW_P2.md §4.2): the up cells of level `M+1` are tiles.  Each is the residual
`α` at an interior point `X_i^M` (`slot2`; every such point has five known cells since
`n₀ ≥ max(j, k)`); a swap there is a b-seed on `ℓ_{M−i}`, `M − i < j`, and the recursive call
`CW(ℓ_{M−i}, m_k)` with `n_X = n₀ = M` and the same c-seed kills it. -/
theorem cw_up (L : LFrame F) {j k nX n0 M : ℕ} (hC : CWH F j k nX n0)
    (IH : ∀ j' < j, ∀ k' nX' n0' : ℕ, ¬ CWH F j' k' nX' n0')
    (hN0 : n0 ≤ M) (hN : M + 2 ≤ k + j) (hI : CWInv F j k M) :
    ∀ i t, i < k → t < j → i + t = M → Present D (T2c F i t) := by
  have FC := L.FC
  intro i t hi ht hit
  have := hC.hjX; have := hC.hX0; have := hC.hk0
  obtain ⟨a, rfl⟩ : ∃ a, i = a + 1 := ⟨i - 1, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b, t = b + 1 := ⟨t - 1, by omega⟩
  have hA := (hI a b (by omega) (by omega) (by omega)).2
  have hXint := D_vertex_int F L hA
  rcases slot2 F L a b hXint hA (hI a (b + 1) (by omega) (by omega) (by omega)).1
      (hI (a + 1) b (by omega) (by omega) (by omega)).2
      (hI (a + 1) b (by omega) (by omega) (by omega)).1
      (hI a (b + 1) (by omega) (by omega) (by omega)).2 with h | hSw
  · exact h
  · exfalso
    obtain ⟨ε, hε, hE⟩ := seed_of_Sw F FC _ _ hSw
    have hNR : ((M : ℕ) : ℝ) = (a : ℝ) + 1 + ((b : ℝ) + 1) := by
      rw [← hit]; push_cast; ring
    apply IH (b + 1) ht k M M
    refine ⟨by omega, hC.hk, by omega, le_rfl, by omega, by omega, ?_, hC.seedB, ?_⟩
    · have e1 : ((M : ℝ) - ((b + 1 : ℕ) : ℝ)) = (a : ℝ) + 1 := by push_cast; linarith
      rw [e1]; push_cast; exact ⟨ε, hε, hE⟩
    · intro i' t' hi' ht' hit'
      exact hI i' t' hi' (by omega) hit'

set_option maxHeartbeats 2000000 in
/-- **Step B(M+1)** (proof_CW_P2.md §4.3): the down cells of level `M+1` are tiles.  On
`σ_{M+1} = [Y, W]` (`Y = (M+1−j)V + jP′` on `ℓ_j`, `W = kV + (M+1−k)P′` on `m_k`): (B1) the band
side of `ℓ_j` straddles `Y` (`band_str`, Lemma A), (B2) the r-side of `m_k` straddles `W` (`r_str`,
A2), so neither end is straddled from the far side (`no_two_straight`); (B3) the far word is `a^q`
(`far_word`, A1); (B4) the tiles across are the half-turns (`ad_march`). -/
theorem cw_down (L : LFrame F) {j k nX n0 M : ℕ} (hC : CWH F j k nX n0)
    (hN0 : n0 ≤ M) (hN : M + 2 ≤ k + j) (hI : CWInv F j k M)
    (hUp : ∀ i t, i < k → t < j → i + t = M → Present D (T2c F i t)) :
    ∀ i t, i < k → t < j → i + t = M → Present D (Kc F i t) := by
  classical
  have FC := L.FC
  obtain ⟨hcb0, hcb1⟩ := cb_pos F
  have hjX := hC.hjX; have hX0 := hC.hX0; have hk0 := hC.hk0
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by have := hC.hj; omega⟩
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by have := hC.hk; omega⟩
  obtain ⟨x0, rfl⟩ : ∃ x0, nX = j' + 1 + x0 := ⟨nX - (j' + 1), by omega⟩
  obtain ⟨a0, hNa⟩ : ∃ a0, M = j' + 1 + a0 := ⟨M - (j' + 1), by omega⟩
  obtain ⟨w0, hNw⟩ : ∃ w0, M = k' + 1 + w0 := ⟨M - (k' + 1), by omega⟩
  -- the two ends: `Y = (a0+1)V + jP′`, `W = kV + (w0+1)P′`, interior
  have hDY := (hI a0 j' (by omega) (by omega) (by omega)).2
  have hDW := (hI k' w0 (by omega) (by omega) (by omega)).2
  have hYint := D_vertex_int F L hDY
  have hWint := D_vertex_int F L hDW
  have hYle := Q2_le F FC (interior_subset hYint)
  have hWle := Q2_le F FC (interior_subset hWint)
  have hYne := O2 F (a0 + 1) (j' + 1) (by omega)
  have hWne := O2 F (k' + 1) (w0 + 1) (by omega)
  push_cast at hYne hWne
  have hYlt : ((j' : ℝ) + 1) + ((a0 : ℝ) + 1) * cb e f < f := lt_of_le_of_ne hYle hYne
  have hWlt : ((w0 : ℝ) + 1) + ((k' : ℝ) + 1) * cb e f < f := lt_of_le_of_ne hWle hWne
  have hNaR : (M : ℝ) = (j' : ℝ) + 1 + a0 := by rw [hNa]; push_cast; ring
  have hNwR : (M : ℝ) = (k' : ℝ) + 1 + w0 := by rw [hNw]; push_cast; ring
  -- (B1) the band straddle at `Y`
  have hBY : BStr F ((j' : ℝ) + 1) (Q2 F ((a0 : ℝ) + 1) ((j' : ℝ) + 1)) := by
    have hq1 : 1 ≤ a0 + 1 - x0 := by omega
    have h := band_str F L j' x0 (a0 + 1 - x0) hq1 (by
        have : ((a0 + 1 : ℕ) : ℝ) < f := by push_cast; nlinarith
        have : a0 + 1 < f := by exact_mod_cast this
        omega)
      (by have : ((x0 : ℝ) + ((a0 + 1 - x0 : ℕ) : ℝ)) = (a0 : ℝ) + 1 := by
            rw [Nat.cast_sub (by omega)]; push_cast; ring
          rw [this]; exact hYlt)
      (fun s hs => (hI (x0 + s) j' (by omega) (by omega) (by omega)).2)
      (by
        obtain ⟨ε, hε, hE⟩ := hC.seedA
        have e1 : (((j' + 1 + x0 : ℕ) : ℝ) - ((j' + 1 : ℕ) : ℝ)) = (x0 : ℝ) := by push_cast; ring
        rw [e1] at hE; push_cast at hε hE; exact ⟨ε, hε, hE⟩)
    have : ((x0 : ℝ) + ((a0 + 1 - x0 : ℕ) : ℝ)) = (a0 : ℝ) + 1 := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [this] at h; exact h
  -- (B2) the r-side straddle at `W`
  have hMW : MStr F ((k' : ℝ) + 1) (Q2 F ((k' : ℝ) + 1) ((w0 : ℝ) + 1)) := by
    have h := r_str F L k' (w0 + 1) (by omega) (by
        have : ((w0 + 1 : ℕ) : ℝ) < f := by push_cast; nlinarith
        have : w0 + 1 < f := by exact_mod_cast this
        omega)
      (by push_cast; exact hWlt)
      (fun s hs => (hI k' s (by omega) (by omega) (by omega)).2)
      (by obtain ⟨ε, hε, hE⟩ := hC.seedB; push_cast at hε hE; exact ⟨ε, hε, hE⟩)
    push_cast at h; exact h
  -- the ends are not straddled from the far side of `AD_{M+1}`
  have gY : ∃ iA : Fin N, (D.tile iA).localAngle (Q2 F ((a0 : ℝ) + 1) ((j' : ℝ) + 1)) = α := by
    obtain ⟨iA, hrA⟩ := hDY; exact ⟨iA, (D_angles F FC hrA).2.2⟩
  have gW : ∃ iA : Fin N, (D.tile iA).localAngle (Q2 F ((k' : ℝ) + 1) ((w0 : ℝ) + 1)) = α := by
    obtain ⟨iA, hrA⟩ := hDW; exact ⟨iA, (D_angles F FC hrA).2.2⟩
  obtain ⟨iY, gY⟩ := gY
  obtain ⟨iW, gW⟩ := gW
  have hYf : ¬ AStr F ((M + 1 : ℕ) : ℝ) (Q2 F ((a0 : ℝ) + 1) ((j' : ℝ) + 1)) := fun h =>
    no_two_straight F hYint hBY h (ind_ell_ad F FC) gY
  have hWf : ¬ AStr F ((M + 1 : ℕ) : ℝ) (Q2 F ((k' : ℝ) + 1) ((w0 : ℝ) + 1)) := fun h =>
    no_two_straight F hWint hMW h (ind_rho_ad F FC) gW
  -- the whole segment is interior
  have hq : 1 ≤ k' - a0 := by omega
  have hseg : ∀ s : ℝ, 0 ≤ s → s ≤ ((k' - a0 : ℕ) : ℝ) →
      Q2 F (((a0 + 1 : ℕ) : ℝ) + s) (((M + 1 : ℕ) : ℝ) - ((a0 + 1 : ℕ) : ℝ) - s)
        ∈ interior D.target.carrier := by
    intro s hs0 hs1
    rw [Nat.cast_sub (by omega)] at hs1
    push_cast at hs1 ⊢
    have hkR : (k' : ℝ) = (a0 : ℝ) + (k' - a0 : ℝ) := by ring
    apply Q2_interior F FC (by positivity) (by linarith) (by linarith)
    have h1 : s * (cb e f - 1) ≤ ((k' : ℝ) - a0) * (cb e f - 1) :=
      mul_le_mul_of_nonneg_right hs1 (by linarith)
    nlinarith
  have hfar := far_word F L (M + 1) (a0 + 1) (k' - a0) hq (by
      have : ((k' + 1 : ℕ) : ℝ) < f := by push_cast; nlinarith
      have : k' + 1 < f := by exact_mod_cast this
      omega) (by omega)
    (fun s hs0 hs1 => hseg s hs0.le hs1.le)
    (fun i t hi1 hi2 hit => hUp i t (by omega) (by omega) (by omega))
    (by
      have : Q2 F (((a0 + 1 : ℕ) : ℝ)) (((M + 1 : ℕ) : ℝ) - ((a0 + 1 : ℕ) : ℝ))
          = Q2 F ((a0 : ℝ) + 1) ((j' : ℝ) + 1) := by push_cast; congr 1; linarith
      rw [this]; exact hYf)
    (by
      have : Q2 F (((a0 + 1 : ℕ) : ℝ) + ((k' - a0 : ℕ) : ℝ))
          (((M + 1 : ℕ) : ℝ) - ((a0 + 1 : ℕ) : ℝ) - ((k' - a0 : ℕ) : ℝ))
          = Q2 F ((k' : ℝ) + 1) ((w0 : ℝ) + 1) := by
        rw [Nat.cast_sub (by omega)]; push_cast; congr 1 <;> linarith
      rw [this]; exact hWf)
  have hmarch := ad_march F L (M + 1) (a0 + 1) (k' - a0) (by omega) (by omega) hfar
    (fun i t hi1 hi2 hit => by
      have h := hseg ((i : ℝ) - ((a0 + 1 : ℕ) : ℝ)) (by
          have : ((a0 + 1 : ℕ) : ℝ) ≤ i := by exact_mod_cast hi1
          linarith) (by
          rw [Nat.cast_sub (by omega)]
          have : (i : ℝ) < ((a0 + 1 + (k' - a0) : ℕ) : ℝ) := by exact_mod_cast hi2
          rw [Nat.cast_add, Nat.cast_sub (by omega)] at this
          push_cast at this ⊢; linarith)
      have hitR : (i : ℝ) + t + 1 = (M : ℝ) + 1 := by exact_mod_cast hit
      convert h using 2 <;> push_cast <;> linarith)
    (fun i t hi1 hi2 hit => hUp i t (by omega) (by omega) (by omega))
    (fun i t hi1 hi2 hit => (hI i t (by omega) (by omega) (by omega)).2)
    ⟨-(ellF F), -(ellF F F.A + ((j' : ℝ) + 1)), by
      have : Q2 F (((a0 + 1 : ℕ) : ℝ)) (((M + 1 : ℕ) : ℝ) - ((a0 + 1 : ℕ) : ℝ))
          = Q2 F ((a0 : ℝ) + 1) ((j' : ℝ) + 1) := by push_cast; congr 1; linarith
      rw [this]; exact hBY, by
      rw [LinearMap.neg_apply, ellF_vec F FC]; intro h; linarith⟩
  intro i t hi ht hit
  exact hmarch i t (by omega) (by omega) (by omega)

set_option maxHeartbeats 1000000 in
/-- **(T1) The apex** (proof_CW_P2.md §4.5): once every cell of `Q_{j,k}` is a tile, the apex
`Z = kV + jP′` (a vertex of `D(k−1, j−1)`, so interior) is straddled from the band side of `ℓ_j`
(`band_str`, Lemma A: the band word would have value `(k + j − n_X)·c`) and from the r-side of `m_k`
(`r_str`, A2: value `j·b`); two straight tiles and the `α` of `D(k−1, j−1)` overfill `Z`. -/
theorem cw_apex (L : LFrame F) {j k nX n0 : ℕ} (hC : CWH F j k nX n0)
    (hI : CWInv F j k (k + j - 1)) : False := by
  classical
  have FC := L.FC
  obtain ⟨hcb0, hcb1⟩ := cb_pos F
  have hjX := hC.hjX; have hX0 := hC.hX0; have hk0 := hC.hk0; have h0k := hC.h0k
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by have := hC.hj; omega⟩
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by have := hC.hk; omega⟩
  obtain ⟨x0, rfl⟩ : ∃ x0, nX = j' + 1 + x0 := ⟨nX - (j' + 1), by omega⟩
  have hDZ := (hI k' j' (by omega) (by omega) (by omega)).2
  have hZint := D_vertex_int F L hDZ
  have hZle := Q2_le F FC (interior_subset hZint)
  have hZne := O2 F (k' + 1) (j' + 1) (by omega)
  push_cast at hZne
  have hZlt : ((j' : ℝ) + 1) + ((k' : ℝ) + 1) * cb e f < f := lt_of_le_of_ne hZle hZne
  have hBZ : BStr F ((j' : ℝ) + 1) (Q2 F ((k' : ℝ) + 1) ((j' : ℝ) + 1)) := by
    have h := band_str F L j' x0 (k' + 1 - x0) (by omega) (by
        have : ((k' + 1 : ℕ) : ℝ) < f := by push_cast; nlinarith
        have : k' + 1 < f := by exact_mod_cast this
        omega)
      (by have : ((x0 : ℝ) + ((k' + 1 - x0 : ℕ) : ℝ)) = (k' : ℝ) + 1 := by
            rw [Nat.cast_sub (by omega)]; push_cast; ring
          rw [this]; exact hZlt)
      (fun s hs => (hI (x0 + s) j' (by omega) (by omega) (by omega)).2)
      (by
        obtain ⟨ε, hε, hE⟩ := hC.seedA
        have e1 : (((j' + 1 + x0 : ℕ) : ℝ) - ((j' + 1 : ℕ) : ℝ)) = (x0 : ℝ) := by push_cast; ring
        rw [e1] at hE; push_cast at hε hE; exact ⟨ε, hε, hE⟩)
    have : ((x0 : ℝ) + ((k' + 1 - x0 : ℕ) : ℝ)) = (k' : ℝ) + 1 := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [this] at h; exact h
  have hMZ : MStr F ((k' : ℝ) + 1) (Q2 F ((k' : ℝ) + 1) ((j' : ℝ) + 1)) := by
    have h := r_str F L k' (j' + 1) (by omega) (by
        have : ((j' + 1 : ℕ) : ℝ) < f := by push_cast; nlinarith
        have : j' + 1 < f := by exact_mod_cast this
        omega)
      (by push_cast; exact hZlt)
      (fun s hs => (hI k' s (by omega) (by omega) (by omega)).2)
      (by obtain ⟨ε, hε, hE⟩ := hC.seedB; push_cast at hε hE; exact ⟨ε, hε, hE⟩)
    push_cast at h; exact h
  obtain ⟨iA, hrA⟩ := hDZ
  exact no_two_straight F hZint hBZ hMZ (ind_ell_rho F FC) (D_angles F FC hrA).2.2

/-- **CW(ℓ_j, m_k) — THE CONVERGING WALLS, frame form — PROVED** (proof_CW_P2.md §§1.1, 4, 6; every
regime, including `j > k`, the regime of Λ3M's calls).  In the apex frame of a dissection (with the
target's cone coordinates), no `CWH F j k n_X n₀` holds.  Outer strong induction on `j` (the only
recursive call, the swap at a slot, lowers `j` and keeps `k` and the c-seed); inner march over the
levels `n₀ ≤ N ≤ k + j − 1` (`cw_up`, `cw_down`); the apex `cw_apex`.  The **m = 1** inputs, and
nothing else: Lemma A on `ℓ_j` (`Inflation.c_side_no_b`, in `band_str`), A2 on `m_k`
(`Inflation.b_side_rigid`, in `r_str`), A1 on `AD_n` (`Inflation.a_side_no_b`, `a_side_rigid`, in
`far_word`); each needs a line of fewer than `f` cells, which fails at `m ≥ 2` (N = 44:
`2c = a + 2b`, `2b = a + c`, `2a = c`).  The b-free leg (`lem:sidenob`) is NOT used. -/
theorem cw_frame (L : LFrame F) : ∀ j k nX n0 : ℕ, ¬ CWH F j k nX n0 := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j IH =>
  intro k nX n0 hC
  have h0k := hC.h0k
  have hk0 := hC.hk0
  have key : ∀ d, n0 + d + 1 ≤ k + j → CWInv F j k (n0 + d) := by
    intro d
    induction d with
    | zero => intro _; rw [Nat.add_zero]; exact hC.cells
    | succ d ih =>
      intro hd
      have hI := ih (by omega)
      have hUp := cw_up F L hC (fun j' hj' k' nX' n0' => IH j' hj' k' nX' n0') (by omega)
        (by omega) hI
      have hDn := cw_down F L hC (by omega) (by omega) hI hUp
      intro i t hi ht hit
      rcases Nat.lt_or_ge (i + t + 1) (n0 + d + 1) with hlt | hge
      · exact hI i t hi ht (by omega)
      · exact ⟨hUp i t hi ht (by omega), hDn i t hi ht (by omega)⟩
  have hfin := key (k + j - 1 - n0) (by omega)
  rw [show n0 + (k + j - 1 - n0) = k + j - 1 by omega] at hfin
  exact cw_apex F L hC hfin

/-! ## §4 For real dissections -/

/-- **CW(ℓ_j, m_k) FOR EVERY APEX FRAME OF A REAL `m = 1` DISSECTION — PROVED.**  For every
congruent dissection of the `m = 1` base-β target (coprime `2 ≤ e ≤ f − 2`, `M1Data`) and every apex
frame `F` of it with cone coordinates: no `CWH F j k n_X n₀`, for all `j, k, n_X, n₀` (every
regime; c-seed at `kV`). -/
theorem cw_real_all {kk : Fin 3} (h : ApexFrameReal.M1Data D e f α β γ kk)
    (FC : ApexPlacement.FrameCoords F) : ∀ j k nX n0 : ℕ, ¬ CWH F j k nX n0 :=
  cw_frame F (lframe_real F h FC)

/-- **CW(ℓ_j, m_k) FOR EVERY REAL `m = 1` DISSECTION — PROVED.**  Every congruent dissection of the
`m = 1` base-β target (coprime `2 ≤ e ≤ f − 2`, `M1Data`) carries its apex frame `F`
(`ApexLegWord.exists_hframe_coords_m1`), and in it no `CWH F j k n_X n₀` holds. -/
theorem cw_real {kk : Fin 3} (h : ApexFrameReal.M1Data D e f α β γ kk) :
    ∃ F : Erdos634.Draft.HalfTurnR3R4Glue.HFrame D e f α β γ, ApexPlacement.FrameCoords F ∧
      ∀ j k nX n0 : ℕ, ¬ CWH F j k nX n0 := by
  obtain ⟨F, FC⟩ := ApexLegWord.exists_hframe_coords_m1 D h.hco h.he h.hef h.hM h.hAng kk
    h.hcorner h.hβ1 h.hβ2 h.hleg1 h.hleg2 h.hbase
  exact ⟨F, FC, cw_real_all F h FC⟩

end Erdos634.Draft.RowWallReal

#print axioms Erdos634.Draft.RowWallReal.far_word
#print axioms Erdos634.Draft.RowWallReal.junction
#print axioms Erdos634.Draft.RowWallReal.ad_march
#print axioms Erdos634.Draft.RowWallReal.cw_up
#print axioms Erdos634.Draft.RowWallReal.cw_down
#print axioms Erdos634.Draft.RowWallReal.cw_apex
#print axioms Erdos634.Draft.RowWallReal.cw_frame
#print axioms Erdos634.Draft.RowWallReal.cw_real_all
#print axioms Erdos634.Draft.RowWallReal.cw_real
