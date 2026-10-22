-- Draft/R1Pierce.lean — R1 steps 1–2 on the parallel frame `R1Frame` (every coprime 1 ≤ e < f):
-- `V` is pierced (thm:pierce(iii)), `T₂` and `T₃` both present `γ` at `P′` (cor:noTP, vertex case),
-- so no tile edge passes through `P′`; `T₂` presents `β` at `V`; the corner census at `V`.
-- Imported into All.lean (header updated 2026-10-01).  Part of the R1 formalization (proof_R1_compressed.md, room W2).
--
-- REUSE LEDGER.  `V_pierced` is `HalfTurnR3R4Glue.HFrame.chain_point_pierced` at `k = 1` (COPIED:
-- the `HFrame` version needs `e + 2 ≤ f`; the only place it enters is `c < f·b`, which holds at every
-- `1 ≤ e < f`, proved here as `c_lt_fb`).  It uses the far-side TRACE COVERING
-- (`TraceCovering.wall_sum`, Draft) + Lemma A (`Inflation.c_side_no_b`, `k = 1 < f`).
-- `two_gamma_at_pprime` is `ApexFrameReal.two_gamma_at_pprime` (itself `TileIdent.t2_t3_gamma`)
-- COPIED onto `R1Frame`.  `no_straight_at_pprime` / `fill_at_V` cite
-- `ThickEFminus1Steps.no_straight_at_two_gamma` / `corners_fill_pi_sub_beta` (Draft, P29).
--
-- Build (scratch oleans; never .lake): R1Frame, ThickEFminus1Steps oleans in $S, then lean_guard.sh.
import Erdos634.Draft.R1Frame
import Erdos634.Draft.ThickEFminus1Steps
import Erdos634.RouteOneThroughEdge
import Erdos634.CornerAnglePerm

namespace Erdos634.Draft.R1Pierce

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.Draft.HalfTurnR3R4Glue
open Erdos634.Draft.R1Frame

variable {N : ℕ} {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ}

/-- `c < f·b` at every `1 ≤ e < f` (`f² − e² ≥ 2f − 1 > f`). -/
theorem c_lt_fb {e f : ℕ} (he : 1 ≤ e) (hef : e < f) :
    (f : ℝ) ^ 2 < (f : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) := by
  have heR : (1 : ℝ) ≤ e := by exact_mod_cast he
  have h1 : (e : ℝ) + 1 ≤ f := by exact_mod_cast hef
  have hf1 : (1 : ℝ) < f := by linarith
  have h2 : (f : ℝ) < (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by nlinarith
  nlinarith

/-- `T₂`'s vertices, indexed: `T₂ = {A, V, P′}` has an edge `m` from `A` to `V` (either order) and
its third vertex `P′`. -/
theorem T2_indexed (F : R1Frame D e f α β γ) :
    ∃ (i2 : Fin N) (m : Fin 3),
      Set.range (D.tile i2).pts = {F.A, F.V, F.P} ∧
      (((D.tile i2).pts m = F.A ∧ (D.tile i2).pts (m + 1) = F.V) ∨
        ((D.tile i2).pts m = F.V ∧ (D.tile i2).pts (m + 1) = F.A)) ∧
      (D.tile i2).pts (m + 2) = F.P := by
  obtain ⟨i2, hi2⟩ := F.hT2
  obtain ⟨kA, hkA⟩ := MarchInduction.mem_range_of_eq hi2 (Set.mem_insert _ _)
  have hfin1 : kA + 2 + 1 = kA := by fin_cases kA <;> rfl
  have hfin2 : kA + 2 + 2 = kA + 1 := by fin_cases kA <;> rfl
  refine ⟨i2, ?_⟩
  rcases MarchInduction.vertex_data_of_range hi2 hkA with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨kA, hi2, Or.inl ⟨hkA, h1⟩, h2⟩
  · exact ⟨kA + 2, hi2, Or.inr ⟨h2, by rw [hfin1, hkA]⟩, by rw [hfin2, h1]⟩

/-- `V` is interior to the target. -/
theorem V_interior (F : R1Frame D e f α β γ) : F.V ∈ interior D.target.carrier := by
  rw [F.hV]
  exact F.hrint _ (pow_pos (by exact_mod_cast (show 0 < f by have := F.hef; omega)) 2)
    (c_lt_fb F.he F.hef)

/-- **`thm:pierce(iii)`, formal, every coprime `1 ≤ e < f`: `V` is pierced** — a far-side edge of the
mismatch ray `r` has `V` in its relative interior.  (Copy of `HFrame.chain_point_pierced` at `k = 1`:
otherwise the far edges on `[A, V]` form a word of value `c` containing `T₁`'s `b`, which Lemma A
(`Inflation.c_side_no_b`, `1 < f`) forbids.) -/
theorem V_pierced (F : R1Frame D e f α β γ) :
    TraceCovering.Straddled D.toDissection (-F.h) (-(F.h F.A)) F.V := by
  classical
  obtain ⟨i2, m2, -, hm01, -⟩ := T2_indexed F
  have hedgeAV : (D.tile i2).edge m2 = segment ℝ F.A F.V := by
    rw [Tri.edge]
    rcases hm01 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
    exact segment_symm ℝ _ _
  by_contra hns
  have hef := F.hef
  have he := F.he
  have hu1 : ‖F.uR‖ = 1 := F.huR
  have hu0 : F.uR ≠ 0 := TraceCovering.ne_zero_of_norm hu1
  have hgd₂ : ∀ y, (-F.h) y = -(F.h F.A) ↔ F.h y = F.h F.A := TraceCovering.neg_iff
  have hh' : (-F.h : Plane →ₗ[ℝ] ℝ) ≠ 0 := fun h => F.hh0 (neg_eq_zero.mp h)
  have hfR : (0 : ℝ) < f := by exact_mod_cast (show 0 < f by omega)
  have hefR : (e : ℝ) < f := by exact_mod_cast hef
  have heR : (0 : ℝ) ≤ e := Nat.cast_nonneg e
  have hb_pos : (0 : ℝ) < (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by nlinarith
  have hc_pos : (0 : ℝ) < (f : ℝ) ^ 2 := by positivity
  have hA0 : F.A + (0 : ℝ) • F.uR = F.A := by rw [zero_smul, add_zero]
  have hcfb := c_lt_fb he hef
  have ht0 : (0 : ℝ) ≤ (f : ℝ) ^ 2 := hc_pos.le
  -- (i) interior
  have hint : ∀ x ∈ Set.Ioo 0 ((f : ℝ) ^ 2), F.A + x • F.uR ∈ interior D.target.carrier :=
    fun x hx => F.hrint x hx.1 (lt_trans hx.2 hcfb)
  -- (ii) the wall: `T₂`'s `c`-edge `[A, V]`
  have hwall : ∀ x ∈ Set.Ioo 0 ((f : ℝ) ^ 2), ∀ i, F.A + x • F.uR ∉ interior (D.tile i).carrier := by
    intro x hx i
    have hmem : F.A + x • F.uR ∈ (D.tile i2).edge m2 := by
      rw [hedgeAV, F.hV]
      have hs := TraceCovering.segment_param (X := F.A) (u := F.uR) 0 ((f : ℝ) ^ 2)
      rw [hA0, min_eq_left ht0, max_eq_right ht0] at hs
      rw [hs]
      exact ⟨x, ⟨hx.1.le, hx.2.le⟩, rfl⟩
    exact D.toDissection.edge_point_not_interior hmem i
  -- (iii) no far edge passes through the apex
  have hback : ∀ s : ℝ, s < 0 → F.A + s • F.uR ∉ D.target.carrier := by
    intro s hs
    obtain ⟨kA, hkA⟩ := MarchInduction.mem_range_of_eq F.htarget (Set.mem_insert _ _)
    have hv : ((f : ℝ) ^ 2 / 2) • F.uR ≠ 0 := smul_ne_zero (by positivity) hu0
    have hin : D.target.pts kA + ((f : ℝ) ^ 2 / 2) • F.uR ∈ D.target.carrier := by
      rw [hkA]; exact interior_subset (hint ((f : ℝ) ^ 2 / 2) ⟨by positivity, by linarith⟩)
    have := TraceCovering.vertex_ray_out D.target kA hv hin (t := s / ((f : ℝ) ^ 2 / 2))
      (div_neg_of_neg_of_pos hs (by positivity))
    rwa [hkA, smul_smul, div_mul_cancel₀ _ (by positivity)] at this
  have hstart := TraceCovering.not_straddled_of_outside_before (D := D.toDissection) (g := -F.h)
    (d := -(F.h F.A)) hgd₂ F.hh0 rfl F.hhuR hu0 (x₀ := 0) hback
  have hns' : ¬ TraceCovering.Straddled D.toDissection (-F.h) (-(F.h F.A))
      (F.A + ((f : ℝ) ^ 2) • F.uR) := by rw [← F.hV]; exact hns
  -- TRACE COVERING, far side, on `[A, V]`
  have hsum := TraceCovering.wall_sum (D := D.toDissection) hh' hgd₂ F.hh0 rfl F.hhuR hu1 ht0
    hint hwall hstart hns'
  -- `T₁`'s `b`-edge is one of them
  obtain ⟨i1, hi1⟩ := F.hT1
  set Bp := F.A + ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) • F.uR with hBp
  set Rf := F.A + (1 / (f : ℝ)) • (F.R - F.A) with hRf
  obtain ⟨kA1, hkA1⟩ := MarchInduction.mem_range_of_eq hi1 (Set.mem_insert _ _)
  have hfin1 : kA1 + 2 + 1 = kA1 := by fin_cases kA1 <;> rfl
  have hfin2 : kA1 + 2 + 2 = kA1 + 1 := by fin_cases kA1 <;> rfl
  obtain ⟨m, hm01', hm2⟩ : ∃ m : Fin 3,
      (((D.tile i1).pts m = F.A ∧ (D.tile i1).pts (m + 1) = Bp) ∨
        ((D.tile i1).pts m = Bp ∧ (D.tile i1).pts (m + 1) = F.A)) ∧
      (D.tile i1).pts (m + 2) = Rf := by
    rcases MarchInduction.vertex_data_of_range hi1 hkA1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨kA1, Or.inl ⟨hkA1, h1⟩, h2⟩
    · exact ⟨kA1 + 2, Or.inr ⟨h2, by rw [hfin1, hkA1]⟩, by rw [hfin2, h1]⟩
  have hhB : F.h Bp = F.h F.A := TraceCovering.f_param rfl F.hhuR _
  have hhRf : F.h F.A < F.h Rf := by
    rw [hRf, map_add, map_smul, map_sub, smul_eq_mul]
    have := F.hhR
    have : 0 < 1 / (f : ℝ) * (F.h F.R - F.h F.A) := mul_pos (by positivity) (by linarith)
    linarith
  have he1 : (i1, m) ∈ D.toDissection.lineChain (-F.h) (-(F.h F.A)) := by
    rw [Dissection.mem_lineChain]
    have h3 : ∀ i m : Fin 3, i = m ∨ i = m + 1 ∨ i = m + 2 := by decide
    refine ⟨?_, ?_, fun i => ?_⟩
    · rcases hm01' with ⟨h1, -⟩ | ⟨h1, -⟩ <;> rw [h1] <;> simp [hhB]
    · rcases hm01' with ⟨-, h1⟩ | ⟨-, h1⟩ <;> rw [h1] <;> simp [hhB]
    · rcases h3 i m with rfl | rfl | rfl
      · rcases hm01' with ⟨h1, -⟩ | ⟨h1, -⟩ <;> rw [h1] <;> simp [hhB]
      · rcases hm01' with ⟨-, h1⟩ | ⟨-, h1⟩ <;> rw [h1] <;> simp [hhB]
      · rw [hm2]; simp only [LinearMap.neg_apply, neg_le_neg_iff]; exact hhRf.le
  have hedge1 : (D.tile i1).edge m = segment ℝ F.A Bp := by
    rw [Tri.edge]
    rcases hm01' with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
    exact segment_symm ℝ _ _
  have hdist1 : dist ((D.tile i1).pts m) ((D.tile i1).pts (m + 1))
      = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
    have hdb : dist F.A Bp = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
      rw [hBp, dist_comm, dist_eq_norm, add_sub_cancel_left, norm_smul, hu1, mul_one,
        Real.norm_of_nonneg hb_pos.le]
    rcases hm01' with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
    · exact hdb
    · rw [dist_comm]; exact hdb
  have hbt : (f : ℝ) ^ 2 - (e : ℝ) ^ 2 ≤ (f : ℝ) ^ 2 := by nlinarith
  have hBseg : Bp ∈ segment ℝ (F.A + (0 : ℝ) • F.uR) (F.A + ((f : ℝ) ^ 2) • F.uR) := by
    rw [TraceCovering.segment_param, min_eq_left ht0, max_eq_right ht0]
    exact ⟨_, ⟨hb_pos.le, hbt⟩, rfl⟩
  have hAseg : F.A ∈ segment ℝ (F.A + (0 : ℝ) • F.uR) (F.A + ((f : ℝ) ^ 2) • F.uR) := by
    convert left_mem_segment ℝ (F.A + (0 : ℝ) • F.uR) (F.A + ((f : ℝ) ^ 2) • F.uR) using 1
    exact hA0.symm
  set sF := (D.toDissection.lineChain (-F.h) (-(F.h F.A))).filter
    (fun e => (D.toDissection.tile e.1).edge e.2 ⊆
      segment ℝ (F.A + (0 : ℝ) • F.uR) (F.A + ((f : ℝ) ^ 2) • F.uR)) with hsF
  have hmemF : (i1, m) ∈ sF := by
    refine Finset.mem_filter.mpr ⟨he1, ?_⟩
    show (D.tile i1).edge m ⊆ _
    rw [hedge1]
    exact (convex_segment _ _).segment_subset hAseg hBseg
  rw [← Finset.add_sum_erase sF _ hmemF] at hsum
  obtain ⟨P', Q', R', hPQR, -⟩ := sum_three_values (sF.erase (i1, m))
    (fun e => dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)))
    ((e : ℝ) * f) ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ((f : ℝ) ^ 2)
    (fun ε _ => edge_len_mem D F.hM.hs0 F.hM.hs1 F.hM.hs2 ε.1 ε.2)
  have hee : e ^ 2 ≤ f ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hnat : P' * (e * f) + (Q' + 1) * (f ^ 2 - e ^ 2) + R' * f ^ 2 = 1 * f ^ 2 := by
    have : ((P' * (e * f) + (Q' + 1) * (f ^ 2 - e ^ 2) + R' * f ^ 2 : ℕ) : ℝ)
        = ((1 * f ^ 2 : ℕ) : ℝ) := by
      push_cast [Nat.cast_sub hee]
      simp only at hsum hdist1
      rw [hdist1] at hsum
      linarith
    exact_mod_cast this
  have := Inflation.c_side_no_b e f (f ^ 2 - e ^ 2) 1 P' (Q' + 1) R' (by omega) (by omega) F.hco
    (by omega) (by omega) hnat
  omega

/-- **`cor:noTP`'s input at `P′`, every coprime `1 ≤ e < f`: `T₂` and `T₃` both present `γ` there.**
(Copy of `ApexFrameReal.two_gamma_at_pprime` onto `R1Frame`.) -/
theorem two_gamma_at_pprime (F : R1Frame D e f α β γ) :
    ∃ i2 i3 : Fin N, i2 ≠ i3 ∧ Set.range (D.tile i2).pts = {F.A, F.V, F.P} ∧
      Set.range (D.tile i3).pts = {F.A, F.P, F.A + ((f : ℝ) ^ 2) • F.uL} ∧
      (D.tile i2).localAngle F.P = γ ∧ (D.tile i3).localAngle F.P = γ := by
  obtain ⟨hab, hac, hbc⟩ := sides_distinct1 F.hco F.he F.hef
  have hloc := fun {i : Fin N} {P Q R : Plane} (hr : Set.range (D.tile i).pts = {P, Q, R}) =>
    localAngle_of_rangeE D hab hac hbc F.hM.hs0 F.hM.hs1 F.hM.hs2 F.hM.hα' F.hM.hβ' F.hM.hγ' hr
  have hf2 : (0 : ℝ) ≤ (f : ℝ) ^ 2 := by positivity
  have hAV : dist F.A F.V = (f : ℝ) ^ 2 := by rw [F.hV]; exact dist_self_add_unit F.huR hf2
  have hAJ : dist F.A (F.A + ((f : ℝ) ^ 2) • F.uL) = (f : ℝ) ^ 2 := dist_self_add_unit F.huL hf2
  obtain ⟨i2, h2⟩ := F.hT2
  obtain ⟨i3, h3⟩ := F.hT3
  have h2' : Set.range (D.tile i2).pts = {F.P, F.A, F.V} := by
    rw [h2]; ext y; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  have h3' : Set.range (D.tile i3).pts = {F.P, F.A, F.A + ((f : ℝ) ^ 2) • F.uL} := by
    rw [h3]; ext y; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  refine ⟨i2, i3, ?_, h2, h3, (hloc h2').2.2 hAV, (hloc h3').2.2 hAJ⟩
  intro heq
  subst heq
  have hVmem : F.V ∈ ({F.A, F.P, F.A + ((f : ℝ) ^ 2) • F.uL} : Set Plane) := by
    rw [← h3, h2]; simp
  have hef := F.hef
  have he := F.he
  have heR : (1 : ℝ) ≤ e := by exact_mod_cast he
  have hefR : (e : ℝ) < f := by exact_mod_cast hef
  have hfpos : (0 : ℝ) < f := by linarith
  have he0 : (0 : ℝ) < e := by linarith
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hVmem
  rcases hVmem with hVA | hVP | hVJ
  · rw [hVA, dist_self] at hAV; nlinarith
  · have := F.hVP; rw [hVP, dist_self] at this; nlinarith
  · have huRL : F.uR = F.uL := by
      have h' : ((f : ℝ) ^ 2) • F.uR = ((f : ℝ) ^ 2) • F.uL := by
        have := hVJ; rw [F.hV] at this; exact add_left_cancel this
      exact smul_right_injective _ (by positivity : ((f : ℝ) ^ 2) ≠ 0) h'
    have hJ3 : F.A + ((f : ℝ) ^ 3) • F.uL ∈ D.target.carrier := by
      apply subset_convexHull ℝ _
      rw [F.htarget]; simp
    apply F.hrbase ((f : ℝ) * (e : ℝ) ^ 2) (mul_pos hfpos (pow_pos he0 2))
    have : F.A + ((f : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) + (f : ℝ) * (e : ℝ) ^ 2) • F.uR
        = F.A + ((f : ℝ) ^ 3) • F.uL := by
      rw [huRL]; congr 2; ring
    rw [this]; exact hJ3

/-- **`cor:noTP` at `P′` (vertex case), every coprime `1 ≤ e < f`: no tile presents a straight
angle at `P′`** (two `γ`'s and `2γ = π + α`; `ThickEFminus1Steps.no_straight_at_two_gamma`). -/
theorem no_straight_at_pprime (F : R1Frame D e f α β γ) :
    ∀ k, (D.tile k).localAngle F.P ≠ Real.pi := by
  obtain ⟨i2, i3, h23, -, -, h2, h3⟩ := two_gamma_at_pprime F
  have hA := F.hAng
  exact ThickEFminus1Steps.no_straight_at_two_gamma D.toDissection hA.hγdef hA.hrel hA.hα hA.hβ
    hA.hirr F.hPint
    (fun i => Erdos634.Geometry.congruentDissection_localAngle_mem_all D α β γ F.hM.hα' F.hM.hβ'
      F.hM.hγ' F.P i) i2 i3 h23 h2 h3

/-- `T₂` presents `β` at `V` (`c` joins its `α` at `A` and its `β` at `V`; `|AP′| = b`). -/
theorem T2_beta_at_V (F : R1Frame D e f α β γ) {i2 : Fin N}
    (h2 : Set.range (D.tile i2).pts = {F.A, F.V, F.P}) : (D.tile i2).localAngle F.V = β := by
  obtain ⟨hab, hac, hbc⟩ := sides_distinct1 F.hco F.he F.hef
  have h2' : Set.range (D.tile i2).pts = {F.V, F.A, F.P} := by
    rw [h2]; ext y; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  exact (localAngle_of_rangeE D hab hac hbc F.hM.hs0 F.hM.hs1 F.hM.hs2 F.hM.hα' F.hM.hβ'
    F.hM.hγ' h2').2.1 F.hAP

/-- **The piercer.**  Some tile has `V` in the relative interior of an edge lying on `r`, with the
tile on the far side (`h ≥ h A`); it presents `π` at `V`. -/
theorem piercer (F : R1Frame D e f α β γ) :
    ∃ ε ∈ D.toDissection.lineChain (-F.h) (-(F.h F.A)),
      F.V ∈ openSegment ℝ ((D.tile ε.1).pts ε.2) ((D.tile ε.1).pts (ε.2 + 1)) ∧
      (D.tile ε.1).localAngle F.V = Real.pi ∧
      ∀ y ∈ (D.tile ε.1).carrier, F.h F.A ≤ F.h y := by
  obtain ⟨ε, hε, hV⟩ := V_pierced F
  refine ⟨ε, hε, hV, ?_, ?_⟩
  · have e1 : ε.2 + 2 + 1 = ε.2 := (by decide : ∀ x : Fin 3, x + 2 + 1 = x) _
    have e2 : ε.2 + 2 + 2 = ε.2 + 1 := (by decide : ∀ x : Fin 3, x + 2 + 2 = x + 1) _
    apply Erdos634.RouteOne.openSegment_localAngle_pi (D.tile ε.1) (ε.2 + 2)
    rw [e1, e2]; exact hV
  · intro y hy
    have := (D.tile ε.1).carrier_subset_halfplane (-F.h) (-(F.h F.A))
      (Dissection.mem_lineChain.mp hε).2.2 y hy
    simp only [LinearMap.neg_apply, neg_le_neg_iff] at this
    exact this

/-- **The census at `V` (step 1's fill)**: with the piercer (`π`) and `T₂` (`β`), exactly one tile is
straight at `V`, none is `2π`, and the other corners fill `π − β`
(`ThickEFminus1Steps.corners_fill_pi_sub_beta`). -/
theorem fill_at_V (F : R1Frame D e f α β γ) {k t : Fin N}
    (hk : (D.tile k).localAngle F.V = Real.pi) (ht : (D.tile t).localAngle F.V = β) :
    ({i | (D.tile i).localAngle F.V = Real.pi} : Finset (Fin N)).card = 1 ∧
    ({i | (D.tile i).localAngle F.V = 2 * Real.pi} : Finset (Fin N)).card = 0 ∧
    (({i | (D.tile i).localAngle F.V = α} : Finset (Fin N)).card : ℝ) * α
      + ((({i | (D.tile i).localAngle F.V = β} : Finset (Fin N)).card : ℝ) - 1) * β
      + (({i | (D.tile i).localAngle F.V = γ} : Finset (Fin N)).card : ℝ) * γ
      = Real.pi - β := by
  have hA := F.hAng
  exact ThickEFminus1Steps.corners_fill_pi_sub_beta D.toDissection hA.hγdef hA.hrel hA.hα hA.hβ
    hA.hirr (V_interior F)
    (fun i => Erdos634.Geometry.congruentDissection_localAngle_mem_all D α β γ F.hM.hα' F.hM.hβ'
      F.hM.hγ' F.V i) k t hk ht

end Erdos634.Draft.R1Pierce

#print axioms Erdos634.Draft.R1Pierce.c_lt_fb
#print axioms Erdos634.Draft.R1Pierce.T2_indexed
#print axioms Erdos634.Draft.R1Pierce.V_interior
#print axioms Erdos634.Draft.R1Pierce.V_pierced
#print axioms Erdos634.Draft.R1Pierce.two_gamma_at_pprime
#print axioms Erdos634.Draft.R1Pierce.no_straight_at_pprime
#print axioms Erdos634.Draft.R1Pierce.T2_beta_at_V
#print axioms Erdos634.Draft.R1Pierce.piercer
#print axioms Erdos634.Draft.R1Pierce.fill_at_V
