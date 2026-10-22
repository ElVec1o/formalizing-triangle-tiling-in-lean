-- Draft/LaczFormalIVcRatB9b.lean -- Laczkovich DCG 48 (2012), Sect. 8.3 (Subcase IVc, rational branch), BLUEPRINT Part B, item B9: `vw_star` (the star statement).
--   `vw_star_frame`: T a VWTiling (finite index types) of a CONVEX A with nonempty interior, F = (X; p, q) a Frame with A inside the quadrant
--   {fa >= 0, fb >= 0} and X = F.pt 0 0 in A => there are k, m >= 1 (naturals) with A = {0 <= fa <= k, 0 <= fb <= m}, a parallelogram.
--   Proof: strong induction on the number of rhombus pieces.  `row_of_rhombi` gives the row R_0..R_{k-1}; `fa_le_row` gives A in {fa <= k};
--   if nothing lies above fb = 1, A is the row; else `complement_row` removes the row (nonempty S), the restriction T' is a VWTiling of
--   A' = A inter {fb >= 1}, convex, in the quadrant of `shiftq`, with the corner X + q; IH gives A' = [0,k'] x [1, 1+m'], and k' = k
--   (X + k p + q in row R_{k-1} is in A'; and A' inside A inside {fa <= k}).
--   `vw_star`: from the area corner of B6 via `corner_cone` (B9a).  No angle at Y and no polygon vertex count is used.
--   Witness: B7w one-rhombus tiling is the case k = m = 1.  Hypotheses of vw_star are witnessed by corner_piece_witness_concl (B6w).
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 8.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIVcRatB9a

open scoped Classical Fin.NatCast
open MeasureTheory
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement Erdos634.CertCoord

namespace Erdos634.Draft.LaczFormal.RG

theorem Frame.mem_rowPar_of {b : ℝ} (F : Frame b) (hb : 0 < b) (i : ℕ) (y : Plane) (h1 : (i : ℝ) ≤ F.fa y) (h2 : F.fa y ≤ i + 1)
    (h3 : 0 ≤ F.fb y) (h4 : F.fb y ≤ 1) : y ∈ VWTiling.rowPar F i := by
  have hr := F.recon hb y
  have e0 := congrArg (fun z : Plane => z 0) hr
  have e1 := congrArg (fun z : Plane => z 1) hr
  simp only [Frame.pt_zero] at e0
  simp only [Frame.pt_one] at e1
  exact ⟨F.fa y - i, F.fb y, by linarith, by linarith, h3, h4, by rw [e0]; ring, by rw [e1]; ring⟩

theorem box_rows {b : ℝ} (F : Frame b) (hb : 0 < b) (j : ℕ) (y : Plane) (h1 : 0 ≤ F.fa y) (h2 : F.fa y ≤ ((j + 1 : ℕ) : ℝ))
    (h3 : 0 ≤ F.fb y) (h4 : F.fb y ≤ 1) : ∃ i : ℕ, i < j + 1 ∧ y ∈ VWTiling.rowPar F i := by
  refine ⟨min ⌊F.fa y⌋₊ j, lt_of_le_of_lt (min_le_right _ _) (Nat.lt_succ_self j), F.mem_rowPar_of hb _ y ?_ ?_ h3 h4⟩
  · exact le_trans (Nat.cast_le.mpr (min_le_left _ _)) (Nat.floor_le h1)
  · rcases min_choice ⌊F.fa y⌋₊ j with h | h
    · rw [h]; exact (Nat.lt_floor_add_one _).le
    · rw [h]; push_cast at h2; linarith

theorem fb_smul_add {b : ℝ} (F : Frame b) (z w : Plane) (s : ℝ) :
    F.fb (s • z + (1 - s) • w) = s * F.fb z + (1 - s) * F.fb w := by
  rw [F.fb_eq, F.fb_eq z, F.fb_eq w]
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  ring

namespace VWTiling
variable {b : ℝ} {ιK : Type} [Fintype ιK]

/-- **B9 (frame form).** -/
theorem vw_star_frame (hb : 0 < b) : ∀ n : ℕ, ∀ {ιR : Type} [Fintype ιR] {A : Set Plane} (T : VWTiling b A ιK ιR),
    Fintype.card ιR = n → Convex ℝ A → ∀ F : Frame b, (∀ y ∈ A, 0 ≤ F.fa y ∧ 0 ≤ F.fb y) → F.pt 0 0 ∈ A → (interior A).Nonempty →
    ∃ k m : ℕ, 1 ≤ k ∧ 1 ≤ m ∧ A = {y | 0 ≤ F.fa y ∧ F.fa y ≤ (k : ℝ) ∧ 0 ≤ F.fb y ∧ F.fb y ≤ (m : ℝ)} := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro ιR _ A T hn hconv F hquad hXA hint
  obtain ⟨k, hk1, hrows, hkA, hend⟩ := T.row_of_rhombi hb hconv F hquad hXA hint
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  obtain ⟨r0, hr0⟩ := hrows j (Nat.lt_succ_self j)
  have hfa := T.fa_le_row hb hconv F (fun y hy => (hquad y hy).2) j hr0 hkA hend
  have rowsub : ∀ i : ℕ, i < j + 1 → ∀ y ∈ rowPar F i, y ∈ A := by
    intro i hi y hy
    obtain ⟨r, hr⟩ := hrows i hi
    exact T.R_subset r (by rw [hr]; exact hy)
  by_cases hw : ∃ w ∈ A, 1 < F.fb w
  · -- remove the row
    obtain ⟨S, hSne, hU⟩ := T.complement_row hb hconv F hquad j hrows hkA hend hw
    have hmemU : ∀ y, y ∈ ((⋃ k, (T.K k).set) ∪ ⋃ r : {r // r ∉ S}, (T.R r.1).set) ↔ y ∈ A ∧ 1 ≤ F.fb y := by
      intro y; rw [hU]; rfl
    obtain ⟨s0, hs0⟩ := hSne
    have hcard : Fintype.card {r // r ∉ S} < n := hn ▸ Fintype.card_subtype_lt (x := s0) (by simpa using hs0)
    have hconv' : Convex ℝ ((⋃ k, (T.K k).set) ∪ ⋃ r : {r // r ∉ S}, (T.R r.1).set) := by
      rw [hU]; exact convex_complement hconv F
    have hquad' : ∀ y ∈ ((⋃ k, (T.K k).set) ∪ ⋃ r : {r // r ∉ S}, (T.R r.1).set), 0 ≤ F.shiftq.fa y ∧ 0 ≤ F.shiftq.fb y := by
      intro y hy
      obtain ⟨hyA, hy1⟩ := (hmemU y).1 hy
      rw [F.shiftq_fa hb, F.shiftq_fb hb]
      exact ⟨(hquad y hyA).1, by linarith⟩
    have hX' : F.shiftq.pt 0 0 ∈ ((⋃ k, (T.K k).set) ∪ ⋃ r : {r // r ∉ S}, (T.R r.1).set) := by
      rw [F.shiftq_pt, (hmemU _)]
      have hm : F.pt 0 (1 + 0) ∈ rowPar F 0 := ⟨0, 1, by norm_num, by norm_num, by norm_num, by norm_num,
        by rw [F.pt_zero]; push_cast; ring, by rw [F.pt_one]; push_cast; ring⟩
      refine ⟨rowsub 0 (Nat.succ_pos j) _ hm, ?_⟩
      rw [F.fb_pt hb]; norm_num
    have hint' : (interior ((⋃ k, (T.K k).set) ∪ ⋃ r : {r // r ∉ S}, (T.R r.1).set)).Nonempty := by
      obtain ⟨z, hz⟩ := hint
      obtain ⟨w, hwA, hw1⟩ := hw
      have hzb := (hquad z (interior_subset hz)).2
      set m := F.fb w with hm
      set c := F.fb z with hc
      set d := |m - c| with hd
      have hd0 : 0 ≤ d := abs_nonneg _
      set s : ℝ := min (1 / 2) ((m - 1) / (2 * (d + 1))) with hs
      have hsp : 0 < s := lt_min (by norm_num) (by apply div_pos <;> [linarith; positivity])
      have hs2 : s ≤ 1 / 2 := min_le_left _ _
      have hs3 : s * (2 * (d + 1)) ≤ m - 1 := by
        have := min_le_right (1 / 2 : ℝ) ((m - 1) / (2 * (d + 1)))
        rw [← hs] at this
        rwa [le_div_iff₀ (by positivity)] at this
      have hu : s • z + (1 - s) • w ∈ interior A := by
        apply hconv.openSegment_interior_self_subset_interior hz hwA
        exact ⟨s, 1 - s, hsp, by linarith, by ring, rfl⟩
      have hfb : 1 < F.fb (s • z + (1 - s) • w) := by
        rw [fb_smul_add]
        have h1 : s * (m - c) ≤ s * d := mul_le_mul_of_nonneg_left (le_abs_self _) hsp.le
        nlinarith
      have hopen : IsOpen {y : Plane | 1 < F.fb y} := isOpen_lt continuous_const F.continuous_fb
      have hmem : s • z + (1 - s) • w ∈ interior (A ∩ {y | 1 < F.fb y}) := by
        rw [interior_inter, hopen.interior_eq]; exact ⟨hu, hfb⟩
      have hsub : A ∩ {y | 1 < F.fb y} ⊆ ((⋃ k, (T.K k).set) ∪ ⋃ r : {r // r ∉ S}, (T.R r.1).set) :=
        fun y hy => (hmemU y).2 ⟨hy.1, le_of_lt hy.2⟩
      exact ⟨_, interior_mono hsub hmem⟩
    obtain ⟨k', m', hk', hm', hset⟩ := ih _ hcard (T.restrict S) rfl hconv' F.shiftq hquad' hX' hint'
    have hset' : ∀ y, y ∈ ((⋃ k, (T.K k).set) ∪ ⋃ r : {r // r ∉ S}, (T.R r.1).set) ↔
        (0 ≤ F.fa y ∧ F.fa y ≤ (k' : ℝ) ∧ 0 ≤ F.fb y - 1 ∧ F.fb y - 1 ≤ (m' : ℝ)) := by
      intro y; rw [hset]; simp only [Set.mem_setOf_eq, F.shiftq_fa hb, F.shiftq_fb hb]
    have hk1' : (k' : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := by
      have hy : F.pt (k' : ℝ) 1 ∈ ((⋃ k, (T.K k).set) ∪ ⋃ r : {r // r ∉ S}, (T.R r.1).set) := by
        rw [hset', F.fa_pt hb, F.fb_pt hb]; exact ⟨by positivity, le_rfl, by norm_num, by simp⟩
      have := hfa _ ((hmemU _).1 hy).1
      rwa [F.fa_pt hb] at this
    have hk2' : ((j + 1 : ℕ) : ℝ) ≤ (k' : ℝ) := by
      have hm : F.pt (((j + 1 : ℕ) : ℝ)) 1 ∈ rowPar F j := ⟨1, 1, by norm_num, by norm_num, by norm_num, by norm_num,
        by rw [F.pt_zero]; push_cast; ring, by rw [F.pt_one]; push_cast; ring⟩
      have hy : F.pt (((j + 1 : ℕ) : ℝ)) 1 ∈ ((⋃ k, (T.K k).set) ∪ ⋃ r : {r // r ∉ S}, (T.R r.1).set) := by
        rw [hmemU]; exact ⟨rowsub j (Nat.lt_succ_self j) _ hm, by rw [F.fb_pt hb]⟩
      have := ((hset' _).1 hy).2.1
      rwa [F.fa_pt hb] at this
    have hkeq : (k' : ℝ) = ((j + 1 : ℕ) : ℝ) := le_antisymm hk1' hk2'
    refine ⟨j + 1, 1 + m', by omega, by omega, ?_⟩
    ext y
    simp only [Set.mem_setOf_eq]
    constructor
    · intro hyA
      have hq := hquad y hyA
      refine ⟨hq.1, hfa y hyA, hq.2, ?_⟩
      by_cases h1 : F.fb y ≤ 1
      · push_cast; linarith [(Nat.cast_nonneg m' : (0 : ℝ) ≤ m')]
      · push_cast
        have := ((hset' y).1 ((hmemU y).2 ⟨hyA, by linarith⟩)).2.2.2
        linarith
    · rintro ⟨h1, h2, h3, h4⟩
      by_cases h5 : F.fb y ≤ 1
      · obtain ⟨i, hi, hyi⟩ := box_rows F hb j y h1 h2 h3 h5
        exact rowsub i hi y hyi
      · push Not at h5
        have : y ∈ ((⋃ k, (T.K k).set) ∪ ⋃ r : {r // r ∉ S}, (T.R r.1).set) := by
          rw [hset']
          refine ⟨h1, by rw [hkeq]; exact h2, by linarith, ?_⟩
          push_cast at h4; linarith
        exact ((hmemU y).1 this).1
  · -- A is the row
    push Not at hw
    refine ⟨j + 1, 1, by omega, le_rfl, ?_⟩
    ext y
    simp only [Set.mem_setOf_eq]
    constructor
    · intro hyA
      have hq := hquad y hyA
      exact ⟨hq.1, hfa y hyA, hq.2, by simpa using hw y hyA⟩
    · rintro ⟨h1, h2, h3, h4⟩
      obtain ⟨i, hi, hyi⟩ := box_rows F hb j y h1 h2 h3 (by simpa using h4)
      exact rowsub i hi y hyi

/-- **B9 (vw_star).** A V/W tiling of a convex `A` with an area corner of angle pi/3 at `X`: `A` is a parallelogram
`{X + a p + t q : 0 <= a <= k, 0 <= t <= m}` for a frame `(X; p, q)`, `|p| = |q| = b`, `p.q = b^2/2`, `k, m >= 1` naturals. -/
theorem vw_star {A : Set Plane} {ιR : Type} [Fintype ιR] (T : VWTiling b A ιK ιR) (hb : 0 < b) (hconv : Convex ℝ A) {X : Plane} {ρ : ℝ} (hρ : 0 < ρ)
    (hX : ∀ r, 0 < r → r ≤ ρ → volume (A ∩ Metric.ball X r) = ENNReal.ofReal (Real.pi / 3 / 2 * r ^ 2)) :
    ∃ F : Frame b, F.pt 0 0 = X ∧ ∃ k m : ℕ, 1 ≤ k ∧ 1 ≤ m ∧
      A = {y | 0 ≤ F.fa y ∧ F.fa y ≤ (k : ℝ) ∧ 0 ≤ F.fb y ∧ F.fb y ≤ (m : ℝ)} := by
  obtain ⟨F, hF0, hquad, hint⟩ := T.corner_cone hb hconv hρ hX
  have hXA : X ∈ A := by
    obtain ⟨c0, ⟨j, hXj⟩, _⟩ := T.corner_cell hb hρ hX
    rw [hXj]
    exact (Set.subset_iUnion (fun c => (T.cellT c).carrier) c0).trans T.cells_cover.subset (pts_mem _ _)
  obtain ⟨k, m, hk, hm, hA⟩ := vw_star_frame hb _ T rfl hconv F hquad (by rw [hF0]; exact hXA) hint
  exact ⟨F, hF0, k, m, hk, hm, hA⟩

end VWTiling

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.VWTiling.vw_star_frame
#print axioms Erdos634.Draft.LaczFormal.RG.VWTiling.vw_star
