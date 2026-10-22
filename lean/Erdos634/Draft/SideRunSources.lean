/-
Draft/SideRunSources.lean -- Stage 4a of the formalization of the side theorem of room GAP3: where the hypotheses
(K1) and (K3) of the run lemma come from ((private working notes, not included), sections 1 and 3).

Figures: `Setup.gamma_alpha_alpha`, `Setup.four_alpha`, `Setup.three_beta` (an open point of the side),
`Setup.corner_two_alpha` (a corner of angle `α + β` does not carry two tiles showing `α`: the rest of the corner
would be a multiple of `α`, against the irrationality of `α/π`).

(K1), in the form `Ctx.hK1` "no tile of the side `σ` has both `P` and `p(0,1)` as vertices":
* `Setup.K1_of_gamma`: `P` is an open point of the side and the side tile beyond `P` shows `γ` at `P`;
* `Setup.K1_of_corner`: `P` is a corner of angle `α + β` of the target;
* `Setup.junction`: at the common end of a run to the left and a run to the right, one of the two has (K1).
The chords: `Setup.hch_pos`, `Setup.hch_corner`.

(K3): `Setup.K3_out_right`, `Setup.K3_out_left` (the run ends at a corner of angle `β`),
`Ctx.K3_of_next` (the tile across the last `a`-edge lays more than `a`, unless it shows `γ` or `β` at the end of the
run), `Setup.bad_nb`, `Setup.bad_corner` (it does not: the side tile beyond the end shows `γ` or `β`; the end is a
corner of angle `α + β`).

Composite-N work; not prime-case work.  No sorry, no native_decide.
-/
import Erdos634.Draft.SideRunK

namespace Erdos634.Draft.SideRun

open Erdos634.Geometry Erdos634.CertCoord Erdos634.MarchKillsFan Erdos634.MarchSlots
  Erdos634.MarchInduction Erdos634.RunPartition Erdos634.E1BaseWord Erdos634.Geometry.Dissection
  Erdos634.Draft.W2E1 Set

variable {N : ℕ} {D : CongruentDissection N} {n : ℕ} {α β γ L ax ay ε x : ℝ}

theorem sum_alpha_or_zero {ι : Type*} (s : Finset ι) (f : ι → ℝ) (a : ℝ)
    (h : ∀ i ∈ s, f i = a ∨ f i = 0) : ∃ c : ℕ, ∑ i ∈ s, f i = c * a := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert i s hi ih =>
    obtain ⟨c, hc⟩ := ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
    rw [Finset.sum_insert hi, hc]
    rcases h i (Finset.mem_insert_self i s) with hg | hg
    · exact ⟨c + 1, by rw [hg]; push_cast; ring⟩
    · exact ⟨c, by rw [hg]; ring⟩

/-- a tile with the `b`-edge `[pts k, pts m]` shows `γ` or `α` at `pts k` -/
theorem b_edge_angle {f : ℝ} (hf : 2 ≤ f) (hM : ModelData D f α β γ) {t : Fin N} {k m : Fin 3}
    (hkm : k ≠ m) (hd : dist ((D.tile t).pts k) ((D.tile t).pts m) = f ^ 2 - 1) :
    (D.tile t).localAngle ((D.tile t).pts k) = γ ∨ (D.tile t).localAngle ((D.tile t).pts k) = α := by
  obtain ⟨j, hjk, hjm⟩ := fin3_third k m hkm
  have hA := angle_at_vertex D hf hM t hkm (Ne.symm hjk) (Ne.symm hjm)
  rcases sides_of_b_edge D hf hM t hkm (Ne.symm hjk) (Ne.symm hjm) hd with ⟨s1, s2⟩ | ⟨s1, s2⟩
  · left; exact hA.2.2 (by rw [dist_comm]; exact s2)
  · right; exact hA.1 (by rw [dist_comm]; exact s2)

theorem lp_step_u (n ε x : ℝ) : lp n ε x (0 + 1) 0 = mkPt (x + ε * n ^ 2) 0 := by
  unfold lp; exact mkPt_congr (by ring) (by ring)

theorem lp_step_v (n ε x : ℝ) : lp n ε x 0 (0 + 1) = mkPt (x + ε * (n ^ 2 - uu n)) (hh n) := by
  unfold lp; exact mkPt_congr (by ring) (by ring)

namespace Setup

/-! ## 1. Figures -/

theorem gamma_alpha_alpha (S : Setup D n α β γ L ax ay) {v : ℝ} (hv0 : 0 < v) (hvL : v < L)
    {i j l : Fin N} (hil : i ≠ l) (hi : (D.tile i).localAngle (mkPt v 0) = α)
    (hj : (D.tile j).localAngle (mkPt v 0) = γ) (hl : (D.tile l).localAngle (mkPt v 0) = α) :
    False :=
  straight_point_gamma_no_second_alpha D S.hA.hα S.hA.hβ S.hA.hαβ S.hA.hγdef S.hA.hrel S.hA.hirr
    S.hM.hα' S.hM.hβ' S.hM.hγ' (S.base_frontier hv0 hvL).1 (S.base_frontier hv0 hvL).2 hil hi hj hl

theorem four_alpha (S : Setup D n α β γ L ax ay) {v : ℝ} (hv0 : 0 < v) (hvL : v < L)
    {i k₁ k₂ l : Fin N} (h12 : i ≠ k₁) (h13 : i ≠ k₂) (h14 : i ≠ l) (h23 : k₁ ≠ k₂)
    (h24 : k₁ ≠ l) (h34 : k₂ ≠ l) (hi : (D.tile i).localAngle (mkPt v 0) = α)
    (hk₁ : (D.tile k₁).localAngle (mkPt v 0) = α) (hk₂ : (D.tile k₂).localAngle (mkPt v 0) = α)
    (hl : (D.tile l).localAngle (mkPt v 0) = α) : False :=
  straight_point_no_fourth_alpha D S.hA.hα S.hA.hβ S.hA.hαβ S.hA.hγdef S.hA.hrel S.hA.hirr
    S.hM.hα' S.hM.hβ' S.hM.hγ' (S.base_frontier hv0 hvL).1 (S.base_frontier hv0 hvL).2 h12 h13 h14
    h23 h24 h34 hi hk₁ hk₂ hl

/-- an open point of the side does not carry three tiles showing `β` -/
theorem three_beta (S : Setup D n α β γ L ax ay) {v : ℝ} (hv0 : 0 < v) (hvL : v < L)
    {i j l : Fin N} (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l)
    (hi : (D.tile i).localAngle (mkPt v 0) = β) (hj : (D.tile j).localAngle (mkPt v 0) = β)
    (hl : (D.tile l).localAngle (mkPt v 0) = β) : False := by
  classical
  obtain ⟨hαβ, hαγ, hαπ, hα0, hβγ, hβπ, hβ0, -, hγπ, hγ0, hπ0⟩ := distinct_of_angleData S.hA
  obtain ⟨hv, hnv⟩ := S.base_frontier hv0 hvL
  have hsub : ({i, j, l} : Finset (Fin N))
      ⊆ ({m | (D.tile m).localAngle (mkPt v 0) = β} : Finset (Fin N)) := by
    intro m hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hm with rfl | rfl | rfl <;> assumption
  have hcard : ({i, j, l} : Finset (Fin N)).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair hjl]
    simp [hij, hil]
  have h3 := Finset.card_le_card hsub
  rw [hcard] at h3
  rcases congruentDissection_boundary_figure_cases D α β γ hαβ hαγ hαπ hα0 hβγ hβπ hβ0 hγπ hγ0 hπ0
    S.hA.hγdef S.hA.hrel S.hA.hirr S.hM.hα' S.hM.hβ' S.hM.hγ' hv hnv with
    ⟨_, _, hB, _⟩ | ⟨_, hB, _⟩ | ⟨_, hB, _⟩
  · omega
  · omega
  · omega

/-- **A corner of angle `α + β` does not carry two tiles showing `α`.** -/
theorem corner_two_alpha (S : Setup D n α β γ L ax ay)
    (hQ : D.target.localAngle (mkPt 0 0) = α + β) {i j : Fin N} (hij : i ≠ j)
    (hi : (D.tile i).localAngle (mkPt 0 0) = α) (hj : (D.tile j).localAngle (mkPt 0 0) = α) :
    False := by
  classical
  obtain ⟨hα, hβ, hγ2, hsum, hγπ⟩ := angle_facts S.hA
  have hγdef := S.hA.hγdef
  have hrel := S.hA.hrel
  have hπ := Real.pi_pos
  have hs := D.toDissection.sum_localAngle_eq (mkPt 0 0)
  rw [hQ] at hs
  have h1 : (D.tile i).localAngle (mkPt 0 0)
      + ∑ m ∈ Finset.univ.erase i, (D.tile m).localAngle (mkPt 0 0)
      = ∑ m, (D.tile m).localAngle (mkPt 0 0) :=
    Finset.add_sum_erase Finset.univ (fun m => (D.tile m).localAngle (mkPt 0 0))
      (Finset.mem_univ i)
  have h2 : (D.tile j).localAngle (mkPt 0 0)
      + ∑ m ∈ (Finset.univ.erase i).erase j, (D.tile m).localAngle (mkPt 0 0)
      = ∑ m ∈ Finset.univ.erase i, (D.tile m).localAngle (mkPt 0 0) :=
    Finset.add_sum_erase (Finset.univ.erase i) (fun m => (D.tile m).localAngle (mkPt 0 0))
      (Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ j⟩)
  rw [hi] at h1
  rw [hj] at h2
  have hrest : ∑ m ∈ (Finset.univ.erase i).erase j, (D.tile m).localAngle (mkPt 0 0) = β - α := by
    linarith
  have hvals : ∀ m ∈ (Finset.univ.erase i).erase j,
      (D.tile m).localAngle (mkPt 0 0) = α ∨ (D.tile m).localAngle (mkPt 0 0) = 0 := by
    intro m hm
    have hmem := congruentDissection_localAngle_mem D α β γ S.hM.hα' S.hM.hβ' S.hM.hγ' 0 m
    rw [S.Q_eq] at hmem
    have hle : (D.tile m).localAngle (mkPt 0 0) ≤ β - α := by
      rw [← hrest]
      exact Finset.single_le_sum (f := fun m => (D.tile m).localAngle (mkPt 0 0))
        (fun a _ => (D.tile a).localAngle_nonneg _) hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h | h | h | h
    · exact Or.inl h
    · exfalso; rw [h] at hle; linarith
    · exfalso; rw [h] at hle; linarith
    · exfalso; rw [h] at hle; linarith
    · exact Or.inr h
  obtain ⟨c, hc⟩ := sum_alpha_or_zero _ _ α hvals
  rw [hrest] at hc
  have h5 : (((2 * c + 5 : ℕ)) : ℝ) * α = Real.pi := by
    push_cast
    linarith
  have hne : (((2 * c + 5 : ℕ)) : ℝ) ≠ 0 := by positivity
  apply S.hA.hirr
  refine ⟨((2 * c + 5 : ℕ) : ℚ)⁻¹, ?_⟩
  rw [Rat.cast_inv, Rat.cast_natCast, ← h5, inv_mul_cancel_left₀ hne]

/-! ## 2. Hypothesis (K1) -/

/-- the chords from an open point of the side are interior to the target -/
theorem hch_pos (S : Setup D n α β γ L ax ay) (hx0 : 0 < x) (hxL : x < L)
    (hP : mkPt x 0 ∈ D.target.carrier) :
    ∀ j : ℕ, 1 ≤ j → lp n ε x 0 j ∈ D.target.carrier →
      openSegment ℝ (lp n ε x 0 0) (lp n ε x 0 j) ⊆ interior D.target.carrier := by
  intro j hj hmem
  rw [lp_zero]
  have hjpos : (0:ℝ) < j := by exact_mod_cast hj
  refine S.interior_seg hP hmem (Or.inr ?_) (Or.inl ?_) (Or.inl ?_)
  · rw [lp_one]; exact mul_pos hjpos (hh_pos S.f1)
  · rw [gA_mk]; nlinarith [mul_pos S.hay hx0]
  · rw [gB_mk]; nlinarith [mul_pos S.hay (sub_pos.mpr hxL)]

/-- the chords from a corner of angle `α + β` at `Q` are interior to the target -/
theorem hch_corner (S : Setup D n α β γ L ax ay) {t : ℝ} (ht : 0 < t) (hax : ax = t)
    (hay' : ay = t * rt n) (hP : mkPt 0 0 ∈ D.target.carrier) :
    ∀ j : ℕ, 1 ≤ j → lp n 1 0 0 j ∈ D.target.carrier →
      openSegment ℝ (lp n 1 0 0 0) (lp n 1 0 0 j) ⊆ interior D.target.carrier := by
  intro j hj hmem
  rw [lp_zero]
  have hjpos : (0:ℝ) < j := by exact_mod_cast hj
  have hhp := hh_pos S.f1
  have h1 := ruh S.f1
  have h2 := two_hh_lt S.f1
  refine S.interior_seg hP hmem (Or.inr ?_) (Or.inr ?_) (Or.inl ?_)
  · rw [lp_one]; exact mul_pos hjpos hhp
  · unfold lp
    rw [gA_mk, hax, hay']
    have e : t * rt n * (0 + 1 * ((0 + (j:ℝ)) * (n:ℝ) ^ 2 - (j:ℝ) * uu n)) - t * ((j:ℝ) * hh n)
        = t * j * (((n:ℝ) ^ 2 - 1) * rt n - 2 * hh n) := by
      linear_combination (-(t * (j:ℝ))) * h1
    rw [e]
    exact mul_pos (mul_pos ht hjpos) (by linarith)
  · rw [gB_mk]; nlinarith [mul_pos S.hay S.hL]

/-- **(K1) from a side tile showing `γ` at `P`.**  `P = (x, 0)` is an open point of the side; a tile `j` has the
vertices `P` and `(x − ε λ, 0)`, `λ ∈ {a, b}`, and shows `γ` at `P`. -/
theorem K1_of_gamma (S : Setup D n α β γ L ax ay) (hε : ε ^ 2 = 1) (hx0 : 0 < x) (hxL : x < L)
    {t₀ : Fin N}
    (h0 : HasV D t₀ (lp n ε x 0 0) (lp n ε x (0 + 1) 0) (lp n ε x 0 (0 + 1)))
    {j : Fin N} {kj mj : Fin 3} {lam : ℝ} (hkmj : kj ≠ mj) (hkj : (D.tile j).pts kj = mkPt x 0)
    (hmj : (D.tile j).pts mj = mkPt (x - ε * lam) 0) (hlam : lam = n ∨ lam = (n:ℝ) ^ 2 - 1)
    (hγj : (D.tile j).localAngle (mkPt x 0) = γ) :
    ∀ (t' : Fin N) (k m : Fin 3), k ≠ m → (D.tile t').pts k = lp n ε x 0 0 →
      (D.tile t').pts m = lp n ε x 0 1 → (∀ i, FX n ε ((D.tile t').pts i) ≤ lv n ε x 0) → False := by
  intro t' k m hkm hk hm hle
  have hf1 := S.f1
  have hf0 := S.f0
  have hf2 := S.f2
  have hb := S.b_pos
  have hhp := hh_pos hf1
  have hn0 : (n:ℝ) ≠ 0 := hf0.ne'
  have hnn : (n:ℝ) < (n:ℝ) ^ 2 - 1 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hf2) hf0.le]
  obtain ⟨hα, hβ, hγ2, hsum, hγπ⟩ := angle_facts S.hA
  have hP : lp n ε x 0 0 = mkPt x 0 := lp_zero _ _ _
  have ht0 : t' ≠ t₀ := by
    obtain ⟨i, hi⟩ := h0.idx₂
    refine ne_of_F (FX n ε) hle (i := i) ?_
    rw [hi, FX_lp hε]
    exact lv_lt hf1 (by norm_num)
  have hd : dist ((D.tile t').pts k) ((D.tile t').pts m) = (n:ℝ) ^ 2 - 1 := by
    rw [hk, hm]
    have := dist_step_v (x := x) hf1 hε 0 0
    rwa [zero_add] at this
  have hG1 : (lp n ε x 0 1) 1 = hh n := by rw [lp_one]; ring
  have hang := b_edge_angle hf2 S.hM hkm hd
  rw [hk, hP] at hang
  rcases hang with hγ' | hα'
  · -- two `γ` at `P`
    have hne : t' ≠ j := by
      rintro rfl
      have hmk : m ≠ kj := by
        intro h
        rw [h, hkj] at hm
        have := congrArg (fun p : Plane => p 1) hm
        simp only [mkPt_one] at this
        rw [hG1] at this
        linarith
      have hmm : m ≠ mj := by
        intro h
        rw [h, hmj] at hm
        have := congrArg (fun p : Plane => p 1) hm
        simp only [mkPt_one] at this
        rw [hG1] at this
        linarith
      have hlampos : 0 < lam := by rcases hlam with h | h <;> rw [h] <;> linarith
      have hdj : dist ((D.tile t').pts kj) ((D.tile t').pts mj) = lam := by
        rw [hkj, hmj]
        refine dist_eq_of_sq_eq ?_ dist_nonneg hlampos.le
        rw [dist_sq_mkPt]
        linear_combination (lam ^ 2) * hε
      have hdG : dist ((D.tile t').pts m) ((D.tile t').pts kj) = (n:ℝ) ^ 2 - 1 := by
        rw [dist_comm, hkj, ← hP, ← hk]; exact hd
      rcases hlam with h | h
      · -- an `A`-tile: its third vertex would be at distance `c` from `(x − ε a, 0)`
        rw [h] at hdj hmj
        rcases sides_of_a_edge D hf2 S.hM t' hkmj (Ne.symm hmk) (Ne.symm hmm) hdj with
          ⟨s1, -⟩ | ⟨-, s2⟩
        · rw [hdG] at s1; linarith
        · have hξ : (n:ℝ) * (1 / (n:ℝ)) = 1 := mul_one_div_cancel hn0
          have hξpos : (0:ℝ) < 1 / (n:ℝ) := by positivity
          have e : mkPt (x - ε * (n:ℝ)) 0 = lp n ε x (-(1 / (n:ℝ))) 0 := by
            unfold lp
            refine mkPt_congr ?_ (by ring)
            linear_combination (ε * (n:ℝ)) * hξ
          rw [hm, hmj, e] at s2
          have hsq := dist_lp_sq (x := x) hf1 hε 0 1 (-(1 / (n:ℝ))) 0
          rw [s2] at hsq
          unfold Qf at hsq
          have e1 : (n:ℝ) ^ 4 * (1 / (n:ℝ)) ^ 2 = (n:ℝ) ^ 2 := by
            linear_combination ((n:ℝ) ^ 2 * ((n:ℝ) * (1 / (n:ℝ)) + 1)) * hξ
          have e2 : (2 * (n:ℝ) ^ 4 - 3 * (n:ℝ) ^ 2 + 1) * (1 / (n:ℝ))
              = 2 * (n:ℝ) ^ 3 - 3 * n + 1 / (n:ℝ) := by
            linear_combination (2 * (n:ℝ) ^ 3 - 3 * n) * hξ
          have hpoly : (0:ℝ) < 2 * (n:ℝ) ^ 3 - (n:ℝ) ^ 2 - 3 * n + 1 := by
            nlinarith [mul_nonneg (sub_nonneg.mpr hf2)
              (show (0:ℝ) ≤ 2 * (n:ℝ) ^ 2 + 3 * n + 3 by positivity)]
          linarith
      · -- a `B`-tile: two sides `b`
        rw [h] at hdj
        rcases sides_of_b_edge D hf2 S.hM t' hkmj (Ne.symm hmk) (Ne.symm hmm) hdj with
          ⟨s1, -⟩ | ⟨s1, -⟩
        · rw [hdG] at s1; linarith
        · rw [hdG] at s1; linarith
    have h2 := two_angles_le D.toDissection (mkPt x 0) hne
    rw [hγ', hγj, S.angle_base hx0 hxL] at h2
    linarith
  · -- `γ`, `α`, `α` at `P`
    have ha0 := (U_angles S hε h0).1
    rw [hP] at ha0
    exact S.gamma_alpha_alpha hx0 hxL ht0 hα' hγj ha0

/-- **(K1) at a corner of angle `α + β`.** -/
theorem K1_of_corner (S : Setup D n α β γ L ax ay) (hε : ε ^ 2 = 1)
    (hQ : D.target.localAngle (mkPt 0 0) = α + β) {t₀ : Fin N}
    (h0 : HasV D t₀ (lp n ε 0 0 0) (lp n ε 0 (0 + 1) 0) (lp n ε 0 0 (0 + 1))) :
    ∀ (t' : Fin N) (k m : Fin 3), k ≠ m → (D.tile t').pts k = lp n ε 0 0 0 →
      (D.tile t').pts m = lp n ε 0 0 1 → (∀ i, FX n ε ((D.tile t').pts i) ≤ lv n ε 0 0) → False := by
  intro t' k m hkm hk hm hle
  have hf1 := S.f1
  obtain ⟨hα, hβ, hγ2, hsum, hγπ⟩ := angle_facts S.hA
  have hP : lp n ε 0 0 0 = mkPt 0 0 := lp_zero _ _ _
  have ht0 : t' ≠ t₀ := by
    obtain ⟨i, hi⟩ := h0.idx₂
    refine ne_of_F (FX n ε) hle (i := i) ?_
    rw [hi, FX_lp hε]
    exact lv_lt hf1 (by norm_num)
  have hd : dist ((D.tile t').pts k) ((D.tile t').pts m) = (n:ℝ) ^ 2 - 1 := by
    rw [hk, hm]
    have := dist_step_v (x := (0:ℝ)) hf1 hε 0 0
    rwa [zero_add] at this
  have hang := b_edge_angle S.f2 S.hM hkm hd
  rw [hk, hP] at hang
  rcases hang with hγ' | hα'
  · have h1 := one_angle_le D.toDissection (mkPt 0 0) t'
    rw [hγ', hQ] at h1
    linarith
  · have ha0 := (U_angles S hε h0).1
    rw [hP] at ha0
    exact S.corner_two_alpha hQ ht0 hα' ha0

/-- **(K1) at a junction.**  At the common end `J = (x, 0)` of a run to the right and a run to the left, an open
point of the side, at least one of the two runs has (K1): otherwise four tiles show `α` at `J`. -/
theorem junction (S : Setup D n α β γ L ax ay) (hx0 : 0 < x) (hxL : x < L) {t₁ t₂ : Fin N}
    (h1 : HasV D t₁ (lp n 1 x 0 0) (lp n 1 x (0 + 1) 0) (lp n 1 x 0 (0 + 1)))
    (h2 : HasV D t₂ (lp n (-1) x 0 0) (lp n (-1) x (0 + 1) 0) (lp n (-1) x 0 (0 + 1))) :
    (∀ (t' : Fin N) (k m : Fin 3), k ≠ m → (D.tile t').pts k = lp n 1 x 0 0 →
      (D.tile t').pts m = lp n 1 x 0 1 → (∀ i, FX n 1 ((D.tile t').pts i) ≤ lv n 1 x 0) → False) ∨
    (∀ (t' : Fin N) (k m : Fin 3), k ≠ m → (D.tile t').pts k = lp n (-1) x 0 0 →
      (D.tile t').pts m = lp n (-1) x 0 1 → (∀ i, FX n (-1) ((D.tile t').pts i) ≤ lv n (-1) x 0) →
      False) := by
  refine or_iff_not_imp_left.mpr (fun hA => ?_)
  intro tb kb mb hkmb hkb hmb hleb
  apply hA
  intro ta ka ma hkma hka hma hlea
  have hf1 := S.f1
  have hf2 := S.f2
  have hb := S.b_pos
  have hc := S.c_pos
  have hhp := hh_pos hf1
  have hu := uu_spec hf1
  have hf0 := S.f0
  have hnn : (n:ℝ) < (n:ℝ) ^ 2 - 1 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hf2) hf0.le]
  have hc4 : (4:ℝ) ≤ (n:ℝ) ^ 2 := by nlinarith
  have huc : uu (n:ℝ) < (n:ℝ) ^ 2 := by
    by_contra hge
    push Not at hge
    have h1 := mul_le_mul_of_nonneg_left hge (by positivity : (0:ℝ) ≤ 2 * (n:ℝ) ^ 2)
    nlinarith [mul_le_mul_of_nonneg_right hc4 hc.le]
  have e1 : (1:ℝ) ^ 2 = 1 := by norm_num
  have em : (-1:ℝ) ^ 2 = 1 := by norm_num
  have hP1 : lp n 1 x 0 0 = mkPt x 0 := lp_zero _ _ _
  have hPm : lp n (-1) x 0 0 = mkPt x 0 := lp_zero _ _ _
  have hB1 : lp n 1 x (0 + 1) 0 = mkPt (x + (n:ℝ) ^ 2) 0 := by
    rw [lp_step_u]; exact mkPt_congr (by ring) rfl
  have hBm : lp n (-1) x (0 + 1) 0 = mkPt (x - (n:ℝ) ^ 2) 0 := by
    rw [lp_step_u]; exact mkPt_congr (by ring) rfl
  have hG1 : lp n 1 x 0 (0 + 1) = mkPt (x + ((n:ℝ) ^ 2 - uu n)) (hh n) := by
    rw [lp_step_v]; exact mkPt_congr (by ring) rfl
  have hGm : lp n (-1) x 0 (0 + 1) = mkPt (x - ((n:ℝ) ^ 2 - uu n)) (hh n) := by
    rw [lp_step_v]; exact mkPt_congr (by ring) rfl
  have hG1' : lp n 1 x 0 1 = mkPt (x + ((n:ℝ) ^ 2 - uu n)) (hh n) := by
    rw [← hG1]; exact lp_congr rfl (by ring)
  have hGm' : lp n (-1) x 0 1 = mkPt (x - ((n:ℝ) ^ 2 - uu n)) (hh n) := by
    rw [← hGm]; exact lp_congr rfl (by ring)
  -- the angles at `J`
  have a1 := (U_angles S e1 h1).1
  have a2 := (U_angles S em h2).1
  rw [hP1] at a1
  rw [hPm] at a2
  have hda : dist ((D.tile ta).pts ka) ((D.tile ta).pts ma) = (n:ℝ) ^ 2 - 1 := by
    rw [hka, hma]
    have := dist_step_v (x := x) hf1 e1 0 0
    rwa [zero_add] at this
  have hdb : dist ((D.tile tb).pts kb) ((D.tile tb).pts mb) = (n:ℝ) ^ 2 - 1 := by
    rw [hkb, hmb]
    have := dist_step_v (x := x) hf1 em 0 0
    rwa [zero_add] at this
  have hanga := b_edge_angle hf2 S.hM hkma hda
  have hangb := b_edge_angle hf2 S.hM hkmb hdb
  rw [hka, hP1] at hanga
  rw [hkb, hPm] at hangb
  rw [hP1] at hka
  rw [hPm] at hkb
  rw [hG1'] at hma
  rw [hGm'] at hmb
  rw [hP1, hB1, hG1] at h1
  rw [hPm, hBm, hGm] at h2
  -- distinctness
  have n12 : t₁ ≠ t₂ := by
    obtain ⟨i, hi⟩ := h1.idx₂
    exact h2.ne_of_vertex hi (mkPt_ne_of_fst (by linarith)) (mkPt_ne_of_fst (by linarith))
      (mkPt_ne_of_snd hhp.ne)
  have n1a : t₁ ≠ ta := by
    obtain ⟨i, hi⟩ := h1.idx₂
    refine (ne_of_F (FX n 1) hlea (i := i) ?_).symm
    rw [hi, ← hB1, FX_lp e1]
    exact lv_lt hf1 (by norm_num)
  have n2b : t₂ ≠ tb := by
    obtain ⟨i, hi⟩ := h2.idx₂
    refine (ne_of_F (FX n (-1)) hleb (i := i) ?_).symm
    rw [hi, ← hBm, FX_lp em]
    exact lv_lt hf1 (by norm_num)
  have n1b : t₁ ≠ tb :=
    (h1.ne_of_vertex hmb (mkPt_ne_of_snd hhp.ne') (mkPt_ne_of_snd hhp.ne')
      (mkPt_ne_of_fst (by linarith))).symm
  have n2a : t₂ ≠ ta :=
    (h2.ne_of_vertex hma (mkPt_ne_of_snd hhp.ne') (mkPt_ne_of_snd hhp.ne')
      (mkPt_ne_of_fst (by linarith))).symm
  rcases hanga with hγa | hαa
  · exact S.gamma_alpha_alpha hx0 hxL n12 a1 hγa a2
  rcases hangb with hγb | hαb
  · exact S.gamma_alpha_alpha hx0 hxL n12 a1 hγb a2
  have nab : ta ≠ tb := by
    rintro rfl
    have hkk : kb = ka := (D.tile ta).indep.injective (hkb.trans hka.symm)
    have hmm : ma ≠ mb := by
      intro h
      rw [h, hmb] at hma
      have := (mkPt_inj hma).1
      linarith
    have hkm' : ka ≠ mb := by rw [← hkk]; exact hkmb
    rcases sides_of_b_edge D hf2 S.hM ta hkma hkm' hmm hda with ⟨s1, -⟩ | ⟨s1, -⟩
    · rw [dist_comm, ← hkk, hdb] at s1; linarith
    · rw [dist_comm, ← hkk, hdb] at s1; linarith
  exact S.four_alpha hx0 hxL n12 n1a n1b n2a n2b nab a1 a2 hαa hαb

/-! ## 3. Hypothesis (K3) -/

/-- a run to the right that ends at the corner `B`, of angle `β` -/
theorem K3_out_right (S : Setup D n α β γ L ax ay) {t : ℝ} (ht : 0 < t)
    (hax : ax = L - t * uu n) (hay' : ay = t * hh n) {k : ℝ} (hx : x + k * (n:ℝ) ^ 2 = L) :
    K3 D n 1 x k 0 := by
  refine Or.inl (fun q hq => ?_)
  have h := (S.mem hq).2.2
  unfold gB at h
  rw [hax, hay'] at h
  have h' : 0 ≤ hh n * (L - q 0) - uu n * q 1 := by
    by_contra hneg
    push Not at hneg
    nlinarith [mul_pos ht (neg_pos.mpr hneg)]
  have e : hh (n:ℝ) * x + (n:ℝ) ^ 2 * hh n * k = hh n * L := by rw [← hx]; ring
  unfold GS lv
  rw [lin_apply]
  linarith

/-- a run to the left that ends at the corner `Q`, of angle `β` -/
theorem K3_out_left (S : Setup D n α β γ L ax ay) {t : ℝ} (ht : 0 < t)
    (hax : ax = t * uu n) (hay' : ay = t * hh n) {k : ℝ} (hx : x - k * (n:ℝ) ^ 2 = 0) :
    K3 D n (-1) x k 0 := by
  refine Or.inl (fun q hq => ?_)
  have h := (S.mem hq).2.1
  unfold gA at h
  rw [hax, hay'] at h
  have h' : 0 ≤ hh n * q 0 - uu n * q 1 := by
    by_contra hneg
    push Not at hneg
    nlinarith [mul_pos ht (neg_pos.mpr hneg)]
  have e : hh (n:ℝ) * x - (n:ℝ) ^ 2 * hh n * k = 0 := by
    have : hh (n:ℝ) * x - (n:ℝ) ^ 2 * hh n * k = hh n * (x - k * (n:ℝ) ^ 2) := by ring
    rw [this, hx, mul_zero]
  unfold GS lv
  rw [lin_apply]
  linarith

/-- the tile across the last `a`-edge of a run does not show `γ` or `β` at the end `V` of the run, an open point
of the side, if the side tile beyond `V` shows `γ` or `β` there -/
theorem bad_nb (S : Setup D n α β γ L ax ay) {xR : ℝ} (hx0 : 0 < xR) (hxL : xR < L)
    {G A₀ Rp Z : Plane} (hG1 : 0 < G 1) {t₀ : Fin N} (h0 : HasV D t₀ A₀ (mkPt xR 0) G)
    (hA₀ : A₀ 1 = 0) (hβ0 : (D.tile t₀).localAngle (mkPt xR 0) = β)
    {j : Fin N} {mj : Fin 3} (hmj : (D.tile j).pts mj = Rp) (hRp1 : Rp 1 = 0)
    (hRpV : Rp ≠ mkPt xR 0) (hRpA : Rp ≠ A₀)
    (hθj : (D.tile j).localAngle (mkPt xR 0) = γ ∨ (D.tile j).localAngle (mkPt xR 0) = β)
    {W : Fin N} (hW : HasV D W (mkPt xR 0) G Z)
    (hθW : (D.tile W).localAngle (mkPt xR 0) = γ ∨ (D.tile W).localAngle (mkPt xR 0) = β)
    (hZ1 : 0 < Z 1) : False := by
  obtain ⟨hα, hβ, hγ2, hsum, hγπ⟩ := angle_facts S.hA
  have hαβ := S.alpha_lt_beta
  have hne1 : ∀ {P Q : Plane}, P 1 = 0 → 0 < Q 1 → P ≠ Q := by
    intro P Q hP hQ h
    rw [h] at hP
    linarith
  have hjW : j ≠ W := hW.ne_of_vertex hmj hRpV (hne1 hRp1 hG1) (hne1 hRp1 hZ1)
  have hjt : j ≠ t₀ := h0.ne_of_vertex hmj hRpA hRpV (hne1 hRp1 hG1)
  have htW : t₀ ≠ W := by
    obtain ⟨k0, m0, j0, hkm0, -, -, hk0, hm0, -⟩ := h0
    have hAV : A₀ ≠ mkPt xR 0 := fun h =>
      hkm0 ((D.tile t₀).indep.injective (hk0.trans (h.trans hm0.symm)))
    exact hW.ne_of_vertex hk0 hAV (hne1 hA₀ hG1) (hne1 hA₀ hZ1)
  have h3 := three_angles_le D.toDissection (mkPt xR 0) htW (Ne.symm hjt) (Ne.symm hjW)
  rw [hβ0, S.angle_base hx0 hxL] at h3
  rcases hθW with hw | hw <;> rcases hθj with hj | hj
  · rw [hw, hj] at h3; linarith
  · rw [hw, hj] at h3; linarith
  · rw [hw, hj] at h3; linarith
  · exact S.three_beta hx0 hxL htW (Ne.symm hjt) (Ne.symm hjW) hβ0 hw hj

/-- the same at a corner of angle `α + β` of the target -/
theorem bad_corner (S : Setup D n α β γ L ax ay) (hQ : D.target.localAngle (mkPt 0 0) = α + β)
    {G A₀ Z : Plane} (hG1 : 0 < G 1) {t₀ : Fin N} (h0 : HasV D t₀ A₀ (mkPt 0 0) G)
    (hA₀ : A₀ 1 = 0) (hβ0 : (D.tile t₀).localAngle (mkPt 0 0) = β)
    {W : Fin N} (hW : HasV D W (mkPt 0 0) G Z)
    (hθW : (D.tile W).localAngle (mkPt 0 0) = γ ∨ (D.tile W).localAngle (mkPt 0 0) = β)
    (hZ1 : 0 < Z 1) : False := by
  obtain ⟨hα, hβ, hγ2, hsum, hγπ⟩ := angle_facts S.hA
  have hαβ := S.alpha_lt_beta
  have hne1 : ∀ {P Q : Plane}, P 1 = 0 → 0 < Q 1 → P ≠ Q := by
    intro P Q hP hQ h
    rw [h] at hP
    linarith
  have htW : t₀ ≠ W := by
    obtain ⟨k0, m0, j0, hkm0, -, -, hk0, hm0, -⟩ := h0
    have hAV : A₀ ≠ mkPt 0 0 := fun h =>
      hkm0 ((D.tile t₀).indep.injective (hk0.trans (h.trans hm0.symm)))
    exact hW.ne_of_vertex hk0 hAV (hne1 hA₀ hG1) (hne1 hA₀ hZ1)
  rcases hθW with hw | hw
  · have h1 := one_angle_le D.toDissection (mkPt 0 0) W
    rw [hw, hQ] at h1
    linarith
  · have h2 := two_angles_le D.toDissection (mkPt 0 0) htW
    rw [hβ0, hw, hQ] at h2
    linarith

end Setup

namespace Ctx

/-- `Ctx.m_next` with the interior of the wall as a hypothesis -/
theorem m_next_int (C : Ctx D n α β γ L ax ay ε x) {ξ η : ℝ} {t₀ : Fin N}
    (hU : HasV D t₀ (lp n ε x ξ η) (lp n ε x (ξ + 1) η) (lp n ε x ξ (η + 1)))
    (hint : openSegment ℝ (lp n ε x (ξ + 1) η) (lp n ε x ξ (η + 1)) ⊆ interior D.target.carrier)
    (hcl : ∃ P' : Plane, GS n ε P' = -lv n ε x (ξ + η + 1) ∧
      lp n ε x (ξ + 1) η ∈ openSegment ℝ P' (lp n ε x ξ (η + 1)) ∧
      ∀ e ∈ D.lineChain (GS n ε) (-lv n ε x (ξ + η + 1)),
        ¬ Straddles ((D.tile e.1).edge e.2) P' (lp n ε x (ξ + 1) η) (lp n ε x ξ (η + 1)))
    (hb : ξ + 2 ≤ n) :
    (∃ t, HasV D t (lp n ε x (ξ + 1) η) (lp n ε x ξ (η + 1)) (lp n ε x (ξ + 1) (η + 1))) ∨
    (∃ t, HasV D t (lp n ε x (ξ + 1) η) (lp n ε x ξ (η + 1)) (lp n ε x (ξ - nu n) (η + 2 + nu n))) ∨
    (∃ w, RhoEdge D n ε x w (ξ + η + 1) η) := by
  have hε := C.e2
  have hf1 := C.S.f1
  have hVG : lp n ε x (ξ + 1) η ≠ lp n ε x ξ (η + 1) := lp_ne_eta hf1 (by linarith)
  have hfV : GS n ε (lp n ε x (ξ + 1) η) = -lv n ε x (ξ + η + 1) := by
    rw [GS_lp hε]; unfold lv; ring
  have hfG : GS n ε (lp n ε x ξ (η + 1)) = -lv n ε x (ξ + η + 1) := by
    rw [GS_lp hε]; unfold lv; ring
  have hwall : ∀ y ∈ openSegment ℝ (lp n ε x (ξ + 1) η) (lp n ε x ξ (η + 1)),
      ∀ i, y ∉ interior (D.tile i).carrier := by
    intro y hy
    obtain ⟨k, m, j, hkm, hkj, hmj, hk, hm, hj⟩ := hU
    refine seg_wall D.toDissection (t := t₀) hmj ?_
    rw [hm, hj]; exact openSegment_subset_segment ℝ _ _ hy
  obtain ⟨P', hfP', hP', hP⟩ := hcl
  obtain ⟨e, he, k', m', t, hk'm', hk', ht, hm', hle, -, -⟩ :=
    next_tile D.toDissection (GS n ε) (GS_ne hf1 hε) (-lv n ε x (ξ + η + 1)) hVG hfV hfG hfP' hP'
      hint hwall hP
  rcases C.m_next_cases hk'm' hk' ht hm' hle hb with hG | hR
  · rcases m_edge_cases C.S hε hk'm' hk' hG hle with h | h
    · exact Or.inl ⟨e.1, h⟩
    · exact Or.inr (Or.inl ⟨e.1, h⟩)
  · exact Or.inr (Or.inr ⟨e.1, hR⟩)

/-- **(K3) from the tile across the last `a`-edge of the run**: it lays more than `a` on the line `m_k`, unless it
has that `a`-edge and shows `γ` or `β` at the end of the run. -/
theorem K3_of_next (C : Ctx D n α β γ L ax ay ε x) {k : ℕ} (hkn : k < n) {t₀ : Fin N}
    (hU : HasV D t₀ (lp n ε x ((k:ℝ) - 1) 0) (lp n ε x ((k:ℝ) - 1 + 1) 0)
      (lp n ε x ((k:ℝ) - 1) (0 + 1)))
    (hint : openSegment ℝ (lp n ε x ((k:ℝ) - 1 + 1) 0) (lp n ε x ((k:ℝ) - 1) (0 + 1))
      ⊆ interior D.target.carrier)
    (hbad : ∀ (W : Fin N) (Z : Plane),
      HasV D W (lp n ε x ((k:ℝ) - 1 + 1) 0) (lp n ε x ((k:ℝ) - 1) (0 + 1)) Z →
      ((D.tile W).localAngle (lp n ε x ((k:ℝ) - 1 + 1) 0) = γ ∨
        (D.tile W).localAngle (lp n ε x ((k:ℝ) - 1 + 1) 0) = β) → 0 < Z 1 → False) :
    K3 D n ε x k 0 := by
  have hε := C.e2
  have hf1 := C.S.f1
  have hhp := hh_pos hf1
  have hν0 := nu_pos hf1
  have hb : (k:ℝ) - 1 + 2 ≤ n := by
    have h' : k + 1 ≤ n := hkn
    have : ((k + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast h'
    push_cast at this
    linarith
  rcases C.m_next_int hU hint (C.m_clamp_base _) hb with ⟨W, h⟩ | ⟨W, h⟩ | ⟨w, hw⟩
  · exfalso
    refine hbad W _ h (Or.inl (D_angles C.S hε h).1) ?_
    rw [lp_one]; linarith
  · exfalso
    refine hbad W _ h (Or.inr (N_angles C.S hε h).1) ?_
    rw [lp_one]; nlinarith [mul_pos hν0 hhp]
  · have e : (k:ℝ) - 1 + 0 + 1 = k := by ring
    rw [e] at hw
    exact Or.inr ⟨w, hw⟩

end Ctx

end Erdos634.Draft.SideRun

#print axioms Erdos634.Draft.SideRun.Setup.corner_two_alpha
#print axioms Erdos634.Draft.SideRun.Setup.K1_of_gamma
#print axioms Erdos634.Draft.SideRun.Setup.K1_of_corner
#print axioms Erdos634.Draft.SideRun.Setup.junction
#print axioms Erdos634.Draft.SideRun.Setup.bad_nb
#print axioms Erdos634.Draft.SideRun.Ctx.K3_of_next
