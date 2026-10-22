-- Draft/LaczFormalGraphKill.lean -- D6: the corner argument of Laczkovich, DCG 48 (2012), Subcase IVa for a regular-triangle target.
-- A target corner carries a single tile with `gamma`; its `beta` lies on one of the two sides at the corner; Lemma 4.3 (ii) (forward along the outgoing side, backward along
-- the incoming side) puts a `beta` at the far end of that side, contradicting the corner equation `gamma = pi/3` there.  UNAUDITED.
-- Credit: Laczkovich (DCG 48 (2012), Sect. 8.1 end of Subcase IVa), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalGraphBdy
import Erdos634.Draft.LaczFormalGraphBack

open scoped Classical
open Erdos634.Geometry Erdos634.KConj

namespace Erdos634.Draft.LaczFormal.Graph

variable {N : ℕ}

/-- **A target corner of angle `π/3` carries exactly one tile, with `γ` there.** -/
theorem corner_single (D : CongruentDissection N) (idx : Fin N → Equiv.Perm (Fin 3))
    (hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v) {w0 w1 w2 : ℕ} {u : ℝ} (W : WtData D w0 w1 w2 u)
    (j : Fin 3) (hT : D.target.angleAt j = (w2 : ℝ) * u)
    (hv : ∃ i k, (D.tile i).pts k = D.target.pts j) (hreg : cnt D idx (D.target.pts j) 0 = cnt D idx (D.target.pts j) 1) :
    cnt D idx (D.target.pts j) 0 = 0 ∧ cnt D idx (D.target.pts j) 1 = 0 ∧ cnt D idx (D.target.pts j) 2 = 1 ∧
      Fintype.card (AtV D.toDissection (D.target.pts j)) = 1 := by
  classical
  set P := D.target.pts j with hP
  have hang := vertex_angle_eq D idx hidxA hv
  rw [hP, Tri.localAngle_vertex] at hang
  have hTj : cornerAngle (D.target.pts (j + 1)) (D.target.pts j) (D.target.pts (j + 2)) = (w2 : ℝ) * u := hT
  rw [hTj] at hang
  rw [Fin.sum_univ_three] at hang
  have hcorn : 0 < (Corn D.toDissection P).card := by
    obtain ⟨i, k, hk⟩ := hv
    exact Finset.card_pos.mpr ⟨i, by simp [Corn]; exact ⟨k, hk⟩⟩
  rw [card_corn D idx P, Fin.sum_univ_three] at hcorn
  have hA0 := model_angle_pos D 0
  have hA1 := model_angle_pos D 1
  have hA2 := model_angle_pos D 2
  have hu := W.hu
  have hw2 : (0 : ℝ) < w2 := by exact_mod_cast W.hw2
  have hpi : Real.pi = 3 * (w2 : ℝ) * u := by
    have := W.hsum
    have hw : ((w0 + w1 + w2 : ℕ) : ℝ) = 3 * w2 := by
      have : w0 + w1 + w2 = 3 * w2 := by have := W.hw; omega
      rw [this]; push_cast; ring
    rw [← this, hw]
  have hSpos : 0 < (cnt D idx P 0 : ℝ) * D.model.angleAt 0 + cnt D idx P 1 * D.model.angleAt 1 + cnt D idx P 2 * D.model.angleAt 2 := by
    by_cases h0' : 0 < cnt D idx P 0
    · have : (0:ℝ) < cnt D idx P 0 := by exact_mod_cast h0'
      have := mul_pos this hA0
      have := mul_nonneg (Nat.cast_nonneg (cnt D idx P 1) : (0:ℝ) ≤ _) hA1.le
      have := mul_nonneg (Nat.cast_nonneg (cnt D idx P 2) : (0:ℝ) ≤ _) hA2.le
      linarith
    · by_cases h1' : 0 < cnt D idx P 1
      · have : (0:ℝ) < cnt D idx P 1 := by exact_mod_cast h1'
        have := mul_pos this hA1
        have := mul_nonneg (Nat.cast_nonneg (cnt D idx P 0) : (0:ℝ) ≤ _) hA0.le
        have := mul_nonneg (Nat.cast_nonneg (cnt D idx P 2) : (0:ℝ) ≤ _) hA2.le
        linarith
      · have h2' : 0 < cnt D idx P 2 := by omega
        have : (0:ℝ) < cnt D idx P 2 := by exact_mod_cast h2'
        have := mul_pos this hA2
        have := mul_nonneg (Nat.cast_nonneg (cnt D idx P 0) : (0:ℝ) ≤ _) hA0.le
        have := mul_nonneg (Nat.cast_nonneg (cnt D idx P 1) : (0:ℝ) ≤ _) hA1.le
        linarith
  have hStr : (Strn D.toDissection P).card = 0 := by
    by_contra hne
    have : (1 : ℝ) ≤ (Strn D.toDissection P).card := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hne
    have hwu : 0 < (w2 : ℝ) * u := mul_pos hw2 hu
    nlinarith
  rw [hStr] at hang
  have hS : (cnt D idx P 0 : ℝ) * D.model.angleAt 0 + cnt D idx P 1 * D.model.angleAt 1 + cnt D idx P 2 * D.model.angleAt 2 = (w2 : ℝ) * u := by
    simpa using hang
  -- natural-number equation
  rw [W.h0, W.h1, W.h2] at hS
  have hnat : cnt D idx P 0 * w0 + cnt D idx P 1 * w1 + cnt D idx P 2 * w2 = w2 := by
    have : ((cnt D idx P 0 * w0 + cnt D idx P 1 * w1 + cnt D idx P 2 * w2 : ℕ) : ℝ) * u = ((w2 : ℕ) : ℝ) * u := by
      push_cast; linarith
    exact_mod_cast mul_right_cancel₀ hu.ne' this
  rw [← hreg] at hnat
  have hw := W.hw
  have hw2n := W.hw2
  have h1 : (2 * cnt D idx P 0 + cnt D idx P 2) * w2 = 1 * w2 := by
    calc (2 * cnt D idx P 0 + cnt D idx P 2) * w2 = cnt D idx P 0 * (2 * w2) + cnt D idx P 2 * w2 := by ring
      _ = cnt D idx P 0 * (w0 + w1) + cnt D idx P 2 * w2 := by rw [← hw]
      _ = cnt D idx P 0 * w0 + cnt D idx P 0 * w1 + cnt D idx P 2 * w2 := by ring
      _ = w2 := hnat
      _ = 1 * w2 := by ring
  have h2 := Nat.eq_of_mul_eq_mul_right hw2n h1
  have c0 : cnt D idx P 0 = 0 := by omega
  have c1 : cnt D idx P 1 = 0 := by omega
  have c2 : cnt D idx P 2 = 1 := by omega
  refine ⟨c0, c1, c2, ?_⟩
  rw [card_atV, card_corn D idx P, hStr, Fin.sum_univ_three]
  omega

theorem walkT_single_end {D : Dissection N} {d : V2} {X Y : Plane} {e : Fin N × Plane × Plane} (W : WalkT D d X Y [e]) :
    e.2.1 = X ∧ e.2.2 = Y ∧ TriStep (D.tile e.1) d X Y := by
  obtain ⟨i, X1, X2⟩ := e
  cases W with
  | cons hS W' =>
    cases W'
    exact ⟨rfl, rfl, hS⟩

theorem walkT_cons_inv {D : Dissection N} {d : V2} {X Y : Plane} {i : Fin N} {X0 X1 : Plane} {L : List (Fin N × Plane × Plane)}
    (W : WalkT D d X Y ((i, X0, X1) :: L)) : X0 = X ∧ TriStep (D.tile i) d X X1 ∧ WalkT D d X1 Y L := by
  cases W with
  | cons hS W' => exact ⟨rfl, hS, W'⟩

theorem par_antiparallel_crs {a d1 d2 : V2} (h1 : Par a d1) (h2 : Par (-a.1, -a.2) d2) : crs d1 d2 = 0 := by
  obtain ⟨c, hc, hca⟩ := h1.smul
  obtain ⟨c', hc', hca'⟩ := h2.smul
  have e1 : -a.1 = c' * d2.1 := congrArg Prod.fst hca'
  have e2 : -a.2 = c' * d2.2 := congrArg Prod.snd hca'
  have f1 : a.1 = c * d1.1 := congrArg Prod.fst hca
  have f2 : a.2 = c * d1.2 := congrArg Prod.snd hca
  unfold crs
  have : c' * (d1.1 * d2.2 - d1.2 * d2.1) = 0 := by linear_combination (d1.2) * e1 + (d1.2) * f1 - (d1.1) * e2 - (d1.1) * f2
  exact (mul_eq_zero.mp this).resolve_left hc'.ne'

/-- **The corner kill** (Laczkovich, Subcase IVa, regular-triangle target): no congruent dissection of an equilateral triangle by a tile whose angles are
`(w0,w1,w2)·u` with `w0 + w1 = 2 w2`, `a = side opposite α` not a nonnegative rational combination of the other two sides, regular counts at every vertex. -/
theorem corner_kill (D : CongruentDissection N) (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    (hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v)
    (hnc : NotComb (slen D 0) (slen D 1) (slen D 2)) (hab : slen D 0 ≠ slen D 1) (hac : slen D 0 ≠ slen D 2)
    {w0 w1 w2 : ℕ} {u : ℝ} (W : WtData D w0 w1 w2 u)
    (hw3 : (w0, w1, w2) = (1, 7, 4) ∨ (w0, w1, w2) = (1, 19, 10) ∨ (w0, w1, w2) = (7, 13, 10))
    (hreg : ∀ P, (∃ i k, (D.tile i).pts k = P) → cnt D idx P 0 = cnt D idx P 1)
    (hT : ∀ j, D.target.angleAt j = (w2 : ℝ) * u) : False := by
  classical
  have hreg' := reg_all D idx hreg
  have hcs : ∀ j, cnt D idx (D.target.pts j) 0 = 0 ∧ cnt D idx (D.target.pts j) 1 = 0 ∧ cnt D idx (D.target.pts j) 2 = 1 ∧
      Fintype.card (AtV D.toDissection (D.target.pts j)) = 1 := fun j =>
    corner_single D idx hidxA W j (hT j) (target_corner_is_tile_vertex D.toDissection j) (hreg' _)
  obtain ⟨fo, fi, hfo, hfi, hfofi, d1, d2, hS1, hS2, hcrs⟩ := exists_corner_sides D.target 0
  have hn1 := hnorm_of_lemma81 D idx hidx hidxA hnc hab hac W hw3 hreg hS1
  have hn2 := hnorm_of_lemma81 D idx hidx hidxA hnc hab hac W hw3 hreg hS2
  obtain ⟨c0, c1, c2, hcard⟩ := hcs 0
  obtain ⟨x0, hx0⟩ := Fintype.card_eq_one_iff.mp hcard
  -- forward walk along the outgoing side
  obtain ⟨L, hL, hLne, hLpairs⟩ := lemma43_ii D idx hidx hab hac hS1 hn1 (2, 1) (Or.inr rfl)
  obtain ⟨e, L', hLe⟩ := List.exists_cons_of_ne_nil hLne
  -- backward walk along the incoming side
  obtain ⟨M, hM, hMne, hMpairs⟩ := lemma43_back D idx hidx hab hac hS2 hn2 (1, 2) (Or.inl rfl)
  rcases List.eq_nil_or_concat M with hM0 | ⟨M', eb, hMe⟩
  · exact hMne hM0
  rw [List.concat_eq_append] at hMe
  -- first step of the forward walk
  obtain ⟨i, X0', X1⟩ := e
  have hLe' := hLe
  have hLorig := hL
  rw [hLe] at hL
  obtain ⟨hX0', hS, W'⟩ := walkT_cons_inv hL
  subst hX0'
  -- last step of the backward walk
  obtain ⟨hMa, hMb⟩ := walkT_split hM (P := M') (e := eb) (Q := []) hMe
  obtain ⟨j, U0, U1⟩ := eb
  obtain ⟨-, hU1, hSb⟩ := walkT_single_end hMb
  simp only at hU1
  subst hU1
  -- the two tiles at `P` coincide
  obtain ⟨kk, f, g, hk, hf, hfk, hgk, hgf, hpar1, hl1⟩ := hS
  obtain ⟨kk', f', g', hk', hf', hfk', hgk', hgf', hpar2, hl2⟩ := hSb
  have hmemi : D.target.pts 0 ∈ (D.tile i).carrier := vertex_mem hk
  have hmemj : D.target.pts 0 ∈ (D.tile j).carrier := vertex_mem hf'
  have hij : i = j := by
    have h1 := hx0 ⟨i, hmemi⟩
    have h2 := hx0 ⟨j, hmemj⟩
    exact congrArg Subtype.val (h1.trans h2.symm)
  subst hij
  have t_kk : idx i kk = 2 := idx_two_of_cnt D idx c0 c1 hk
  have t_f' : idx i f' = 2 := idx_two_of_cnt D idx c0 c1 hf'
  have hf01 : idx i f = 0 ∨ idx i f = 1 := by
    have hne : idx i f ≠ 2 := fun h => hfk ((idx i).injective (h.trans t_kk.symm))
    generalize idx i f = z at hne ⊢; revert z; decide
  have hk01 : idx i kk' = 0 ∨ idx i kk' = 1 := by
    have hne : idx i kk' ≠ 2 := fun h => hfk' ((idx i).injective (t_f'.trans h.symm))
    generalize idx i kk' = z at hne ⊢; revert z; decide
  have hcorner_end : ∀ j' : Fin 3, ∀ (t : Fin N) (k : Fin 3), (D.tile t).pts k = D.target.pts j' → idx t k ≠ 1 := by
    intro j' t k hk0 h1
    have := cnt_one D idx 1 hk0 h1
    have := (hcs j').2.1
    omega
  rcases hf01 with hf0 | hf1
  · rcases hk01 with hk0 | hk1
    · -- both far vertices have type `α`: they coincide, impossible
      have hff : f = kk' := (idx i).injective (hf0.trans hk0.symm)
      have hX1 : X1 = U0 := hf.symm.trans ((congrArg (D.tile i).pts hff).trans hk')
      apply hcrs
      apply par_antiparallel_crs (a := toV2 (X1 - D.target.pts 0)) hpar1
      have e : (-(toV2 (X1 - D.target.pts 0)).1, -(toV2 (X1 - D.target.pts 0)).2) = toV2 (D.target.pts 0 - U0) := by
        rw [hX1]; unfold toV2; ext <;> simp
      rw [e]; exact hpar2
    · -- backward walk: the last tile has `β` at the far end of the incoming side
      have hPair : PairIs D idx i U0 (D.target.pts 0) (1, 2) := by
        intro k k' hk0 hk0'
        have e1 : k = kk' := (D.tile i).indep.injective (hk0.trans hk'.symm)
        have e2 : k' = f' := (D.tile i).indep.injective (hk0'.trans hf'.symm)
        rw [e1, e2, hk1, t_f']
      have hall := hMpairs (i, U0, D.target.pts 0) M' hMe hPair
      -- the first tile of the backward walk
      obtain ⟨i2, Z0, Z1, M2, hM2⟩ : ∃ i2 Z0 Z1 M2, M = (i2, Z0, Z1) :: M2 := by
        rcases M with _ | ⟨⟨i2, Z0, Z1⟩, M2⟩
        · exact absurd rfl hMne
        · exact ⟨i2, Z0, Z1, M2, rfl⟩
      have hM' := hM
      rw [hM2] at hM'
      obtain ⟨hZ0, hS', W''⟩ := walkT_cons_inv hM'
      obtain ⟨kk2, f2, g2, hk2, hf2, -⟩ := hS'
      have hmem : (i2, Z0, Z1) ∈ M := by rw [hM2]; simp
      have hp := hall _ hmem kk2 f2 (hk2.trans hZ0.symm) hf2
      have e1 : idx i2 kk2 = 1 := (Prod.mk.injEq _ _ _ _ ▸ hp).1
      exact hcorner_end fi i2 kk2 hk2 e1
  · -- forward walk: `β` on the outgoing side
    have hPair : PairIs D idx i (D.target.pts 0) X1 (2, 1) := by
      intro k k' hk0 hk0'
      have e1 : k = kk := (D.tile i).indep.injective (hk0.trans hk.symm)
      have e2 : k' = f := (D.tile i).indep.injective (hk0'.trans hf.symm)
      rw [e1, e2, hf1, t_kk]
    have hallF := (hLpairs (i, D.target.pts 0, X1) L' hLe' hPair).1
    obtain ⟨i3, U, hmem3, hS3⟩ := walkT_last hLorig hLne
    obtain ⟨kk3, f3, g3, hk3, hf3, -⟩ := hS3
    have hp := hallF _ hmem3 kk3 f3 hk3 hf3
    have e1 : idx i3 f3 = 1 := (Prod.mk.injEq _ _ _ _ ▸ hp).2
    exact hcorner_end fo i3 f3 hf3 e1

end Erdos634.Draft.LaczFormal.Graph
