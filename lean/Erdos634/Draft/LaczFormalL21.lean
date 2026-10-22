import Erdos634.RegionDissection

/-!
# Laczkovich (Discrete Math 140 (1995) 79-94), Lemma 2.1, in the project's framework

NOTE, UNAUDITED.  Credit: Laczkovich (Discrete Math. 140 (1995), Lemma 2.1), Beeson, Beeson-Zhang, Zhang.

Paper statement.  Let `Δ` be a rational triangle.  If a polygon `P` is dissected into finitely many
rational triangles similar to `Δ`, then `P` is dissected into congruent triangles similar to `Δ`.

Formalisation (a region dissection replaces "polygon"; similarity = congruence to a homothetic copy
`scaleTri r Δ`, reflections allowed as everywhere in the project).

* `lemma21_nat`   : tiles congruent to `scaleTri (p_i / q) Δ` with `p_i, q` positive naturals: there is
  a `CongruentRegionDissection` of the same region with `Σ p_i²` tiles and model `scaleTri (1/q) Δ`.
* `lemma21_rat`   : tiles congruent to `scaleTri r_i Δ`, `r_i` positive RATIONAL: the same, for some
  `q` (the product of the denominators), tile count `Σ p_i²`.
* `ratio_rat`     : if `Δ` and `A` have rational side lengths and `A ≅ scaleTri r Δ` (`r > 0`) then
  `r` is rational, so "rational triangle similar to `Δ`" is exactly the hypothesis of `lemma21_rat`.
* `lemma21`       : the paper's statement (rational `Δ`, rational tiles, any real ratios).
Proof as in the paper (common denominator, then the ladder `Realizable.cut_scale` inside each tile,
transported by an isometry).  Witness: `lemma21_witness` (a trivial one-tile dissection, `p = q = 1`).
-/

namespace Erdos634.LaczL21

open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Realizable Erdos634.DissectionMap

/-- The one-tile congruent dissection of a triangle by itself. -/
noncomputable def oneDiss (T : Tri) : CongruentDissection 1 where
  target := T
  tile := fun _ => T
  covers := Set.iUnion_const _
  interiors_disjoint := fun i j hij => absurd (Subsingleton.elim i j) hij
  model := T
  tiles_congruent := fun _ => Tri.Congruent.refl T

/-- A congruent dissection of `T` yields one of any triangle congruent to `T` (same model, same
count): transport by the isometry (Mazur-Ulam). -/
theorem exists_of_congruent_target {N : ℕ} (D : CongruentDissection N) (U : Tri)
    (h : D.target.Congruent U) :
    ∃ E : CongruentDissection N, E.target.carrier = U.carrier ∧ E.model = D.model := by
  obtain ⟨f, σ, hf⟩ := h
  refine ⟨{ mapDissection (Erdos634.Ladder.isoAff f) D.toDissection with
            model := D.model
            tiles_congruent := ?_ }, ?_, rfl⟩
  · intro n
    show Tri.Congruent (mapTri (Erdos634.Ladder.isoAff f) (D.tile n)) D.model
    exact (Erdos634.Ladder.congruent_mapTri f (D.tile n)).symm.trans (D.tiles_congruent n)
  · show (mapTri (Erdos634.Ladder.isoAff f) D.target).carrier = _
    rw [mapTri_carrier, Erdos634.Ladder.isoAff_coe]
    exact Erdos634.CongruentArea.image_carrier_of_congruent hf

/-- Any triangle congruent to the scale-`p` copy of `t` is cut into `p*p*1` copies of `t`
(carrier-level). -/
theorem cut_nat_congruent (t U : Tri) (p : ℕ) (hp : 0 < p) (hU : U.Congruent (scaleN p hp t)) :
    ∃ E : CongruentDissection (p * p * 1), E.target.carrier = U.carrier ∧ E.model = t := by
  have h1 : Cut t t 1 := ⟨oneDiss t, rfl, rfl⟩
  obtain ⟨D, hD, hM⟩ := cut_scale h1 p hp
  obtain ⟨E, hE, hEm⟩ := exists_of_congruent_target D U (by rw [hD]; exact hU.symm)
  exact ⟨E, hE, by rw [hEm, hM]⟩

/-- Reindexing sum over `Fin N`. -/
theorem lemma21_nat {N : ℕ} (Δ : Tri) (R : RegionDissection N) (q : ℕ) (hq : 0 < q)
    (p : Fin N → ℕ) (hp : ∀ i, 0 < p i)
    (hsim : ∀ i, (R.tile i).Congruent
      (scaleTri ((p i : ℝ) / q) (by have := hp i; positivity) Δ)) :
    ∃ M : ℕ, M = ∑ i, p i * p i ∧ ∃ C : CongruentRegionDissection M,
      C.region = R.region ∧
      C.model = scaleTri (1 / (q : ℝ)) (by positivity) Δ := by
  set t : Tri := scaleTri (1 / (q : ℝ)) (by positivity) Δ with ht
  have hq' : ((q : ℝ)) ≠ 0 := by positivity
  have hex : ∀ i, ∃ E : CongruentDissection (p i * p i * 1),
      E.target.carrier = (R.tile i).carrier ∧ E.model = t := by
    intro i
    refine cut_nat_congruent t _ (p i) (hp i) ?_
    have hpos : (p i : ℝ) / q ≠ 0 := by have := hp i; positivity
    have : scaleN (p i) (hp i) t = scaleTri ((p i : ℝ) / q) hpos Δ := by
      rw [ht, scaleN, scaleTri_scaleTri _ _ _ _ (by have := hp i; positivity)]
      congr 1
      ring
    rw [this]
    exact hsim i
  choose E hEc hEm using hex
  let m : Fin N → ℕ := fun i => p i * p i * 1
  let e : (Σ i : Fin N, Fin (m i)) ≃ Fin (∑ i, m i) := finSigmaFinEquiv
  refine ⟨∑ i, m i, by simp [m], ?_⟩
  refine ⟨{ region := R.region
            tile := fun n => (E (e.symm n).1).tile (e.symm n).2
            covers := ?_
            interiors_disjoint := ?_
            model := t
            tiles_congruent := ?_ }, rfl, rfl⟩
  · rw [← R.covers]
    ext x
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨n, hn⟩
      refine ⟨(e.symm n).1, ?_⟩
      rw [← hEc]
      exact Erdos634.Geometry.tile_subset_target (E (e.symm n).1).toDissection _ hn
    · rintro ⟨i, hi⟩
      rw [← hEc, ← (E i).covers] at hi
      simp only [Set.mem_iUnion] at hi
      obtain ⟨j, hj⟩ := hi
      refine ⟨e ⟨i, j⟩, ?_⟩
      show x ∈ ((E (e.symm (e ⟨i, j⟩)).1).tile (e.symm (e ⟨i, j⟩)).2).carrier
      rw [Equiv.symm_apply_apply]
      exact hj
  · intro n n' hnn'
    have hne : e.symm n ≠ e.symm n' := fun h => hnn' (e.symm.injective h)
    generalize e.symm n = a at hne ⊢
    generalize e.symm n' = b at hne ⊢
    obtain ⟨i, j⟩ := a
    obtain ⟨i', j'⟩ := b
    by_cases hii : i = i'
    · subst hii
      have hjj : j ≠ j' := fun h => hne (by rw [h])
      exact (E i).interiors_disjoint (fun h => hjj (by simpa using h))
    · have h1 : interior ((E i).tile j).carrier ⊆ interior (R.tile i).carrier := by
        rw [← hEc i]
        exact interior_mono (Erdos634.Geometry.tile_subset_target (E i).toDissection j)
      have h2 : interior ((E i').tile j').carrier ⊆ interior (R.tile i').carrier := by
        rw [← hEc i']
        exact interior_mono (Erdos634.Geometry.tile_subset_target (E i').toDissection j')
      exact (R.interiors_disjoint hii).mono h1 h2
  · intro n
    have := (E (e.symm n).1).tiles_congruent (e.symm n).2
    rwa [hEm] at this


/-- Positive rationals have a common denominator. -/
theorem common_denominator {N : ℕ} (r : Fin N → ℚ) (hr : ∀ i, 0 < r i) :
    ∃ (q : ℕ) (p : Fin N → ℕ), 0 < q ∧ (∀ i, 0 < p i) ∧ ∀ i, ((r i : ℚ) : ℝ) = (p i : ℝ) / q := by
  classical
  set q : ℕ := ∏ i, (r i).den with hq
  have hqpos : 0 < q := Finset.prod_pos (fun i _ => (r i).den_pos)
  have hdvd : ∀ i, (r i).den ∣ q := fun i => Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  refine ⟨q, fun i => (r i).num.toNat * (q / (r i).den), hqpos, ?_, ?_⟩
  · intro i
    have hn : 0 < (r i).num := Rat.num_pos.mpr (hr i)
    have hk : 0 < q / (r i).den := Nat.div_pos (Nat.le_of_dvd hqpos (hdvd i)) (r i).den_pos
    exact Nat.mul_pos (by omega) hk
  · intro i
    have hn : 0 < (r i).num := Rat.num_pos.mpr (hr i)
    obtain ⟨k, hk⟩ := hdvd i
    have hkq : q / (r i).den = k := by
      rw [hk]; exact Nat.mul_div_cancel_left _ (r i).den_pos
    have hnr : (((r i).num.toNat : ℕ) : ℝ) = ((r i).num : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg hn.le
    have hd : ((r i).den : ℝ) ≠ 0 := by exact_mod_cast (r i).den_pos.ne'
    have hkr : (q : ℝ) = (r i).den * k := by exact_mod_cast hk
    have hk0 : (k : ℝ) ≠ 0 := by
      have : 0 < k := by
        rcases Nat.eq_zero_or_pos k with h | h
        · rw [h] at hk; omega
        · exact h
      positivity
    show ((r i : ℚ) : ℝ) = (((r i).num.toNat * (q / (r i).den) : ℕ) : ℝ) / q
    rw [hkq, Rat.cast_def]
    push_cast
    rw [hnr, hkr]
    field_simp

/-- **Lemma 2.1 (Laczkovich 1995), rational-ratio form.**  Tiles of a region dissection congruent to
`scaleTri (r_i) Δ` with `r_i` positive rationals: the region is dissected into `Σ p_i²` tiles all
congruent to `scaleTri (1/q) Δ` (a triangle similar to `Δ`). -/
theorem lemma21_rat {N : ℕ} (Δ : Tri) (R : RegionDissection N) (r : Fin N → ℚ)
    (hr : ∀ i, 0 < r i)
    (hsim : ∀ i, (R.tile i).Congruent
      (scaleTri ((r i : ℚ) : ℝ) (by have := hr i; positivity) Δ)) :
    ∃ (q : ℕ) (hq : 0 < q) (p : Fin N → ℕ), (∀ i, 0 < p i) ∧ (∀ i, ((r i : ℚ) : ℝ) = p i / q) ∧
      ∃ M : ℕ, M = ∑ i, p i * p i ∧ ∃ C : CongruentRegionDissection M,
        C.region = R.region ∧
        C.model = scaleTri (1 / (q : ℝ)) (one_div_pos.mpr (Nat.cast_pos.mpr hq)).ne' Δ := by
  obtain ⟨q, p, hq, hp, hrp⟩ := common_denominator r hr
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  refine ⟨q, hq, p, hp, hrp, ?_⟩
  have hsim' : ∀ i, (R.tile i).Congruent
      (scaleTri ((p i : ℝ) / q) (by have := hp i; positivity) Δ) := by
    intro i
    have h : scaleTri ((r i : ℚ) : ℝ) (by have := hr i; positivity) Δ
        = scaleTri ((p i : ℝ) / q) (by have := hp i; positivity) Δ := by
      congr 1
      exact hrp i
    rw [← h]; exact hsim i
  exact lemma21_nat Δ R q hq p hp hsim'

/-- Rational side lengths. -/
def IsRationalTri (T : Tri) : Prop := ∀ j k, ∃ s : ℚ, dist (T.pts j) (T.pts k) = s

/-- A rational triangle similar (by a homothetic copy of ratio `r > 0`) to a rational `Δ` has
rational ratio. -/
theorem ratio_rat (Δ A : Tri) (hΔ : IsRationalTri Δ) (hA : IsRationalTri A) (r : ℝ) (hr : 0 < r)
    (hc : A.Congruent (scaleTri r hr.ne' Δ)) : ∃ s : ℚ, r = s := by
  obtain ⟨f, σ, hf⟩ := hc
  have hσ : σ 0 ≠ σ 1 := fun h => by have := σ.injective h; exact absurd this (by decide)
  obtain ⟨a, ha⟩ := hA 0 1
  obtain ⟨b, hb⟩ := hΔ (σ 0) (σ 1)
  have hbne : (b : ℝ) ≠ 0 := by
    rw [← hb]; exact dist_ne_zero.mpr (fun h => hσ (Δ.indep.injective h))
  have hd : dist (A.pts 0) (A.pts 1) = r * dist (Δ.pts (σ 0)) (Δ.pts (σ 1)) := by
    rw [← f.dist_eq, hf 0, hf 1]
    simp only [scaleTri_pts]
    rw [Erdos634.Realizable.dist_homothety, abs_of_pos hr]
  rw [ha, hb] at hd
  refine ⟨a / b, ?_⟩
  push_cast
  field_simp
  linarith

/-- **Lemma 2.1 (Laczkovich 1995), as printed.**  `Δ` rational; every tile of the region dissection a
rational triangle similar to `Δ` (a homothetic copy of ratio `ρ_i > 0`).  Then the region is dissected
into finitely many congruent triangles similar to `Δ`. -/
theorem lemma21 {N : ℕ} (Δ : Tri) (hΔ : IsRationalTri Δ) (R : RegionDissection N)
    (ρ : Fin N → ℝ) (hρ : ∀ i, 0 < ρ i) (hrat : ∀ i, IsRationalTri (R.tile i))
    (hsim : ∀ i, (R.tile i).Congruent (scaleTri (ρ i) (hρ i).ne' Δ)) :
    ∃ (q : ℕ) (hq : 0 < q) (M : ℕ) (C : CongruentRegionDissection M),
      C.region = R.region ∧
      C.model = scaleTri (1 / (q : ℝ)) (one_div_pos.mpr (Nat.cast_pos.mpr hq)).ne' Δ := by
  have hex : ∀ i, ∃ s : ℚ, ρ i = s := fun i => ratio_rat Δ _ hΔ (hrat i) (ρ i) (hρ i) (hsim i)
  choose s hs using hex
  have hspos : ∀ i, 0 < s i := fun i => by
    have := hρ i; rw [hs i] at this; exact_mod_cast this
  have hsim' : ∀ i, (R.tile i).Congruent
      (scaleTri ((s i : ℚ) : ℝ) (by have := hspos i; positivity) Δ) := by
    intro i
    have h : scaleTri (ρ i) (hρ i).ne' Δ
        = scaleTri ((s i : ℚ) : ℝ) (by have := hspos i; positivity) Δ := by
      congr 1
      exact hs i
    rw [← h]; exact hsim i
  obtain ⟨q, hq, p, _, _, M, _, C, hC1, hC2⟩ := lemma21_rat Δ R s hspos hsim'
  exact ⟨q, hq, M, C, hC1, hC2⟩

/-! ### Witnesses (hypotheses are satisfiable, and the ladder is exercised) -/

/-- A single tile `scaleTri 2 Δ` (`p = 2`, `q = 1`) as a region dissection. -/
noncomputable def witnessRegion (Δ : Tri) : RegionDissection 1 :=
  (oneDiss (scaleTri (2 : ℝ) (by norm_num) Δ)).toDissection.toRegion

theorem lemma21_nat_witness (Δ : Tri) :
    ∃ M : ℕ, M = 4 ∧ ∃ C : CongruentRegionDissection M,
      C.region = (witnessRegion Δ).region ∧
      C.model = scaleTri (1 / ((1 : ℕ) : ℝ)) (by norm_num) Δ := by
  have h := lemma21_nat Δ (witnessRegion Δ) 1 one_pos (fun _ => 2) (fun _ => by norm_num)
    (fun i => by
      have : scaleTri (((fun _ : Fin 1 => 2) i : ℕ) / (1 : ℕ) : ℝ) (by norm_num) Δ
          = scaleTri (2 : ℝ) (by norm_num) Δ := by
        congr 1; norm_num
      show Tri.Congruent (scaleTri (2 : ℝ) (by norm_num) Δ) _
      rw [this]
      exact Tri.Congruent.refl _)
  obtain ⟨M, hM, C, h1, h2⟩ := h
  exact ⟨M, by simpa using hM, C, h1, h2⟩

end Erdos634.LaczL21
