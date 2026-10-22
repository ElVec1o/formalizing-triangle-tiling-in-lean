/-
Draft/H1cCaseC.lean — atom H1.c of (private working notes, not included) §2 Case C (right-tile branch, flux coordinates).
Proves `H1k.RightCaseC N` for ALL `N`:  in normal form with `lam = AB/c ∉ ℚ`, `a/b ∉ ℚ`, `c ∉ ℚa + ℚb`  ⇒  False.
Route (paper §2 Case C, only the X = -3,-2,-1 coefficients are needed):
  1. `flux_data`: the c = 1 Gaussian flux identity `Σ_i tileVal_i(X) = bdryVal(lam, X)` for every grid degree X,
     re-derived from `gaussWeight_flux_cancel`, `rightTile_flux_value_c`, `target_flux_general` (as in
     `Row3.RP.row3_RP_even`, whose `hsum` is internal), for either orientation of the target.
  2. `coef_eqn`: multiplied by c:  `c(P_X+Q_X) - (b+ia)P_{X+1} - (b-ia)Q_{X-1} = c·bdryVal(X)`.
  3. `sep`: `a,b,c` ℚ-independent and Gaussian-integer coefficients ⇒ each coefficient vanishes.
  4. X=-3 gives `P_{-2} = 0`; X=-1 gives `Q_{-2} = (u_b + i u_a)/2`; X=-2 gives `P_{-2}+Q_{-2} = 0`; so `u_a = u_b = 0`,
     hence `lam c = u_c c`, `lam = u_c ∈ ℚ`, contradiction.
*** UNAUDITED.  Formalization debt, NOT /goal progress.  No sorry, no native_decide, no cited theorem. ***
-/
import Erdos634.Draft.H1kAssembly

open scoped Classical

namespace Erdos634.Draft.H1c

open Erdos634.Geometry Erdos634.Geometry.Row3 Erdos634.Geometry.Row3.RP Erdos634.Draft.H1a
  Erdos634.Draft.H1k

/-! ### 1. The flux identity, extracted -/

/-- The c = 1 flux identity for a positively oriented target in normal position (`hsum` of `row3_RP_even`). -/
theorem flux_data_pos {N : ℕ} (D : CongruentDissection N) {α : ℝ} (hα0 : 0 < α)
    (hα2 : α < Real.pi / 2) (hirr : Irrational (α / Real.pi))
    (hm0 : D.model.angleAt 0 = α) (hm2 : D.model.angleAt 2 = Real.pi / 2)
    (ht0 : D.target.angleAt 0 = α) (ht1 : D.target.angleAt 1 = α) (htdet : 0 < D.target.det) :
    ∃ (g r : Fin N → Prop) (k j : Fin N → ℤ), ∀ X : ℤ,
      ∑ i, Step6.tileVal α (g i) (r i) (k i) (j i) X
        = Step6.bdryVal α (D.target.oppLen 1 / D.model.oppLen 2) X := by
  set c := D.model.oppLen 2 with hc
  have hc0 : 0 < c := oppLen_pos _ _
  have hm1 : D.model.angleAt 1 = Real.pi / 2 - α := by
    have := D.model.angleAt_sum; linarith
  obtain ⟨hmb, hma⟩ := right_sides D.model hm2
  rw [hm0] at hmb hma
  obtain ⟨te0, te2⟩ := iso_sides D.target hα0 hα2 ht0 ht1
  have ht2 : D.target.angleAt 2 = Real.pi - 2 * α := by
    have := D.target.angleAt_sum; linarith
  set L := D.target.oppLen 1 with hL
  set lam := L / c with hlam
  have hLc : L = lam * c := by rw [hlam]; field_simp
  choose τ hτ using fun i => Tri.Congruent.exists_normal (D.tiles_congruent i)
  set T' : Fin N → Tri := fun i => (D.tile i).relabel (τ i) with hT'
  set θ₀ := (D.target.leftUnit 0).angle.toReal with hθ₀
  refine ⟨fun i => IsGridA α θ₀ ((T' i).leftUnit 0).angle, fun i => (T' i).det < 0,
    fun i => gridK α θ₀ ((T' i).leftUnit 0).angle, fun i => gridJ α θ₀ ((T' i).leftUnit 0).angle, ?_⟩
  intro X
  have hcancel := gaussWeight_flux_cancel (θ₀ := θ₀) hirr X D.toDissection
  have htgt : D.toDissection.target.flux (gaussWeight α θ₀ X) = (c : ℂ) * Step6.bdryVal α lam X :=
    target_flux_general hirr D.target htdet ht1 ht2 (by rw [te0, hLc]) hLc
      (by rw [te2, hLc]; ring) X
  have htile : ∀ i, (D.toDissection.tile i).flux (gaussWeight α θ₀ X)
      = (c : ℂ) * Step6.tileVal α (IsGridA α θ₀ ((T' i).leftUnit 0).angle)
        ((T' i).det < 0) (gridK α θ₀ ((T' i).leftUnit 0).angle)
        (gridJ α θ₀ ((T' i).leftUnit 0).angle) X := by
    intro i
    show (D.tile i).flux _ = _
    rw [← Tri.flux_relabel (D.tile i) (τ i)]
    exact rightTile_flux_value_c hirr (T' i) ((hτ i 1).1.trans hm1) ((hτ i 2).1.trans hm2)
      ((hτ i 0).2.trans hma) ((hτ i 1).2.trans hmb) ((hτ i 2).2) X
  rw [Finset.sum_congr rfl (fun i _ => htile i), ← Finset.mul_sum, htgt] at hcancel
  exact mul_left_cancel₀ (by exact_mod_cast hc0.ne') hcancel

/-- The flux identity for a normal-form dissection of either orientation. -/
theorem flux_data {N : ℕ} {D : CongruentDissection N} {α : ℝ} (h : RightNormal D α) :
    ∃ (g r : Fin N → Prop) (k j : Fin N → ℤ), ∀ X : ℤ,
      ∑ i, Step6.tileVal α (g i) (r i) (k i) (j i) X
        = Step6.bdryVal α (D.target.oppLen 1 / D.model.oppLen 2) X := by
  rcases lt_or_gt_of_ne D.target.det_ne_zero with hneg | hpos
  · set D3 := D.relabelTarget' (Equiv.swap 0 1) with hD3
    have e0 : D3.target.angleAt 0 = α := by
      rw [angleAt_of_pts (T := D.target) (Equiv.swap 0 1) (fun k => rfl)]
      simpa using h.t1
    have e1 : D3.target.angleAt 1 = α := by
      rw [angleAt_of_pts (T := D.target) (Equiv.swap 0 1) (fun k => rfl)]
      simpa using h.t0
    have hdet : D3.target.det = - D.target.det := by
      have p0 : D3.target.pts 0 = D.target.pts 1 := rfl
      have p1 : D3.target.pts 1 = D.target.pts 0 := rfl
      have p2 : D3.target.pts 2 = D.target.pts 2 := rfl
      unfold Tri.det; rw [p0, p1, p2]; simp only [PiLp.sub_apply]; ring
    have hopp : D3.target.oppLen 1 = D.target.oppLen 1 := by
      rw [oppLen_of_pts (T := D.target) (U := D3.target) (Equiv.swap 0 1) (fun k => rfl)]
      have := h.sides.2.2.1
      simpa using this
    obtain ⟨g, r, k, j, hs⟩ := flux_data_pos D3 h.pos h.lt h.irr h.m0 h.m2 e0 e1
      (by rw [hdet]; linarith)
    refine ⟨g, r, k, j, fun X => ?_⟩
    rw [hs X]
    show Step6.bdryVal α (D3.target.oppLen 1 / D.model.oppLen 2) X = _
    rw [hopp]
  · exact flux_data_pos D h.pos h.lt h.irr h.m0 h.m2 h.t0 h.t1 hpos

/-! ### 2. The identity scaled by c -/

theorem coef_eqn {N : ℕ} (α a b c lam : ℝ) (ha : a = c * Real.sin α) (hb : b = c * Real.cos α)
    (g r : Fin N → Prop) (k j : Fin N → ℤ)
    (hsum : ∀ X, ∑ i, Step6.tileVal α (g i) (r i) (k i) (j i) X = Step6.bdryVal α lam X) (X : ℤ) :
    (c : ℂ) * (Step6.PP g r k j X + Step6.QQ g r k j X)
      - ((b : ℂ) + (a : ℂ) * Complex.I) * Step6.PP g r k j (X + 1)
      - ((b : ℂ) - (a : ℂ) * Complex.I) * Step6.QQ g r k j (X - 1)
      = (c : ℂ) * Step6.bdryVal α lam X := by
  have h := hsum X
  rw [Step6.sum_tileVal] at h
  subst ha hb
  unfold Step6.vv Step6.uu at h
  simp only [Complex.ofReal_mul]
  linear_combination (c : ℂ) * h

/-! ### 3. Coordinate separation -/

theorem indep {a b c : ℝ} (hb : 0 < b) (hab : Irrational (a / b))
    (hc : ¬ ∃ r s : ℚ, c = r * a + s * b) :
    ∀ x y z : ℤ, (x : ℝ) * c + y * b + z * a = 0 → x = 0 ∧ y = 0 ∧ z = 0 := by
  intro x y z h
  have hx : x = 0 := by
    by_contra hx
    apply hc
    have hx' : (x : ℝ) ≠ 0 := by exact_mod_cast hx
    refine ⟨-(z : ℚ) / x, -(y : ℚ) / x, ?_⟩
    push_cast
    field_simp
    linarith
  subst hx
  have hz : z = 0 := by
    by_contra hz
    have hz' : (z : ℝ) ≠ 0 := by exact_mod_cast hz
    apply hab
    refine ⟨-(y : ℚ) / z, ?_⟩
    push_cast
    field_simp
    simp at h
    linarith
  subst hz
  refine ⟨rfl, ?_, rfl⟩
  simp at h
  rcases h with h | h
  · exact h
  · exact absurd h hb.ne'

theorem sep {a b c : ℝ} (hind : ∀ x y z : ℤ, (x : ℝ) * c + y * b + z * a = 0 → x = 0 ∧ y = 0 ∧ z = 0)
    {A B C : ℂ} (hA : Step6.IsGI A) (hB : Step6.IsGI B) (hC : Step6.IsGI C)
    (h : (c : ℂ) * A + (b : ℂ) * B + (a : ℂ) * C = 0) : A = 0 ∧ B = 0 ∧ C = 0 := by
  obtain ⟨p1, q1, rfl⟩ := hA
  obtain ⟨p2, q2, rfl⟩ := hB
  obtain ⟨p3, q3, rfl⟩ := hC
  have h1 := congrArg Complex.re h
  have h2 := congrArg Complex.im h
  simp at h1 h2
  obtain ⟨e1, e2, e3⟩ := hind p1 p2 p3 (by linarith)
  obtain ⟨f1, f2, f3⟩ := hind q1 q2 q3 (by linarith)
  subst e1 e2 e3 f1 f2 f3
  simp

theorem pq_zero {P Q : ℂ} (hB : -P - Q = 0) (hC : Complex.I * (Q - P) = 0) : P = 0 ∧ Q = 0 := by
  have h : Q - P = 0 := by
    rcases mul_eq_zero.mp hC with h | h
    · exact absurd h Complex.I_ne_zero
    · exact h
  constructor
  · linear_combination (-1 / 2 : ℂ) * hB + (-1 / 2 : ℂ) * h
  · linear_combination (-1 / 2 : ℂ) * hB + (1 / 2 : ℂ) * h

theorem isGI_PP {N : ℕ} (g r : Fin N → Prop) (k j : Fin N → ℤ) (X : ℤ) :
    Step6.IsGI (Step6.PP g r k j X) :=
  Step6.isGI_sum _ (fun i => Step6.isGI_ite _ (Step6.isGI_I_zpow _))

theorem isGI_QQ {N : ℕ} (g r : Fin N → Prop) (k j : Fin N → ℤ) (X : ℤ) :
    Step6.IsGI (Step6.QQ g r k j X) :=
  Step6.isGI_sum _ (fun i => Step6.isGI_ite _ (Step6.isGI_I_zpow _))

theorem isGI_nat (n : ℕ) : Step6.IsGI (n : ℂ) := ⟨n, 0, by simp⟩

theorem isGI_nat_I (n : ℕ) : Step6.IsGI ((n : ℂ) * Complex.I) := ⟨0, n, by simp⟩

/-! ### 4. Case C -/

theorem bdryVal_neg_one (α lam : ℝ) : Step6.bdryVal α lam (-1) = -(lam : ℂ) := by
  unfold Step6.bdryVal; rw [if_neg (by omega), if_pos rfl, if_neg (by omega)]; ring

/-- **Case C core**: the c = 1 identity plus the side word of `AB` forces `u_a = u_b = 0`. -/
theorem caseC_core {N : ℕ} (α a b c lam : ℝ) (ha : a = c * Real.sin α) (hb : b = c * Real.cos α)
    (hind : ∀ x y z : ℤ, (x : ℝ) * c + y * b + z * a = 0 → x = 0 ∧ y = 0 ∧ z = 0)
    (g r : Fin N → Prop) (k j : Fin N → ℤ)
    (hsum : ∀ X, ∑ i, Step6.tileVal α (g i) (r i) (k i) (j i) X = Step6.bdryVal α lam X)
    (ua ub uc : ℕ) (hw : lam * c = ua * a + ub * b + uc * c) : ua = 0 ∧ ub = 0 := by
  have hw' : (lam : ℂ) * c = (ua : ℂ) * a + (ub : ℂ) * b + (uc : ℂ) * c := by exact_mod_cast hw
  set P := Step6.PP g r k j with hP
  set Q := Step6.QQ g r k j with hQ
  have hPG : ∀ X, Step6.IsGI (P X) := fun X => isGI_PP g r k j X
  have hQG : ∀ X, Step6.IsGI (Q X) := fun X => isGI_QQ g r k j X
  -- X = -3
  have e3 := coef_eqn α a b c lam ha hb g r k j hsum (-3)
  rw [show (-3 : ℤ) + 1 = -2 by norm_num, show (-3 : ℤ) - 1 = -4 by norm_num,
    Step6.bdryVal_low α lam (-3) (by norm_num), mul_zero] at e3
  have s3 := sep hind (A := P (-3) + Q (-3)) (B := -P (-2) - Q (-4))
    (C := Complex.I * (Q (-4) - P (-2)))
    (Step6.isGI_add (hPG _) (hQG _))
    (Step6.isGI_sub (Step6.isGI_neg (hPG _)) (hQG _))
    (Step6.isGI_mul ⟨0, 1, by simp⟩ (Step6.isGI_sub (hQG _) (hPG _)))
    (by linear_combination e3)
  have hP2 : P (-2) = 0 := (pq_zero s3.2.1 s3.2.2).1
  -- X = -2
  have e2 := coef_eqn α a b c lam ha hb g r k j hsum (-2)
  rw [show (-2 : ℤ) + 1 = -1 by norm_num, show (-2 : ℤ) - 1 = -3 by norm_num,
    Step6.bdryVal_low α lam (-2) (by norm_num), mul_zero] at e2
  have s2 := sep hind (A := P (-2) + Q (-2)) (B := -P (-1) - Q (-3))
    (C := Complex.I * (Q (-3) - P (-1)))
    (Step6.isGI_add (hPG _) (hQG _))
    (Step6.isGI_sub (Step6.isGI_neg (hPG _)) (hQG _))
    (Step6.isGI_mul ⟨0, 1, by simp⟩ (Step6.isGI_sub (hQG _) (hPG _)))
    (by linear_combination e2)
  have hQ2 : Q (-2) = 0 := by
    have := s2.1; rw [hP2] at this; simpa using this
  -- X = -1
  have e1 := coef_eqn α a b c lam ha hb g r k j hsum (-1)
  rw [show (-1 : ℤ) + 1 = 0 by norm_num, show (-1 : ℤ) - 1 = -2 by norm_num,
    bdryVal_neg_one] at e1
  have s1 := sep hind (A := P (-1) + Q (-1) + (uc : ℂ)) (B := -P 0 - Q (-2) + (ub : ℂ))
    (C := Complex.I * (Q (-2) - P 0) + (ua : ℂ))
    (Step6.isGI_add (Step6.isGI_add (hPG _) (hQG _)) (isGI_nat _))
    (Step6.isGI_add (Step6.isGI_sub (Step6.isGI_neg (hPG _)) (hQG _)) (isGI_nat _))
    (Step6.isGI_add (Step6.isGI_mul ⟨0, 1, by simp⟩ (Step6.isGI_sub (hQG _) (hPG _))) (isGI_nat _))
    (by linear_combination e1 - hw')
  have hb1 := s1.2.1
  have hc1 := s1.2.2
  rw [hQ2] at hb1 hc1
  -- hb1 : -P 0 - 0 + ub = 0 ;  hc1 : I*(0 - P 0) + ua = 0
  have hPb : P 0 = (ub : ℂ) := by linear_combination -hb1
  rw [hPb] at hc1
  -- I * (-ub) + ua = 0  ⇒ ua = I ub ⇒ both 0
  have h1 := congrArg Complex.re hc1
  have h2 := congrArg Complex.im hc1
  simp at h1 h2
  exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩

/-- **`RightCaseC N` for every `N`.** -/
theorem rightCaseC (N : ℕ) : RightCaseC N := by
  intro D α hN hlam hab hc
  obtain ⟨M, hF⟩ := hN.facts
  obtain ⟨sa, sb, -, -⟩ := hN.sides
  obtain ⟨g, r, k, j, hsum⟩ := flux_data hN
  obtain ⟨ua, ub, uc, hw⟩ := hF.wAB
  have hind := indep hF.hb hab hc
  obtain ⟨hua, hub⟩ := caseC_core (N := N) α _ _ _ _ sa sb hind g r k j hsum ua ub uc hw
  subst hua hub
  apply hlam
  refine ⟨(uc : ℚ), ?_⟩
  have hc0 : D.model.oppLen 2 ≠ 0 := hF.hc.ne'
  have h' : D.target.oppLen 1 / D.model.oppLen 2 = uc :=
    mul_right_cancel₀ hc0 (by simpa using hw)
  push_cast
  exact h'.symm

end Erdos634.Draft.H1c

#print axioms Erdos634.Draft.H1c.flux_data
#print axioms Erdos634.Draft.H1c.rightCaseC
