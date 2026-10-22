import Erdos634.Draft.LaczFormalL30Chart

/-!
# Laczkovich Theorem 2.5, triple `(2α, 2β, α+β)`: the trapezoid `M L O' O` (Lemma 2.2 (ii))

NOTE, UNAUDITED.  Credit: Laczkovich (Discrete Math. 140 (1995) 79-94, Lemma 2.2 (ii), Theorem 2.5, Fig. 7), Beeson,
Beeson-Zhang, Zhang.

The trapezoid has angle `β` at `L`, so Lemma 2.2 (ii) (`trap_ii`) applies in the sub-chart
`(L; w' = O' - L, d' = M - L)` with `W = ν a`, `Dd = c a (a-b) / (b (2a+b))` and top-to-bottom ratio `τ = 1/ν`
(a rational identity, `tTau_eq`).  The standard trapezoid is the union of two standard triangles
(`trapSet_split`); their images are the halves `O O' M`, `O' L M` of `LaczFormalL30Geo`.
-/

namespace Erdos634.LaczL30

open Erdos634.Geometry Erdos634.CertCoord Erdos634.LaczL22 Erdos634.LaczL21 Erdos634.LaczL24 Erdos634.Realizable
  Erdos634.DissectionMap

/-! ### the standard trapezoid is two triangles -/

private theorem htri' : ∀ i : Fin 3, i = 0 ∨ i = 1 ∨ i = 2 := by decide

theorem trapSet_split (τ : ℝ) (hτ : 0 < τ) :
    trapSet τ = (mkTri 1 0 τ 1 0 1 (by simp only [det3]; nlinarith)).carrier
      ∪ (mkTri 0 0 1 0 0 1 (by simp only [det3]; norm_num)).carrier := by
  have hdX : 0 < det3 1 0 τ 1 0 1 := by simp only [det3]; nlinarith
  have hdY : 0 < det3 0 0 1 0 0 1 := by simp only [det3]; norm_num
  apply Set.Subset.antisymm
  · intro z hz
    obtain ⟨h1, h2, h3, h4⟩ := hz
    rw [← mkPt_self z]
    by_cases hs : z 0 + z 1 ≤ 1
    · right
      exact mem_carrier_of_dets hdY (by simp only [det3]; nlinarith) (by simp only [det3]; nlinarith)
        (by simp only [det3]; nlinarith)
    · left
      push_neg at hs
      exact mem_carrier_of_dets hdX (by simp only [det3]; nlinarith) (by simp only [det3]; nlinarith)
        (by simp only [det3]; nlinarith)
  · intro z hz
    have hcv := convex_trapSet τ
    rcases hz with hz | hz
    · refine (convexHull_min (Set.range_subset_iff.mpr (fun i => ?_)) hcv) hz
      rcases htri' i with rfl | rfl | rfl
      · show mkPt 1 0 ∈ trapSet τ
        refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [mkPt_zero, mkPt_one] <;> linarith
      · show mkPt τ 1 ∈ trapSet τ
        refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [mkPt_zero, mkPt_one] <;> linarith
      · show mkPt 0 1 ∈ trapSet τ
        refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [mkPt_zero, mkPt_one] <;> linarith
    · refine (convexHull_min (Set.range_subset_iff.mpr (fun i => ?_)) hcv) hz
      rcases htri' i with rfl | rfl | rfl
      · show mkPt 0 0 ∈ trapSet τ
        refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [mkPt_zero, mkPt_one] <;> linarith
      · show mkPt 1 0 ∈ trapSet τ
        refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [mkPt_zero, mkPt_one] <;> linarith
      · show mkPt 0 1 ∈ trapSet τ
        refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [mkPt_zero, mkPt_one] <;> linarith

/-- images of triangles with the same vertex set (up to a permutation of the vertices). -/
theorem image_tri_eq (e e' : Plane ≃ᵃ[ℝ] Plane) (X S : Tri) (σ : Equiv.Perm (Fin 3))
    (h : ∀ i, e' (X.pts i) = e (S.pts (σ i))) : e' '' X.carrier = e '' S.carrier := by
  rw [← mapTri_carrier, ← mapTri_carrier]
  simp only [Tri.carrier, mapTri]
  have : (e' ∘ X.pts) = (e ∘ S.pts) ∘ σ := by funext i; exact h i
  rw [this, Function.Surjective.range_comp σ.surjective]

/-! ### rational data -/

/-- the leg `Dd = c a (a - b) / (b (2a + b))` of the trapezoid. -/
noncomputable def Ddq (R : RTri) : ℚ := R.c * R.a * (R.a - R.b) / (R.b * (2 * R.a + R.b))

/-- the base `W = ν a`. -/
noncomputable def Wq (R : RTri) : ℚ := nuq R * R.a

/-- the ratio `τ = 1/ν` of the parallel sides. -/
noncomputable def tauq (R : RTri) : ℚ := 1 / nuq R

theorem ddcos (R : RTri) (hγ : R.a ^ 2 + R.a * R.b + R.b ^ 2 = R.c ^ 2) (hab : R.b < R.a) :
    Ddq R * R.cos1 = R.a * (R.a - R.b) / (2 * R.b) := by
  have hc := R.pc; have ha := R.pa; have hb := R.pb
  have h2 : 0 < 2 * R.a + R.b := by linarith
  have e : R.a ^ 2 + R.c ^ 2 - R.b ^ 2 = R.a * (2 * R.a + R.b) := by linear_combination (-1 : ℚ) * hγ
  unfold Ddq RTri.cos1
  rw [e]
  field_simp

theorem tTau_eq (R : RTri) (hγ : R.a ^ 2 + R.a * R.b + R.b ^ 2 = R.c ^ 2) :
    tTau R.a R.b R.c (Wq R) (Ddq R) = tauq R := by
  have hc := R.pc; have ha := R.pa; have hb := R.pb
  have h2 : 0 < 2 * R.a + R.b := by linarith
  have h3 : 0 < R.a + 2 * R.b := by linarith
  have e : R.b ^ 2 - R.c ^ 2 = -(R.a * (R.a + R.b)) := by linear_combination hγ
  unfold tTau
  rw [e]
  unfold Wq Ddq tauq nuq
  field_simp
  ring

theorem tauq_pos (R : RTri) : 0 < tauq R := by unfold tauq; have := nuq_pos R; positivity

theorem Wq_pos (R : RTri) : 0 < Wq R := by unfold Wq; have := nuq_pos R; have := R.pa; positivity

theorem Ddq_pos (R : RTri) (hab : R.b < R.a) : 0 < Ddq R := by
  have := R.pa; have := R.pb; have := R.pc; have : 0 < R.a - R.b := by linarith
  unfold Ddq; positivity

section chart

variable (R : RTri) (hγ : R.a ^ 2 + R.a * R.b + R.b ^ 2 = R.c ^ 2) (hab : R.b < R.a)
  (w d : Plane) (hdet : w 0 * d 1 - w 1 * d 0 ≠ 0)
  (hw : inner ℝ w w = (R.a : ℝ) ^ 2) (hd : inner ℝ d d = (R.a : ℝ) ^ 2)
  (hwd : inner ℝ w d = (R.a : ℝ) * (R.a : ℝ) * (-1 / 2))

include hγ hab hdet hw hd hwd

set_option maxHeartbeats 4000000 in
/-- **The trapezoid piece** `Strap = O O' M ∪ O' L M` is a rational similar dissection in the chart `(O; w, d)`. -/
theorem chart_strap :
    ChartRSD R 0 w d hdet ((tS1 (hK0 R) (hK1 R hab)).carrier ∪ (tS2 (hK0 R) (hK1 R hab)).carrier) := by
  obtain ⟨hb, hc2⟩ := real_facts R hγ
  have hk0 := hK0 R
  have hk1 := hK1 R hab
  set K : ℝ := ((kq R : ℚ) : ℝ) with hKdef
  have hn := nu_pos hk0 hk1
  have ht := th_pos hk0 hk1
  have h1 : K ≠ 0 := hk0.ne'
  have h2 : (2 : ℝ) + K ≠ 0 := by linarith
  have hnc : ((nuq R : ℚ) : ℝ) = nu K := nuq_cast R
  have ha : (0 : ℝ) < R.a := by exact_mod_cast R.pa
  have hb0 : (0 : ℝ) < R.b := by exact_mod_cast R.pb
  have hc0 : (0 : ℝ) < R.c := by exact_mod_cast R.pc
  have h2a : (0 : ℝ) < 2 * R.a + R.b := by linarith
  have hab' : (R.b : ℝ) < R.a := by exact_mod_cast hab
  -- the sub-chart
  have hdet' : ((0 : ℝ) • w + (-(nu K)) • d) 0 * ((-(th K)) • w + (1 - nu K) • d) 1
      - ((0 : ℝ) • w + (-(nu K)) • d) 1 * ((-(th K)) • w + (1 - nu K) • d) 0 ≠ 0 := by
    rw [Erdos634.LaczL25.det_comb]
    refine mul_ne_zero ?_ hdet
    have := mul_pos hn ht
    intro h; nlinarith
  have hwG : inner ℝ ((0 : ℝ) • w + (-(nu K)) • d) ((0 : ℝ) • w + (-(nu K)) • d) = ((Wq R : ℚ) : ℝ) ^ 2 := by
    rw [Erdos634.LaczL26.gram2, hw, hd, hwd]
    unfold Wq; push_cast; rw [hnc]; ring
  have hdG : inner ℝ ((-(th K)) • w + (1 - nu K) • d) ((-(th K)) • w + (1 - nu K) • d) = ((Ddq R : ℚ) : ℝ) ^ 2 := by
    rw [Erdos634.LaczL26.gram2, hw, hd, hwd]
    have e : ((Ddq R : ℚ) : ℝ) ^ 2 = (R.c : ℝ) ^ 2 * ((R.a : ℝ) * ((R.a : ℝ) - R.b) / (R.b * (2 * R.a + R.b))) ^ 2 := by
      unfold Ddq; push_cast; ring
    rw [e, hc2, hb]
    unfold th nu; field_simp; ring
  have hdd := ddcos R hγ hab
  have hwdG : inner ℝ ((0 : ℝ) • w + (-(nu K)) • d) ((-(th K)) • w + (1 - nu K) • d)
      = ((Wq R : ℚ) : ℝ) * ((Ddq R : ℚ) : ℝ) * ((R.cos1 : ℚ) : ℝ) := by
    have e : ((Wq R : ℚ) : ℝ) * ((Ddq R : ℚ) : ℝ) * ((R.cos1 : ℚ) : ℝ)
        = ((Wq R : ℚ) : ℝ) * (((Ddq R * R.cos1 : ℚ)) : ℝ) := by push_cast; ring
    rw [e, hdd, Erdos634.LaczL26.gram2, hw, hd, hwd]
    unfold Wq; push_cast; rw [hnc, hb]
    unfold th nu; field_simp; ring
  have ct := trap_ii R ((th K) • w + (nu K) • d) ((0 : ℝ) • w + (-(nu K)) • d) ((-(th K)) • w + (1 - nu K) • d)
    hdet' (Wq R) (Ddq R) (Wq_pos R) (Ddq_pos R hab) hwG hdG hwdG (tauq R) (tTau_eq R hγ).symm (tauq_pos R)
  have hτR : (0 : ℝ) < ((tauq R : ℚ) : ℝ) := by exact_mod_cast tauq_pos R
  have hτ' : ((tauq R : ℚ) : ℝ) = 1 / nu K := by unfold tauq; push_cast; rw [hnc]
  -- vertex identities of the sub-chart
  have sub : ∀ x y : ℝ, chartEquiv ((th K) • w + (nu K) • d) ((0 : ℝ) • w + (-(nu K)) • d)
      ((-(th K)) • w + (1 - nu K) • d) hdet' (mkPt x y)
      = chartEquiv 0 w d hdet (mkPt (th K - y * th K) (nu K - x * nu K + y * (1 - nu K))) := by
    intro x y
    rw [chartEquiv_apply, chartEquiv_apply]
    simp only [mkPt_zero, mkPt_one]
    module
  unfold ChartRSD at ct ⊢
  rw [trapSet_split _ hτR, Set.image_union] at ct
  rw [Set.image_union]
  have hτn : ((tauq R : ℚ) : ℝ) * nu K = 1 := by rw [hτ']; field_simp
  have eX : chartEquiv ((th K) • w + (nu K) • d) ((0 : ℝ) • w + (-(nu K)) • d)
      ((-(th K)) • w + (1 - nu K) • d) hdet' ''
        (mkTri 1 0 ((tauq R : ℚ) : ℝ) 1 0 1 (by simp only [det3]; nlinarith)).carrier
      = chartEquiv 0 w d hdet '' (tS1 hk0 hk1).carrier := by
    refine image_tri_eq _ _ _ _ (Equiv.swap 0 1) (fun i => ?_)
    rcases htri' i with rfl | rfl | rfl
    · show chartEquiv _ _ _ hdet' (mkPt 1 0) = chartEquiv 0 w d hdet (mkPt (th K) 0)
      rw [sub]; congr 2 <;> ring
    · show chartEquiv _ _ _ hdet' (mkPt ((tauq R : ℚ) : ℝ) 1) = chartEquiv 0 w d hdet (mkPt 0 0)
      rw [sub]; congr 2
      · ring
      · linear_combination (-1 : ℝ) * hτn
    · show chartEquiv _ _ _ hdet' (mkPt 0 1) = chartEquiv 0 w d hdet (mkPt 0 1)
      rw [sub]; congr 2 <;> ring
  have eY : chartEquiv ((th K) • w + (nu K) • d) ((0 : ℝ) • w + (-(nu K)) • d)
      ((-(th K)) • w + (1 - nu K) • d) hdet' ''
        (mkTri 0 0 1 0 0 1 (by simp only [det3]; norm_num)).carrier
      = chartEquiv 0 w d hdet '' (tS2 hk0 hk1).carrier := by
    refine image_tri_eq _ _ _ _ (Equiv.swap 0 1) (fun i => ?_)
    rcases htri' i with rfl | rfl | rfl
    · show chartEquiv _ _ _ hdet' (mkPt 0 0) = chartEquiv 0 w d hdet (mkPt (th K) (nu K))
      rw [sub]; congr 2 <;> ring
    · show chartEquiv _ _ _ hdet' (mkPt 1 0) = chartEquiv 0 w d hdet (mkPt (th K) 0)
      rw [sub]; congr 2 <;> ring
    · show chartEquiv _ _ _ hdet' (mkPt 0 1) = chartEquiv 0 w d hdet (mkPt 0 1)
      rw [sub]; congr 2 <;> ring
  rw [eX, eY] at ct
  exact ct

end chart

end Erdos634.LaczL30
