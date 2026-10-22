import Erdos634.Draft.LaczFormalL30Trap

/-!
# Laczkovich Theorem 2.5, triple `(2α, 2β, α+β)`: the triangle `Θ = A L V` is a rational similar dissection

NOTE, UNAUDITED.  Credit: Laczkovich (Discrete Math. 140 (1995) 79-94, Theorem 2.5, Fig. 7), Beeson, Beeson-Zhang, Zhang.

In the chart `(O; w, d)` (`|w| = |d| = a`, `⟨w,d⟩ = -a²/2`), for a rational tile with `γ = 2π/3` and `b < a`:
`Θ = A V L = A O M ∪ A V O ∪ V L O' ∪ (O O' M ∪ O' L M)` (the last two being the trapezoid of Lemma 2.2 (ii)).
-/

namespace Erdos634.LaczL30

open Erdos634.Geometry Erdos634.CertCoord Erdos634.LaczL22 Erdos634.LaczL24 Erdos634.Realizable

private theorem htri'' : ∀ i : Fin 3, i = 0 ∨ i = 1 ∨ i = 2 := by decide

section strapsep

variable {k : ℝ} (hk0 : 0 < k) (hk1 : k < 1)

/-- the trapezoid `O O' M ∪ O' L M` as a set. -/
noncomputable def strap : Set Plane := (tS1 hk0 hk1).carrier ∪ (tS2 hk0 hk1).carrier

theorem strap_closed : IsClosed (strap hk0 hk1) :=
  ((tS1 hk0 hk1).isCompact.isClosed).union ((tS2 hk0 hk1).isCompact.isClosed)

theorem d_P1_strap : Disjoint (interior (tP1 hk0 hk1).carrier) (interior (strap hk0 hk1)) := by
  have ht := th_pos hk0 hk1
  refine disjoint_interior_of_sep (coordFun 1 0 0) (coordFun_linear_ne_zero 0 (Or.inl one_ne_zero)) 0 ?_ ?_
  · exact Erdos634.CertGeom.le_of_forall_pts_le _
      (fun i => by rcases htri'' i with rfl | rfl | rfl <;> simp [tP1, mkPt_zero, mkPt_one, hk0.le])
  · intro x hx
    rcases hx with hx | hx
    · exact ge_of_forall_pts_ge (coordFun 1 0 0)
        (fun i => by rcases htri'' i with rfl | rfl | rfl <;> simp [tS1, mkPt_zero, mkPt_one, ht.le]) x hx
    · exact ge_of_forall_pts_ge (coordFun 1 0 0)
        (fun i => by rcases htri'' i with rfl | rfl | rfl <;> simp [tS2, mkPt_zero, mkPt_one, ht.le]) x hx

theorem d_P2_strap : Disjoint (interior (tP2 hk0 hk1).carrier) (interior (strap hk0 hk1)) := by
  have hn := nu_pos hk0 hk1
  refine disjoint_interior_of_sep (coordFun 0 1 0) (coordFun_linear_ne_zero 0 (Or.inr one_ne_zero)) 0 ?_ ?_
  · exact Erdos634.CertGeom.le_of_forall_pts_le _
      (fun i => by rcases htri'' i with rfl | rfl | rfl <;> simp [tP2, mkPt_zero, mkPt_one, hk0.le])
  · intro x hx
    rcases hx with hx | hx
    · exact ge_of_forall_pts_ge (coordFun 0 1 0)
        (fun i => by rcases htri'' i with rfl | rfl | rfl <;> simp [tS1, mkPt_zero, mkPt_one]) x hx
    · exact ge_of_forall_pts_ge (coordFun 0 1 0)
        (fun i => by rcases htri'' i with rfl | rfl | rfl <;> simp [tS2, mkPt_zero, mkPt_one, hn.le]) x hx

theorem d_strap_P3 : Disjoint (interior (strap hk0 hk1)) (interior (tP3 hk0 hk1).carrier) := by
  have ht := th_pos hk0 hk1
  have h1 := th_lt_one hk0 hk1
  refine disjoint_interior_of_sep (coordFun 1 0 0) (coordFun_linear_ne_zero 0 (Or.inl one_ne_zero)) (th k) ?_ ?_
  · intro x hx
    rcases hx with hx | hx
    · exact Erdos634.CertGeom.le_of_forall_pts_le (coordFun 1 0 0)
        (fun i => by rcases htri'' i with rfl | rfl | rfl <;> simp [tS1, mkPt_zero, mkPt_one, ht.le]) x hx
    · exact Erdos634.CertGeom.le_of_forall_pts_le (coordFun 1 0 0)
        (fun i => by rcases htri'' i with rfl | rfl | rfl <;> simp [tS2, mkPt_zero, mkPt_one, ht.le]) x hx
  · exact ge_of_forall_pts_ge _
      (fun i => by rcases htri'' i with rfl | rfl | rfl <;> simp [tP3, mkPt_zero, mkPt_one, h1.le])

/-- the four chart pieces. -/
noncomputable def cpieces : Fin 4 → Set Plane :=
  ![(tP1 hk0 hk1).carrier, (tP2 hk0 hk1).carrier, (tP3 hk0 hk1).carrier, strap hk0 hk1]

theorem cpieces_cover : (⋃ i, cpieces hk0 hk1 i) = (tTh hk0 hk1).carrier := by
  rw [← cover5 hk0 hk1]
  ext z
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨i, hi⟩
    fin_cases i
    · exact ⟨0, hi⟩
    · exact ⟨1, hi⟩
    · exact ⟨4, hi⟩
    · rcases hi with hi | hi
      · exact ⟨2, hi⟩
      · exact ⟨3, hi⟩
  · rintro ⟨i, hi⟩
    fin_cases i
    · exact ⟨0, hi⟩
    · exact ⟨1, hi⟩
    · exact ⟨3, Or.inl hi⟩
    · exact ⟨3, Or.inr hi⟩
    · exact ⟨2, hi⟩

end strapsep

section theta

variable (R : RTri) (hγ : R.a ^ 2 + R.a * R.b + R.b ^ 2 = R.c ^ 2) (hab : R.b < R.a)
  (w d : Plane) (hdet : w 0 * d 1 - w 1 * d 0 ≠ 0)
  (hw : inner ℝ w w = (R.a : ℝ) ^ 2) (hd : inner ℝ d d = (R.a : ℝ) ^ 2)
  (hwd : inner ℝ w d = (R.a : ℝ) * (R.a : ℝ) * (-1 / 2))

include hγ hab hdet hw hd hwd

/-- **The triangle `Θ = A V L` of Fig. 7 (second picture) is a rational similar dissection.** -/
theorem chart_Theta : ChartRSD R 0 w d hdet (tTh (hK0 R) (hK1 R hab)).carrier := by
  have hk0 := hK0 R
  have hk1 := hK1 R hab
  have key := Erdos634.LaczL26.chart_iUnion (R := R) (A := 0) (w := w) (d := d) (h := hdet) (ι := Fin 4) (cpieces hk0 hk1)
    (by
      intro i; fin_cases i
      · exact chart_P1 R hγ hab w d hdet hw hd hwd
      · exact chart_P2 R hγ hab w d hdet hw hd hwd
      · exact chart_P3 R hγ hab w d hdet hw hd hwd
      · exact chart_strap R hγ hab w d hdet hw hd hwd)
    (by
      intro i; fin_cases i
      · exact (tP1 hk0 hk1).isCompact.isClosed
      · exact (tP2 hk0 hk1).isCompact.isClosed
      · exact (tP3 hk0 hk1).isCompact.isClosed
      · exact strap_closed hk0 hk1)
    (by
      intro i j hij
      fin_cases i <;> fin_cases j
      · exact absurd rfl hij
      · exact d_P1_P2 hk0 hk1
      · exact d_P1_P3 hk0 hk1
      · exact d_P1_strap hk0 hk1
      · exact (d_P1_P2 hk0 hk1).symm
      · exact absurd rfl hij
      · exact d_P2_P3 hk0 hk1
      · exact d_P2_strap hk0 hk1
      · exact (d_P1_P3 hk0 hk1).symm
      · exact (d_P2_P3 hk0 hk1).symm
      · exact absurd rfl hij
      · exact (d_strap_P3 hk0 hk1).symm
      · exact (d_P1_strap hk0 hk1).symm
      · exact (d_P2_strap hk0 hk1).symm
      · exact d_strap_P3 hk0 hk1
      · exact absurd rfl hij)
  rw [cpieces_cover hk0 hk1] at key
  exact key

end theta

#print axioms chart_Theta

end Erdos634.LaczL30
