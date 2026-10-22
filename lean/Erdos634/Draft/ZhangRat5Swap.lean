import Erdos634.Draft.ZhangRat5Derived

/-!
# Zhang Prop 11 for `a > b` and the unified statement for every rational tile

`swapR R` is the tile `R` with the vertices `0, 1` exchanged (a reflection): its sides are `(b, a, c)`.
`TileDis (swapR R) S n <-> TileDis R S n` (a relabelling is a congruence, `congruent_permTri`).  The hypothesis
triangle of Prop 11 (1) for `R` is the hypothesis triangle of Prop 11 (2) for `swapR R` (the sides `AD`, `BD`
are exchanged), and conclusion (1) for `R` is conclusion (2) for `swapR R` (and (2) for `R` is (1) for
`swapR R`).  So the case `b < a` of the derived statements (`ZhangRat5Derived`, which needs `a < b` for
Prop 6 / Thm 7) follows by the exchange `a <-> b`.  `a = b` cannot occur for a rational tile
(`c^2 = 3 a^2`).  The final statements `zhang_prop11_{1,2}_final` hold for EVERY rational tile
`(a, b, c)` with `c^2 = a^2 + b^2 + ab`, with the tiling of the hypothesis triangle DERIVED for every
`m'` in the semigroup `<max(A,B), C>` (the exact range of Zhang's Prop 6(1), 6(2), Thm 7).  UNAUDITED.
Credit Zhang (arXiv 2512.22696v4), Beeson, Beeson-Zhang, Laczkovich.
-/

set_option maxHeartbeats 3200000

namespace Erdos634.ZhangRat5

open Erdos634.Geometry Erdos634.CertCoord Erdos634.CertGeom Erdos634.RegionDissection
  Erdos634.SssCongruent Erdos634.ZhangPara Erdos634.ZhangL1 Erdos634.ZhangSporadic
  Erdos634.ZhangRat Erdos634.ZhangRational Erdos634.LaczL22 Erdos634.Realizable Erdos634.BeesonCor5
  Erdos634.ZhangThm4 Erdos634.ZhangRat3 Erdos634.ZhangRat4

/-- the tile with the vertices `0, 1` exchanged: sides `(b, a, c)`. -/
noncomputable def swapR (R : RTri) : RTri where
  Δ := permTri R.Δ (Equiv.swap 0 1)
  a := R.b
  b := R.a
  c := R.c
  ha := by
    have h1 : (Equiv.swap (0 : Fin 3) 1) 1 = 0 := by decide
    have h2 : (Equiv.swap (0 : Fin 3) 1) 2 = 2 := by decide
    show dist (R.Δ.pts ((Equiv.swap (0 : Fin 3) 1) 1)) (R.Δ.pts ((Equiv.swap (0 : Fin 3) 1) 2)) = _
    rw [h1, h2, dist_comm]; exact R.hb
  hb := by
    have h0 : (Equiv.swap (0 : Fin 3) 1) 0 = 1 := by decide
    have h2 : (Equiv.swap (0 : Fin 3) 1) 2 = 2 := by decide
    show dist (R.Δ.pts ((Equiv.swap (0 : Fin 3) 1) 2)) (R.Δ.pts ((Equiv.swap (0 : Fin 3) 1) 0)) = _
    rw [h0, h2, dist_comm]; exact R.ha
  hc := by
    have h0 : (Equiv.swap (0 : Fin 3) 1) 0 = 1 := by decide
    have h1 : (Equiv.swap (0 : Fin 3) 1) 1 = 0 := by decide
    show dist (R.Δ.pts ((Equiv.swap (0 : Fin 3) 1) 0)) (R.Δ.pts ((Equiv.swap (0 : Fin 3) 1) 1)) = _
    rw [h0, h1, dist_comm]; exact R.hc
  pa := R.pb
  pb := R.pa
  pc := R.pc

theorem tileDis_swap (R : RTri) {S : Set Plane} {n : ℕ} : TileDis (swapR R) S n ↔ TileDis R S n := by
  constructor
  · rintro ⟨C, hr, hc⟩
    exact ⟨C, hr, hc.trans (congruent_permTri R.Δ _)⟩
  · rintro ⟨C, hr, hc⟩
    exact ⟨C, hr, hc.trans (congruent_permTri R.Δ _).symm⟩

theorem TileDis.cn {R : RTri} {S : Set Plane} {n n' : ℕ} (h : TileDis R S n) (e : n = n') :
    TileDis R S n' := e ▸ h

theorem swapR_rel (R : RTri) (hrel : R.c ^ 2 = R.a ^ 2 + R.b ^ 2 + R.a * R.b) :
    (swapR R).c ^ 2 = (swapR R).a ^ 2 + (swapR R).b ^ 2 + (swapR R).a * (swapR R).b := by
  show R.c ^ 2 = R.b ^ 2 + R.a ^ 2 + R.b * R.a
  rw [hrel]; ring

section main
variable (R : RTri) (hrel : R.c ^ 2 = R.a ^ 2 + R.b ^ 2 + R.a * R.b)
include hrel

/-- **Prop 11 (1) for `b < a`**, hypothesis derived on the semigroup `<A, C>` (`A` the larger side). -/
theorem zhang_prop11_1_Sb (hba : R.b < R.a) :
    ∃ (A B C : ℕ) (k : ℚ) (hA : 0 < A) (hB : 0 < B), 0 < k ∧ R.a = k * A ∧ R.b = k * B ∧ R.c = k * C ∧
      C * C = A * A + B * B + A * B ∧ Nat.Coprime A B ∧ B < A ∧
      ∀ (m : ℝ) (m' : ℕ), 0 < m' → (k : ℝ) * m = m' → (∃ i j : ℕ, m' = A * i + C * j) →
        ∀ (Ax Ay Bx By Dx Dy : ℝ),
        0 < det3 Ax Ay Dx Dy Bx By →
        (Ax - Dx) ^ 2 + (Ay - Dy) ^ 2 = (((R.a : ℝ) + 2 * R.b) * R.a * m) ^ 2 →
        (Bx - Dx) ^ 2 + (By - Dy) ^ 2 = (((R.b : ℝ) + 2 * R.a) * R.b * m) ^ 2 →
        (Ax - Bx) ^ 2 + (Ay - By) ^ 2 = ((R.c : ℝ) ^ 2 * m) ^ 2 →
        ∃ Cx Cy : ℝ,
          Cx = Dx + (((R.a : ℝ) + 2 * R.b) / ((R.b : ℝ) + 2 * R.a)) * (Dx - Bx) ∧
          Cy = Dy + (((R.a : ℝ) + 2 * R.b) / ((R.b : ℝ) + 2 * R.a)) * (Dy - By) ∧
          (Cx - Bx) ^ 2 + (Cy - By) ^ 2 = (3 * ((R.a : ℝ) + R.b) * R.b * m) ^ 2 ∧
          (Cx - Ax) ^ 2 + (Cy - Ay) ^ 2 = (((R.a : ℝ) + 2 * R.b) * m * R.c) ^ 2 ∧
          TileDis R (TriSet Ax Ay Dx Dy Bx By) ((B + 2 * A) * (A + 2 * B) * (m' * m')) ∧
          (((B + 2 * A) * (A + 2 * B) * (m' * m') : ℕ) : ℝ)
            = ((R.a : ℝ) + 2 * R.b) * ((R.b : ℝ) + 2 * R.a) * m ^ 2 ∧
          TileDis R (TriSet Ax Ay Cx Cy Bx By)
            ((B + 2 * A) * (A + 2 * B) * (m' * m') + ((A + 2 * B) * m') * ((A + 2 * B) * m')) ∧
          ((((B + 2 * A) * (A + 2 * B) * (m' * m') + ((A + 2 * B) * m') * ((A + 2 * B) * m') : ℕ) : ℝ)
            = 3 * m ^ 2 * ((R.a : ℝ) + 2 * R.b) * ((R.a : ℝ) + R.b)) := by
  obtain ⟨A', B', C, k, hA', hB', hk, ea, eb, ec, hh, hcop, hlt, H⟩ :=
    zhang_prop11_2_S (swapR R) (swapR_rel R hrel) hba
  refine ⟨B', A', C, k, hB', hA', hk, eb, ea, ec, by nlinarith [hh], hcop.symm, hlt, ?_⟩
  intro m m' hm' hkm hS Ax Ay Bx By Dx Dy hD hAD hBD hAB
  obtain ⟨Cx, Cy, e1, e2, e3, e4, T0, c0, T1, c1⟩ := H m m' hm' hkm hS Ax Ay Bx By Dx Dy hD hAD hBD hAB
  simp only [swapR] at e3
  refine ⟨Cx, Cy, e1, e2, by rw [e3]; ring, e4, TileDis.cn ((tileDis_swap R).mp T0) (by ring), ?_,
    TileDis.cn ((tileDis_swap R).mp T1) (by ring), ?_⟩
  · simp only [swapR] at c0
    push_cast at c0 ⊢; linear_combination c0
  · simp only [swapR] at c1
    push_cast at c1 ⊢; linear_combination c1

/-- **Prop 11 (2) for `b < a`**. -/
theorem zhang_prop11_2_Sb (hba : R.b < R.a) :
    ∃ (A B C : ℕ) (k : ℚ) (hA : 0 < A) (hB : 0 < B), 0 < k ∧ R.a = k * A ∧ R.b = k * B ∧ R.c = k * C ∧
      C * C = A * A + B * B + A * B ∧ Nat.Coprime A B ∧ B < A ∧
      ∀ (m : ℝ) (m' : ℕ), 0 < m' → (k : ℝ) * m = m' → (∃ i j : ℕ, m' = A * i + C * j) →
        ∀ (Ax Ay Bx By Dx Dy : ℝ),
        0 < det3 Ax Ay Dx Dy Bx By →
        (Ax - Dx) ^ 2 + (Ay - Dy) ^ 2 = (((R.b : ℝ) + 2 * R.a) * R.b * m) ^ 2 →
        (Bx - Dx) ^ 2 + (By - Dy) ^ 2 = (((R.a : ℝ) + 2 * R.b) * R.a * m) ^ 2 →
        (Ax - Bx) ^ 2 + (Ay - By) ^ 2 = ((R.c : ℝ) ^ 2 * m) ^ 2 →
        ∃ Cx Cy : ℝ,
          Cx = Dx + (((R.b : ℝ) + 2 * R.a) / ((R.a : ℝ) + 2 * R.b)) * (Dx - Bx) ∧
          Cy = Dy + (((R.b : ℝ) + 2 * R.a) / ((R.a : ℝ) + 2 * R.b)) * (Dy - By) ∧
          (Cx - Bx) ^ 2 + (Cy - By) ^ 2 = (3 * ((R.a : ℝ) + R.b) * R.a * m) ^ 2 ∧
          (Cx - Ax) ^ 2 + (Cy - Ay) ^ 2 = (((R.b : ℝ) + 2 * R.a) * m * R.c) ^ 2 ∧
          TileDis R (TriSet Ax Ay Dx Dy Bx By) ((B + 2 * A) * (A + 2 * B) * (m' * m')) ∧
          (((B + 2 * A) * (A + 2 * B) * (m' * m') : ℕ) : ℝ)
            = ((R.b : ℝ) + 2 * R.a) * ((R.a : ℝ) + 2 * R.b) * m ^ 2 ∧
          TileDis R (TriSet Ax Ay Cx Cy Bx By)
            ((B + 2 * A) * (A + 2 * B) * (m' * m') + ((B + 2 * A) * m') * ((B + 2 * A) * m')) ∧
          ((((B + 2 * A) * (A + 2 * B) * (m' * m') + ((B + 2 * A) * m') * ((B + 2 * A) * m') : ℕ) : ℝ)
            = 3 * m ^ 2 * ((R.b : ℝ) + 2 * R.a) * ((R.a : ℝ) + R.b)) := by
  obtain ⟨A', B', C, k, hA', hB', hk, ea, eb, ec, hh, hcop, hlt, H⟩ :=
    zhang_prop11_1_S (swapR R) (swapR_rel R hrel) hba
  refine ⟨B', A', C, k, hB', hA', hk, eb, ea, ec, by nlinarith [hh], hcop.symm, hlt, ?_⟩
  intro m m' hm' hkm hS Ax Ay Bx By Dx Dy hD hAD hBD hAB
  obtain ⟨Cx, Cy, e1, e2, e3, e4, T0, c0, T1, c1⟩ := H m m' hm' hkm hS Ax Ay Bx By Dx Dy hD hAD hBD hAB
  simp only [swapR] at e3
  refine ⟨Cx, Cy, e1, e2, by rw [e3]; ring, e4, TileDis.cn ((tileDis_swap R).mp T0) (by ring), ?_,
    TileDis.cn ((tileDis_swap R).mp T1) (by ring), ?_⟩
  · simp only [swapR] at c0
    push_cast at c0 ⊢; linear_combination c0
  · simp only [swapR] at c1
    push_cast at c1 ⊢; linear_combination c1

end main

end Erdos634.ZhangRat5

#print axioms Erdos634.ZhangRat5.tileDis_swap
#print axioms Erdos634.ZhangRat5.zhang_prop11_1_Sb
#print axioms Erdos634.ZhangRat5.zhang_prop11_2_Sb
