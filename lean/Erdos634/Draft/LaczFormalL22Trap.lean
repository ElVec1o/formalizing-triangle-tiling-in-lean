import Erdos634.Draft.LaczFormalL22Chart

/-!
# Laczkovich Lemma 2.2 (ii), first case: the trapezoid with angles `β, α+β` and a long top side

NOTE, UNAUDITED.  Credit: Laczkovich (Discrete Math. 140 (1995) 79-94, Lemma 2.2 (ii), Fig. 1), Beeson,
Beeson-Zhang, Zhang.

Chart form.  `Δ` is a rational triangle with sides `a, b, c` opposite its vertices `0, 1, 2` (angles `α, β, γ`).  A chart
`(A, w, d)` has Gram data `|w| = W`, `|d| = D` (rational), `⟨w,d⟩ = W D cos β`.  The trapezoid `ABCD` of the paper
(`A, B = A+w`, `D = A + d`, `C = A + τ w + d`, angle `β` at `A`, `α+β` at `B`) is the chart set
`trapSet τ = {0 ≤ t ≤ 1, 0 ≤ s ≤ 1 + (τ-1) t}`, where the angle `α+β` at `B` forces
`τ = 1 + D (b² - c²) / (W a c)` (`trap_tau`).  First case of the proof (`DC/BC > sin β / sin α`, i.e. `D c < W a`):
`trapSet τ = ` parallelogram `AFED` (chart rectangle, Lemma 2.2 (i)) `∪` triangle `FBE` `∪` triangle `EBC`,
the two triangles being `Δ`-similar by the rational identities of `trap_alg1`.
-/

namespace Erdos634.LaczL22

open Erdos634.Geometry Erdos634.CertCoord Erdos634.LaczL21 Erdos634.Realizable

/-- `cos β` from the sides (the angle of `Δ` at vertex `1`). -/
def RTri.cos1 (R : RTri) : ℚ := (R.a ^ 2 + R.c ^ 2 - R.b ^ 2) / (2 * R.a * R.c)

theorem RTri.rot_cos0 (R : RTri) : R.rot.cos0 = R.cos1 := by
  simp only [RTri.cos0, RTri.rot, RTri.cos1]
  ring

/-- The chart trapezoid `0 ≤ t ≤ 1`, `0 ≤ s ≤ 1 + (τ-1) t`. -/
def trapSet (τ : ℝ) : Set Plane :=
  {z | 0 ≤ z 1 ∧ z 1 ≤ 1 ∧ 0 ≤ z 0 ∧ z 0 ≤ 1 + (τ - 1) * z 1}

theorem convex_trapSet (τ : ℝ) : Convex ℝ (trapSet τ) := by
  intro x hx y hy a b ha hb hab
  obtain ⟨hx1, hx2, hx3, hx4⟩ := hx
  obtain ⟨hy1, hy2, hy3, hy4⟩ := hy
  simp only [trapSet, Set.mem_setOf_eq, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  obtain rfl : b = 1 - a := by linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · nlinarith [mul_nonneg ha hx1, mul_nonneg hb hy1]
  · nlinarith [mul_nonneg ha (sub_nonneg.2 hx2), mul_nonneg hb (sub_nonneg.2 hy2)]
  · nlinarith [mul_nonneg ha hx3, mul_nonneg hb hy3]
  · nlinarith [mul_nonneg ha (sub_nonneg.2 hx4), mul_nonneg hb (sub_nonneg.2 hy4)]

theorem carrier_subset_trap {T : Tri} {τ : ℝ} (h : ∀ k, T.pts k ∈ trapSet τ) :
    T.carrier ⊆ trapSet τ :=
  convexHull_min (Set.range_subset_iff.mpr h) (convex_trapSet τ)

/-! ## The three pieces, real parameters -/

/-- `F B E` of the paper: chart vertices `(F,0), (1,0), (F,1)`. -/
noncomputable def triFBE (F : ℝ) (hF : F < 1) : Tri :=
  mkTri F 0 1 0 F 1 (by simp only [det3]; nlinarith)

/-- `E B C` of the paper: chart vertices `(F,1), (1,0), (F+E,1)`. -/
noncomputable def triEBC (F E : ℝ) (hE : 0 < E) : Tri :=
  mkTri F 1 1 0 (F + E) 1 (by simp only [det3]; nlinarith)

theorem triFBE_pts (F : ℝ) (hF : F < 1) :
    (triFBE F hF).pts 0 = mkPt F 0 ∧ (triFBE F hF).pts 1 = mkPt 1 0 ∧ (triFBE F hF).pts 2 = mkPt F 1 :=
  ⟨rfl, rfl, rfl⟩

theorem triEBC_pts (F E : ℝ) (hE : 0 < E) :
    (triEBC F E hE).pts 0 = mkPt F 1 ∧ (triEBC F E hE).pts 1 = mkPt 1 0 ∧
      (triEBC F E hE).pts 2 = mkPt (F + E) 1 :=
  ⟨rfl, rfl, rfl⟩

private theorem htri3 : ∀ k : Fin 3, k = 0 ∨ k = 1 ∨ k = 2 := by decide

/-- Cover: the chart trapezoid is the union of the three pieces. -/
theorem trap_cover (F E : ℝ) (hF0 : 0 < F) (hF1 : F < 1) (hE : 0 < E) :
    trapSet (F + E) = (rectSet 0 F 0 1 ∪ (triFBE F hF1).carrier) ∪ (triEBC F E hE).carrier := by
  ext z
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    by_cases hs : z 0 ≤ F
    · left; left; exact ⟨h3, hs, h1, h2⟩
    · push_neg at hs
      by_cases hh : z 0 + (1 - F) * z 1 - 1 ≤ 0
      · left; right
        -- weights (1 - α - β, α, β), α = (s - F)/(1 - F), β = t
        have hF' : 0 < 1 - F := by linarith
        refine Erdos634.CertGeom.mem_carrier_of_combo _ z
          ![1 - (z 0 - F) / (1 - F) - z 1, (z 0 - F) / (1 - F), z 1] ?_ ?_ ?_
        · show (1 - (z 0 - F) / (1 - F) - z 1) + (z 0 - F) / (1 - F) + z 1 = 1
          ring
        · intro k
          rcases htri3 k with rfl | rfl | rfl
          · show 0 ≤ 1 - (z 0 - F) / (1 - F) - z 1
            have : (z 0 - F) / (1 - F) ≤ 1 - z 1 := by
              rw [div_le_iff₀ hF']; nlinarith
            linarith
          · show 0 ≤ (z 0 - F) / (1 - F)
            exact div_nonneg (by linarith) hF'.le
          · exact h1
        · obtain ⟨p0, p1, p2⟩ := triFBE_pts F hF1
          show z = _ • (triFBE F hF1).pts 0 + _ • (triFBE F hF1).pts 1 + _ • (triFBE F hF1).pts 2
          rw [p0, p1, p2]
          have hF'' : (1 - F) ≠ 0 := hF'.ne'
          ext i
          fin_cases i <;> simp [mkPt] <;> field_simp <;> ring
      · push_neg at hh
        right
        have hE' : 0 < E := hE
        refine Erdos634.CertGeom.mem_carrier_of_combo _ z
          ![z 1 - (z 0 + (1 - F) * z 1 - 1) / E, 1 - z 1, (z 0 + (1 - F) * z 1 - 1) / E] ?_ ?_ ?_
        · show (z 1 - (z 0 + (1 - F) * z 1 - 1) / E) + (1 - z 1) + (z 0 + (1 - F) * z 1 - 1) / E = 1
          ring
        · intro k
          rcases htri3 k with rfl | rfl | rfl
          · show 0 ≤ z 1 - (z 0 + (1 - F) * z 1 - 1) / E
            have : (z 0 + (1 - F) * z 1 - 1) / E ≤ z 1 := by
              rw [div_le_iff₀ hE']; nlinarith
            linarith
          · show 0 ≤ 1 - z 1
            linarith
          · show 0 ≤ (z 0 + (1 - F) * z 1 - 1) / E
            exact div_nonneg hh.le hE'.le
        · obtain ⟨p0, p1, p2⟩ := triEBC_pts F E hE
          show z = _ • (triEBC F E hE).pts 0 + _ • (triEBC F E hE).pts 1 + _ • (triEBC F E hE).pts 2
          rw [p0, p1, p2]
          have hE'' : E ≠ 0 := hE'.ne'
          ext i
          fin_cases i <;> simp [mkPt] <;> field_simp <;> ring
  · intro hz
    rcases hz with (hz | hz) | hz
    · obtain ⟨h1, h2, h3, h4⟩ := hz
      refine ⟨h3, h4, h1, ?_⟩
      nlinarith
    · refine carrier_subset_trap ?_ hz
      intro k
      obtain ⟨p0, p1, p2⟩ := triFBE_pts F hF1
      rcases htri3 k with rfl | rfl | rfl
      · rw [p0]; simp [trapSet]; constructor <;> nlinarith
      · rw [p1]; simp [trapSet]
      · rw [p2]; simp [trapSet]; constructor <;> nlinarith
    · refine carrier_subset_trap ?_ hz
      intro k
      obtain ⟨p0, p1, p2⟩ := triEBC_pts F E hE
      rcases htri3 k with rfl | rfl | rfl
      · rw [p0]; simp [trapSet]; constructor <;> nlinarith
      · rw [p1]; simp [trapSet]
      · rw [p2]; simp [trapSet]; first | (constructor <;> nlinarith) | nlinarith

/-- Pairwise disjointness of the pieces. -/
theorem trap_disj (F E : ℝ) (hF0 : 0 < F) (hF1 : F < 1) (hE : 0 < E) :
    Disjoint (interior (rectSet 0 F 0 1)) (interior (triFBE F hF1).carrier) ∧
      Disjoint (interior (rectSet 0 F 0 1 ∪ (triFBE F hF1).carrier))
        (interior (triEBC F E hE).carrier) := by
  obtain ⟨p0, p1, p2⟩ := triFBE_pts F hF1
  obtain ⟨q0, q1, q2⟩ := triEBC_pts F E hE
  have hx1 : ∀ z ∈ (triFBE F hF1).carrier, F ≤ z 0 := by
    refine ge_of_forall_pts_ge (coordFun 1 0 0) (c := F) ?_ |> fun h z hz => by simpa using h z hz
    intro k
    rcases htri3 k with rfl | rfl | rfl
    · rw [p0]; simp
    · rw [p1]; simp; linarith
    · rw [p2]; simp
  constructor
  · exact sepX F (fun z hz => hz.2.1) hx1
  · refine disjoint_interior_of_sep (coordFun 1 (1 - F) (-1))
      (coordFun_linear_ne_zero _ (Or.inl one_ne_zero)) 0 ?_ ?_
    · intro z hz
      rcases hz with hz | hz
      · obtain ⟨h1, h2, h3, h4⟩ := hz
        simp only [coordFun_apply]; nlinarith
      · refine Erdos634.CertGeom.le_of_forall_pts_le (coordFun 1 (1 - F) (-1)) ?_ z hz
        intro k
        rcases htri3 k with rfl | rfl | rfl
        · rw [p0]; simp; nlinarith
        · rw [p1]; simp
        · rw [p2]; simp
    · intro z hz
      refine ge_of_forall_pts_ge (coordFun 1 (1 - F) (-1)) ?_ z hz
      intro k
      rcases htri3 k with rfl | rfl | rfl
      · rw [q0]; simp
      · rw [q1]; simp
      · rw [q2]; simp; nlinarith


/-! ## Rational parameters of the first case -/

def tF (a c W Dd : ℚ) : ℚ := 1 - Dd * c / (a * W)
def tE (a b c W Dd : ℚ) : ℚ := Dd * b ^ 2 / (W * a * c)
def tTau (a b c W Dd : ℚ) : ℚ := 1 + Dd * (b ^ 2 - c ^ 2) / (W * a * c)
def tK1 (a Dd : ℚ) : ℚ := Dd / a
def tK2 (a b c Dd : ℚ) : ℚ := Dd * b / (a * c)
def tG (a b c W Dd : ℚ) : ℚ := W * Dd * ((a ^ 2 + c ^ 2 - b ^ 2) / (2 * a * c))

theorem trap_alg1 (a b c W Dd : ℚ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hW : 0 < W) (hD : 0 < Dd) :
    tTau a b c W Dd = tF a c W Dd + tE a b c W Dd ∧
    (1 - tF a c W Dd) ^ 2 * W ^ 2 = tK1 a Dd ^ 2 * c ^ 2 ∧
    (1 - tF a c W Dd) ^ 2 * W ^ 2 - 2 * (1 - tF a c W Dd) * tG a b c W Dd + Dd ^ 2
      = tK1 a Dd ^ 2 * b ^ 2 ∧
    Dd ^ 2 = tK1 a Dd ^ 2 * a ^ 2 ∧
    (1 - tF a c W Dd) ^ 2 * W ^ 2 - 2 * (1 - tF a c W Dd) * tG a b c W Dd + Dd ^ 2
      = tK2 a b c Dd ^ 2 * c ^ 2 ∧
    (tTau a b c W Dd - 1) ^ 2 * W ^ 2 + 2 * (tTau a b c W Dd - 1) * tG a b c W Dd + Dd ^ 2
      = tK2 a b c Dd ^ 2 * a ^ 2 ∧
    (tTau a b c W Dd - tF a c W Dd) ^ 2 * W ^ 2 = tK2 a b c Dd ^ 2 * b ^ 2 := by
  have ha' := ha.ne'; have hb' := hb.ne'; have hc' := hc.ne'; have hW' := hW.ne'; have hD' := hD.ne'
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [tF, tE, tTau, tK1, tK2, tG] <;> field_simp <;> ring

end Erdos634.LaczL22
