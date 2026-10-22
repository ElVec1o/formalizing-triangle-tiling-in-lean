-- Draft/RMinus4Full.lean — **S2 (R-4): target (2α, α, 2β) forces N = 2**, a contradiction with
-- N prime and N > 3.
--
-- Strategy: relabel D so that target vertices 0,1,2 carry 2α, α, 2β (using `relabelTarget'`);
-- apply `Row15.setup` to get the area equation `N·h(s)² = S²·g(s)` with s ∈ ℚ; identify
-- s = r; clear denominators to get an integer equation; apply `chain_unconditional` → N = 2.
--
-- Formalization of paper row R-4 (Table 5); this is direct /goal progress (prime exclusion).
import Erdos634.Draft.FluxFRow15Setup
import Erdos634.FCStep2
import Erdos634.Draft.FluxFRow14AnyLabel
import Erdos634.Draft.TheoremPConditional

open scoped Classical

namespace Erdos634.Geometry

open Row14AnyLabel Erdos634.Draft.TheoremPConditional

set_option maxHeartbeats 800000 in
theorem rMinus4 : RMinus4Statement := by
  unfold RMinus4Statement
  intro N D hNp hNmod h3N α β a b c r hirr hrel hmod ha hb htgt
  -- Step 1: unpack TgtAngles to get the permutation σ placing 2α, α, 2β at 0, 1, 2
  obtain ⟨σ, hσ0, hσ1, hσ2⟩ := htgt
  -- Step 2: relabel target by σ so that target vertex k carries angle σ k
  set D' := D.relabelTarget' σ with hD'def
  have hT : ∀ k, D'.target.pts k = D.target.pts (σ k) := fun k => rfl
  -- Step 3: angle transfers via angleAt_of_pts
  have hP0 : D'.target.angleAt 0 = 2 * α := by
    rw [angleAt_of_pts σ hT 0, hσ0]
  have hP1 : D'.target.angleAt 1 = α := by
    rw [angleAt_of_pts σ hT 1, hσ1]
  have hP2 : D'.target.angleAt 2 = 2 * β := by
    rw [angleAt_of_pts σ hT 2, hσ2]
  -- Step 4: D'.model = D.model (rfl), so ThreeAlphaData transfers
  have hmod' : D'.model.ThreeAlphaData α β a b c := hmod
  -- Step 5: apply Row15.setup
  obtain ⟨s, S, hs0, hs1, hcpos, ha', _hb', _hX, _hZ, hSc, harea⟩ :=
    Row15.setup D' hirr hrel hmod' hP0 hP1 hP2
  -- Step 6: s = (r : ℝ)  (from ha' : a = s*c and ha : a = r*c and 0 < c)
  have hsr : s = (r : ℝ) := by
    have : s * c = (r : ℝ) * c := ha'.symm.trans ha
    exact mul_right_cancel₀ hcpos.ne' this
  -- Step 7: write r in lowest terms
  -- r.num and r.den are coprime natural/int
  -- Get positivity of r
  have hr_pos : 0 < (r : ℝ) := hsr ▸ hs0
  have hr_lt1 : (r : ℝ) < 1 := hsr ▸ hs1
  -- r.num > 0
  have hrnum_pos : 0 < r.num := Rat.num_pos.mpr (by exact_mod_cast hr_pos)
  -- r.den > 0
  have hrden_pos : (0 : ℤ) < r.den := by exact_mod_cast r.pos
  -- r.num < r.den: from (r:ℝ) < 1 and r = r.num / r.den
  have hrnum_lt_den : r.num < r.den := by
    have hd : (0 : ℝ) < r.den := by exact_mod_cast r.pos
    have hrcast : (r : ℝ) = (r.num : ℝ) / (r.den : ℝ) := by
      rw [Rat.cast_def]
    rw [hrcast, div_lt_one hd] at hr_lt1
    exact_mod_cast hr_lt1
  -- Coprimality: Rat.isCoprime_num_den gives IsCoprime r.num (r.den : ℤ)
  have hcop : IsCoprime r.num (r.den : ℤ) := Rat.isCoprime_num_den r
  -- Step 8: rewrite harea in terms of r
  -- harea : (N:ℝ) * ((1 - s) * (2 + s))^2 = (S:ℝ)^2 * ((2 - s^2) * (3 - s^2))
  -- substitute s = (r:ℝ)
  rw [hsr] at harea
  -- Step 9: lift to ℤ
  -- Set p = r.num (ℤ), q = r.den cast to ℤ
  set p : ℤ := r.num with hp_def
  set q : ℤ := (r.den : ℤ) with hq_def
  have hq_pos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hrden_pos
  have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hrnum_pos
  have hrpq : (r : ℝ) = (p : ℝ) / (q : ℝ) := by
    simp [Rat.cast_def, hp_def, hq_def]
  -- Multiply harea by q^4 and rearrange
  -- LHS * q^4: N * ((1 - p/q)*(2 + p/q))^2 * q^4 = N * ((q-p)*(2q+p))^2
  -- RHS * q^4: S^2 * (2 - (p/q)^2) * (3 - (p/q)^2) * q^4 = S^2 * (2q^2 - p^2) * (3q^2 - p^2)
  have harea_int : (N : ℤ) * ((q - p) * (2 * q + p)) ^ 2 =
      S ^ 2 * (2 * q ^ 2 - p ^ 2) * (3 * q ^ 2 - p ^ 2) := by
    have hq4 : (q : ℝ) ^ 4 ≠ 0 := by positivity
    apply_fun (· * (q : ℝ) ^ 4) at harea
    have key : (N : ℝ) * ((q - p) * (2 * q + p)) ^ 2 =
        (S : ℝ) ^ 2 * (2 * q ^ 2 - p ^ 2) * (3 * q ^ 2 - p ^ 2) := by
      rw [hrpq] at harea
      field_simp at harea ⊢
      linarith
    exact_mod_cast key
  -- Step 10: apply chain_unconditional with e=p, f=q, R=(q-p)*(2q+p), M=S
  -- Need hM : S ≠ 0
  have hS_ne : S ≠ 0 := by
    intro hS0
    rw [hS0, Int.cast_zero, zero_mul] at hSc
    -- hSc : 0 = (1 - s) * (2 + s) * D'.target.oppLen 1
    -- (1-s) > 0, (2+s) > 0, oppLen > 0 → contradiction
    have h1s : 0 < 1 - s := by linarith
    have h2s : 0 < 2 + s := by linarith
    have hY : 0 < D'.target.oppLen 1 := D'.target.oppLen_pos 1
    have := mul_pos (mul_pos h1s h2s) hY
    linarith
  -- chain_unconditional needs (N:ℤ) * R^2 = M^2 * (2*f^2 - e^2) * (3*f^2 - e^2)
  -- where R = (q-p)*(2q+p), M = S, e = p, f = q
  have hchain : N = 2 :=
    FCStep2.chain_unconditional hcop hNp hrnum_pos hrnum_lt_den hS_ne harea_int
  -- Step 11: contradiction: N = 2 but N > 3
  omega

#print axioms rMinus4

end Erdos634.Geometry
