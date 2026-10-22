-- Draft/LaczFormalCondEConj.lean -- Condition (E) at the CONJUGATE angles (interior-vertex analogue of KConj.lemmaK).
-- Laczkovich (arXiv 2002.12013, Lemma 9 / Condition (K)) states the conjugate vertex equation (2) for the vertices of R_N.  For a triangle target and an
-- INTERIOR (non-corner) vertex P of the dissection, the same conjugation argument gives: with x'(k) the conjugate angle vector of the tile, the tile
-- corners at P satisfy  sum_l cnt_P(l) x'(k)_l  in {1, 2}.  Proof: the conjugated tiles form a genuine dissection E of the conjugated target
-- (`phiDissection`, as in `lemmaK`), whose tiles have angles pi x'(m)_l and whose incidences are those of D; apply the vertex-sum lemma to E at P.
-- UNAUDITED.  Credit: Laczkovich (conjugate tilings; Lemma 9); the extension to interior vertices is ours.
import Erdos634.Draft.LaczFormalCondE2

open Complex
open scoped BigOperators Classical

namespace Erdos634.KConj

open Erdos634.Geometry Erdos634.Geometry.CaseA.LemmaV Erdos634.Geometry.CaseA.LemmaK1
  Erdos634.LemmaKStar Erdos634.DissectionMap Erdos634.CertCoord

variable {N : ℕ}

/-- Vertex sum at a non-corner point, for any dissection: the tile corners at `P` sum to `π` or `2π`. -/
theorem diss_vertex_nc (E : Dissection N) (P : Plane) (hP : ∃ p : Fin N × Fin 3, (E.tile p.1).pts p.2 = P)
    (hnc : ∀ j, P ≠ E.target.pts j) :
    ∑ i, vc (E.tile i) P = Real.pi ∨ ∑ i, vc (E.tile i) P = 2 * Real.pi := by
  have hpi := Real.pi_pos
  have hpos : ∀ T : Tri, ∀ v, 0 < T.angleAt v := fun T v => Erdos634.MarchFlank.cornerAngle_pos T v
  have hloc : ∀ i, ∃ a : ℕ, (E.tile i).localAngle P = vc (E.tile i) P + a * Real.pi := by
    intro i
    by_cases hv : ∃ v, (E.tile i).pts v = P
    · obtain ⟨v, hv⟩ := hv
      refine ⟨0, ?_⟩
      rw [← hv, vc_of_vertex]; simp
    · push Not at hv
      have hv' : ∀ v, P ≠ (E.tile i).pts v := fun v h => hv v h.symm
      rw [vc_of_nonvertex _ _ hv']
      rcases Erdos634.PinPlumbing.localAngle_cases (E.tile i) P with ⟨j, hj, -⟩ | h2 | h1 | h0
      · exact absurd hj (hv' j)
      · exact ⟨2, by rw [h2]; push_cast; ring⟩
      · exact ⟨1, by rw [h1]; push_cast; ring⟩
      · exact ⟨0, by rw [h0]; simp⟩
  choose a hloc using hloc
  set A : ℕ := ∑ i, a i with hA
  set S : ℝ := ∑ i, vc (E.tile i) P with hS
  have hsum : ∑ i, (E.tile i).localAngle P = S + A * Real.pi := by
    rw [hS, hA]
    push_cast
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => hloc i)
  have hnn : ∀ i, 0 ≤ vc (E.tile i) P := by
    intro i; unfold vc
    exact Finset.sum_nonneg (fun v _ => by
      split_ifs
      · exact (hpos _ v).le
      · exact le_refl _)
  obtain ⟨p0, hp0⟩ := hP
  have hSpos : 0 < S := by
    have h1 : 0 < vc (E.tile p0.1) P := by
      unfold vc
      have := Finset.single_le_sum (f := fun v => if (E.tile p0.1).pts v = P then (E.tile p0.1).angleAt v else 0)
        (fun v _ => by
          dsimp only
          split_ifs
          · exact (hpos _ v).le
          · exact le_refl _) (Finset.mem_univ p0.2)
      refine lt_of_lt_of_le ?_ this
      beta_reduce
      rw [if_pos hp0]
      exact hpos _ _
    exact lt_of_lt_of_le h1 (Finset.single_le_sum (f := fun i => vc (E.tile i) P) (fun i _ => hnn i)
      (Finset.mem_univ p0.1))
  have htot := E.sum_localAngle_eq P
  rw [hsum] at htot
  have hAnn : (0 : ℝ) ≤ A := by positivity
  rcases Erdos634.PinPlumbing.localAngle_cases E.target P with ⟨j, hj, -⟩ | h2 | h1 | h0
  · exact absurd hj (hnc j)
  · rw [h2] at htot
    have : A = 0 ∨ A = 1 ∨ 2 ≤ A := by omega
    rcases this with h | h | h
    · right; rw [h] at htot; simp at htot; linarith
    · left; rw [h] at htot; simp at htot; linarith
    · exfalso
      have : (2 : ℝ) ≤ A := by exact_mod_cast h
      nlinarith
  · rw [h1] at htot
    have : A = 0 ∨ 1 ≤ A := by omega
    rcases this with h | h
    · left; rw [h] at htot; simp at htot; linarith
    · exfalso
      have : (1 : ℝ) ≤ A := by exact_mod_cast h
      nlinarith
  · rw [h0] at htot
    exfalso
    nlinarith

/-- `xp` depends on `k` only mod `n` and up to sign (the vector part of `K2_congr`). -/
theorem xp_congr {n : ℕ} (hn : 0 < n) {a : Fin 3 → ℕ} (hsum : ∑ i, a i = n) (ha1 : ∀ i, 1 ≤ a i)
    {k m : ℤ} (hk : Int.gcd k n = 1) (h : (n : ℤ) ∣ m - k ∨ (n : ℤ) ∣ m + k) (i : Fin 3) :
    xp n a m i = xp n a k i := by
  rcases h with h | h
  · have hy : ∀ l, yv n a m l = yv n a k l := fun l => yv_congr h hn l
    have hs : sT n a m = sT n a k := by unfold sT; simp only [hy]
    unfold xp; rw [hs, hy]
  · have h' : (n : ℤ) ∣ m - (-k) := by simpa using h
    have hy : ∀ l, yv n a m l = 1 - yv n a k l := fun l => by
      rw [yv_congr h' hn l, yv_neg hsum ha1 hk]
    have hs : sT n a m = 3 - sT n a k := by
      unfold sT; simp only [hy, Fin.sum_univ_three]; ring
    rcases sT_12 hsum ha1 hk with h1 | h1
    · have hm : sT n a m ≠ 1 := by rw [hs, h1]; norm_num
      unfold xp; rw [if_neg hm, if_pos h1, hy]; ring
    · have hm : sT n a m = 1 := by rw [hs, h1]; norm_num
      have hk1 : sT n a k ≠ 1 := by rw [h1]; norm_num
      unfold xp; rw [if_pos hm, if_neg hk1, hy]

/-- **Interior-vertex Lemma K.**  For a real congruent dissection with rational model angles `a_i π/n`, every unit `k` and every non-corner vertex `P`, the
corner counts `cnt P` satisfy `∑_l cnt_P(l) · x'(k)_l ∈ {1, 2}` (the conjugate of "tile angles at `P` sum to `π` or `2π`"). -/
theorem conj_interior_sum (D : CongruentDissection N) {n : ℕ} (hn : 0 < n) (a : Fin 3 → ℕ)
    (ha : ∀ k, D.model.angleAt k = a k * Real.pi / n) (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i v, (D.tile i).angleAt v = a (idx i v) * Real.pi / n) {k : ℤ} (hk : Int.gcd k n = 1)
    (P : Plane) (hP : ∃ p : Fin N × Fin 3, (D.tile p.1).pts p.2 = P) (hnc : ∀ j, P ≠ D.target.pts j) :
    ∑ l, (Erdos634.Draft.LaczFormal.cnt D idx P l : ℚ) * xp n a k l = 1 ∨
    ∑ l, (Erdos634.Draft.LaczFormal.cnt D idx P l : ℚ) * xp n a k l = 2 := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have sum_of : ∀ (T : Tri) (b : Fin 3 → ℕ), (∀ i, T.angleAt i = b i * Real.pi / n) →
      ∑ i, b i = n := by
    intro T b hb
    have hs := T.angleAt_sum
    rw [hb 0, hb 1, hb 2] at hs
    have hnn : (n : ℝ) * (Real.pi / n) = Real.pi := by field_simp
    have key : (((b 0 + b 1 + b 2 : ℕ) : ℝ) - n) * (Real.pi / n) = 0 := by
      push_cast; linear_combination hs - hnn
    have := sub_eq_zero.mp ((mul_eq_zero.mp key).resolve_right (div_ne_zero Real.pi_ne_zero hn'))
    rw [Fin.sum_univ_three]; exact_mod_cast this
  have hsum := sum_of _ a ha
  have ha1 : ∀ i, 1 ≤ a i := fun i => (nat_bounds hn (ha i) (angle_pos _ i) (angle_lt_pi _ i)).1
  obtain ⟨m, hmc, hm4, hmk⟩ := exists_m hn hk
  obtain ⟨σ, hσ⟩ := exists_sigma hn hmc
  have hmg : Int.gcd (m : ℤ) n = 1 := by
    rw [Int.gcd_natCast_natCast]; exact Nat.Coprime.coprime_mul_left_right hmc
  set Dn' := Dn D
  set E := phiDissection hn σ hσ hm4 Dn' (Dn_hK D hn a ha) (Dn_hKT D hn a ha) (PN D) (Dn_hP D)
    (Dn_hPT D)
  have hy : ∀ l, yf n m (a l) = ((yv n a m l : ℚ) : ℝ) := fun l => rfl
  have hyp : ∀ l, 0 < yv n a m l :=  fun l =>
    lt_of_le_of_ne (Int.fract_nonneg _) (Ne.symm (yv_ne hsum ha1 hmg l))
  have hyl : ∀ l, yv n a m l < 1 := fun l => Int.fract_lt_one _
  have hs12 : sT n a m = 1 ∨ sT n a m = 2 := sT_12 hsum ha1 hmg
  have tile_ang : ∀ i v, (E.tile i).angleAt v = Real.pi * ((xp n a m (idx i v) : ℚ) : ℝ) := by
    intro i
    have hang : ∀ v, (E.tile i).angleAt v = Real.pi * yf n m (a (idx i v)) ∨
        (E.tile i).angleAt v = Real.pi * (1 - yf n m (a (idx i v))) := by
      intro v
      refine phi_angle hn σ hσ hm4 (Dn'.tile i) (Dn_hK D hn a ha i) v (a (idx i v)) ?_ ?_
      · rw [show Dn'.tile i = mapTri (eN D) (D.tile i) from rfl, angleAt_eN]; exact hidx i v
      · rw [hy]; exact_mod_cast hyp _
    have hsumβ := (E.tile i).angleAt_sum
    set y : Fin 3 → ℝ := fun v => ((yv n a m (idx i v) : ℚ) : ℝ)
    set β : Fin 3 → ℝ := fun v => (E.tile i).angleAt v / Real.pi
    have hpi := Real.pi_pos
    have hsy : y 0 + y 1 + y 2 = ((sT n a m : ℚ) : ℝ) := by
      have : ∑ v, y v = ∑ l, ((yv n a m l : ℚ) : ℝ) :=
        Equiv.sum_comp (idx i) (fun l => ((yv n a m l : ℚ) : ℝ))
      rw [Fin.sum_univ_three, Fin.sum_univ_three] at this
      rw [this, sT, Fin.sum_univ_three]; push_cast; ring
    have hF := forced y β
      (fun v => by show (0 : ℝ) < ((yv n a m (idx i v) : ℚ) : ℝ); exact_mod_cast hyp _)
      (fun v => by show ((yv n a m (idx i v) : ℚ) : ℝ) < 1; exact_mod_cast hyl _)
      (fun v => by
        rcases hang v with h | h
        · left; simp only [β, y, h, ← hy]; field_simp
        · right; simp only [β, y, h, ← hy]; field_simp)
      (by simp only [β]; field_simp; linarith) hsy
      (by rcases hs12 with h | h <;> [left; right] <;> rw [h] <;> norm_num)
    intro v
    have := hF v
    simp only [β] at this
    rw [div_eq_iff hpi.ne'] at this
    rw [this, xp]
    split_ifs with h1 h2 h2
    · simp [y]; ring
    · exact absurd (by exact_mod_cast h1) h2
    · exact absurd (by rw [h2]; norm_num) h1
    · push_cast; simp [y]; ring
  -- incidences
  have hpred : ∀ i v i' w, ((E.tile i).pts v = (E.tile i').pts w) ↔ ((D.tile i).pts v = (D.tile i').pts w) := by
    intro i v i' w
    rw [show E.tile i = phiTri hn σ hσ hm4 (Dn'.tile i) (Dn_hK D hn a ha i) from rfl,
      show E.tile i' = phiTri hn σ hσ hm4 (Dn'.tile i') (Dn_hK D hn a ha i') from rfl, phi_pts_eq,
      Dn_tile_pts, Dn_tile_pts, eN_inj]
  have hpredT : ∀ i v j, ((E.tile i).pts v = E.target.pts j) ↔ ((D.tile i).pts v = D.target.pts j) := by
    intro i v j
    rw [show E.tile i = phiTri hn σ hσ hm4 (Dn'.tile i) (Dn_hK D hn a ha i) from rfl,
      show E.target = phiTri hn σ hσ hm4 Dn'.target (Dn_hKT D hn a ha) from rfl, phi_pts_eq,
      Dn_tile_pts, Dn_target_pts, eN_inj]
  obtain ⟨p0, hp0⟩ := hP
  set P' := (E.tile p0.1).pts p0.2 with hP'
  have hPE : ∀ i v, ((E.tile i).pts v = P') ↔ ((D.tile i).pts v = P) := by
    intro i v
    rw [hP', hpred, hp0]
  have hnc' : ∀ j, P' ≠ E.target.pts j := by
    intro j h
    apply hnc j
    rw [← hp0]; exact (hpredT p0.1 p0.2 j).mp h
  have hvE := diss_vertex_nc E P' ⟨p0, rfl⟩ hnc'
  simp only [vc] at hvE
  have e : ∀ i v, (if (E.tile i).pts v = P' then (E.tile i).angleAt v else 0)
      = (if (D.tile i).pts v = P then
          (fun l => Real.pi * ((xp n a m l : ℚ) : ℝ)) (idx i v) else 0) := by
    intro i v
    by_cases hp : (D.tile i).pts v = P
    · rw [if_pos ((hPE i v).mpr hp), if_pos hp, tile_ang]
    · rw [if_neg (fun h => hp ((hPE i v).mp h)), if_neg hp]
  simp only [e] at hvE
  have hfs := Erdos634.Draft.LaczFormal.fiber_sum_P D idx P (fun l => Real.pi * ((xp n a m l : ℚ) : ℝ))
  beta_reduce at hfs
  rw [hfs] at hvE
  have hpi := Real.pi_pos
  have hX : ∑ l, (Erdos634.Draft.LaczFormal.cnt D idx P l : ℝ) * ((xp n a m l : ℚ) : ℝ)
      = ((∑ l, (Erdos634.Draft.LaczFormal.cnt D idx P l : ℚ) * xp n a m l : ℚ) : ℝ) := by
    push_cast; rfl
  have hcg : ∀ l, xp n a m l = xp n a k l := fun l => xp_congr hn hsum ha1 hk hmk l
  have hqk : ∑ l, (Erdos634.Draft.LaczFormal.cnt D idx P l : ℚ) * xp n a k l
      = ∑ l, (Erdos634.Draft.LaczFormal.cnt D idx P l : ℚ) * xp n a m l := by
    refine Finset.sum_congr rfl (fun l _ => by rw [hcg])
  rw [hqk]
  have hmul : ∀ l, Real.pi * ((xp n a m l : ℚ) : ℝ) * 1 = Real.pi * ((xp n a m l : ℚ) : ℝ) := fun l => mul_one _
  have hL : ∑ l, (Erdos634.Draft.LaczFormal.cnt D idx P l : ℝ) * (Real.pi * ((xp n a m l : ℚ) : ℝ))
      = Real.pi * ∑ l, (Erdos634.Draft.LaczFormal.cnt D idx P l : ℝ) * ((xp n a m l : ℚ) : ℝ) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun l _ => by ring)
  rw [hL, hX] at hvE
  rcases hvE with h | h
  · left
    have : ((∑ l, (Erdos634.Draft.LaczFormal.cnt D idx P l : ℚ) * xp n a m l : ℚ) : ℝ) = 1 := by
      apply mul_left_cancel₀ hpi.ne'; linarith
    exact_mod_cast this
  · right
    have : ((∑ l, (Erdos634.Draft.LaczFormal.cnt D idx P l : ℚ) * xp n a m l : ℚ) : ℝ) = 2 := by
      apply mul_left_cancel₀ hpi.ne'; linarith
    exact_mod_cast this

end Erdos634.KConj
