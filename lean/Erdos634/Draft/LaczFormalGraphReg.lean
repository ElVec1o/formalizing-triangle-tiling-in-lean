-- Draft/LaczFormalGraphReg.lean -- D0' (arithmetic): the tiling is REGULAR (equal numbers of alpha- and beta-corners at EVERY vertex) for the three
-- tiles with an equilateral target: (pi/12, 7pi/12, pi/3), (pi/30, 19pi/30, pi/3), (7pi/30, 13pi/30, pi/3).  This is the "mod 4 / mod 10" step of
-- Laczkovich (DCG 48 (2012), Thm 3.3 / Case IV, Sect. 3): at every vertex the vertex equation forces #alpha >= #beta (reduction mod 4 or mod 10 and the bound
-- on #beta), and `sum_P #alpha = sum_P #beta = N` then gives equality everywhere.  Reuses Condition (E) infrastructure (`vertSet`, `sum_cnt`, `vertex_group`).
-- UNAUDITED.  Credit: Laczkovich (2012 Thm 3.3 and Case IV of Thm 2.1; 2020 Condition (E)); Beeson-Rosu.
import Erdos634.Draft.LaczFormalCondE3

open scoped BigOperators Classical
open Erdos634.Geometry Erdos634.KConj Erdos634.TilePlacement Erdos634.Draft.TheoremPConditional

namespace Erdos634.Draft.LaczFormal

variable {N : ℕ}

/-- **Regularity from a one-sided vertex inequality.**  If every admissible vertex vector `c` (non-corner equation `∑ a_i c_i ∈ {n, 2n}` or corner
equation `∑ a_i c_i = u_j`) satisfies `c 1 ≤ c 0`, then `cnt` of type `σ 0` equals `cnt` of type `σ 1` at every vertex. -/
theorem regular_pair (D : CongruentDissection N) (n : ℕ) (hn : 0 < n) (a u : Fin 3 → ℕ) (σ σt : Equiv.Perm (Fin 3))
    (hm : ∀ i, D.model.angleAt (σ i) = a i * Real.pi / n)
    (ht : ∀ j, D.target.angleAt (σt j) = u j * Real.pi / n)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hidx : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v)
    (hge : ∀ c : Fin 3 → ℕ, (∑ i, a i * c i = n ∨ ∑ i, a i * c i = 2 * n ∨ ∃ j, ∑ i, a i * c i = u j) → c 1 ≤ c 0) :
    ∀ P ∈ vertSet D, cnt D idx P (σ 0) = cnt D idx P (σ 1) := by
  have hpi := Real.pi_pos
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set c : Plane → Fin 3 → ℕ := fun P i => cnt D idx P (σ i) with hc
  have hconv : ∀ P, ∑ l, (cnt D idx P l : ℝ) * D.model.angleAt l
      = ((∑ i, a i * c P i : ℕ) : ℝ) * Real.pi / n := by
    intro P
    rw [← Equiv.sum_comp σ (fun l => (cnt D idx P l : ℝ) * D.model.angleAt l)]
    push_cast
    rw [Finset.sum_mul, Finset.sum_div]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hm i]; simp only [hc]; ring
  have hcast : ∀ (X K : ℕ), (X : ℝ) * Real.pi / n = K * Real.pi → X = K * n := by
    intro X K h
    have : (X : ℝ) = K * n := by
      field_simp at h
      nlinarith
    exact_mod_cast this
  have hcast1 : ∀ (X : ℕ), (X : ℝ) * Real.pi / n = Real.pi → X = n := by
    intro X h
    have := hcast X 1 (by simpa using h); simpa using this
  have hcast2 : ∀ (X : ℕ), (X : ℝ) * Real.pi / n = 2 * Real.pi → X = 2 * n := by
    intro X h
    have := hcast X 2 (by simpa using h); simpa [mul_comm] using this
  have hle : ∀ P ∈ vertSet D, c P 1 ≤ c P 0 := by
    intro P hP
    have hP' : ∃ p : Fin N × Fin 3, (D.tile p.1).pts p.2 = P := by
      obtain ⟨p, -, hp⟩ := Finset.mem_image.mp hP
      exact ⟨p, hp⟩
    refine hge (c P) ?_
    rcases vertex_group D idx hidx P hP' with ⟨j, hj, h⟩ | ⟨-, h⟩
    · right; right
      refine ⟨σt.symm j, ?_⟩
      rw [hconv P] at h
      have hj' : D.target.angleAt j = u (σt.symm j) * Real.pi / n := by
        have := ht (σt.symm j); rwa [Equiv.apply_symm_apply] at this
      rw [hj'] at h
      have hX : ((∑ i, a i * c P i : ℕ) : ℝ) = (u (σt.symm j) : ℝ) := by
        field_simp at h
        exact h
      exact_mod_cast hX
    · rw [hconv P] at h
      rcases h with h | h
      · exact Or.inl (hcast1 _ h)
      · exact Or.inr (Or.inl (hcast2 _ h))
  have hs0 := sum_cnt D idx (σ 0)
  have hs1 := sum_cnt D idx (σ 1)
  have hsumz : ∑ P ∈ vertSet D, ((c P 0 : ℤ) - (c P 1 : ℤ)) = 0 := by
    rw [Finset.sum_sub_distrib]
    have e0 : ∑ P ∈ vertSet D, (c P 0 : ℤ) = N := by exact_mod_cast hs0
    have e1 : ∑ P ∈ vertSet D, (c P 1 : ℤ) = N := by exact_mod_cast hs1
    rw [e0, e1]; ring
  have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun P hP => by have := hle P hP; omega)).mp hsumz
  intro P hP
  have := hz P hP
  have h2 := hle P hP
  simp only [hc] at this h2 ⊢
  omega

/-- Weights `(1,7,4)` (n = 12). -/
def w12 : Fin 3 → ℕ := fun i => match i with | 0 => 1 | 1 => 7 | 2 => 4
/-- Weights `(1,19,10)` (n = 30). -/
def w30a : Fin 3 → ℕ := fun i => match i with | 0 => 1 | 1 => 19 | 2 => 10
/-- Weights `(7,13,10)` (n = 30). -/
def w30b : Fin 3 → ℕ := fun i => match i with | 0 => 7 | 1 => 13 | 2 => 10

/-- The vertex inequality for the `(π/12, 7π/12, π/3)` tile: weights `(1,7,4)` over `n = 12`, corner `4`. -/
theorem hge_12 (c : Fin 3 → ℕ)
    (h : (∑ i, w12 i * c i = 12) ∨ (∑ i, w12 i * c i = 24) ∨ ∃ j : Fin 3, ∑ i, w12 i * c i = (fun _ => 4) j) :
    c 1 ≤ c 0 := by
  simp only [Fin.sum_univ_three, w12] at h
  rcases h with h | h | ⟨j, h⟩
  · omega
  · omega
  · omega

theorem hge_30a (c : Fin 3 → ℕ)
    (h : (∑ i, w30a i * c i = 30) ∨ (∑ i, w30a i * c i = 60) ∨ ∃ j : Fin 3, ∑ i, w30a i * c i = (fun _ => 10) j) :
    c 1 ≤ c 0 := by
  simp only [Fin.sum_univ_three, w30a] at h
  rcases h with h | h | ⟨j, h⟩
  · omega
  · omega
  · omega

theorem hge_30b (c : Fin 3 → ℕ)
    (h : (∑ i, w30b i * c i = 30) ∨ (∑ i, w30b i * c i = 60) ∨ ∃ j : Fin 3, ∑ i, w30b i * c i = (fun _ => 10) j) :
    c 1 ≤ c 0 := by
  simp only [Fin.sum_univ_three, w30b] at h
  rcases h with h | h | ⟨j, h⟩
  · omega
  · omega
  · omega

/-- **Regular tiling, tile `(π/12, 7π/12, π/3)` with equilateral target.**  There is a vertex correspondence of the model with angles `(π/12, 7π/12, π/3)`
(types `0,1,2`) such that at EVERY vertex of the tiling the number of `π/12`-corners equals the number of `7π/12`-corners. -/
theorem regular_12 (D : CongruentDissection N)
    (hT : TileAngles D (1 * Real.pi / 12) (7 * Real.pi / 12) (4 * Real.pi / 12))
    (hG : TgtAngles D (4 * Real.pi / 12) (4 * Real.pi / 12) (4 * Real.pi / 12))
    (idx : Fin N → Equiv.Perm (Fin 3)) (hidx : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v) :
    ∃ σ : Equiv.Perm (Fin 3), D.model.angleAt (σ 0) = 1 * Real.pi / 12 ∧ D.model.angleAt (σ 1) = 7 * Real.pi / 12 ∧
      D.model.angleAt (σ 2) = 4 * Real.pi / 12 ∧ ∀ P ∈ vertSet D, cnt D idx P (σ 0) = cnt D idx P (σ 1) := by
  obtain ⟨σ, h0, h1, h2⟩ := hT
  obtain ⟨τ, g0, g1, g2⟩ := hG
  refine ⟨σ, h0, h1, h2, ?_⟩
  refine regular_pair D 12 (by norm_num) w12 (fun _ => 4) σ τ ?_ ?_ idx hidx hge_12
  · intro i; fin_cases i <;> simp [w12, h0, h1, h2]
  · intro j; fin_cases j <;> simp [g0, g1, g2]

theorem regular_30a (D : CongruentDissection N)
    (hT : TileAngles D (1 * Real.pi / 30) (19 * Real.pi / 30) (10 * Real.pi / 30))
    (hG : TgtAngles D (10 * Real.pi / 30) (10 * Real.pi / 30) (10 * Real.pi / 30))
    (idx : Fin N → Equiv.Perm (Fin 3)) (hidx : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v) :
    ∃ σ : Equiv.Perm (Fin 3), D.model.angleAt (σ 0) = 1 * Real.pi / 30 ∧ D.model.angleAt (σ 1) = 19 * Real.pi / 30 ∧
      D.model.angleAt (σ 2) = 10 * Real.pi / 30 ∧ ∀ P ∈ vertSet D, cnt D idx P (σ 0) = cnt D idx P (σ 1) := by
  obtain ⟨σ, h0, h1, h2⟩ := hT
  obtain ⟨τ, g0, g1, g2⟩ := hG
  refine ⟨σ, h0, h1, h2, ?_⟩
  refine regular_pair D 30 (by norm_num) w30a (fun _ => 10) σ τ ?_ ?_ idx hidx hge_30a
  · intro i; fin_cases i <;> simp [w30a, h0, h1, h2]
  · intro j; fin_cases j <;> simp [g0, g1, g2]

theorem regular_30b (D : CongruentDissection N)
    (hT : TileAngles D (7 * Real.pi / 30) (13 * Real.pi / 30) (10 * Real.pi / 30))
    (hG : TgtAngles D (10 * Real.pi / 30) (10 * Real.pi / 30) (10 * Real.pi / 30))
    (idx : Fin N → Equiv.Perm (Fin 3)) (hidx : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v) :
    ∃ σ : Equiv.Perm (Fin 3), D.model.angleAt (σ 0) = 7 * Real.pi / 30 ∧ D.model.angleAt (σ 1) = 13 * Real.pi / 30 ∧
      D.model.angleAt (σ 2) = 10 * Real.pi / 30 ∧ ∀ P ∈ vertSet D, cnt D idx P (σ 0) = cnt D idx P (σ 1) := by
  obtain ⟨σ, h0, h1, h2⟩ := hT
  obtain ⟨τ, g0, g1, g2⟩ := hG
  refine ⟨σ, h0, h1, h2, ?_⟩
  refine regular_pair D 30 (by norm_num) w30b (fun _ => 10) σ τ ?_ ?_ idx hidx hge_30b
  · intro i; fin_cases i <;> simp [w30b, h0, h1, h2]
  · intro j; fin_cases j <;> simp [g0, g1, g2]

/-- Non-vacuity of the vertex inequality: `(1,1,1)` (the normal vertex `α+β+γ = π`) and the corner vertex `(4,0,0)` satisfy the hypotheses of `hge_12`. -/
theorem hge_12_witness :
    (∑ i, w12 i * ![1, 1, 1] i = 12) ∧ (∑ i, w12 i * ![4, 0, 0] i = 4) := by
  decide

end Erdos634.Draft.LaczFormal
