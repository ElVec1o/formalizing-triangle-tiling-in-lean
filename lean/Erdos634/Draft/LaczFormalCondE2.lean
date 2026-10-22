-- Draft/LaczFormalCondE2.lean -- CONDITION (E) of Laczkovich (arXiv 2002.12013, Sect. 1.3), part 2: the count identity
-- sum_{P in V} cnt P l = N (the paper's  sum p_j = sum q_j = sum r_j = N ), and the abstract linear-programming (Farkas) step.
-- UNAUDITED.  Credit: Laczkovich (Condition (E)); the Farkas-certificate method is ours.
import Erdos634.Draft.LaczFormalCondE

open scoped BigOperators Classical
open Erdos634.Geometry Erdos634.KConj Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal

variable {N : ℕ}

/-- The set of vertices (positions of tile corners). -/
noncomputable def vertSet (D : CongruentDissection N) : Finset Plane :=
  Finset.univ.image (fun p : Fin N × Fin 3 => (D.tile p.1).pts p.2)

/-- **Count identity.**  Every tile has exactly one corner of each model type, so the corners of type `l` number `N`. -/
theorem sum_cnt (D : CongruentDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) (l : Fin 3) :
    ∑ P ∈ vertSet D, cnt D idx P l = N := by
  set s : Finset (Fin N × Fin 3) := Finset.univ.filter (fun p => idx p.1 p.2 = l) with hs
  have h1 : s.card = N := by
    have : s = Finset.univ.image (fun i : Fin N => (i, (idx i).symm l)) := by
      ext ⟨i, v⟩
      simp only [hs, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Prod.mk.injEq]
      constructor
      · intro h; exact ⟨i, rfl, by rw [← h]; simp⟩
      · rintro ⟨j, rfl, rfl⟩; simp
    rw [this, Finset.card_image_of_injective _ (fun a b h => by simpa using congrArg Prod.fst h)]
    simp
  have h2 := Finset.card_eq_sum_card_fiberwise (f := fun p : Fin N × Fin 3 => (D.tile p.1).pts p.2)
    (s := s) (t := vertSet D) (fun p _ => by simp [vertSet])
  refine Eq.trans ?_ (h2.symm.trans h1)
  refine Finset.sum_congr rfl (fun P _ => ?_)
  unfold cnt
  congr 1
  ext p
  simp only [hs, Finset.mem_filter, Finset.mem_univ, true_and]
  tauto

/-- **Farkas step.**  If the vertex vectors `c P` (for `P ∈ V`) sum to `(M,M,M)`, every non-corner vertex has `Y·c ≥ 0`, `∑ Y ≤ 0`, and the three corner
vertices have total `Y·c > 0`, contradiction. -/
theorem lp_core {ι : Type*} (V : Finset ι) (c : ι → Fin 3 → ℕ) (Y : Fin 3 → ℤ) (M : ℕ) (cor : Fin 3 → ι)
    (hinj : Function.Injective cor) (hcV : ∀ j, cor j ∈ V) (hsum : ∀ i, ∑ P ∈ V, c P i = M)
    (hnon : ∀ P ∈ V, (∀ j, P ≠ cor j) → 0 ≤ ∑ i, Y i * (c P i : ℤ)) (hY : ∑ i, Y i ≤ 0)
    (hcor : 0 < ∑ j, ∑ i, Y i * (c (cor j) i : ℤ)) : False := by
  have htot : ∑ P ∈ V, ∑ i, Y i * (c P i : ℤ) = (M : ℤ) * ∑ i, Y i := by
    rw [Finset.sum_comm]
    have : ∀ i, ∑ P ∈ V, Y i * (c P i : ℤ) = Y i * M := fun i => by
      rw [← Finset.mul_sum]; congr 1; exact_mod_cast hsum i
    simp only [this]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  have hle : (M : ℤ) * ∑ i, Y i ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) hY
  rw [← Finset.sum_filter_add_sum_filter_not V (fun P => ∃ j, P = cor j)] at htot
  have himg : V.filter (fun P => ∃ j, P = cor j) = Finset.univ.image cor := by
    ext P
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨-, j, rfl⟩; exact ⟨j, rfl⟩
    · rintro ⟨j, rfl⟩; exact ⟨hcV j, j, rfl⟩
  rw [himg, Finset.sum_image (fun a _ b _ h => hinj h)] at htot
  have hrest : 0 ≤ ∑ P ∈ V.filter (fun P => ¬ ∃ j, P = cor j), ∑ i, Y i * (c P i : ℤ) :=
    Finset.sum_nonneg (fun P hP => by
      rw [Finset.mem_filter] at hP
      exact hnon P hP.1 (fun j h => hP.2 ⟨j, h⟩))
  linarith

/-- **Condition (E), killing form.**  Let the model's angles be `a_i π/n` (in the order `σ`) and the target's `u_j π/n` (in the order `σt`).  If integer
`Y` satisfies the three Farkas inequalities (`cert1`: every admissible non-corner vertex vector `c` with `a·c ∈ {n,2n}` has `Y·c ≥ 0`; `cert2`: `∑ Y ≤ 0`;
`cert3`: every triple of corner vectors `f_j` with `a·f_j = u_j` has `Y·(f_0+f_1+f_2) > 0`), then no congruent dissection has this tile and target. -/
theorem E_kill (D : CongruentDissection N) (n : ℕ) (hn : 0 < n) (a u : Fin 3 → ℕ) (Y : Fin 3 → ℤ)
    (σ σt : Equiv.Perm (Fin 3))
    (hm : ∀ i, D.model.angleAt (σ i) = a i * Real.pi / n)
    (ht : ∀ j, D.target.angleAt (σt j) = u j * Real.pi / n)
    (cert1 : ∀ c : Fin 3 → ℕ, (∑ i, a i * c i = n ∨ ∑ i, a i * c i = 2 * n) → 0 ≤ ∑ i, Y i * (c i : ℤ))
    (cert2 : ∑ i, Y i ≤ 0)
    (cert3 : ∀ f : Fin 3 → Fin 3 → ℕ, (∀ j, ∑ i, a i * f j i = u j) →
      0 < ∑ j, ∑ i, Y i * (f j i : ℤ)) : False := by
  have hpi := Real.pi_pos
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨idx, hidx⟩ := exists_idx_general D
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
  have hinj : Function.Injective (fun j => D.target.pts (σt j)) :=
    D.target.indep.injective.comp σt.injective
  have hcV : ∀ j, D.target.pts (σt j) ∈ vertSet D := fun j => by
    obtain ⟨i, m, h⟩ := A1Pos.target_vertex_is_tile_vertex D.toDissection (σt j)
    exact Finset.mem_image.mpr ⟨(i, m), Finset.mem_univ _, h.symm⟩
  refine lp_core (vertSet D) c Y N (fun j => D.target.pts (σt j)) hinj hcV
    (fun i => sum_cnt D idx (σ i)) ?_ cert2 ?_
  · intro P hP hnc
    have hP' : ∃ p : Fin N × Fin 3, (D.tile p.1).pts p.2 = P := by
      obtain ⟨p, -, hp⟩ := Finset.mem_image.mp hP
      exact ⟨p, hp⟩
    rcases vertex_group D idx hidx P hP' with ⟨j, hj, -⟩ | ⟨-, h⟩
    · exact absurd (by simpa using hj) (hnc (σt.symm j))
    · rw [hconv P] at h
      refine cert1 (c P) ?_
      rcases h with h | h
      · exact Or.inl (hcast1 _ h)
      · exact Or.inr (hcast2 _ h)
  · refine cert3 (fun j => c (D.target.pts (σt j))) ?_
    intro j
    have hP' : ∃ p : Fin N × Fin 3, (D.tile p.1).pts p.2 = D.target.pts (σt j) := by
      obtain ⟨p, -, hp⟩ := Finset.mem_image.mp (hcV j)
      exact ⟨p, hp⟩
    rcases vertex_group D idx hidx _ hP' with ⟨j', hj', h⟩ | ⟨h0, -⟩
    · have : j' = σt j := (D.target.indep.injective hj').symm
      subst this
      rw [hconv, ht j] at h
      have h' : ((∑ i, a i * c (D.target.pts (σt j)) i : ℕ) : ℝ) * Real.pi / n = (u j : ℝ) * Real.pi / n := h
      have hX : ((∑ i, a i * c (D.target.pts (σt j)) i : ℕ) : ℝ) = (u j : ℝ) := by
        field_simp at h'
        exact h'
      exact_mod_cast hX
    · exact absurd rfl (h0 (σt j))

end Erdos634.Draft.LaczFormal
