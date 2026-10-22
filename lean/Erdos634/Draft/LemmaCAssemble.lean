-- Draft/LemmaCAssemble.lean — Lemma C, geometric assembly: (F1)-(F3) for a real
-- CongruentDissection feed `LemmaCArith.lemmaC_arith`.  Remaining input: `c ≠ (1,1,1)`.
-- Imported via AllNew8.lean → All.lean:853 (stale "NOT imported" header corrected 2026-10-04).
import Erdos634.Draft.LemmaCArith
import Erdos634.Draft.LemmaCFigures
import Erdos634.CertNode

open scoped Classical
open Erdos634.Geometry Erdos634.Draft.LemmaCFigures

namespace Erdos634.Draft.LemmaCAssemble

/-- Number of tiles presenting angle `θ` at `v`. -/
noncomputable def cnt {N : ℕ} (D : CongruentDissection N) (θ : ℝ) (v : Plane) : ℕ :=
  ({i | (D.tile i).localAngle v = θ} : Finset (Fin N)).card

/-- Corner-figure total for label `j`: tiles presenting `x j` at the three target corners. -/
noncomputable def cfig {N : ℕ} (D : CongruentDissection N) (x : Fin 3 → ℝ) (j : Fin 3) : ℕ :=
  ∑ k : Fin 3, cnt D (x j) (D.target.pts k)

theorem lemmaC_geometric {N : ℕ} (D : CongruentDissection N) (α β γ : ℝ)
    (hmα : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hmβ : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hmγ : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hβγ : β ≠ γ)
    (hα0 : 0 < α) (hβ0 : 0 < β) (hγ0 : 0 < γ)
    (hαπ : α < Real.pi) (hβπ : β < Real.pi) (hγπ : γ < Real.pi)
    (hirr : ∃ i, ¬ ∃ r : ℚ, ![α, β, γ] i = (r : ℝ) * Real.pi)
    (hne : ¬ (cfig D ![α, β, γ] 0 = 1 ∧ cfig D ![α, β, γ] 1 = 1 ∧ cfig D ![α, β, γ] 2 = 1)) :
    ∃ d : Fin 3 → ℤ, (∀ j, (cfig D ![α, β, γ] j : ℤ) = 1 + d j) ∧ (∀ j, -1 ≤ d j ∧ d j ≤ 2) ∧
      (∃ j, d j = -1) ∧ (∃ j, 0 < d j) ∧ 0 ≤ d 0 + d 1 + d 2 ∧
      (d 0 : ℝ) * α + d 1 * β + d 2 * γ = 0 := by
  have hpi := Real.pi_pos
  set x : Fin 3 → ℝ := ![α, β, γ] with hx
  have hsum : x 0 + x 1 + x 2 = Real.pi := by
    have := Erdos634.Geometry.cornerAngle_sum D.model
    simp only [hx, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons]
    linarith
  have hpos : ∀ i, 0 < x i := by intro i; fin_cases i <;> simp [hx, hα0, hβ0, hγ0]
  -- vertex figures at non-corner vertices
  set s : Finset Plane := (cornerPts D.toDissection).filter (fun v => v ∉ Set.range D.target.pts)
    with hs
  have hF1 : ∀ v ∈ s, ∃ k : ℕ, (k = 1 ∨ k = 2) ∧
      (cnt D α v : ℝ) * α + (cnt D β v : ℝ) * β + (cnt D γ v : ℝ) * γ = (k : ℝ) * Real.pi := by
    intro v hv
    obtain ⟨hv1, hv2⟩ := Finset.mem_filter.mp hv
    exact vertex_figure_sum D α β γ hmα hmβ hmγ hαβ hαγ hβγ hα0 hβ0 hγ0 hαπ hβπ hγπ hv1 hv2
  choose! k hk hf using hF1
  -- corner data
  have hcorner := fun kk => corner_figure D α β γ hmα hmβ hmγ hαβ hαγ hβγ hα0 hβ0 hγ0 hαπ hβπ hγπ kk
  -- the model angle at each index
  have hxk : ∀ kk : Fin 3, cornerAngle (D.model.pts (kk + 1)) (D.model.pts kk)
      (D.model.pts (kk + 2)) = x kk := by
    intro kk; fin_cases kk
    · simpa [hx] using hmα
    · simpa [hx] using hmβ
    · simpa [hx] using hmγ
  have hxinj : ∀ a b : Fin 3, x a = x b → a = b := by
    intro a b h
    have hd : ∀ u v : ℝ, u = v → v = u → u ≠ v → False := fun u v h _ hn => hn h
    fin_cases a <;> fin_cases b <;> simp [hx] at h ⊢ <;> simp_all [eq_comm]
  -- F2: total count
  have htotal : ∀ j : Fin 3, ∑ v ∈ cornerPts D.toDissection, cnt D (x j) v = N := by
    intro j
    have := congruentDissection_corner_balance D
      (fun a b h => hxinj a b (by rw [← hxk a, ← hxk b]; exact h)) j
      (by rw [hxk j]; exact (hpos j).ne')
      (by rw [hxk j]; fin_cases j <;> simp [hx] <;> linarith)
      (by rw [hxk j]; fin_cases j <;> simp [hx] <;> linarith)
    rw [hxk j] at this
    exact this
  have hcorn_mem : ∀ kk, D.target.pts kk ∈ cornerPts D.toDissection := fun kk => (hcorner kk).1
  have himg : (cornerPts D.toDissection).filter (fun v => v ∈ Set.range D.target.pts)
      = Finset.univ.image D.target.pts := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and, Set.mem_range]
    constructor
    · rintro ⟨_, kk, hkk⟩; exact ⟨kk, hkk⟩
    · rintro ⟨kk, rfl⟩; exact ⟨hcorn_mem kk, kk, rfl⟩
  have hsplit : ∀ j, ∑ v ∈ s, cnt D (x j) v + cfig D x j = N := by
    intro j
    have h1 := Finset.sum_filter_add_sum_filter_not (cornerPts D.toDissection)
      (fun v => v ∈ Set.range D.target.pts) (fun v => cnt D (x j) v)
    rw [himg, Finset.sum_image (fun a _ b _ hab => Erdos634.CertNode.pts_injective D.target hab),
      htotal j] at h1
    have h2 : cfig D x j = ∑ kk : Fin 3, cnt D (x j) (D.target.pts kk) := rfl
    have h3 : s = (cornerPts D.toDissection).filter (fun v => ¬ v ∈ Set.range D.target.pts) := rfl
    rw [h3]; omega
  have e0 := (hcorner 0).2
  have e1 := (hcorner 1).2
  have e2 := (hcorner 2).2
  simp only [show (0 : Fin 3) + 1 = 1 from rfl, show (0 : Fin 3) + 2 = 2 from rfl,
    show (1 : Fin 3) + 1 = 2 from rfl, show (1 : Fin 3) + 2 = 0 from rfl,
    show (2 : Fin 3) + 1 = 0 from rfl, show (2 : Fin 3) + 2 = 1 from rfl] at e0 e1 e2
  have hT := Erdos634.Geometry.cornerAngle_sum D.target
  have hc3 : 3 ≤ cfig D x 0 + cfig D x 1 + cfig D x 2 := by
    obtain ⟨-, a0⟩ := e0
    obtain ⟨-, a1⟩ := e1
    obtain ⟨-, a2⟩ := e2
    simp only [cfig, cnt, Fin.sum_univ_three, hx, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    omega
  have hc : (cfig D x 0 : ℝ) * x 0 + cfig D x 1 * x 1 + cfig D x 2 * x 2 = Real.pi := by
    obtain ⟨b0, -⟩ := e0
    obtain ⟨b1, -⟩ := e1
    obtain ⟨b2, -⟩ := e2
    simp only [cfig, cnt, Fin.sum_univ_three, hx, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    push_cast
    linarith
  have hf' : ∀ v ∈ s, (cnt D (x 0) v : ℝ) * x 0 + (cnt D (x 1) v : ℝ) * x 1
      + (cnt D (x 2) v : ℝ) * x 2 = (k v : ℝ) * Real.pi := by
    intro v hv
    have := (hf v hv)
    simpa [hx] using this
  obtain ⟨d, hd1, hd2, hd3, hd4, hd5, hd6⟩ := Erdos634.Draft.LemmaCArith.lemmaC_arith x hpos hsum
    hirr (fun j => cfig D x j) hc3 hc hne s (fun v j => cnt D (x j) v) k (fun v hv => hk v hv)
    hf' N hsplit
  refine ⟨d, hd1, hd2, hd3, hd4, hd5, ?_⟩
  simpa [hx] using hd6

end Erdos634.Draft.LemmaCAssemble

#print axioms Erdos634.Draft.LemmaCAssemble.lemmaC_geometric
