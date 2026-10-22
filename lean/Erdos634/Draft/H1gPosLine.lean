-- Draft/H1gPosLine.lean — ATOM H1.g (position half): the real parametrisation of a line, the
-- interval of a tile edge lying on it, and the edge group.  No dissection hypotheses used except
-- through `lineChain` membership (an edge on the line `{crossL d = cross d O}`).
-- Formalization debt; NOT /goal progress.  Standard axioms, no sorry.
import Erdos634.Draft.H1gPos1D
import Erdos634.WallChain

open Set

namespace Erdos634.H1gPos

open Erdos634.Geometry

/-- Z-span of all tile-edge vectors. -/
def edgeGroup {N : ℕ} (D : Dissection N) : AddSubgroup Plane :=
  AddSubgroup.closure {v | ∃ i k, v = (D.tile i).pts (k + 1) - (D.tile i).pts k}

theorem edgeVec_mem {N : ℕ} (D : Dissection N) (i : Fin N) (k : Fin 3) :
    (D.tile i).pts (k + 1) - (D.tile i).pts k ∈ edgeGroup D :=
  AddSubgroup.subset_closure ⟨i, k, rfl⟩

/-- Any two corners of a tile differ by an element of the edge group. -/
theorem corner_sub_mem {N : ℕ} (D : Dissection N) (i : Fin N) (a b : Fin 3) :
    (D.tile i).pts a - (D.tile i).pts b ∈ edgeGroup D := by
  have h0 := edgeVec_mem D i 0
  have h1 := edgeVec_mem D i 1
  have h2 := edgeVec_mem D i 2
  have e0 : ((0 : Fin 3) + 1) = 1 := rfl
  have e1 : ((1 : Fin 3) + 1) = 2 := rfl
  have e2 : ((2 : Fin 3) + 1) = 0 := rfl
  rw [e0] at h0; rw [e1] at h1; rw [e2] at h2
  fin_cases a <;> fin_cases b <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, sub_self] <;>
    first
    | exact (edgeGroup D).zero_mem
    | exact h0 | exact h1 | exact h2
    | (have := (edgeGroup D).neg_mem h0; simpa using this)
    | (have := (edgeGroup D).neg_mem h1; simpa using this)
    | (have := (edgeGroup D).neg_mem h2; simpa using this)

/-! ## The real parametrisation of a line -/

/-- Point of the line `O + ℝ d` at parameter `t`. -/
def pt (O d : Plane) (t : ℝ) : Plane := O + t • d

/-- Parameter of a point (correct on the line). -/
noncomputable def pos (O d X : Plane) : ℝ :=
  (d 0 * (X 0 - O 0) + d 1 * (X 1 - O 1)) / (d 0 ^ 2 + d 1 ^ 2)

theorem dsq_pos {d : Plane} (hd : d ≠ 0) : 0 < d 0 ^ 2 + d 1 ^ 2 := by
  by_contra hc
  apply hd
  have h0 : d 0 = 0 := by nlinarith [sq_nonneg (d 0), sq_nonneg (d 1)]
  have h1 : d 1 = 0 := by nlinarith [sq_nonneg (d 0), sq_nonneg (d 1)]
  ext i; fin_cases i <;> simp [h0, h1]

theorem pos_pt {O d : Plane} (hd : d ≠ 0) (t : ℝ) : pos O d (pt O d t) = t := by
  have := (dsq_pos hd).ne'
  simp only [pos, pt, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  field_simp
  ring

theorem pt_inj {O d : Plane} (hd : d ≠ 0) : Function.Injective (pt O d) := by
  intro s t h
  have := congrArg (pos O d) h
  rwa [pos_pt hd, pos_pt hd] at this

theorem pt_pos {O d X : Plane} (hd : d ≠ 0) (hX : cross d (X - O) = 0) :
    pt O d (pos O d X) = X := by
  obtain ⟨τ, hτ⟩ := parallel_of_cross_eq_zero hd hX
  have hX' : X = pt O d τ := by simp only [pt]; rw [← hτ]; abel
  rw [hX', pos_pt hd]

/-! ## The interval of a tile edge on the line -/

section
variable {N : ℕ} (D : Dissection N) (O d : Plane)

/-- The edge's two endpoints lie on the line `O + ℝ d`. -/
def OnLine (e : Fin N × Fin 3) : Prop :=
  cross d ((D.tile e.1).pts e.2 - O) = 0 ∧ cross d ((D.tile e.1).pts (e.2 + 1) - O) = 0

/-- Parameters of the two endpoints. -/
noncomputable def eA (e : Fin N × Fin 3) : ℝ := pos O d ((D.tile e.1).pts e.2)
noncomputable def eB (e : Fin N × Fin 3) : ℝ := pos O d ((D.tile e.1).pts (e.2 + 1))
noncomputable def eLo (e : Fin N × Fin 3) : ℝ := min (eA D O d e) (eB D O d e)
noncomputable def eHi (e : Fin N × Fin 3) : ℝ := max (eA D O d e) (eB D O d e)

variable {D O d}

theorem onLine_of_mem_lineChain {e : Fin N × Fin 3}
    (he : e ∈ D.lineChain (crossL d) (cross d O)) : OnLine D O d e := by
  obtain ⟨h1, h2, -⟩ := Dissection.mem_lineChain.mp he
  simp only [crossL_apply] at h1 h2
  exact ⟨by rw [cross_sub_right, h1, sub_self], by rw [cross_sub_right, h2, sub_self]⟩

theorem onLine_of_mem_lineChain_neg {e : Fin N × Fin 3}
    (he : e ∈ D.lineChain (-(crossL d)) (-(cross d O))) : OnLine D O d e := by
  obtain ⟨h1, h2, -⟩ := Dissection.mem_lineChain.mp he
  simp only [LinearMap.neg_apply, crossL_apply, neg_inj] at h1 h2
  exact ⟨by rw [cross_sub_right, h1, sub_self], by rw [cross_sub_right, h2, sub_self]⟩

theorem pts_eq_pt (hd : d ≠ 0) {e : Fin N × Fin 3} (he : OnLine D O d e) :
    (D.tile e.1).pts e.2 = pt O d (eA D O d e) ∧
      (D.tile e.1).pts (e.2 + 1) = pt O d (eB D O d e) :=
  ⟨(pt_pos hd he.1).symm, (pt_pos hd he.2).symm⟩

theorem eA_ne_eB (hd : d ≠ 0) {e : Fin N × Fin 3} (he : OnLine D O d e) :
    eA D O d e ≠ eB D O d e := by
  intro h
  obtain ⟨h1, h2⟩ := pts_eq_pt hd he
  have : (D.tile e.1).pts e.2 = (D.tile e.1).pts (e.2 + 1) := by rw [h1, h2, h]
  have h3 := (D.tile e.1).indep.injective this
  have h4 : ∀ m : Fin 3, m ≠ m + 1 := by decide
  exact h4 _ h3

theorem eLo_lt_eHi (hd : d ≠ 0) {e : Fin N × Fin 3} (he : OnLine D O d e) :
    eLo D O d e < eHi D O d e := by
  have := eA_ne_eB hd he
  unfold eLo eHi
  rcases lt_or_gt_of_ne this with h | h
  · rw [min_eq_left h.le, max_eq_right h.le]; exact h
  · rw [min_eq_right h.le, max_eq_left h.le]; exact h

/-- **The edge is the real interval `[eLo, eHi]` on the line.** -/
theorem pt_mem_edge_iff (hd : d ≠ 0) {e : Fin N × Fin 3} (he : OnLine D O d e) (t : ℝ) :
    pt O d t ∈ (D.tile e.1).edge e.2 ↔ eLo D O d e ≤ t ∧ t ≤ eHi D O d e := by
  obtain ⟨h1, h2⟩ := pts_eq_pt hd he
  have hseg : (D.tile e.1).edge e.2 = segment ℝ (pt O d (eA D O d e)) (pt O d (eB D O d e)) := by
    rw [Tri.edge, h1, h2]
  rw [hseg]
  constructor
  · rintro ⟨s, u, hs, hu, hsu, hx⟩
    have hx' : pt O d t = pt O d (s * eA D O d e + u * eB D O d e) := by
      rw [← hx]
      have : s = 1 - u := by linarith
      subst this
      simp only [pt, smul_eq_mul]; module
    have ht := pt_inj hd hx'
    unfold eLo eHi
    subst ht
    have hu' : s = 1 - u := by linarith
    have hs' : u = 1 - s := by linarith
    have e1 : s * eA D O d e + u * eB D O d e = eA D O d e + u * (eB D O d e - eA D O d e) := by
      rw [hu']; ring
    have e2 : s * eA D O d e + u * eB D O d e = eB D O d e + s * (eA D O d e - eB D O d e) := by
      rw [hs']; ring
    constructor
    · rcases le_total (eA D O d e) (eB D O d e) with h | h
      · rw [min_eq_left h, e1]; nlinarith [mul_nonneg hu (sub_nonneg.2 h)]
      · rw [min_eq_right h, e2]; nlinarith [mul_nonneg hs (sub_nonneg.2 h)]
    · rcases le_total (eA D O d e) (eB D O d e) with h | h
      · rw [max_eq_right h, e2]; nlinarith [mul_nonneg hs (sub_nonneg.2 h)]
      · rw [max_eq_left h, e1]; nlinarith [mul_nonneg hu (sub_nonneg.2 h)]
  · rintro ⟨hl, hh⟩
    have ht : t ∈ segment ℝ (eA D O d e) (eB D O d e) := by
      rw [segment_eq_uIcc]
      exact ⟨hl, hh⟩
    obtain ⟨s, u, hs, hu, hsu, hx⟩ := ht
    refine ⟨s, u, hs, hu, hsu, ?_⟩
    have : s = 1 - u := by linarith
    subst this
    simp only [pt, smul_eq_mul] at hx ⊢
    rw [← hx]; module

/-- Distinct same-side chain edges have disjoint open intervals. -/
theorem open_disjoint (hd : d ≠ 0) {e e' : Fin N × Fin 3} (he : OnLine D O d e)
    (he' : OnLine D O d e')
    (hsub : ((D.tile e.1).edge e.2 ∩ (D.tile e'.1).edge e'.2).Subsingleton) :
    Disjoint (Ioo (eLo D O d e) (eHi D O d e)) (Ioo (eLo D O d e') (eHi D O d e')) := by
  rw [Set.disjoint_left]
  intro t ht ht'
  set L := max (eLo D O d e) (eLo D O d e')
  set U := min (eHi D O d e) (eHi D O d e')
  have hLU : L < U := by
    have h1 := ht.1; have h2 := ht.2; have h3 := ht'.1; have h4 := ht'.2
    have : L < t := max_lt h1 h3
    have : t < U := lt_min h2 h4
    linarith
  have hin : ∀ s, L < s → s < U → pt O d s ∈ (D.tile e.1).edge e.2 ∩ (D.tile e'.1).edge e'.2 := by
    intro s h1 h2
    refine ⟨(pt_mem_edge_iff hd he s).mpr ⟨?_, ?_⟩, (pt_mem_edge_iff hd he' s).mpr ⟨?_, ?_⟩⟩
    · have := le_max_left (eLo D O d e) (eLo D O d e'); linarith
    · have := min_le_left (eHi D O d e) (eHi D O d e'); linarith
    · have := le_max_right (eLo D O d e) (eLo D O d e'); linarith
    · have := min_le_right (eHi D O d e) (eHi D O d e'); linarith
  have := hsub (hin ((2 * L + U) / 3) (by linarith) (by linarith))
    (hin ((L + 2 * U) / 3) (by linarith) (by linarith))
  have h := pt_inj hd this
  linarith

/-- The endpoint congruence: `(hi - lo) • d ∈ M`. -/
theorem hi_sub_lo_mem (hd : d ≠ 0) {e : Fin N × Fin 3} (he : OnLine D O d e) :
    (eHi D O d e - eLo D O d e) • d ∈ edgeGroup D := by
  obtain ⟨h1, h2⟩ := pts_eq_pt hd he
  have hv := edgeVec_mem D e.1 e.2
  have hdiff : (D.tile e.1).pts (e.2 + 1) - (D.tile e.1).pts e.2 =
      (eB D O d e - eA D O d e) • d := by
    rw [h1, h2]; simp only [pt]; module
  rw [hdiff] at hv
  unfold eLo eHi
  rcases le_total (eA D O d e) (eB D O d e) with h | h
  · rw [min_eq_left h, max_eq_right h]; exact hv
  · rw [min_eq_right h, max_eq_left h]
    have := (edgeGroup D).neg_mem hv
    convert this using 1
    module

end

end Erdos634.H1gPos

#print axioms Erdos634.H1gPos.corner_sub_mem
#print axioms Erdos634.H1gPos.pt_mem_edge_iff
#print axioms Erdos634.H1gPos.open_disjoint
#print axioms Erdos634.H1gPos.hi_sub_lo_mem
