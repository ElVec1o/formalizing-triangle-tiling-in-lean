import Erdos634.Draft.FluxValue
import Erdos634.BADPlacement

/-!
# BAD layer L2, step S1: a Laurent-valued grid character

Written 2026-10-03.  UNAUDITED.  The unit-valued character `psi0 (i,j) = (-1)^(i-j) T^(2i-3j)` of
`ℤ²` into `ℝ[T;T⁻¹]`, pushed to the direction group `L = {iα + jβ}` of `ℝ/2πℤ` (kernel lemma needs
`α/π` irrational and `3α+2β = π`), packaged as `GridChar (LaurentPolynomial ℝ)`.
-/

open LaurentPolynomial

namespace Erdos634.BADL2
open Erdos634.Geometry

noncomputable section

abbrev LR := LaurentPolynomial ℝ

/-- generic: an `R`-valued character of a parameter group, trivial on the kernel of `φ`. -/
def ofAddChar {A R : Type*} [AddCommGroup A] [CommRing R] (φ : A →+ Real.Angle) (ψ0 : AddChar A R)
    (hker : ∀ a, φ a = 0 → ψ0 a = 1) (a₀ : A)
    (hπ : φ a₀ = ((Real.pi : ℝ) : Real.Angle)) (hψ : ψ0 a₀ = -1) (anchor : Real.Angle) :
    GridChar R where
  L := φ.range
  pi_mem := AddMonoidHom.mem_range.mpr ⟨a₀, hπ⟩
  ψ :=
    { toFun := fun x => ψ0 (rangePre φ x)
      map_zero_eq_one' := by
        have h := rangePre_spec φ 0
        exact hker _ (by rw [h]; rfl)
      map_add_eq_mul' := by
        intro x y
        have hx := rangePre_spec φ x
        have hy := rangePre_spec φ y
        have hxy := rangePre_spec φ (x + y)
        have h0 : φ (rangePre φ (x + y) - rangePre φ x - rangePre φ y) = 0 := by
          rw [map_sub, map_sub, hxy, hx, hy, AddSubgroup.coe_add]
          abel
        have h1 := hker _ h0
        have h2 : rangePre φ (x + y) = (rangePre φ (x + y) - rangePre φ x - rangePre φ y)
            + rangePre φ x + rangePre φ y := by abel
        show ψ0 (rangePre φ (x + y)) = ψ0 (rangePre φ x) * ψ0 (rangePre φ y)
        rw [h2, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, h1, one_mul] }
  ψ_pi := by
    have hs := rangePre_spec φ ⟨((Real.pi : ℝ) : Real.Angle), AddMonoidHom.mem_range.mpr ⟨a₀, hπ⟩⟩
    have h0 : φ (rangePre φ ⟨((Real.pi : ℝ) : Real.Angle), AddMonoidHom.mem_range.mpr ⟨a₀, hπ⟩⟩
        - a₀) = 0 := by rw [map_sub, hs, hπ]; exact sub_self _
    have h1 := hker _ h0
    have h2 : rangePre φ ⟨((Real.pi : ℝ) : Real.Angle), AddMonoidHom.mem_range.mpr ⟨a₀, hπ⟩⟩
        = (rangePre φ ⟨((Real.pi : ℝ) : Real.Angle), AddMonoidHom.mem_range.mpr ⟨a₀, hπ⟩⟩ - a₀)
          + a₀ := by abel
    show ψ0 (rangePre φ _) = -1
    rw [h2, AddChar.map_add_eq_mul, h1, hψ, one_mul]
  anchor := anchor

theorem ofAddChar_chi {A R : Type*} [AddCommGroup A] [CommRing R] (φ : A →+ Real.Angle)
    (ψ0 : AddChar A R) (hker : ∀ a, φ a = 0 → ψ0 a = 1) (a₀ : A)
    (hπ : φ a₀ = ((Real.pi : ℝ) : Real.Angle)) (hψ : ψ0 a₀ = -1) (anchor : Real.Angle) (a : A) :
    (ofAddChar φ ψ0 hker a₀ hπ hψ anchor).chi (φ a) = ψ0 a := by
  rw [GridChar.chi_of_mem _ (AddMonoidHom.mem_range.mpr ⟨a, rfl⟩)]
  show ψ0 (rangePre φ ⟨φ a, _⟩) = _
  have hs := rangePre_spec φ ⟨φ a, AddMonoidHom.mem_range.mpr ⟨a, rfl⟩⟩
  have h0 : φ (rangePre φ ⟨φ a, AddMonoidHom.mem_range.mpr ⟨a, rfl⟩⟩ - a) = 0 := by
    rw [map_sub, hs]; exact sub_self _
  have h1 := hker _ h0
  have h2 : rangePre φ ⟨φ a, AddMonoidHom.mem_range.mpr ⟨a, rfl⟩⟩
      = (rangePre φ ⟨φ a, AddMonoidHom.mem_range.mpr ⟨a, rfl⟩⟩ - a) + a := by abel
  rw [h2, AddChar.map_add_eq_mul, h1, one_mul]

theorem ofAddChar_val {A R : Type*} [AddCommGroup A] [CommRing R] (φ : A →+ Real.Angle)
    (ψ0 : AddChar A R) (hker : ∀ a, φ a = 0 → ψ0 a = 1) (a₀ : A)
    (hπ : φ a₀ = ((Real.pi : ℝ) : Real.Angle)) (hψ : ψ0 a₀ = -1) (anchor : Real.Angle)
    (θ : Real.Angle) :
    ∃ a, (ofAddChar φ ψ0 hker a₀ hπ hψ anchor).val θ = ψ0 a := by
  have hm := (ofAddChar φ ψ0 hker a₀ hπ hψ anchor).sub_rep_mem θ
  obtain ⟨a, ha⟩ := AddMonoidHom.mem_range.mp hm
  refine ⟨a, ?_⟩
  unfold GridChar.val
  rw [← ha]
  exact ofAddChar_chi φ ψ0 hker a₀ hπ hψ anchor a

/-! ## the concrete parameter group `ℤ × ℤ` -/

/-- `φ (i,j) = iα + jβ`. -/
def phi (α β : ℝ) : (ℤ × ℤ) →+ Real.Angle :=
  AddMonoidHom.mk' (fun p => (((p.1 : ℝ) * α + (p.2 : ℝ) * β : ℝ) : Real.Angle)) (by
    intro x y
    rw [← Real.Angle.coe_add]
    refine congrArg _ ?_
    simp only [Prod.fst_add, Prod.snd_add]
    push_cast
    ring)

/-- `ψ0 (i,j) = (-1)^(i-j) T^(2i-3j)`. -/
def psi0 : AddChar (ℤ × ℤ) LR where
  toFun p := C ((BAD.ee p.1 p.2 : ℤ) : ℝ) * T (BAD.kk p.1 p.2)
  map_zero_eq_one' := by simp [BAD.ee, BAD.kk]
  map_add_eq_mul' := by
    intro x y
    have h1 : BAD.ee (x.1 + y.1) (x.2 + y.2) = BAD.ee x.1 x.2 * BAD.ee y.1 y.2 :=
      BAD.ee_shift _ _ _ _
    have h2 : BAD.kk (x.1 + y.1) (x.2 + y.2) = BAD.kk x.1 x.2 + BAD.kk y.1 y.2 := by
      unfold BAD.kk; ring
    show C ((BAD.ee (x.1 + y.1) (x.2 + y.2) : ℤ) : ℝ) * T (BAD.kk (x.1 + y.1) (x.2 + y.2)) = _
    rw [h1, h2, T_add]
    push_cast
    rw [map_mul]
    ring

theorem psi0_apply (i j : ℤ) :
    psi0 (i, j) = C ((BAD.ee i j : ℤ) : ℝ) * T (BAD.kk i j) := rfl

/-- kernel lemma: `iα + jβ ≡ 0 (2π)` forces `ψ0 (i,j) = 1`. -/
theorem psi0_ker (α β : ℝ) (hα : ¬∃ r : ℚ, α = r * Real.pi) (hβ : 3 * α + 2 * β = Real.pi)
    (p : ℤ × ℤ) (h : phi α β p = 0) : psi0 p = 1 := by
  obtain ⟨i, j⟩ := p
  have h' : (((i : ℝ) * α + (j : ℝ) * β : ℝ) : Real.Angle) = ((0 : ℝ) : Real.Angle) := by
    simpa [phi] using h
  obtain ⟨n, hn⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.mp h'
  have h2 : (2 * (i : ℝ) - 3 * j) * α + j * Real.pi = 4 * Real.pi * n := by
    linear_combination 2 * hn - (j : ℝ) * hβ
  have hpi := Real.pi_pos
  have hm : 2 * i - 3 * j = 0 := by
    by_contra hne
    apply hα
    have hmR : (2 * (i : ℝ) - 3 * j) ≠ 0 := by exact_mod_cast hne
    refine ⟨((4 * n - j : ℤ) : ℚ) / ((2 * i - 3 * j : ℤ) : ℚ), ?_⟩
    push_cast
    rw [div_mul_eq_mul_div, eq_div_iff hmR]
    linarith
  have hj : (j : ℝ) = 4 * n := by
    have hkR : (2 * (i : ℝ) - 3 * j) = 0 := by exact_mod_cast hm
    rw [hkR, zero_mul, zero_add] at h2
    have : ((j : ℝ) - 4 * n) * Real.pi = 0 := by linarith
    rcases mul_eq_zero.mp this with h0 | h0
    · linarith
    · linarith
  have hj' : j = 4 * n := by exact_mod_cast hj
  have hi : i = 6 * n := by omega
  have hee : BAD.ee i j = 1 := by
    unfold BAD.ee
    have : i - j = 2 * n := by omega
    rw [this, Int.negOnePow_two_mul]; rfl
  have hk0 : BAD.kk i j = 0 := hm
  rw [psi0_apply, hee, hk0]
  simp

end

end Erdos634.BADL2

#print axioms Erdos634.BADL2.psi0_ker
#print axioms Erdos634.BADL2.ofAddChar_val
