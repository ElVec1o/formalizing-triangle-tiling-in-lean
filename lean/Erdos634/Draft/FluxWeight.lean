-- Draft/FluxWeight.lean — layer 2, part 2: the COSET-REPRESENTATIVE WEIGHT built from a character
-- of a direction subgroup `L ⊆ ℝ/2πℤ` containing `π`, and its oddness.  Imported into All.lean (All.lean:504; header corrected 2026-10-03);
-- on the theoremP_6 closure (UNAUDITED).
-- Design: (private working notes, not included) §3.6 (`FluxWeight.lean`), §4.1 (why a coset representative:
-- no global direction-grid lemma is needed by any consumer).
--
-- Formalization debt (the blocker of `lem:value`); not progress on the three /goal outcomes.
import Erdos634.Draft.FluxTurn

open scoped Classical

namespace Erdos634.Geometry

/-- **A grid character.**  A subgroup `L` of `ℝ/2πℤ` containing `π`, an additive character `ψ` on
it with `ψ π = −1`, and an anchor angle (the weight is `1` there). -/
structure GridChar (R : Type*) [CommRing R] where
  L : AddSubgroup Real.Angle
  pi_mem : ((Real.pi : ℝ) : Real.Angle) ∈ L
  ψ : AddChar L R
  ψ_pi : ψ ⟨((Real.pi : ℝ) : Real.Angle), pi_mem⟩ = -1
  anchor : Real.Angle

namespace GridChar

variable {R : Type*} [CommRing R] (G : GridChar R)

/-- `χ` extended by `0` off `L`. -/
noncomputable def chi (θ : Real.Angle) : R := if h : θ ∈ G.L then G.ψ ⟨θ, h⟩ else 0

theorem chi_of_mem {θ : Real.Angle} (h : θ ∈ G.L) : G.chi θ = G.ψ ⟨θ, h⟩ := dif_pos h

theorem chi_add {l l' : Real.Angle} (hl : l ∈ G.L) (hl' : l' ∈ G.L) :
    G.chi (l + l') = G.chi l * G.chi l' := by
  rw [G.chi_of_mem (G.L.add_mem hl hl'), G.chi_of_mem hl, G.chi_of_mem hl']
  exact AddChar.map_add_eq_mul G.ψ ⟨l, hl⟩ ⟨l', hl'⟩

theorem chi_zero : G.chi 0 = 1 := by
  rw [G.chi_of_mem G.L.zero_mem]
  exact AddChar.map_zero_eq_one G.ψ

theorem chi_pi : G.chi ((Real.pi : ℝ) : Real.Angle) = -1 := by
  rw [G.chi_of_mem G.pi_mem]
  exact G.ψ_pi

/-- The representative of `θ`'s coset of `L`: the anchor on the anchor's coset, `Quotient.out`
elsewhere. -/
noncomputable def rep (θ : Real.Angle) : Real.Angle :=
  if θ - G.anchor ∈ G.L then G.anchor else (QuotientAddGroup.mk θ : Real.Angle ⧸ G.L).out

theorem sub_rep_mem (θ : Real.Angle) : θ - G.rep θ ∈ G.L := by
  unfold rep
  split_ifs with h
  · exact h
  · obtain ⟨l, hl⟩ := QuotientAddGroup.mk_out_eq_mul G.L θ
    rw [hl, show θ - (θ + (l : Real.Angle)) = -(l : Real.Angle) by abel]
    exact G.L.neg_mem l.2

theorem rep_add (θ : Real.Angle) {l : Real.Angle} (hl : l ∈ G.L) : G.rep (θ + l) = G.rep θ := by
  unfold rep
  have hiff : (θ + l - G.anchor ∈ G.L) ↔ (θ - G.anchor ∈ G.L) := by
    rw [show θ + l - G.anchor = (θ - G.anchor) + l by abel]
    exact G.L.add_mem_cancel_right hl
  have hmk : (QuotientAddGroup.mk (θ + l) : Real.Angle ⧸ G.L) = QuotientAddGroup.mk θ :=
    QuotientAddGroup.mk_add_of_mem θ hl
  by_cases h : θ - G.anchor ∈ G.L
  · rw [if_pos (hiff.mpr h), if_pos h]
  · rw [if_neg (fun h' => h (hiff.mp h')), if_neg h, hmk]

/-- The value of the weight at an angle: `χ(θ − rep θ)`. -/
noncomputable def val (θ : Real.Angle) : R := G.chi (θ - G.rep θ)

theorem val_add (θ : Real.Angle) {l : Real.Angle} (hl : l ∈ G.L) :
    G.val (θ + l) = G.chi l * G.val θ := by
  unfold val
  rw [G.rep_add θ hl, show θ + l - G.rep θ = (θ - G.rep θ) + l by abel,
    G.chi_add (G.sub_rep_mem θ) hl, mul_comm]

theorem val_anchor : G.val G.anchor = 1 := by
  have h : G.rep G.anchor = G.anchor := by
    unfold rep
    rw [if_pos (by rw [sub_self]; exact G.L.zero_mem)]
  unfold val
  rw [h, sub_self, G.chi_zero]

/-- **The weight** on directions. -/
noncomputable def weight (d : Dir) : R := G.val d.angle

/-- **The weight is odd** — the hypothesis of `Dissection.flux_cancel`. -/
theorem weight_odd (d : Dir) : G.weight (Dir.neg d) = - G.weight d := by
  unfold weight
  rw [Dir.angle_neg, G.val_add _ G.pi_mem, G.chi_pi, neg_one_mul]

theorem val_sq (hsq : ∀ l ∈ G.L, G.chi l * G.chi l = 1) (θ : Real.Angle) :
    G.val θ * G.val θ = 1 :=
  hsq _ (G.sub_rep_mem θ)

end GridChar

/-! ## A source of grid characters: a `ZMod 2`-valued map on a parameter group -/

/-- The `±1` character of a `ZMod 2`-valued additive map. -/
def signChar {A : Type*} [AddCommGroup A] (χ : A →+ ZMod 2) : AddChar A ℝ where
  toFun x := if χ x = 0 then 1 else -1
  map_zero_eq_one' := by simp
  map_add_eq_mul' := by
    intro a b
    simp only [map_add]
    have hcase : ∀ u : ZMod 2, u = 0 ∨ u = 1 := by decide
    have h11 : (1 : ZMod 2) + 1 = 0 := by decide
    have h10 : (1 : ZMod 2) ≠ 0 := by decide
    rcases hcase (χ a) with h1 | h1 <;> rcases hcase (χ b) with h2 | h2 <;>
      simp [h1, h2, h11, h10]

theorem signChar_apply {A : Type*} [AddCommGroup A] (χ : A →+ ZMod 2) (x : A) :
    signChar χ x = if χ x = 0 then 1 else -1 := rfl

/-- A preimage of a point of the range. -/
noncomputable def rangePre {A : Type*} [AddCommGroup A] (φ : A →+ Real.Angle) (x : φ.range) : A :=
  Classical.choose (AddMonoidHom.mem_range.mp x.2)

theorem rangePre_spec {A : Type*} [AddCommGroup A] (φ : A →+ Real.Angle) (x : φ.range) :
    φ (rangePre φ x) = x :=
  Classical.choose_spec (AddMonoidHom.mem_range.mp x.2)

/-- `χ` pushed to the range of `φ`, well defined because `ker φ ⊆ ker χ`. -/
noncomputable def rangeChar {A : Type*} [AddCommGroup A] (φ : A →+ Real.Angle)
    (χ : A →+ ZMod 2) (hker : ∀ a, φ a = 0 → χ a = 0) : φ.range →+ ZMod 2 where
  toFun x := χ (rangePre φ x)
  map_zero' := by
    have h := rangePre_spec φ 0
    exact hker _ (by rw [h]; rfl)
  map_add' := by
    intro x y
    have hx := rangePre_spec φ x
    have hy := rangePre_spec φ y
    have hxy := rangePre_spec φ (x + y)
    have h0 : φ (rangePre φ (x + y) - rangePre φ x - rangePre φ y) = 0 := by
      rw [map_sub, map_sub, hxy, hx, hy, AddSubgroup.coe_add]
      abel
    have h1 := hker _ h0
    rw [map_sub, map_sub] at h1
    linear_combination h1

theorem rangeChar_apply {A : Type*} [AddCommGroup A] (φ : A →+ Real.Angle)
    (χ : A →+ ZMod 2) (hker : ∀ a, φ a = 0 → χ a = 0) (a : A) :
    rangeChar φ χ hker ⟨φ a, AddMonoidHom.mem_range.mpr ⟨a, rfl⟩⟩ = χ a := by
  show χ (rangePre φ ⟨φ a, _⟩) = χ a
  have hs := rangePre_spec φ ⟨φ a, AddMonoidHom.mem_range.mpr ⟨a, rfl⟩⟩
  have h0 : φ (rangePre φ ⟨φ a, AddMonoidHom.mem_range.mpr ⟨a, rfl⟩⟩ - a) = 0 := by
    rw [map_sub, hs]; exact sub_self _
  have h1 := hker _ h0
  rw [map_sub] at h1
  linear_combination h1

/-- **A grid character from a parameter group.**  `φ : A →+ ℝ/2πℤ` parametrises the directions,
`χ : A →+ ZMod 2` is the parity, constant on the fibres of `φ` (`hker`), with `φ a₀ = π` and
`χ a₀ = 1`.  `L` is the range of `φ` and `ψ = (−1)^χ`. -/
noncomputable def GridChar.ofHom {A : Type*} [AddCommGroup A] (φ : A →+ Real.Angle)
    (χ : A →+ ZMod 2) (hker : ∀ a, φ a = 0 → χ a = 0) (a₀ : A)
    (hπ : φ a₀ = ((Real.pi : ℝ) : Real.Angle)) (hχ : χ a₀ = 1) (anchor : Real.Angle) :
    GridChar ℝ where
  L := φ.range
  pi_mem := AddMonoidHom.mem_range.mpr ⟨a₀, hπ⟩
  ψ := signChar (rangeChar φ χ hker)
  ψ_pi := by
    have h := rangeChar_apply φ χ hker a₀
    have e : (⟨((Real.pi : ℝ) : Real.Angle), AddMonoidHom.mem_range.mpr ⟨a₀, hπ⟩⟩ : φ.range)
        = ⟨φ a₀, AddMonoidHom.mem_range.mpr ⟨a₀, rfl⟩⟩ := Subtype.ext hπ.symm
    rw [e, signChar_apply, h, hχ]
    simp
  anchor := anchor

theorem GridChar.ofHom_chi {A : Type*} [AddCommGroup A] (φ : A →+ Real.Angle)
    (χ : A →+ ZMod 2) (hker : ∀ a, φ a = 0 → χ a = 0) (a₀ : A)
    (hπ : φ a₀ = ((Real.pi : ℝ) : Real.Angle)) (hχ : χ a₀ = 1) (anchor : Real.Angle) (a : A) :
    (GridChar.ofHom φ χ hker a₀ hπ hχ anchor).chi (φ a) = if χ a = 0 then 1 else -1 := by
  rw [GridChar.chi_of_mem _ (AddMonoidHom.mem_range.mpr ⟨a, rfl⟩)]
  show signChar (rangeChar φ χ hker) ⟨φ a, _⟩ = _
  rw [signChar_apply, rangeChar_apply]

/-- A `ZMod 2` grid character is `±1`-valued on `L`. -/
theorem GridChar.ofHom_sq {A : Type*} [AddCommGroup A] (φ : A →+ Real.Angle)
    (χ : A →+ ZMod 2) (hker : ∀ a, φ a = 0 → χ a = 0) (a₀ : A)
    (hπ : φ a₀ = ((Real.pi : ℝ) : Real.Angle)) (hχ : χ a₀ = 1) (anchor : Real.Angle) :
    ∀ l ∈ (GridChar.ofHom φ χ hker a₀ hπ hχ anchor).L,
      (GridChar.ofHom φ χ hker a₀ hπ hχ anchor).chi l
        * (GridChar.ofHom φ χ hker a₀ hπ hχ anchor).chi l = 1 := by
  intro l hl
  obtain ⟨a, rfl⟩ := AddMonoidHom.mem_range.mp hl
  rw [GridChar.ofHom_chi]
  split_ifs <;> norm_num

end Erdos634.Geometry

#print axioms Erdos634.Geometry.GridChar.weight_odd
#print axioms Erdos634.Geometry.GridChar.ofHom_sq
