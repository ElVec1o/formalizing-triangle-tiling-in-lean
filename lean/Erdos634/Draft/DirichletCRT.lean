-- Draft/DirichletCRT.lean — CRT decomposition of Dirichlet characters (Lemma S infrastructure, A61).
-- For coprime m₁ m₂: every χ mod m₁·m₂ is uniquely changeLevel ψ · changeLevel η (ψ mod m₁, η mod m₂);
-- FactorsThrough (d₁·d₂) splits componentwise; conductor(χ) = conductor(ψ)·conductor(η);
-- χ* = ψ*·η* (at level conductor χ); χ primitive ↔ ψ, η primitive.
-- Classical (Washington ch. 3); absent from Mathlib (which has changeLevel, mul,
-- conductor_mul_dvd_lcm_conductor only). Formalization debt, not /goal progress.
import Mathlib
import Erdos634.Draft.LemmaSB1

namespace Erdos634.DirichletCRT

open DirichletCharacter

variable {R : Type*} [CommMonoidWithZero R] {m₁ m₂ : ℕ}

/-- CRT on unit groups. -/
noncomputable def unitsCRT (h : m₁.Coprime m₂) : (ZMod (m₁ * m₂))ˣ ≃* (ZMod m₁)ˣ × (ZMod m₂)ˣ :=
  (Units.mapEquiv (ZMod.chineseRemainder h).toMulEquiv).trans MulEquiv.prodUnits

theorem unitsCRT_fst (h : m₁.Coprime m₂) (x : (ZMod (m₁ * m₂))ˣ) :
    (unitsCRT h x).1 = ZMod.unitsMap (Nat.dvd_mul_right m₁ m₂) x := by
  have key : (RingHom.fst (ZMod m₁) (ZMod m₂)).comp (ZMod.chineseRemainder h).toRingHom =
      ZMod.castHom (Nat.dvd_mul_right m₁ m₂) (ZMod m₁) := RingHom.ext_zmod _ _
  ext
  have := congrArg (fun f => f (x : ZMod (m₁ * m₂))) key
  simp only [RingHom.comp_apply, RingHom.coe_fst, ZMod.castHom_apply] at this
  simp [unitsCRT, MulEquiv.prodUnits, ZMod.unitsMap_val, ← this]

theorem unitsCRT_snd (h : m₁.Coprime m₂) (x : (ZMod (m₁ * m₂))ˣ) :
    (unitsCRT h x).2 = ZMod.unitsMap (Nat.dvd_mul_left m₂ m₁) x := by
  have key : (RingHom.snd (ZMod m₁) (ZMod m₂)).comp (ZMod.chineseRemainder h).toRingHom =
      ZMod.castHom (Nat.dvd_mul_left m₂ m₁) (ZMod m₂) := RingHom.ext_zmod _ _
  ext
  have := congrArg (fun f => f (x : ZMod (m₁ * m₂))) key
  simp only [RingHom.comp_apply, RingHom.coe_snd, ZMod.castHom_apply] at this
  simp [unitsCRT, MulEquiv.prodUnits, ZMod.unitsMap_val, ← this]

/-- Value of a level-raised character at a unit. -/
theorem changeLevel_unit {n m : ℕ} (hm : n ∣ m) (ψ : DirichletCharacter R n) (x : (ZMod m)ˣ) :
    changeLevel hm ψ (x : ZMod m) = ψ (ZMod.unitsMap hm x : ZMod n) := by
  rw [changeLevel_def, MulChar.ofUnitHom_coe]
  simp

/-- The m₁-component of χ. -/
noncomputable def comp₁ (h : m₁.Coprime m₂) (χ : DirichletCharacter R (m₁ * m₂)) :
    DirichletCharacter R m₁ :=
  MulChar.ofUnitHom (χ.toUnitHom.comp ((unitsCRT h).symm.toMonoidHom.comp (MonoidHom.inl _ _)))

/-- The m₂-component of χ. -/
noncomputable def comp₂ (h : m₁.Coprime m₂) (χ : DirichletCharacter R (m₁ * m₂)) :
    DirichletCharacter R m₂ :=
  MulChar.ofUnitHom (χ.toUnitHom.comp ((unitsCRT h).symm.toMonoidHom.comp (MonoidHom.inr _ _)))

theorem comp₁_unit (h : m₁.Coprime m₂) (χ : DirichletCharacter R (m₁ * m₂)) (a : (ZMod m₁)ˣ) :
    comp₁ h χ (a : ZMod m₁) = χ (((unitsCRT h).symm (a, 1) : (ZMod (m₁ * m₂))ˣ) : ZMod (m₁ * m₂)) := by
  rw [comp₁, MulChar.ofUnitHom_coe]; simp

theorem comp₂_unit (h : m₁.Coprime m₂) (χ : DirichletCharacter R (m₁ * m₂)) (b : (ZMod m₂)ˣ) :
    comp₂ h χ (b : ZMod m₂) = χ (((unitsCRT h).symm (1, b) : (ZMod (m₁ * m₂))ˣ) : ZMod (m₁ * m₂)) := by
  rw [comp₂, MulChar.ofUnitHom_coe]; simp

/-- **Existence.** χ = changeLevel (comp₁ χ) · changeLevel (comp₂ χ). -/
theorem decomp (h : m₁.Coprime m₂) (χ : DirichletCharacter R (m₁ * m₂)) :
    χ = changeLevel (Nat.dvd_mul_right m₁ m₂) (comp₁ h χ) *
      changeLevel (Nat.dvd_mul_left m₂ m₁) (comp₂ h χ) := by
  ext x
  rw [MulChar.coeToFun_mul, Pi.mul_apply, changeLevel_unit, changeLevel_unit, comp₁_unit,
    comp₂_unit, ← unitsCRT_fst h, ← unitsCRT_snd h, ← map_mul, ← Units.val_mul, ← map_mul]
  simp

/-- Evaluation of a CRT product at a unit. -/
theorem prod_unit (h : m₁.Coprime m₂) (ψ : DirichletCharacter R m₁) (η : DirichletCharacter R m₂)
    (x : (ZMod (m₁ * m₂))ˣ) :
    (changeLevel (Nat.dvd_mul_right m₁ m₂) ψ * changeLevel (Nat.dvd_mul_left m₂ m₁) η)
      (x : ZMod (m₁ * m₂)) = ψ ((unitsCRT h x).1 : ZMod m₁) * η ((unitsCRT h x).2 : ZMod m₂) := by
  rw [MulChar.coeToFun_mul, Pi.mul_apply, changeLevel_unit, changeLevel_unit, unitsCRT_fst,
    unitsCRT_snd]

/-- **Uniqueness.** -/
theorem decomp_unique (h : m₁.Coprime m₂) {ψ ψ' : DirichletCharacter R m₁}
    {η η' : DirichletCharacter R m₂}
    (he : changeLevel (Nat.dvd_mul_right m₁ m₂) ψ * changeLevel (Nat.dvd_mul_left m₂ m₁) η =
      changeLevel (Nat.dvd_mul_right m₁ m₂) ψ' * changeLevel (Nat.dvd_mul_left m₂ m₁) η') :
    ψ = ψ' ∧ η = η' := by
  constructor
  · ext a
    have := congrArg (fun χ : DirichletCharacter R (m₁ * m₂) =>
      χ (((unitsCRT h).symm (a, 1) : (ZMod (m₁ * m₂))ˣ) : ZMod (m₁ * m₂))) he
    simpa [prod_unit h] using this
  · ext b
    have := congrArg (fun χ : DirichletCharacter R (m₁ * m₂) =>
      χ (((unitsCRT h).symm (1, b) : (ZMod (m₁ * m₂))ˣ) : ZMod (m₁ * m₂))) he
    simpa [prod_unit h] using this

theorem comp_of_eq (h : m₁.Coprime m₂) {χ : DirichletCharacter R (m₁ * m₂)}
    {ψ : DirichletCharacter R m₁} {η : DirichletCharacter R m₂}
    (hχ : χ = changeLevel (Nat.dvd_mul_right m₁ m₂) ψ * changeLevel (Nat.dvd_mul_left m₂ m₁) η) :
    comp₁ h χ = ψ ∧ comp₂ h χ = η :=
  decomp_unique h ((decomp h χ).symm.trans hχ)

/-- **The group isomorphism** `DirichletCharacter R (m₁ m₂) ≃* DirichletCharacter R m₁ × … m₂`. -/
noncomputable def crtEquiv (h : m₁.Coprime m₂) :
    DirichletCharacter R (m₁ * m₂) ≃* DirichletCharacter R m₁ × DirichletCharacter R m₂ where
  toFun χ := (comp₁ h χ, comp₂ h χ)
  invFun p := changeLevel (Nat.dvd_mul_right m₁ m₂) p.1 * changeLevel (Nat.dvd_mul_left m₂ m₁) p.2
  left_inv χ := (decomp h χ).symm
  right_inv p := by
    obtain ⟨h1, h2⟩ := comp_of_eq h (χ := changeLevel (Nat.dvd_mul_right m₁ m₂) p.1 *
      changeLevel (Nat.dvd_mul_left m₂ m₁) p.2) rfl
    exact Prod.ext h1 h2
  map_mul' χ χ' := by
    refine Prod.ext ?_ ?_
    · ext a; simp [comp₁_unit]
    · ext b; simp [comp₂_unit]

/-! ### FactorsThrough compatibility -/

section FT
variable (h : m₁.Coprime m₂) {χ : DirichletCharacter R (m₁ * m₂)}
  {ψ : DirichletCharacter R m₁} {η : DirichletCharacter R m₂}
  (hχ : χ = changeLevel (Nat.dvd_mul_right m₁ m₂) ψ * changeLevel (Nat.dvd_mul_left m₂ m₁) η)
include h hχ

theorem factorsThrough_mul_of {d₁ d₂ : ℕ} (h₁ : ψ.FactorsThrough d₁) (h₂ : η.FactorsThrough d₂) :
    χ.FactorsThrough (d₁ * d₂) := by
  obtain ⟨hd₁, ψ₀, rfl⟩ := h₁
  obtain ⟨hd₂, η₀, rfl⟩ := h₂
  refine ⟨Nat.mul_dvd_mul hd₁ hd₂, changeLevel (Nat.dvd_mul_right d₁ d₂) ψ₀ *
    changeLevel (Nat.dvd_mul_left d₂ d₁) η₀, ?_⟩
  rw [hχ, map_mul, ← changeLevel_trans, ← changeLevel_trans, ← changeLevel_trans,
    ← changeLevel_trans]

theorem factorsThrough_of_mul {d₁ d₂ : ℕ} (hd₁ : d₁ ∣ m₁) (hd₂ : d₂ ∣ m₂)
    (hf : χ.FactorsThrough (d₁ * d₂)) : ψ.FactorsThrough d₁ ∧ η.FactorsThrough d₂ := by
  have hd : d₁.Coprime d₂ := (h.coprime_dvd_left hd₁).coprime_dvd_right hd₂
  obtain ⟨hdd, χ₀, hχ₀⟩ := hf
  have e := decomp hd χ₀
  have key : χ = changeLevel (Nat.dvd_mul_right m₁ m₂) (changeLevel hd₁ (comp₁ hd χ₀)) *
      changeLevel (Nat.dvd_mul_left m₂ m₁) (changeLevel hd₂ (comp₂ hd χ₀)) := by
    rw [hχ₀]
    conv_lhs => rw [e]
    rw [map_mul, ← changeLevel_trans, ← changeLevel_trans, ← changeLevel_trans,
      ← changeLevel_trans]
  obtain ⟨e1, e2⟩ := decomp_unique h (hχ.symm.trans key)
  exact ⟨⟨hd₁, _, e1⟩, ⟨hd₂, _, e2⟩⟩

/-- **FactorsThrough splits**: for d₁ ∣ m₁, d₂ ∣ m₂. -/
theorem factorsThrough_mul_iff {d₁ d₂ : ℕ} (hd₁ : d₁ ∣ m₁) (hd₂ : d₂ ∣ m₂) :
    χ.FactorsThrough (d₁ * d₂) ↔ ψ.FactorsThrough d₁ ∧ η.FactorsThrough d₂ :=
  ⟨factorsThrough_of_mul h hχ hd₁ hd₂, fun ⟨a, b⟩ => factorsThrough_mul_of h hχ a b⟩

/-- **Conductor multiplicativity.** -/
theorem conductor_eq [NeZero m₁] [NeZero m₂] :
    χ.conductor = ψ.conductor * η.conductor := by
  haveI : NeZero (m₁ * m₂) := ⟨Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _)⟩
  apply Nat.dvd_antisymm
  · exact conductor_dvd_of_mem_conductorSet _
      (factorsThrough_mul_of h hχ (factorsThrough_conductor ψ) (factorsThrough_conductor η))
  · set c := χ.conductor
    have hc : c = c.gcd m₁ * c.gcd m₂ := by
      rw [← Nat.Coprime.gcd_mul c h, Nat.gcd_eq_left (conductor_dvd_level χ)]
    have hf : χ.FactorsThrough (c.gcd m₁ * c.gcd m₂) := hc ▸ factorsThrough_conductor χ
    obtain ⟨f1, f2⟩ := factorsThrough_of_mul h hχ (Nat.gcd_dvd_right _ _) (Nat.gcd_dvd_right _ _) hf
    rw [hc]
    exact Nat.mul_dvd_mul (conductor_dvd_of_mem_conductorSet ψ f1)
      (conductor_dvd_of_mem_conductorSet η f2)

/-- **Primitive part of the product**: χ* = ψ* · η*, changed to level conductor χ. -/
theorem primitiveCharacter_eq [NeZero m₁] [NeZero m₂] :
    χ.primitiveCharacter =
      changeLevel (show ψ.conductor ∣ χ.conductor by
          rw [conductor_eq h hχ]; exact Nat.dvd_mul_right _ _) ψ.primitiveCharacter *
      changeLevel (show η.conductor ∣ χ.conductor by
          rw [conductor_eq h hχ]; exact Nat.dvd_mul_left _ _) η.primitiveCharacter := by
  haveI : NeZero (m₁ * m₂) := ⟨Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _)⟩
  apply changeLevel_injective (conductor_dvd_level χ)
  rw [changeLevel_primitiveCharacter, map_mul, ← changeLevel_trans, ← changeLevel_trans]
  conv_lhs => rw [hχ]
  congr 1
  · conv_lhs => rw [← changeLevel_primitiveCharacter ψ]
    rw [← changeLevel_trans]
  · conv_lhs => rw [← changeLevel_primitiveCharacter η]
    rw [← changeLevel_trans]

/-- **Primitivity splits.** -/
theorem isPrimitive_iff [NeZero m₁] [NeZero m₂] :
    χ.IsPrimitive ↔ ψ.IsPrimitive ∧ η.IsPrimitive := by
  simp only [isPrimitive_def, conductor_eq h hχ]
  have a1 := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne m₁)) (conductor_dvd_level ψ)
  have a2 := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne m₂)) (conductor_dvd_level η)
  have p1 : 0 < ψ.conductor := Nat.pos_of_ne_zero (conductor_ne_zero ψ)
  have p2 : 0 < η.conductor := Nat.pos_of_ne_zero (conductor_ne_zero η)
  constructor
  · intro e
    constructor
    · by_contra hne
      have : ψ.conductor < m₁ := lt_of_le_of_ne a1 hne
      have := Nat.mul_lt_mul_of_lt_of_le this a2 (Nat.pos_of_ne_zero (NeZero.ne m₂))
      omega
    · by_contra hne
      have : η.conductor < m₂ := lt_of_le_of_ne a2 hne
      have := Nat.mul_lt_mul_of_le_of_lt a1 this (Nat.pos_of_ne_zero (NeZero.ne m₁))
      omega
  · rintro ⟨e1, e2⟩; rw [e1, e2]

end FT

/-! ### Witnesses (level 12 = 3 · 4; the odd primitive character mod 3 from LemmaSB1) -/

theorem cop34 : (3 : ℕ).Coprime 4 := by decide

/-- Non-vacuity: the decomposition hypothesis is realised by every χ mod 12. -/
theorem witness_every_char_mod12 (χ : DirichletCharacter ℂ (3 * 4)) :
    ∃ ψ : DirichletCharacter ℂ 3, ∃ η : DirichletCharacter ℂ 4,
      χ = changeLevel (Nat.dvd_mul_right 3 4) ψ * changeLevel (Nat.dvd_mul_left 4 3) η :=
  ⟨_, _, decomp cop34 χ⟩

/-- The odd primitive χ₃ mod 3 lifted to 12 (times the trivial character mod 4) has conductor 3,
is not primitive mod 12, and its primitive part is χ₃. -/
theorem witness_lift_mod3 : ∃ ψ : DirichletCharacter ℂ 3, ψ.IsPrimitive ∧ ψ.Odd ∧
    (changeLevel (Nat.dvd_mul_right 3 4) ψ *
      changeLevel (Nat.dvd_mul_left 4 3) (1 : DirichletCharacter ℂ 4)).conductor = 3 ∧
    ¬ (changeLevel (Nat.dvd_mul_right 3 4) ψ *
      changeLevel (Nat.dvd_mul_left 4 3) (1 : DirichletCharacter ℂ 4)).IsPrimitive := by
  obtain ⟨ψ, hp, ho⟩ := Erdos634.LemmaSB1.exists_odd_primitive_mod3
  have hc := conductor_eq cop34 (χ := changeLevel (Nat.dvd_mul_right 3 4) ψ *
      changeLevel (Nat.dvd_mul_left 4 3) (1 : DirichletCharacter ℂ 4)) rfl
  have hp' : ψ.conductor = 3 := hp
  rw [conductor_one, mul_one, hp'] at hc
  refine ⟨ψ, hp, ho, hc, ?_⟩
  intro h
  rw [isPrimitive_def, hc] at h
  norm_num at h

/-! ### The G′ bridge: constancy over primitive characters splits across coprime factors -/

theorem unit_val_ne_zero {n : ℕ} (ψ : DirichletCharacter ℂ n) (a : (ZMod n)ˣ) : ψ (a : ZMod n) ≠ 0 := by
  rw [← MulChar.coe_toUnitHom]; exact Units.ne_zero _

/-- **G′ product step.** If each factor has a primitive character, then the value at `g` is
constant over primitive χ mod m₁m₂ iff the values at the CRT components are constant over primitive
characters mod m₁ and mod m₂ (and the constants multiply). -/
theorem const_iff (h : m₁.Coprime m₂) [NeZero m₁] [NeZero m₂] (g : (ZMod (m₁ * m₂))ˣ)
    (hne₁ : ∃ ψ : DirichletCharacter ℂ m₁, ψ.IsPrimitive)
    (hne₂ : ∃ η : DirichletCharacter ℂ m₂, η.IsPrimitive) :
    (∃ c : ℂ, ∀ χ : DirichletCharacter ℂ (m₁ * m₂), χ.IsPrimitive → χ (g : ZMod (m₁ * m₂)) = c) ↔
    (∃ c₁ : ℂ, ∀ ψ : DirichletCharacter ℂ m₁, ψ.IsPrimitive → ψ ((unitsCRT h g).1 : ZMod m₁) = c₁) ∧
    (∃ c₂ : ℂ, ∀ η : DirichletCharacter ℂ m₂, η.IsPrimitive → η ((unitsCRT h g).2 : ZMod m₂) = c₂) := by
  obtain ⟨ψ₀, hψ₀⟩ := hne₁
  obtain ⟨η₀, hη₀⟩ := hne₂
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨⟨c / η₀ ((unitsCRT h g).2 : ZMod m₂), fun ψ hψ => ?_⟩,
      ⟨c / ψ₀ ((unitsCRT h g).1 : ZMod m₁), fun η hη => ?_⟩⟩
    · have := hc _ ((isPrimitive_iff h (ψ := ψ) (η := η₀) rfl).2 ⟨hψ, hη₀⟩)
      rw [prod_unit h] at this
      rw [← this, mul_div_cancel_right₀ _ (unit_val_ne_zero _ _)]
    · have := hc _ ((isPrimitive_iff h (ψ := ψ₀) (η := η) rfl).2 ⟨hψ₀, hη⟩)
      rw [prod_unit h] at this
      rw [← this, mul_div_cancel_left₀ _ (unit_val_ne_zero _ _)]
  · rintro ⟨⟨c₁, h₁⟩, ⟨c₂, h₂⟩⟩
    refine ⟨c₁ * c₂, fun χ hχ => ?_⟩
    have e := decomp h χ
    obtain ⟨p1, p2⟩ := (isPrimitive_iff h e).1 hχ
    rw [e, prod_unit h, h₁ _ p1, h₂ _ p2]

/-- Witness for `const_iff`'s first hypothesis with m₁ = 3 (from LemmaSB1). The mod-4 hypothesis
is NOT witnessed in this file. -/
theorem const_iff_hyp_mod3 : ∃ ψ : DirichletCharacter ℂ 3, ψ.IsPrimitive := by
  obtain ⟨ψ, hp, -⟩ := Erdos634.LemmaSB1.exists_odd_primitive_mod3
  exact ⟨ψ, hp⟩

end Erdos634.DirichletCRT

#print axioms Erdos634.DirichletCRT.crtEquiv
#print axioms Erdos634.DirichletCRT.decomp
#print axioms Erdos634.DirichletCRT.decomp_unique
#print axioms Erdos634.DirichletCRT.factorsThrough_mul_iff
#print axioms Erdos634.DirichletCRT.conductor_eq
#print axioms Erdos634.DirichletCRT.primitiveCharacter_eq
#print axioms Erdos634.DirichletCRT.isPrimitive_iff
#print axioms Erdos634.DirichletCRT.witness_every_char_mod12
#print axioms Erdos634.DirichletCRT.witness_lift_mod3
#print axioms Erdos634.DirichletCRT.const_iff
#print axioms Erdos634.DirichletCRT.const_iff_hyp_mod3
