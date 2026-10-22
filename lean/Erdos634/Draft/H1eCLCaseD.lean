/-
Draft/H1eCLCaseD.lean — atoms H1.e/H1.j: the Case D argument D5–D9 of (private working notes, not included) §2, from
  * the corner facts `cornerB_fact`, `cornerA_fact` (H1eCLFacts, PROVED there from `corner_aligned`, the counts, `leg_tile`),
  * the sign lemma (`H1iSLMain.side_sign_lemma`, PROVED), via the typed form `side_full` below,
  * `H1dCaseD.caseD_algebra` (the field `K = ℚ(λ)` and its nontrivial embedding `σ`, PROVED),
  * and ONE explicit hypothesis `hL1` (the output of Lemma L1: all corners of all tiles and of the target lie in any
    subfield `K ∋ a, b, c`), plus the scale normalisation `b = 1`.
Conclusion `rightCaseD_of_pieces : False`.

Outline of what is proved here (D5–D9, all of it):
  D5  `side_full` : for each side, multiplicities `P,Q,R` of the three edge types with the walk equation, the ψ-sign rule
      (`P ≠ 0 → 0 < ψa·ψL`, ...), and "an edge of type X lies on the side ⇒ its multiplicity is ≠ 0".
  D6–D9 `caseD_core` (pure real arithmetic): from the sign rule at the sides `AB` (ψL = -λc') and `BC` (ψL = -2λ), the
      corner-B fact `(Q≠0 ∧ R₂≠0) ∨ (R≠0 ∧ Q₂≠0)` and the corner-A fact `P≠0 ∨ R≠0`:
        b ∉ BC (σb = 1 > 0 but σ|BC| < 0);   c' < 0 (c ⊂ BC);   c ∉ AB;   a ⊂ AB so a' > 0;   a ∉ BC;
        BC = R₂·c, AB = P·a + Q·b, hence  P·a = N/R₂ - Q  ∈ ℚ,  contradicting  a/b ∉ ℚ.
  The step the paper flags ("D9 closes only if u_a > 0") is exactly the corner-A input `P ≠ 0 ∨ R ≠ 0`; it is PROVED
  (H1eCLFacts.cornerA_fact), not assumed.  No part of D6–D9 uses `σ(c)² = σ(a)²+1`.

*** UNAUDITED.  Formalization debt, NOT /goal progress.  No sorry. ***
-/
import Erdos634.Draft.H1eCLFacts
import Erdos634.Draft.H1iSLMain
import Erdos634.Draft.H1dCaseD
import Erdos634.EdgeWordConversion

open scoped Classical

namespace Erdos634.Draft.H1eCL

open Erdos634.Geometry Erdos634.Draft.H1a Erdos634.Geometry.Row3.RP Erdos634.H1iSL

variable {N : ℕ}

/-! ### Splitting a finite family of three-valued quantities -/

theorem three_split {ι : Type*} (s : Finset ι) (len : ι → ℝ) (a b c : ℝ) (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) (h : ∀ e ∈ s, len e = a ∨ len e = b ∨ len e = c) :
    ∃ P Q R : ℕ, (P : ℝ) * a + (Q : ℝ) * b + (R : ℝ) * c = ∑ e ∈ s, len e ∧
      (P ≠ 0 ↔ ∃ e ∈ s, len e = a) ∧ (Q ≠ 0 ↔ ∃ e ∈ s, len e = b) ∧ (R ≠ 0 ↔ ∃ e ∈ s, len e = c) := by
  classical
  have hmaps : ∀ x ∈ s, len x ∈ ({a, b, c} : Finset ℝ) := by
    intro x hx; rcases h x hx with h | h | h <;> simp [h]
  have hfib := Finset.sum_fiberwise_of_maps_to (s := s) (t := ({a, b, c} : Finset ℝ)) (g := len) hmaps len
  rw [Finset.sum_insert (by simp [hab, hac]), Finset.sum_insert (by simp [hbc]),
    Finset.sum_singleton] at hfib
  have hconst : ∀ y : ℝ, ∑ x ∈ s with len x = y, len x = ((s.filter fun x => len x = y).card : ℝ) * y := by
    intro y
    rw [Finset.sum_congr rfl (fun x hx => (Finset.mem_filter.mp hx).2), Finset.sum_const, nsmul_eq_mul]
  have key : ∀ y : ℝ, ((s.filter fun x => len x = y).card ≠ 0 ↔ ∃ e ∈ s, len e = y) := by
    intro y
    rw [Ne, Finset.card_eq_zero, ← Ne, ← Finset.nonempty_iff_ne_empty, Finset.filter_nonempty_iff]
  refine ⟨(s.filter fun x => len x = a).card, (s.filter fun x => len x = b).card,
    (s.filter fun x => len x = c).card, ?_, key a, key b, key c⟩
  rw [← hfib, hconst a, hconst b, hconst c]
  ring

/-! ### D5: the typed sign lemma, with support information -/

theorem side_full (D : CongruentDissection N) (K : Subfield ℝ) (ψ : K →+* ℝ)
    (hK : ∀ i k v, (D.tile i).pts k v ∈ K) (hKT : ∀ k v, D.target.pts k v ∈ K)
    (a b c : K) (hab : (a : ℝ) ≠ b) (hac : (a : ℝ) ≠ c) (hbc : (b : ℝ) ≠ c)
    (habc : ∀ (j : Fin N) (k : Fin 3),
      dist ((D.tile j).pts k) ((D.tile j).pts (k + 1)) = (a : ℝ)
      ∨ dist ((D.tile j).pts k) ((D.tile j).pts (k + 1)) = (b : ℝ)
      ∨ dist ((D.tile j).pts k) ((D.tile j).pts (k + 1)) = (c : ℝ)) (s : Fin 3) :
    ∃ (L : K) (P Q R : ℕ), (L : ℝ) = dist (D.target.pts s) (D.target.pts (s + 1)) ∧
      (P : ℝ) * a + (Q : ℝ) * b + (R : ℝ) * c = (L : ℝ) ∧
      (P ≠ 0 → 0 < ψ a * ψ L) ∧ (Q ≠ 0 → 0 < ψ b * ψ L) ∧ (R ≠ 0 → 0 < ψ c * ψ L) ∧
      ((∃ i e, OnSide D s i e ∧ elen D i e = (a : ℝ)) → P ≠ 0) ∧
      ((∃ i e, OnSide D s i e ∧ elen D i e = (b : ℝ)) → Q ≠ 0) ∧
      ((∃ i e, OnSide D s i e ∧ elen D i e = (c : ℝ)) → R ≠ 0) := by
  classical
  have hlen : ∀ i k, dist ((D.tile i).pts k) ((D.tile i).pts (k + 1)) ∈ K := by
    intro i k
    rcases habc i k with h | h | h <;> rw [h]
    · exact a.2
    · exact b.2
    · exact c.2
  obtain ⟨part, hL, hcov, -, hchar, hsum, hpos, -⟩ := side_sign_lemma D K ψ hK hKT hlen s
  obtain ⟨P, Q, R, hPQR, hPs, hQs, hRs⟩ := three_split part
    (fun e => dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1))) (a : ℝ) b c hab hac hbc
    (fun e _ => habc e.1 e.2)
  have hsign : ∀ (e : Fin N × Fin 3) (x : K), e ∈ part →
      dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) = (x : ℝ) →
      0 < ψ x * ψ ⟨dist (D.target.pts s) (D.target.pts (s + 1)), hL⟩ := by
    intro e x he hx
    have := hpos e he
    have hk : (⟨dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)), hlen e.1 e.2⟩ : K) = x :=
      Subtype.ext hx
    rwa [hk] at this
  have hmem : ∀ i e, OnSide D s i e → (i, e) ∈ part := by
    intro i e he
    exact (part_char D.toDissection s part hcov (i, e)).mpr he
  refine ⟨⟨_, hL⟩, P, Q, R, rfl, hPQR.trans hsum, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hP
    obtain ⟨e, he, hea⟩ := hPs.mp hP
    exact hsign e a he hea
  · intro hQ
    obtain ⟨e, he, heb⟩ := hQs.mp hQ
    exact hsign e b he heb
  · intro hR
    obtain ⟨e, he, hec⟩ := hRs.mp hR
    exact hsign e c he hec
  · rintro ⟨i, e, hon, hl⟩
    exact hPs.mpr ⟨(i, e), hmem i e hon, hl⟩
  · rintro ⟨i, e, hon, hl⟩
    exact hQs.mpr ⟨(i, e), hmem i e hon, hl⟩
  · rintro ⟨i, e, hon, hl⟩
    exact hRs.mpr ⟨(i, e), hmem i e hon, hl⟩

/-! ### D6–D9: the core arithmetic -/

/-- **D6–D9, pure real arithmetic.**  `a' = ψ a`, `c' = ψ c` (`ψ b = 1`, `ψ λ = -λ`).  Side `AB`: `ψ|AB| = -λ c'`,
side `BC`: `ψ|BC| = -2λ`.  Multiplicities `(P,Q,R)` on `AB`, `(P₂,Q₂,R₂)` on `BC`. -/
theorem caseD_core {a c lam a' c' : ℝ} {M : ℕ} (hlam : 0 < lam) (hlam2 : lam ^ 2 = M)
    (hirr : Irrational a)
    {P Q R P₂ Q₂ R₂ : ℕ}
    (hAB : (P : ℝ) * a + (Q : ℝ) * 1 + (R : ℝ) * c = lam * c)
    (sAP : P ≠ 0 → 0 < a' * (-lam * c')) (sAQ : Q ≠ 0 → 0 < 1 * (-lam * c'))
    (sAR : R ≠ 0 → 0 < c' * (-lam * c'))
    (hBC : (P₂ : ℝ) * a + (Q₂ : ℝ) * 1 + (R₂ : ℝ) * c = 2 * lam)
    (sBP : P₂ ≠ 0 → 0 < a' * (-(2 * lam))) (sBQ : Q₂ ≠ 0 → 0 < 1 * (-(2 * lam)))
    (sBR : R₂ ≠ 0 → 0 < c' * (-(2 * lam)))
    (cornerB : (Q ≠ 0 ∧ R₂ ≠ 0) ∨ (R ≠ 0 ∧ Q₂ ≠ 0))
    (cornerA : P ≠ 0 ∨ R ≠ 0) : False := by
  -- b ∉ BC
  have hQ2 : Q₂ = 0 := by
    by_contra h
    have := sBQ h
    nlinarith
  -- corner B: c on BC, b on AB
  have hR2 : R₂ ≠ 0 := by
    rcases cornerB with ⟨-, h⟩ | ⟨-, h⟩
    · exact h
    · exact absurd hQ2 h
  have hc' : c' < 0 := by
    have := sBR hR2
    nlinarith
  -- c ∉ AB
  have hR : R = 0 := by
    by_contra h
    have := sAR h
    nlinarith [sq_nonneg c']
  -- a on AB
  have hP : P ≠ 0 := by
    rcases cornerA with h | h
    · exact h
    · exact absurd hR h
  have ha' : 0 < a' := by
    have := sAP hP
    have h2 : 0 < -lam * c' := by nlinarith
    by_contra hneg
    push Not at hneg
    nlinarith
  -- a ∉ BC
  have hP2 : P₂ = 0 := by
    by_contra h
    have := sBP h
    nlinarith
  -- arithmetic: BC = R₂ c, AB = P a + Q
  subst hQ2 hR hP2
  have hR2' : (R₂ : ℝ) ≠ 0 := by exact_mod_cast hR2
  have hP' : (P : ℝ) ≠ 0 := by exact_mod_cast hP
  have hc : c = 2 * lam / R₂ := by
    have h2 : (R₂ : ℝ) * c = 2 * lam := by simpa using hBC
    field_simp
    linarith
  have hPa : (P : ℝ) * a = 2 * (M : ℝ) / R₂ - Q := by
    have h1 : (P : ℝ) * a = lam * c - Q := by simp at hAB; linarith
    rw [h1, hc]
    field_simp
    rw [← hlam2]; ring
  apply hirr
  refine ⟨(2 * (M : ℚ) / R₂ - Q) / P, ?_⟩
  push_cast
  rw [div_eq_iff hP', ← hPa]
  ring

/-! ### Assembly -/

/-- The three tile-edge lengths are `a`, `b`, `c` (in the `oppLen` labelling). -/
theorem edge_len_abc (D : CongruentDissection N) (j : Fin N) (k : Fin 3) :
    dist ((D.tile j).pts k) ((D.tile j).pts (k + 1)) = D.model.oppLen 0 ∨
    dist ((D.tile j).pts k) ((D.tile j).pts (k + 1)) = D.model.oppLen 1 ∨
    dist ((D.tile j).pts k) ((D.tile j).pts (k + 1)) = D.model.oppLen 2 := by
  have h := Erdos634.EdgeWordConversion.edge_length_trichotomy D j k
  simp only [Erdos634.EdgeWordConversion.sideLen] at h
  have e0 : D.model.oppLen 2 = dist (D.model.pts 0) (D.model.pts (0 + 1)) := rfl
  have e1 : D.model.oppLen 0 = dist (D.model.pts 1) (D.model.pts (1 + 1)) := rfl
  have e2 : D.model.oppLen 1 = dist (D.model.pts 2) (D.model.pts (2 + 1)) := by
    show dist (D.model.pts (1 + 1)) (D.model.pts (1 + 2)) = _
    rfl
  rw [e0, e1, e2]
  rcases h with h | h | h
  · exact Or.inr (Or.inr h)
  · exact Or.inl h
  · exact Or.inr (Or.inl h)

/-- **Case D, assembled (D5–D9).**  `D` a congruent dissection in normal form (`RightNormal`), scaled so that the model leg
`b = oppLen 1 = 1`, with `λ = |AB|/c ∉ ℚ`, `a/b ∉ ℚ`, `c = r a + s b` (Case D).  Assume the L1 output `hL1`:
every subfield `K` containing `a, b, c` contains all corners of all tiles and of the target.  Then `False`.

Residual hypotheses (everything else is proved in Lean):
 * `hb1`  — the similarity normalisation `b = 1` (to be supplied by `scaleDissection`, with invariance of `RightNormal`,
   of `λ`, of `a/b`, and of `c = r a + s b`).
 * `hL1`  — Lemma L1 (vertices lie in the field), in the precise form of the hypotheses `hK`, `hKT` of
   `H1hCT.conj_congruentDissection_subfield`.  It is a statement about `D` in its actual position in the plane, so it
   presupposes that `D` has been moved by an isometry to the frame `B = 0`, `BC` along the x-axis (the paper's frame):
   the consumer must supply that normalisation. -/
theorem rightCaseD_of_pieces {N : ℕ} (D : CongruentDissection N) {α : ℝ} (hR : RightNormal D α)
    (hb1 : D.model.oppLen 1 = 1)
    (hlam : Irrational (D.target.oppLen 1 / D.model.oppLen 2))
    (hirr : Irrational (D.model.oppLen 0 / D.model.oppLen 1))
    (hrs : ∃ r s : ℚ, D.model.oppLen 2 = r * D.model.oppLen 0 + s * D.model.oppLen 1)
    (hL1 : ∀ K : Subfield ℝ, D.model.oppLen 0 ∈ K → D.model.oppLen 1 ∈ K → D.model.oppLen 2 ∈ K →
      (∀ i k v, (D.tile i).pts k v ∈ K) ∧ (∀ k v, D.target.pts k v ∈ K)) : False := by
  obtain ⟨M, hF⟩ := hR.facts
  obtain ⟨r, s, hrs⟩ := hrs
  obtain ⟨ua, ub, uc, hw⟩ := hF.wAB
  obtain ⟨wa, wb, wc, hw'⟩ := hF.wBC
  obtain ⟨K, hl, ht, hct, σ, -, hσl, -, -, -, -, -, -⟩ :=
    Erdos634.Draft.H1d.caseD_algebra hF.hb hF.hc (by linarith [hF.pyth]) hrs hirr hF.hlam hF.hlam2 hlam hw hw'
  -- the numbers
  set a := D.model.oppLen 0 with ha
  set b := D.model.oppLen 1 with hb
  set c := D.model.oppLen 2 with hc
  set lam := D.target.oppLen 1 / D.model.oppLen 2 with hlamdef
  have haK : a ∈ K := by
    have : a / b = a := by rw [hb1, div_one]
    rw [← this]; exact ht
  have hbK : b ∈ K := by rw [hb1]; exact K.one_mem
  have hcK : c ∈ K := by
    have : c / b = c := by rw [hb1, div_one]
    rw [← this]; exact hct
  obtain ⟨hK, hKT⟩ := hL1 K.toSubfield haK hbK hcK
  -- ψ : K →+* ℝ
  let ψ : K.toSubfield →+* ℝ := σ.toRingHom
  let A : K.toSubfield := ⟨a, haK⟩
  let B : K.toSubfield := ⟨b, hbK⟩
  let C : K.toSubfield := ⟨c, hcK⟩
  let Λ : K.toSubfield := ⟨lam, hl⟩
  have hψΛ : ψ Λ = -lam := hσl
  have hBone : B = 1 := Subtype.ext hb1
  have hψB : ψ B = 1 := by rw [hBone]; exact map_one ψ
  have hab : (A : ℝ) ≠ B := by
    intro h
    apply hirr
    refine ⟨1, ?_⟩
    have : a = b := h
    rw [hb1] at this ⊢
    rw [this]; simp [hb1]
  have hc2 : c ^ 2 = a ^ 2 + b ^ 2 := by linarith [hF.pyth]
  have hac : (A : ℝ) ≠ C := by
    intro h
    have h1 : a = c := h
    have h2 : (0 : ℝ) < b ^ 2 := by have := hF.hb; positivity
    have h3 : a ^ 2 = c ^ 2 := by rw [h1]
    linarith
  have hbc : (B : ℝ) ≠ C := by
    intro h
    have h1 : b = c := h
    have h2 : (0 : ℝ) < a ^ 2 := by have := hF.ha; positivity
    have h3 : b ^ 2 = c ^ 2 := by rw [h1]
    linarith
  have habc := edge_len_abc D
  -- the two sides
  obtain ⟨L2, P, Q, R, hL2, hwalk2, sAP, sAQ, sAR, exA, exB, exC⟩ :=
    side_full D K.toSubfield ψ hK hKT A B C hab hac hbc habc 2
  obtain ⟨L0, P₂, Q₂, R₂, hL0, hwalk0, sBP, sBQ, sBR, exA0, exB0, exC0⟩ :=
    side_full D K.toSubfield ψ hK hKT A B C hab hac hbc habc 0
  -- side lengths
  obtain ⟨-, sb, -, tt2⟩ := hR.sides
  have hLc : D.target.oppLen 1 = lam * c := by rw [hlamdef, hc]; field_simp [(oppLen_pos D.model 2).ne']
  have hL2val : (L2 : ℝ) = lam * c := by
    rw [hL2]; exact hLc
  have hL0val : (L0 : ℝ) = 2 * lam := by
    rw [hL0]
    have h0 : dist (D.target.pts 0) (D.target.pts (0 + 1)) = D.target.oppLen 2 := rfl
    rw [h0, tt2, hLc]
    have : 2 * (lam * c) * Real.cos α = 2 * lam * (c * Real.cos α) := by ring
    have hb1' : D.model.oppLen 1 = 1 := hb1
    rw [this, ← sb, hb1']; ring
  -- ψ-values of the two side lengths
  have hψL2 : ψ L2 = -lam * ψ C := by
    have : L2 = Λ * C := Subtype.ext (by rw [hL2val]; rfl)
    rw [this, map_mul, hψΛ]
  have hψL0 : ψ L0 = -(2 * lam) := by
    have : L0 = Λ + Λ := Subtype.ext (by rw [hL0val]; exact two_mul lam)
    rw [this, map_add, hψΛ]; ring
  -- the walk equations, in the scale `b = 1`
  have hb1' : D.model.oppLen 1 = 1 := hb1
  have hAB : (P : ℝ) * a + (Q : ℝ) * 1 + (R : ℝ) * c = lam * c := by
    have h := hwalk2
    rw [hL2val] at h
    change (P : ℝ) * a + (Q : ℝ) * b + (R : ℝ) * c = _ at h
    rw [hb1] at h; exact h
  have hBC : (P₂ : ℝ) * a + (Q₂ : ℝ) * 1 + (R₂ : ℝ) * c = 2 * lam := by
    have h := hwalk0
    rw [hL0val] at h
    change (P₂ : ℝ) * a + (Q₂ : ℝ) * b + (R₂ : ℝ) * c = _ at h
    rw [hb1] at h; exact h
  -- sign rules
  have sAP' : P ≠ 0 → 0 < ψ A * (-lam * ψ C) := fun h => by have := sAP h; rwa [hψL2] at this
  have sAQ' : Q ≠ 0 → 0 < 1 * (-lam * ψ C) := fun h => by
    have := sAQ h; rwa [hψL2, hψB] at this
  have sAR' : R ≠ 0 → 0 < ψ C * (-lam * ψ C) := fun h => by have := sAR h; rwa [hψL2] at this
  have sBP' : P₂ ≠ 0 → 0 < ψ A * (-(2 * lam)) := fun h => by have := sBP h; rwa [hψL0] at this
  have sBQ' : Q₂ ≠ 0 → 0 < 1 * (-(2 * lam)) := fun h => by
    have := sBQ h; rwa [hψL0, hψB] at this
  have sBR' : R₂ ≠ 0 → 0 < ψ C * (-(2 * lam)) := fun h => by have := sBR h; rwa [hψL0] at this
  -- the corner facts
  have cornerB : (Q ≠ 0 ∧ R₂ ≠ 0) ∨ (R ≠ 0 ∧ Q₂ ≠ 0) := by
    obtain ⟨i, e, e', h | h⟩ := cornerB_fact hR
    · exact Or.inl ⟨exB ⟨i, e, h.1, h.2.1⟩, exC0 ⟨i, e', h.2.2.1, h.2.2.2⟩⟩
    · exact Or.inr ⟨exC ⟨i, e, h.1, h.2.1⟩, exB0 ⟨i, e', h.2.2.1, h.2.2.2⟩⟩
  have cornerA : P ≠ 0 ∨ R ≠ 0 := by
    obtain ⟨i, e, hon, h | h⟩ := cornerA_fact hR
    · exact Or.inl (exA ⟨i, e, hon, h⟩)
    · exact Or.inr (exC ⟨i, e, hon, h⟩)
  have hirr' : Irrational a := by
    have : a / b = a := by rw [hb1, div_one]
    rwa [this] at hirr
  exact caseD_core hF.hlam hF.hlam2 hirr' hAB sAP' sAQ' sAR' hBC sBP' sBQ' sBR' cornerB cornerA

end Erdos634.Draft.H1eCL

#print axioms Erdos634.Draft.H1eCL.three_split
#print axioms Erdos634.Draft.H1eCL.side_full
#print axioms Erdos634.Draft.H1eCL.caseD_core
#print axioms Erdos634.Draft.H1eCL.rightCaseD_of_pieces
