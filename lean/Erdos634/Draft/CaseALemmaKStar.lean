-- Draft/CaseALemmaKStar.lean — CASE A, node A4: **Lemma K\*** (reduction to a sawtooth relation),
-- (private working notes, not included) §3.4, notation of the Paperwork block (l.470–480):
--
--   n ≥ 3; a ∈ ℤ≥1³, Σa = n; corner figures f_j ∈ ℤ≥0³ \ {0} with Σ_j f_j·a = n.  Then
--   [K1(k) ∧ K2(k) for all k ∈ (ℤ/n)^×] ⇔ [∀ k, s_T(k) = 1 ⇒ F·y(k) = 1] ⇔ e ∈ R(a).
--
-- K1/K2 are here *predicates on arithmetic data* (they are Lemma K's conclusion; K\* itself is a
-- standalone arithmetic lemma and takes no dissection).  `saw`, `relSpaceInt` (R(a) with integer
-- units, as written) are reused from CaseACorF / CaseACorFIntUnits, not redefined.
-- Formalization debt on a paper-level PROVED node; NOT /goal progress.  Imported into All.lean (All.lean:646).
import Erdos634.Draft.CaseACorFIntUnits

open scoped BigOperators

namespace Erdos634.LemmaKStar

open Erdos634.LemmaS

variable (n : ℕ) (a : Fin 3 → ℕ) (f : Fin 3 → Fin 3 → ℕ)

/-- y_i(k) = {k a_i / n}. -/
def yv (k : ℤ) (i : Fin 3) : ℚ := Int.fract (((k * (a i : ℤ) : ℤ) : ℚ) / n)
/-- s_T(k). -/
def sT (k : ℤ) : ℚ := ∑ i, yv n a k i
/-- u_j = f_j · a. -/
def uu (j : Fin 3) : ℕ := ∑ i, f j i * a i
/-- x_j(k) = {k u_j / n}. -/
def xv (k : ℤ) (j : Fin 3) : ℚ := Int.fract (((k * (uu a f j : ℤ) : ℤ) : ℚ) / n)
/-- s_ABC(k). -/
def sABC (k : ℤ) : ℚ := ∑ j, xv n a f k j
/-- x′(k)_i. -/
def xp (k : ℤ) (i : Fin 3) : ℚ := if sT n a k = 1 then yv n a k i else 1 - yv n a k i
/-- x′_{u_j}(k). -/
def xpu (k : ℤ) (j : Fin 3) : ℚ := if sT n a k = 1 then xv n a f k j else 1 - xv n a f k j
/-- K1(k): s_T(k) = s_ABC(k). -/
def K1 (k : ℤ) : Prop := sT n a k = sABC n a f k
/-- K2(k): f_j · x′(k) = x′_{u_j}(k) for j = 1, 2, 3. -/
def K2 (k : ℤ) : Prop := ∀ j, ∑ i, (f j i : ℚ) * xp n a k i = xpu n a f k j
/-- F = f₁ + f₂ + f₃. -/
def FF (i : Fin 3) : ℕ := ∑ j, f j i
/-- (K\*): for every unit k with s_T(k) = 1, F·y(k) = 1. -/
def KStar : Prop :=
  ∀ k : ℤ, Int.gcd k n = 1 → sT n a k = 1 → ∑ i, (FF f i : ℚ) * yv n a k i = 1
/-- d = F − (1,1,1). -/
def dv (i : Fin 3) : ℚ := (FF f i : ℚ) - 1
/-- δ = Σ d_i. -/
def δ : ℚ := ∑ i, dv f i
/-- e = d − δ(1,1,1). -/
def ev (i : Fin 3) : ℚ := dv f i - δ f

/-! ## Arithmetic facts -/

variable {n a f}

theorem a_lt (hsum : ∑ i, a i = n) (ha : ∀ i, 1 ≤ a i) (i : Fin 3) : a i < n := by
  have h0 := ha 0; have h1 := ha 1; have h2 := ha 2
  rw [Fin.sum_univ_three] at hsum
  fin_cases i <;> simp <;> omega

theorem yv_ne (hsum : ∑ i, a i = n) (ha : ∀ i, 1 ≤ a i) {k : ℤ} (hk : Int.gcd k n = 1)
    (i : Fin 3) : yv n a k i ≠ 0 := by
  intro h
  unfold yv at h
  have hn : (0 : ℚ) < n := by
    have := a_lt hsum ha i; exact_mod_cast (show 0 < n by omega)
  set x : ℚ := (((k * (a i : ℤ) : ℤ) : ℚ) / n)
  have hx : x = ⌊x⌋ := by have := Int.floor_add_fract x; rw [h] at this; linarith
  have hq : ((k * (a i : ℤ) : ℤ) : ℚ) = ((⌊x⌋ * (n : ℤ) : ℤ) : ℚ) := by
    have hxn : ((k * (a i : ℤ) : ℤ) : ℚ) = x * n := by simp only [x]; field_simp
    rw [hxn]; push_cast; rw [← hx]
  have hz : k * (a i : ℤ) = ⌊x⌋ * (n : ℤ) := by exact_mod_cast hq
  have hdvd : (n : ℤ) ∣ (a i : ℤ) * k := ⟨⌊x⌋, by rw [mul_comm, hz, mul_comm]⟩
  have hcop : IsCoprime (n : ℤ) k := by
    rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_comm]; exact hk
  have := Int.le_of_dvd (by have := ha i; omega) (hcop.dvd_of_dvd_mul_right hdvd)
  have := a_lt hsum ha i
  omega

theorem sum_raw (hsum : ∑ i, a i = n) (hn : 0 < n) (k : ℤ) :
    ∑ i, (((k * (a i : ℤ) : ℤ) : ℚ) / n) = k := by
  have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  have hs : ((a 0 : ℚ) + a 1 + a 2) = n := by
    rw [Fin.sum_univ_three] at hsum; exact_mod_cast hsum
  rw [Fin.sum_univ_three]; push_cast
  field_simp
  rw [hs]

theorem sT_int (hsum : ∑ i, a i = n) (hn : 0 < n) (k : ℤ) : ∃ z : ℤ, sT n a k = z := by
  refine ⟨k - ∑ i, ⌊(((k * (a i : ℤ) : ℤ) : ℚ) / n)⌋, ?_⟩
  unfold sT yv
  simp only [← Int.self_sub_floor, Finset.sum_sub_distrib, sum_raw hsum hn]
  push_cast; ring

theorem sT_12 (hsum : ∑ i, a i = n) (ha : ∀ i, 1 ≤ a i) {k : ℤ} (hk : Int.gcd k n = 1) :
    sT n a k = 1 ∨ sT n a k = 2 := by
  have hn : 0 < n := by have := a_lt hsum ha 0; omega
  obtain ⟨z, hz⟩ := sT_int hsum hn k
  have hpos : ∀ i, 0 < yv n a k i := fun i =>
    lt_of_le_of_ne (Int.fract_nonneg _) (Ne.symm (yv_ne hsum ha hk i))
  have hlt : ∀ i, yv n a k i < 1 := fun i => Int.fract_lt_one _
  have h1 : (0 : ℚ) < z := by
    rw [← hz]; unfold sT; rw [Fin.sum_univ_three]; linarith [hpos 0, hpos 1, hpos 2]
  have h2 : (z : ℚ) < 3 := by
    rw [← hz]; unfold sT; rw [Fin.sum_univ_three]; linarith [hlt 0, hlt 1, hlt 2]
  have h1' : 0 < z := by exact_mod_cast h1
  have h2' : z < 3 := by exact_mod_cast h2
  rw [hz]
  rcases (show z = 1 ∨ z = 2 by omega) with h | h <;> simp [h]

theorem gcd_neg' {k : ℤ} (hk : Int.gcd k n = 1) : Int.gcd (-k) n = 1 := by
  rwa [Int.neg_gcd]

theorem fract_neg_raw (m : ℤ) : (((-m : ℤ) : ℚ) / n) = -(((m : ℤ) : ℚ) / n) := by
  push_cast; ring

theorem yv_neg (hsum : ∑ i, a i = n) (ha : ∀ i, 1 ≤ a i) {k : ℤ} (hk : Int.gcd k n = 1)
    (i : Fin 3) : yv n a (-k) i = 1 - yv n a k i := by
  have := yv_ne hsum ha hk i
  unfold yv at this ⊢
  rw [neg_mul, fract_neg_raw, Int.fract_neg this]

theorem sT_neg (hsum : ∑ i, a i = n) (ha : ∀ i, 1 ≤ a i) {k : ℤ} (hk : Int.gcd k n = 1) :
    sT n a (-k) = 3 - sT n a k := by
  unfold sT; simp only [yv_neg hsum ha hk, Fin.sum_univ_three]; ring

/-- f_j · y(k). -/
def fy (n : ℕ) (a : Fin 3 → ℕ) (f : Fin 3 → Fin 3 → ℕ) (k : ℤ) (j : Fin 3) : ℚ :=
  ∑ i, (f j i : ℚ) * yv n a k i

theorem FF_dot (k : ℤ) : ∑ i, (FF f i : ℚ) * yv n a k i = ∑ j, fy n a f k j := by
  unfold FF fy; push_cast
  simp only [Finset.sum_mul]; rw [Finset.sum_comm]

theorem fy_pos (hsum : ∑ i, a i = n) (ha : ∀ i, 1 ≤ a i) (hf : ∀ j, f j ≠ 0) {k : ℤ}
    (hk : Int.gcd k n = 1) (j : Fin 3) : 0 < fy n a f k j := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp (hf j)
  have hy : ∀ i, 0 < yv n a k i := fun i =>
    lt_of_le_of_ne (Int.fract_nonneg _) (Ne.symm (yv_ne hsum ha hk i))
  apply Finset.sum_pos' (fun i _ => mul_nonneg (by positivity) (hy i).le)
  exact ⟨i, Finset.mem_univ _, mul_pos (by exact_mod_cast Nat.pos_of_ne_zero hi) (hy i)⟩

theorem fy_int (hn : 0 < n) (k : ℤ) (j : Fin 3) :
    ∃ z : ℤ, (((k * (uu a f j : ℤ) : ℤ) : ℚ) / n) - fy n a f k j = z := by
  refine ⟨∑ i, (f j i : ℤ) * ⌊(((k * (a i : ℤ) : ℤ) : ℚ) / n)⌋, ?_⟩
  have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  unfold fy yv uu
  simp only [← Int.self_sub_floor]
  push_cast
  simp only [Fin.sum_univ_three]
  field_simp; ring

/-- The core: s_T(k) = 1 and F·y(k) = 1 give x_j(k) = f_j·y(k) for every j. -/
theorem xv_eq_fy (hsum : ∑ i, a i = n) (ha : ∀ i, 1 ≤ a i) (hf : ∀ j, f j ≠ 0) {k : ℤ}
    (hk : Int.gcd k n = 1) (hF1 : ∑ j, fy n a f k j = 1) (j : Fin 3) :
    xv n a f k j = fy n a f k j := by
  have hn : 0 < n := by have := a_lt hsum ha 0; omega
  have hp := fy_pos hsum ha hf hk
  have hlt : fy n a f k j < 1 := by
    rw [Fin.sum_univ_three] at hF1
    fin_cases j <;> simp <;> linarith [hp 0, hp 1, hp 2]
  obtain ⟨z, hz⟩ := fy_int (f := f) hn k j
  unfold xv
  rw [Int.fract_eq_iff]
  exact ⟨(hp j).le, hlt, z, hz⟩

/-! ## Part 1: [K1 ∧ K2 for all units k] ⇔ (K\*) -/

theorem part1 (hsum : ∑ i, a i = n) (ha : ∀ i, 1 ≤ a i) (hf : ∀ j, f j ≠ 0) :
    (∀ k : ℤ, Int.gcd k n = 1 → K1 n a f k ∧ K2 n a f k) ↔ KStar n a f := by
  constructor
  · intro h k hk hs
    obtain ⟨h1, h2⟩ := h k hk
    rw [FF_dot]
    have : ∀ j, fy n a f k j = xv n a f k j := by
      intro j; have := h2 j; unfold xp xpu at this; simp only [hs, if_true] at this; exact this
    simp only [this]
    unfold K1 at h1; unfold sABC at h1; rw [← h1, hs]
  · intro hK k hk
    rcases sT_12 hsum ha hk with hs | hs
    · have hF1 : ∑ j, fy n a f k j = 1 := by rw [← FF_dot]; exact hK k hk hs
      have hx := xv_eq_fy hsum ha hf hk hF1
      refine ⟨?_, ?_⟩
      · unfold K1 sABC; simp only [hx]; rw [hF1, hs]
      · intro j; unfold xp xpu; simp only [hs, if_true]; exact (hx j).symm
    · have hk' := gcd_neg' hk
      have hs' : sT n a (-k) = 1 := by rw [sT_neg hsum ha hk, hs]; norm_num
      have hF1 : ∑ j, fy n a f (-k) j = 1 := by rw [← FF_dot]; exact hK (-k) hk' hs'
      have hx := xv_eq_fy hsum ha hf hk' hF1
      have hp := fy_pos hsum ha hf hk'
      -- x_j(−k) = 1 − x_j(k)
      have hneg : ∀ j, xv n a f (-k) j = 1 - xv n a f k j := by
        intro j
        have hne : xv n a f (-k) j ≠ 0 := by rw [hx j]; exact (hp j).ne'
        unfold xv at hne ⊢
        rw [neg_mul, fract_neg_raw] at hne ⊢
        rw [Int.fract_neg (fun h0 => hne (Int.fract_neg_eq_zero.mpr h0))]
      have hne1 : sT n a k ≠ 1 := by rw [hs]; norm_num
      refine ⟨?_, ?_⟩
      · unfold K1 sABC
        have : ∀ j, xv n a f k j = 1 - fy n a f (-k) j := by
          intro j; rw [← hx j, hneg j]; ring
        simp only [this, Fin.sum_univ_three] at hF1 ⊢
        rw [hs]; linarith
      · intro j
        unfold xp xpu; simp only [hne1, if_false]
        have e1 : ∑ i, (f j i : ℚ) * (1 - yv n a k i) = fy n a f (-k) j := by
          unfold fy; simp only [yv_neg hsum ha hk]
        rw [e1, ← hx j, hneg j]

/-! ## Part 2: (K\*) ⇔ e ∈ R(a) -/

/-- Σ e_i ((k a_i/n)) = F·y(k) − s_T(k) − δ(s_T(k) − 1). -/
theorem G_eq (hsum : ∑ i, a i = n) (ha : ∀ i, 1 ≤ a i) {k : ℤ} (hk : Int.gcd k n = 1) :
    ∑ i, saw (((k * (a i : ℤ) : ℤ) : ℚ) / n) * ev f i
      = ∑ i, (FF f i : ℚ) * yv n a k i - sT n a k - δ f * (sT n a k - 1) := by
  have hsaw : ∀ i, saw (((k * (a i : ℤ) : ℤ) : ℚ) / n) = yv n a k i - 1 / 2 := by
    intro i; unfold saw; rw [if_neg (show Int.fract ((((k * (a i : ℤ) : ℤ) : ℚ) / n)) ≠ 0 from yv_ne hsum ha hk i)]; rfl
  simp only [hsaw]
  unfold ev δ dv sT
  simp only [Fin.sum_univ_three]; ring

theorem part2 (hsum : ∑ i, a i = n) (ha : ∀ i, 1 ≤ a i) :
    KStar n a f ↔ ev f ∈ relSpaceInt n a := by
  rw [mem_relSpaceInt]
  constructor
  · intro hK k hk
    rw [G_eq hsum ha hk]
    rcases sT_12 hsum ha hk with hs | hs
    · rw [hK k hk hs, hs]; ring
    · have hk' := gcd_neg' hk
      have hs' : sT n a (-k) = 1 := by rw [sT_neg hsum ha hk, hs]; norm_num
      have h1 := hK (-k) hk' hs'
      have hy : ∀ i, yv n a k i = 1 - yv n a (-k) i := by
        intro i; rw [yv_neg hsum ha hk]; ring
      simp only [hy, Fin.sum_univ_three] at h1 ⊢
      rw [hs]; unfold δ dv; simp only [Fin.sum_univ_three]; linarith
  · intro hG k hk hs
    have := hG k hk
    rw [G_eq hsum ha hk, hs] at this
    linarith

/-! ## Lemma K\*, as written -/

/-- **Lemma K\*** (PROOF_row0c.md §3.4 / Paperwork table).  Hypotheses exactly as recorded:
n ≥ 3; a ∈ ℤ≥1³ with Σa = n; f_j ∈ ℤ≥0³ \ {0} with Σ_j f_j·a = n.  (gcd not used; `hn`, `hu`
are carried as written although the proof does not need them.) -/
theorem lemmaKStar (_hn : 3 ≤ n) (ha : ∀ i, 1 ≤ a i) (hsum : ∑ i, a i = n)
    (hf : ∀ j, f j ≠ 0) (_hu : ∑ j, uu a f j = n) :
    ((∀ k : ℤ, Int.gcd k n = 1 → K1 n a f k ∧ K2 n a f k) ↔ KStar n a f) ∧
    (KStar n a f ↔ ev f ∈ relSpaceInt n a) :=
  ⟨part1 hsum ha hf, part2 hsum ha⟩

/-- The form consumed downstream (A8 step 2 → Lemma S): Lemma K's conclusion ⇒ e ∈ R(a),
with R(a) as `relSpace` (ℕ-units, the form Lemma S / Corollary F use). -/
theorem lemmaKStar_toRel (hn : 3 ≤ n) (ha : ∀ i, 1 ≤ a i) (hsum : ∑ i, a i = n)
    (hf : ∀ j, f j ≠ 0) (hu : ∑ j, uu a f j = n)
    (hK : ∀ k : ℤ, Int.gcd k n = 1 → K1 n a f k ∧ K2 n a f k) : ev f ∈ relSpace n a := by
  have := (lemmaKStar hn ha hsum hf hu).2.mp ((lemmaKStar hn ha hsum hf hu).1.mp hK)
  rwa [relSpaceInt_eq (by omega)] at this

/-! ## Witness: tile (2,5,7)π/14, corner figures (1,0,0), (0,1,0), (1,1,0)  (§5: F = (2,2,0),
e = (0,0,−2) ∈ R₀).  Every hypothesis holds, and K1 ∧ K2 hold for every unit k. -/

def aW : Fin 3 → ℕ := ![2, 5, 7]
def fW : Fin 3 → Fin 3 → ℕ := ![![1, 0, 0], ![0, 1, 0], ![1, 1, 0]]

theorem witness_hyps :
    3 ≤ 14 ∧ (∀ i, 1 ≤ aW i) ∧ ∑ i, aW i = 14 ∧ (∀ j, fW j ≠ 0) ∧ ∑ j, uu aW fW j = 14 := by
  refine ⟨by norm_num, by decide, by decide, ?_, by decide⟩
  intro j h
  fin_cases j <;> [exact absurd (congrFun h 0) (by simp [fW]);
    exact absurd (congrFun h 1) (by simp [fW]); exact absurd (congrFun h 0) (by simp [fW])]

theorem witness_e : ev fW = (-2 : ℚ) • Pi.single 2 1 := by
  have h0 : FF fW 0 = 2 := by decide
  have h1 : FF fW 1 = 2 := by decide
  have h2 : FF fW 2 = 0 := by decide
  funext i
  fin_cases i <;> simp [ev, dv, δ, Fin.sum_univ_three, h0, h1, h2] <;> norm_num

theorem witness_mem : ev fW ∈ relSpaceInt 14 aW := by
  rw [relSpaceInt_eq (by norm_num)]
  apply trivSpace_le
  rw [witness_e]
  apply Submodule.smul_mem
  apply Submodule.subset_span
  right
  exact ⟨2, by decide, rfl⟩

/-- Lemma K's conclusion is satisfiable: on the witness, K1(k) ∧ K2(k) for every unit k. -/
theorem witness_K1K2 : ∀ k : ℤ, Int.gcd k 14 = 1 → K1 14 aW fW k ∧ K2 14 aW fW k := by
  obtain ⟨h3, ha, hs, hf, hu⟩ := witness_hyps
  exact (lemmaKStar h3 ha hs hf hu).1.mpr ((lemmaKStar h3 ha hs hf hu).2.mpr witness_mem)

/-! ## Negative control: tile (1,2,2)π/5 on a target with corner figures (1,0,0), (1,0,0),
(1,1,0) (angles (1,1,3)π/5, not similar).  e = (1,−1,−2) ∉ R(a) (k = 2 gives −1), so by K\*
Lemma K's conclusion FAILS for some unit k: the equivalence has teeth. -/

def aN : Fin 3 → ℕ := ![1, 2, 2]
def fN : Fin 3 → Fin 3 → ℕ := ![![1, 0, 0], ![1, 0, 0], ![1, 1, 0]]

theorem neg_hyps :
    3 ≤ 5 ∧ (∀ i, 1 ≤ aN i) ∧ ∑ i, aN i = 5 ∧ (∀ j, fN j ≠ 0) ∧ ∑ j, uu aN fN j = 5 := by
  refine ⟨by norm_num, by decide, by decide, ?_, by decide⟩
  intro j h
  fin_cases j <;> exact absurd (congrFun h 0) (by simp [fN])

theorem neg_not_mem : ev fN ∉ relSpaceInt 5 aN := by
  rw [mem_relSpaceInt]
  intro h
  have := h 2 (by decide)
  have h0 : FF fN 0 = 3 := by decide
  have h1 : FF fN 1 = 1 := by decide
  have h2 : FF fN 2 = 0 := by decide
  have hd : δ fN = 1 := by simp [δ, dv, Fin.sum_univ_three, h0, h1, h2]
  have e0 : ev fN 0 = 1 := by simp [ev, dv, hd, h0]; norm_num
  have e1 : ev fN 1 = -1 := by simp [ev, dv, hd, h1]
  have e2 : ev fN 2 = -2 := by simp [ev, dv, hd, h2]; norm_num
  have a0 : aN 0 = 1 := rfl
  have a1 : aN 1 = 2 := rfl
  have a2 : aN 2 = 2 := rfl
  have s1 : saw ((((2 : ℤ) * ((1 : ℕ) : ℤ) : ℤ) : ℚ) / ((5 : ℕ) : ℚ)) = -1 / 10 := by
    unfold saw; norm_num
  have s2 : saw ((((2 : ℤ) * ((2 : ℕ) : ℤ) : ℤ) : ℚ) / ((5 : ℕ) : ℚ)) = 3 / 10 := by
    unfold saw; norm_num
  rw [Fin.sum_univ_three, e0, e1, e2, a0, a1, a2, s1, s2] at this
  norm_num at this

theorem neg_control : ¬ ∀ k : ℤ, Int.gcd k 5 = 1 → K1 5 aN fN k ∧ K2 5 aN fN k := by
  obtain ⟨h3, ha, hs, hf, hu⟩ := neg_hyps
  intro hK
  exact neg_not_mem ((lemmaKStar h3 ha hs hf hu).2.mp ((lemmaKStar h3 ha hs hf hu).1.mp hK))

end Erdos634.LemmaKStar

#print axioms Erdos634.LemmaKStar.lemmaKStar
#print axioms Erdos634.LemmaKStar.lemmaKStar_toRel
#print axioms Erdos634.LemmaKStar.witness_K1K2
#print axioms Erdos634.LemmaKStar.neg_control
