-- Draft/LemmaPProof.lean — **C3 (Lemma P): π/3 tile with IrrPi α forces equilateral target**
--
-- `LemmaPStatement`: SixtyData tile (α, 2π/3−α, π/3), IrrPi α, ¬SimilarTM → Equilateral D
--
-- Strategy: sum local angles at target vertices, apply angle_indep to extract integer
-- constraints, case-split: s23=0 forces equilateral; s23=1 gives SimilarTM (proved; no sorry remains, 2026-09-30).
--
-- Imported directly by All.lean (stale "NOT imported" header corrected 2026-10-04) (Draft file).
import Erdos634.Draft.TheoremPConditional
import Erdos634.VertexFigureReal
import Erdos634.RouteOneVertexKill
import Erdos634.Draft.FluxCRow12

open scoped Classical
namespace Erdos634.Draft.LemmaPProof

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.Draft.TheoremPConditional
open Erdos634.VertexFigureReal Erdos634.RouteOneVertexKill

/-! ## Distinctness of SixtyData tile angles under IrrPi -/

lemma irrPi_ne_pi_third {α : ℝ} (hα : IrrPi α) : α ≠ Real.pi / 3 := fun h =>
  hα ⟨1/3, by rw [h]; ring⟩

lemma irrPi_ne_two_thirds_minus {α : ℝ} (hα : IrrPi α) : α ≠ 2 * Real.pi / 3 - α := fun h =>
  hα ⟨1/3, by linarith⟩

lemma irrPi_ne_zero {α : ℝ} (hα : IrrPi α) : α ≠ 0 := fun h =>
  hα ⟨0, by rw [h]; ring⟩

lemma pi_third_ne_two_thirds_minus {α : ℝ} (hα : IrrPi α) : Real.pi / 3 ≠ 2 * Real.pi / 3 - α :=
  fun h => hα ⟨1/3, by linarith⟩

lemma pi_third_ne_zero : Real.pi / 3 ≠ 0 :=
  div_ne_zero Real.pi_ne_zero (by norm_num)

lemma two_thirds_minus_ne_zero {α : ℝ} (hα : IrrPi α) : 2 * Real.pi / 3 - α ≠ 0 := fun h =>
  hα ⟨2/3, by linarith⟩

/-! ## Tile corner angles ∈ {α, 2π/3−α, π/3} -/

lemma sixtyData_cornerAngle_mem {N : ℕ} (D : CongruentDissection N) {α a b c : ℝ}
    (hd : D.model.SixtyData α a b c) (i : Fin N) (j : Fin 3) :
    cornerAngle ((D.tile i).pts (j + 1)) ((D.tile i).pts j) ((D.tile i).pts (j + 2))
      ∈ ({α, 2 * Real.pi / 3 - α, Real.pi / 3} : Finset ℝ) := by
  classical
  obtain ⟨σ, hσ0, -, hσ1, -, hσ2, -⟩ := hd
  obtain ⟨k, hk⟩ := congruent_corner_angles (D.tiles_congruent i).symm j
  rw [hk]; obtain ⟨m, rfl⟩ := σ.surjective k
  fin_cases m <;> simp only [Finset.mem_insert, Finset.mem_singleton]
  · exact Or.inl hσ0
  · exact Or.inr (Or.inl hσ1)
  · exact Or.inr (Or.inr hσ2)

/-! ## localAngle at target vertex ∈ {α, 2π/3−α, π/3, 0} -/

lemma localAngle_at_vertex_mem {N : ℕ} (D : CongruentDissection N) {α a b c : ℝ}
    (hd : D.model.SixtyData α a b c) (k : Fin 3) (i : Fin N) :
    (D.tile i).localAngle (D.target.pts k)
      ∈ ({α, 2 * Real.pi / 3 - α, Real.pi / 3, 0} : Finset ℝ) := by
  classical
  have hcas := corner_angle_sum D.toDissection k
  have hlt := cornerAngle_lt_pi D.target k
  have hnneg : ∀ m : Fin N, 0 ≤ (D.tile m).localAngle (D.target.pts k) :=
    fun m => (D.tile m).localAngle_nonneg _
  rcases Erdos634.PinPlumbing.localAngle_cases (D.tile i) (D.target.pts k) with
    ⟨j, _, hval⟩ | h2pi | hpi | h0
  · rw [hval]
    have hcm := sixtyData_cornerAngle_mem D hd i j
    simp only [Finset.mem_insert, Finset.mem_singleton] at hcm ⊢; tauto
  · exfalso
    have hge2 : 2 * Real.pi ≤ ∑ i, (D.tile i).localAngle (D.target.pts k) :=
      h2pi.symm.le.trans (Finset.single_le_sum (fun m _ => hnneg m) (Finset.mem_univ i))
    linarith [hge2.trans_eq hcas, hlt, Real.pi_pos]
  · exfalso
    have hge1 : Real.pi ≤ ∑ i, (D.tile i).localAngle (D.target.pts k) :=
      hpi.symm.le.trans (Finset.single_le_sum (fun m _ => hnneg m) (Finset.mem_univ i))
    linarith [hge1.trans_eq hcas, hlt, Real.pi_pos]
  · simp [h0]

/-! ## Per-vertex angle multiplicity equation -/

-- Uses `{i : Fin N | ...} : Finset (Fin N)` to match `sum_by_value`'s output.
noncomputable def multOf {N : ℕ} (D : CongruentDissection N) (v : ℝ) (k : Fin 3) : ℕ :=
  ({i : Fin N | (D.tile i).localAngle (D.target.pts k) = v} : Finset (Fin N)).card

lemma per_vertex_eq {N : ℕ} (D : CongruentDissection N) {α a b c : ℝ}
    (hα : IrrPi α) (hd : D.model.SixtyData α a b c) (k : Fin 3) :
    D.target.angleAt k = (multOf D α k : ℝ) * α +
      (multOf D (2 * Real.pi / 3 - α) k : ℝ) * (2 * Real.pi / 3 - α) +
      (multOf D (Real.pi / 3) k : ℝ) * (Real.pi / 3) := by
  classical
  have hcas := corner_angle_sum D.toDissection k
  rw [show cornerAngle (D.target.pts (k + 1)) (D.target.pts k) (D.target.pts (k + 2))
      = D.target.angleAt k from rfl] at hcas
  have hmem : ∀ i, (D.tile i).localAngle (D.target.pts k) ∈
      ({α, 2 * Real.pi / 3 - α, Real.pi / 3, 0} : Finset ℝ) :=
    fun i => localAngle_at_vertex_mem D hd k i
  rw [sum_by_value _ _ hmem] at hcas
  -- hcas : ∑ v ∈ {α,23,13,0}, {i|..=v}.card * v = angleAt k
  rw [← hcas]
  -- goal : ∑ v ∈ {α,23,13,0}, {i|..=v}.card * v = multOf * α + multOf * 23 + multOf * 13
  have hα23 : α ∉ ({2 * Real.pi / 3 - α, Real.pi / 3, 0} : Finset ℝ) := by
    simp [irrPi_ne_two_thirds_minus hα, irrPi_ne_pi_third hα, irrPi_ne_zero hα]
  have h23_rest : 2 * Real.pi / 3 - α ∉ ({Real.pi / 3, 0} : Finset ℝ) := by
    intro h
    simp only [Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with h1 | h2
    · exact pi_third_ne_two_thirds_minus hα h1.symm
    · exact two_thirds_minus_ne_zero hα h2
  have h13_0 : Real.pi / 3 ∉ ({0} : Finset ℝ) := by simp [pi_third_ne_zero]
  simp only [show ({α, 2 * Real.pi / 3 - α, Real.pi / 3, 0} : Finset ℝ) =
      insert α (insert (2 * Real.pi / 3 - α) (insert (Real.pi / 3) {0})) from rfl,
    Finset.sum_insert hα23, Finset.sum_insert h23_rest, Finset.sum_insert h13_0,
    Finset.sum_singleton, mul_zero, add_zero, multOf]
  ring

/-! ## Triangle angle sum -/

lemma target_angle_sum {N : ℕ} (D : CongruentDissection N) :
    D.target.angleAt 0 + D.target.angleAt 1 + D.target.angleAt 2 = Real.pi := by
  show cornerAngle (D.target.pts 1) (D.target.pts 0) (D.target.pts 2) +
       cornerAngle (D.target.pts 2) (D.target.pts 1) (D.target.pts 0) +
       cornerAngle (D.target.pts 0) (D.target.pts 2) (D.target.pts 1) = Real.pi
  exact Erdos634.Geometry.cornerAngle_sum D.target

/-! ## Main theorem -/

theorem lemmaPStatement : LemmaPStatement := by
  unfold LemmaPStatement
  intro N D hNp h4 h3 α a b c hα hd hB
  unfold Equilateral; intro k; classical
  -- Per-vertex equations
  have hpv0 := per_vertex_eq D hα hd 0
  have hpv1 := per_vertex_eq D hα hd 1
  have hpv2 := per_vertex_eq D hα hd 2
  have hpi := target_angle_sum D
  -- Abbreviations for total multiplicities (as ℤ for angle_indep)
  let SA : ℤ := (multOf D α 0 : ℤ) + multOf D α 1 + multOf D α 2
  let S23 : ℤ := (multOf D (2 * Real.pi / 3 - α) 0 : ℤ) +
    multOf D (2 * Real.pi / 3 - α) 1 + multOf D (2 * Real.pi / 3 - α) 2
  let S13 : ℤ := (multOf D (Real.pi / 3) 0 : ℤ) +
    multOf D (Real.pi / 3) 1 + multOf D (Real.pi / 3) 2
  -- Global angle equation
  have hglobal : (SA : ℝ) * α + (S23 : ℝ) * (2 * Real.pi / 3 - α) +
      (S13 : ℝ) * (Real.pi / 3) = Real.pi := by
    simp only [SA, S23, S13]; push_cast; linarith
  -- Apply angle_indep: 3*(SA-S23)*α + (2*S23+S13-3)*π = 0
  obtain ⟨hA, hB'⟩ := Erdos634.Geometry.angle_indep hα
    (3 * (SA - S23)) (2 * S23 + S13 - 3)
    (by simp only [SA, S23, S13]; push_cast; linarith)
  -- Deduce SA = S23 and 2*S23+S13 = 3
  have heqA : SA = S23 := by omega
  have hsum3 : 2 * S23 + S13 = 3 := by omega
  -- s23_total ≤ 1
  have hs23_nn : 0 ≤ S23 := by
    simp only [S23]; positivity
  have hs23_le1 : S23 ≤ 1 := by omega
  -- Case split on s23_total: either 0 or 1
  have hS23_cases : S23 = 0 ∨ S23 = 1 := by omega
  rcases hS23_cases with hs0 | hs1
  · -- Case S23 = 0 → SA = 0, S13 = 3: equilateral
    have hSA0 : SA = 0 := by omega
    have hS130 : S13 = 3 := by omega
    -- All α and 23 multiplicities are 0
    -- All α and 23 multiplicities are 0: their ℤ sums are 0 and all terms ≥ 0
    have hSA_exp : (multOf D α 0 : ℤ) + multOf D α 1 + multOf D α 2 = 0 := by
      have h : SA = 0 := hSA0; simp only [SA] at h; exact h
    have hS23_exp : (multOf D (2 * Real.pi / 3 - α) 0 : ℤ) +
        multOf D (2 * Real.pi / 3 - α) 1 + multOf D (2 * Real.pi / 3 - α) 2 = 0 := by
      have h : S23 = 0 := hs0; simp only [S23] at h; exact h
    have hmα : ∀ j : Fin 3, multOf D α j = 0 := by
      have hsum : multOf D α 0 + multOf D α 1 + multOf D α 2 = 0 := by exact_mod_cast hSA_exp
      have e0 : multOf D α 0 = 0 := by omega
      have e1 : multOf D α 1 = 0 := by omega
      have e2 : multOf D α 2 = 0 := by omega
      intro j; fin_cases j; exact e0; exact e1; exact e2
    have hm23 : ∀ j : Fin 3, multOf D (2 * Real.pi / 3 - α) j = 0 := by
      have hsum : multOf D (2 * Real.pi / 3 - α) 0 + multOf D (2 * Real.pi / 3 - α) 1 +
          multOf D (2 * Real.pi / 3 - α) 2 = 0 := by exact_mod_cast hS23_exp
      have e0 : multOf D (2 * Real.pi / 3 - α) 0 = 0 := by omega
      have e1 : multOf D (2 * Real.pi / 3 - α) 1 = 0 := by omega
      have e2 : multOf D (2 * Real.pi / 3 - α) 2 = 0 := by omega
      intro j; fin_cases j; exact e0; exact e1; exact e2
    -- Per-vertex: angleAt v = n13_v * (π/3)
    have ha : ∀ j : Fin 3, D.target.angleAt j = (multOf D (Real.pi / 3) j : ℝ) * (Real.pi / 3) := by
      intro j
      have hpv := per_vertex_eq D hα hd j
      have hαj : multOf D α j = 0 := hmα j
      have h23j : multOf D (2 * Real.pi / 3 - α) j = 0 := hm23 j
      rw [hpv, hαj, h23j]; push_cast; ring
    -- n13_j = 1 for each j
    have hn13_each : ∀ j : Fin 3, multOf D (Real.pi / 3) j = 1 := by
      have hpos : ∀ j : Fin 3, 1 ≤ multOf D (Real.pi / 3) j := by
        intro j; by_contra hlt; push_neg at hlt
        have hj0 : multOf D (Real.pi / 3) j = 0 := Nat.lt_one_iff.mp hlt
        have hay := ha j; rw [hj0] at hay; push_cast at hay
        linarith [Tri.angleAt_pos' D.target j]
      have htot' : multOf D (Real.pi / 3) 0 + multOf D (Real.pi / 3) 1 +
          multOf D (Real.pi / 3) 2 = 3 := by
        have h : S13 = 3 := hS130; simp only [S13] at h; exact_mod_cast h
      have h0 := hpos 0; have h1 := hpos 1; have h2 := hpos 2
      -- Prove each component directly (avoid fin_cases changing Fin representation for omega)
      have e0 : multOf D (Real.pi / 3) 0 = 1 := by omega
      have e1 : multOf D (Real.pi / 3) 1 = 1 := by omega
      have e2 : multOf D (Real.pi / 3) 2 = 1 := by omega
      intro j; fin_cases j
      · exact e0
      · exact e1
      · exact e2
    -- Conclude angleAt k = π/3
    have hk := ha k; rw [hn13_each k] at hk; push_cast at hk; linarith
  · -- Case S23 = 1: construct SimilarTM D (contradicts hB)
    exfalso; apply hB
    -- SA = S23 = S13 = 1
    have hSA1 : SA = 1 := heqA.trans hs1
    have hS131 : S13 = 1 := by omega
    -- Cast to ℕ
    have hα_n : multOf D α 0 + multOf D α 1 + multOf D α 2 = 1 := by
      have h : SA = 1 := hSA1; simp only [SA] at h; exact_mod_cast h
    have h23_n : multOf D (2*Real.pi/3-α) 0 + multOf D (2*Real.pi/3-α) 1 +
        multOf D (2*Real.pi/3-α) 2 = 1 := by
      have h : S23 = 1 := hs1; simp only [S23] at h; exact_mod_cast h
    have h13_n : multOf D (Real.pi/3) 0 + multOf D (Real.pi/3) 1 +
        multOf D (Real.pi/3) 2 = 1 := by
      have h : S13 = 1 := hS131; simp only [S13] at h; exact_mod_cast h
    -- Each vertex has exactly one angle type
    have hT_pos : ∀ j : Fin 3, 0 < multOf D α j + multOf D (2*Real.pi/3-α) j + multOf D (Real.pi/3) j := by
      intro j; by_contra hc; push_neg at hc
      have h0 : multOf D α j = 0 := by omega
      have h1 : multOf D (2*Real.pi/3-α) j = 0 := by omega
      have h2 : multOf D (Real.pi/3) j = 0 := by omega
      have := per_vertex_eq D hα hd j; rw [h0, h1, h2] at this; push_cast at this
      linarith [Tri.angleAt_pos' D.target j]
    have hTe0 : multOf D α 0 + multOf D (2*Real.pi/3-α) 0 + multOf D (Real.pi/3) 0 = 1 := by
      have p0 := hT_pos 0; have p1 := hT_pos 1; have p2 := hT_pos 2; omega
    have hTe1 : multOf D α 1 + multOf D (2*Real.pi/3-α) 1 + multOf D (Real.pi/3) 1 = 1 := by
      have p0 := hT_pos 0; have p1 := hT_pos 1; have p2 := hT_pos 2; omega
    have hTe2 : multOf D α 2 + multOf D (2*Real.pi/3-α) 2 + multOf D (Real.pi/3) 2 = 1 := by
      have p0 := hT_pos 0; have p1 := hT_pos 1; have p2 := hT_pos 2; omega
    -- Per-vertex angle value (which angle type is at each vertex)
    have hpv_val : ∀ j : Fin 3,
        (multOf D α j = 1 → D.target.angleAt j = α) ∧
        (multOf D (2*Real.pi/3-α) j = 1 → D.target.angleAt j = 2*Real.pi/3-α) ∧
        (multOf D (Real.pi/3) j = 1 → D.target.angleAt j = Real.pi/3) := by
      intro j
      have hTj : multOf D α j + multOf D (2*Real.pi/3-α) j + multOf D (Real.pi/3) j = 1 := by
        fin_cases j; exact hTe0; exact hTe1; exact hTe2
      have hpv := per_vertex_eq D hα hd j
      refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
      · have h1 : multOf D (2*Real.pi/3-α) j = 0 := by omega
        have h2 : multOf D (Real.pi/3) j = 0 := by omega
        rw [hpv, h, h1, h2]; push_cast; ring
      · have h0 : multOf D α j = 0 := by omega
        have h2 : multOf D (Real.pi/3) j = 0 := by omega
        rw [hpv, h0, h, h2]; push_cast; ring
      · have h0 : multOf D α j = 0 := by omega
        have h1 : multOf D (2*Real.pi/3-α) j = 0 := by omega
        rw [hpv, h0, h1, h]; push_cast; ring
    -- Model σ from SixtyData
    obtain ⟨σ, hσα, hσα_len, hσ23, hσ23_len, hσ13, hσ13_len⟩ := hd
    -- oppLen ratio helper: sin cancels to give oppLen ratio equality
    have oppLen_ratio : ∀ (τ : Equiv.Perm (Fin 3)) (k : Fin 3),
        (∀ j : Fin 3, D.target.angleAt j = D.model.angleAt (τ j)) →
        D.target.oppLen k * D.model.oppLen (τ 0) = D.target.oppLen 0 * D.model.oppLen (τ k) := by
      intro τ k hangle
      have hls_t : Real.sin (D.model.angleAt (τ 0)) * D.target.oppLen k =
          Real.sin (D.model.angleAt (τ k)) * D.target.oppLen 0 := by
        have := Tri.lawSin D.target 0 k; rw [hangle 0, hangle k] at this; exact this
      have hls_m : Real.sin (D.model.angleAt (τ 0)) * D.model.oppLen (τ k) =
          Real.sin (D.model.angleAt (τ k)) * D.model.oppLen (τ 0) :=
        Tri.lawSin D.model (τ 0) (τ k)
      have hsin0 : 0 < Real.sin (D.model.angleAt (τ 0)) :=
        Real.sin_pos_of_pos_of_lt_pi (Tri.angleAt_pos' D.model (τ 0)) (cornerAngle_lt_pi D.model (τ 0))
      have step : Real.sin (D.model.angleAt (τ 0)) * (D.target.oppLen k * D.model.oppLen (τ 0)) =
          Real.sin (D.model.angleAt (τ 0)) * (D.target.oppLen 0 * D.model.oppLen (τ k)) :=
        calc Real.sin (D.model.angleAt (τ 0)) * (D.target.oppLen k * D.model.oppLen (τ 0))
            = Real.sin (D.model.angleAt (τ 0)) * D.target.oppLen k * D.model.oppLen (τ 0) := by ring
          _ = Real.sin (D.model.angleAt (τ k)) * D.target.oppLen 0 * D.model.oppLen (τ 0) := by rw [hls_t]
          _ = D.target.oppLen 0 * (Real.sin (D.model.angleAt (τ k)) * D.model.oppLen (τ 0)) := by ring
          _ = D.target.oppLen 0 * (Real.sin (D.model.angleAt (τ 0)) * D.model.oppLen (τ k)) := by rw [hls_m]
          _ = Real.sin (D.model.angleAt (τ 0)) * (D.target.oppLen 0 * D.model.oppLen (τ k)) := by ring
      exact mul_left_cancel₀ (ne_of_gt hsin0) step
    -- Construct SimilarTM by case-splitting on which vertex has α
    have hα_case : (multOf D α 0 = 1 ∧ multOf D α 1 = 0 ∧ multOf D α 2 = 0) ∨
        (multOf D α 0 = 0 ∧ multOf D α 1 = 1 ∧ multOf D α 2 = 0) ∨
        (multOf D α 0 = 0 ∧ multOf D α 1 = 0 ∧ multOf D α 2 = 1) := by omega
    -- For each α case, determine 23 case and build τ
    have build_similar : ∀ (τ : Equiv.Perm (Fin 3)),
        (∀ j : Fin 3, D.target.angleAt j = D.model.angleAt (τ j)) → SimilarTM D := by
      intro τ hangle
      exact ⟨D.target.oppLen 0 / D.model.oppLen (τ 0), τ, fun k => ⟨hangle k, by
        rcases Nat.eq_zero_or_pos k.val with hk | hk
        · have : k = 0 := by ext; exact hk
          subst this; simp [div_mul_cancel₀, ne_of_gt (Tri.oppLen_pos D.model (τ 0))]
        · have hrat := oppLen_ratio τ k hangle
          have hpos := Tri.oppLen_pos D.model (τ 0)
          field_simp [ne_of_gt hpos]; linarith [hrat]⟩⟩
    rcases hα_case with ⟨hα0, hα10, hα20⟩ | ⟨hα00, hα1, hα20⟩ | ⟨hα00, hα10, hα2⟩
    · -- α at vertex 0
      have h23_02 : multOf D (2*Real.pi/3-α) 0 = 0 := by have := hTe0; omega
      have h13_02 : multOf D (Real.pi/3) 0 = 0 := by have := hTe0; omega
      have h23_case : (multOf D (2*Real.pi/3-α) 1 = 1 ∧ multOf D (2*Real.pi/3-α) 2 = 0) ∨
          (multOf D (2*Real.pi/3-α) 1 = 0 ∧ multOf D (2*Real.pi/3-α) 2 = 1) := by omega
      rcases h23_case with ⟨h231, h232⟩ | ⟨h231, h232⟩
      · -- α@0, 23@1, 13@2
        have h13_2 : multOf D (Real.pi/3) 2 = 1 := by have := hTe2; omega
        have hta0 := (hpv_val 0).1 hα0
        have hta1 := (hpv_val 1).2.1 h231
        have hta2 := (hpv_val 2).2.2 h13_2
        exact build_similar σ (fun k => by
          fin_cases k
          · simp [hta0, hσα]
          · simp [hta1, hσ23]
          · simp [hta2, hσ13])
      · -- α@0, 23@2, 13@1  →  τ = (swap 1 2).trans σ: τ0=σ0, τ1=σ2, τ2=σ1
        have h13_1 : multOf D (Real.pi/3) 1 = 1 := by have := hTe1; omega
        have hta0 := (hpv_val 0).1 hα0
        have hta1 := (hpv_val 1).2.2 h13_1
        have hta2 := (hpv_val 2).2.1 h232
        exact build_similar ((Equiv.swap (1:Fin 3) 2).trans σ) (fun k => by
          fin_cases k
          · change D.target.angleAt 0 = D.model.angleAt (σ 0); rw [hta0, hσα]
          · change D.target.angleAt 1 = D.model.angleAt (σ 2); rw [hta1, hσ13]
          · change D.target.angleAt 2 = D.model.angleAt (σ 1); rw [hta2, hσ23])
    · -- α at vertex 1
      have h23_12 : multOf D (2*Real.pi/3-α) 1 = 0 := by have := hTe1; omega
      have h13_12 : multOf D (Real.pi/3) 1 = 0 := by have := hTe1; omega
      have h23_case : (multOf D (2*Real.pi/3-α) 0 = 1 ∧ multOf D (2*Real.pi/3-α) 2 = 0) ∨
          (multOf D (2*Real.pi/3-α) 0 = 0 ∧ multOf D (2*Real.pi/3-α) 2 = 1) := by omega
      rcases h23_case with ⟨h230, h232⟩ | ⟨h230, h232⟩
      · -- α@1, 23@0, 13@2  →  τ = (swap 0 1).trans σ: τ0=σ1, τ1=σ0, τ2=σ2
        have h13_2 : multOf D (Real.pi/3) 2 = 1 := by have := hTe2; omega
        have hta0 := (hpv_val 0).2.1 h230
        have hta1 := (hpv_val 1).1 hα1
        have hta2 := (hpv_val 2).2.2 h13_2
        exact build_similar ((Equiv.swap (0:Fin 3) 1).trans σ) (fun k => by
          fin_cases k
          · change D.target.angleAt 0 = D.model.angleAt (σ 1); rw [hta0, hσ23]
          · change D.target.angleAt 1 = D.model.angleAt (σ 0); rw [hta1, hσα]
          · change D.target.angleAt 2 = D.model.angleAt (σ 2); rw [hta2, hσ13])
      · -- α@1, 23@2, 13@0  →  τ = ((swap 0 2).trans (swap 0 1)).trans σ: τ0=σ2, τ1=σ0, τ2=σ1
        have h13_0 : multOf D (Real.pi/3) 0 = 1 := by have := hTe0; omega
        have hta0 := (hpv_val 0).2.2 h13_0
        have hta1 := (hpv_val 1).1 hα1
        have hta2 := (hpv_val 2).2.1 h232
        exact build_similar (((Equiv.swap (0:Fin 3) 2).trans (Equiv.swap 0 1)).trans σ) (fun k => by
          fin_cases k
          · change D.target.angleAt 0 = D.model.angleAt (σ 2); rw [hta0, hσ13]
          · change D.target.angleAt 1 = D.model.angleAt (σ 0); rw [hta1, hσα]
          · change D.target.angleAt 2 = D.model.angleAt (σ 1); rw [hta2, hσ23])
    · -- α at vertex 2
      have h23_22 : multOf D (2*Real.pi/3-α) 2 = 0 := by have := hTe2; omega
      have h13_22 : multOf D (Real.pi/3) 2 = 0 := by have := hTe2; omega
      have h23_case : (multOf D (2*Real.pi/3-α) 0 = 1 ∧ multOf D (2*Real.pi/3-α) 1 = 0) ∨
          (multOf D (2*Real.pi/3-α) 0 = 0 ∧ multOf D (2*Real.pi/3-α) 1 = 1) := by omega
      rcases h23_case with ⟨h230, h231⟩ | ⟨h230, h231⟩
      · -- α@2, 23@0, 13@1  →  τ = ((swap 0 1).trans (swap 0 2)).trans σ: τ0=σ1, τ1=σ2, τ2=σ0
        have h13_1 : multOf D (Real.pi/3) 1 = 1 := by have := hTe1; omega
        have hta0 := (hpv_val 0).2.1 h230
        have hta1 := (hpv_val 1).2.2 h13_1
        have hta2 := (hpv_val 2).1 hα2
        exact build_similar (((Equiv.swap (0:Fin 3) 1).trans (Equiv.swap 0 2)).trans σ) (fun k => by
          fin_cases k
          · change D.target.angleAt 0 = D.model.angleAt (σ 1); rw [hta0, hσ23]
          · change D.target.angleAt 1 = D.model.angleAt (σ 2); rw [hta1, hσ13]
          · change D.target.angleAt 2 = D.model.angleAt (σ 0); rw [hta2, hσα])
      · -- α@2, 23@1, 13@0  →  τ = (swap 0 2).trans σ: τ0=σ2, τ1=σ1, τ2=σ0
        have h13_0 : multOf D (Real.pi/3) 0 = 1 := by have := hTe0; omega
        have hta0 := (hpv_val 0).2.2 h13_0
        have hta1 := (hpv_val 1).2.1 h231
        have hta2 := (hpv_val 2).1 hα2
        exact build_similar ((Equiv.swap (0:Fin 3) 2).trans σ) (fun k => by
          fin_cases k
          · change D.target.angleAt 0 = D.model.angleAt (σ 2); rw [hta0, hσ13]
          · change D.target.angleAt 1 = D.model.angleAt (σ 1); rw [hta1, hσ23]
          · change D.target.angleAt 2 = D.model.angleAt (σ 0); rw [hta2, hσα])

/-- **Lemma P without the primality binders** (2026-09-30, room ALLN): the proof never used
`N.Prime`, `N % 4 = 3`, `3 < N`.  For every `N`. -/
theorem lemmaP_general {N : ℕ} (D : CongruentDissection N) (α a b c : ℝ) (hα : IrrPi α)
    (hd : D.model.SixtyData α a b c) (hB : ¬ SimilarTM D) : Equilateral D := by
  unfold Equilateral; intro k; classical
  -- Per-vertex equations
  have hpv0 := per_vertex_eq D hα hd 0
  have hpv1 := per_vertex_eq D hα hd 1
  have hpv2 := per_vertex_eq D hα hd 2
  have hpi := target_angle_sum D
  -- Abbreviations for total multiplicities (as ℤ for angle_indep)
  let SA : ℤ := (multOf D α 0 : ℤ) + multOf D α 1 + multOf D α 2
  let S23 : ℤ := (multOf D (2 * Real.pi / 3 - α) 0 : ℤ) +
    multOf D (2 * Real.pi / 3 - α) 1 + multOf D (2 * Real.pi / 3 - α) 2
  let S13 : ℤ := (multOf D (Real.pi / 3) 0 : ℤ) +
    multOf D (Real.pi / 3) 1 + multOf D (Real.pi / 3) 2
  -- Global angle equation
  have hglobal : (SA : ℝ) * α + (S23 : ℝ) * (2 * Real.pi / 3 - α) +
      (S13 : ℝ) * (Real.pi / 3) = Real.pi := by
    simp only [SA, S23, S13]; push_cast; linarith
  -- Apply angle_indep: 3*(SA-S23)*α + (2*S23+S13-3)*π = 0
  obtain ⟨hA, hB'⟩ := Erdos634.Geometry.angle_indep hα
    (3 * (SA - S23)) (2 * S23 + S13 - 3)
    (by simp only [SA, S23, S13]; push_cast; linarith)
  -- Deduce SA = S23 and 2*S23+S13 = 3
  have heqA : SA = S23 := by omega
  have hsum3 : 2 * S23 + S13 = 3 := by omega
  -- s23_total ≤ 1
  have hs23_nn : 0 ≤ S23 := by
    simp only [S23]; positivity
  have hs23_le1 : S23 ≤ 1 := by omega
  -- Case split on s23_total: either 0 or 1
  have hS23_cases : S23 = 0 ∨ S23 = 1 := by omega
  rcases hS23_cases with hs0 | hs1
  · -- Case S23 = 0 → SA = 0, S13 = 3: equilateral
    have hSA0 : SA = 0 := by omega
    have hS130 : S13 = 3 := by omega
    -- All α and 23 multiplicities are 0
    -- All α and 23 multiplicities are 0: their ℤ sums are 0 and all terms ≥ 0
    have hSA_exp : (multOf D α 0 : ℤ) + multOf D α 1 + multOf D α 2 = 0 := by
      have h : SA = 0 := hSA0; simp only [SA] at h; exact h
    have hS23_exp : (multOf D (2 * Real.pi / 3 - α) 0 : ℤ) +
        multOf D (2 * Real.pi / 3 - α) 1 + multOf D (2 * Real.pi / 3 - α) 2 = 0 := by
      have h : S23 = 0 := hs0; simp only [S23] at h; exact h
    have hmα : ∀ j : Fin 3, multOf D α j = 0 := by
      have hsum : multOf D α 0 + multOf D α 1 + multOf D α 2 = 0 := by exact_mod_cast hSA_exp
      have e0 : multOf D α 0 = 0 := by omega
      have e1 : multOf D α 1 = 0 := by omega
      have e2 : multOf D α 2 = 0 := by omega
      intro j; fin_cases j; exact e0; exact e1; exact e2
    have hm23 : ∀ j : Fin 3, multOf D (2 * Real.pi / 3 - α) j = 0 := by
      have hsum : multOf D (2 * Real.pi / 3 - α) 0 + multOf D (2 * Real.pi / 3 - α) 1 +
          multOf D (2 * Real.pi / 3 - α) 2 = 0 := by exact_mod_cast hS23_exp
      have e0 : multOf D (2 * Real.pi / 3 - α) 0 = 0 := by omega
      have e1 : multOf D (2 * Real.pi / 3 - α) 1 = 0 := by omega
      have e2 : multOf D (2 * Real.pi / 3 - α) 2 = 0 := by omega
      intro j; fin_cases j; exact e0; exact e1; exact e2
    -- Per-vertex: angleAt v = n13_v * (π/3)
    have ha : ∀ j : Fin 3, D.target.angleAt j = (multOf D (Real.pi / 3) j : ℝ) * (Real.pi / 3) := by
      intro j
      have hpv := per_vertex_eq D hα hd j
      have hαj : multOf D α j = 0 := hmα j
      have h23j : multOf D (2 * Real.pi / 3 - α) j = 0 := hm23 j
      rw [hpv, hαj, h23j]; push_cast; ring
    -- n13_j = 1 for each j
    have hn13_each : ∀ j : Fin 3, multOf D (Real.pi / 3) j = 1 := by
      have hpos : ∀ j : Fin 3, 1 ≤ multOf D (Real.pi / 3) j := by
        intro j; by_contra hlt; push_neg at hlt
        have hj0 : multOf D (Real.pi / 3) j = 0 := Nat.lt_one_iff.mp hlt
        have hay := ha j; rw [hj0] at hay; push_cast at hay
        linarith [Tri.angleAt_pos' D.target j]
      have htot' : multOf D (Real.pi / 3) 0 + multOf D (Real.pi / 3) 1 +
          multOf D (Real.pi / 3) 2 = 3 := by
        have h : S13 = 3 := hS130; simp only [S13] at h; exact_mod_cast h
      have h0 := hpos 0; have h1 := hpos 1; have h2 := hpos 2
      -- Prove each component directly (avoid fin_cases changing Fin representation for omega)
      have e0 : multOf D (Real.pi / 3) 0 = 1 := by omega
      have e1 : multOf D (Real.pi / 3) 1 = 1 := by omega
      have e2 : multOf D (Real.pi / 3) 2 = 1 := by omega
      intro j; fin_cases j
      · exact e0
      · exact e1
      · exact e2
    -- Conclude angleAt k = π/3
    have hk := ha k; rw [hn13_each k] at hk; push_cast at hk; linarith
  · -- Case S23 = 1: construct SimilarTM D (contradicts hB)
    exfalso; apply hB
    -- SA = S23 = S13 = 1
    have hSA1 : SA = 1 := heqA.trans hs1
    have hS131 : S13 = 1 := by omega
    -- Cast to ℕ
    have hα_n : multOf D α 0 + multOf D α 1 + multOf D α 2 = 1 := by
      have h : SA = 1 := hSA1; simp only [SA] at h; exact_mod_cast h
    have h23_n : multOf D (2*Real.pi/3-α) 0 + multOf D (2*Real.pi/3-α) 1 +
        multOf D (2*Real.pi/3-α) 2 = 1 := by
      have h : S23 = 1 := hs1; simp only [S23] at h; exact_mod_cast h
    have h13_n : multOf D (Real.pi/3) 0 + multOf D (Real.pi/3) 1 +
        multOf D (Real.pi/3) 2 = 1 := by
      have h : S13 = 1 := hS131; simp only [S13] at h; exact_mod_cast h
    -- Each vertex has exactly one angle type
    have hT_pos : ∀ j : Fin 3, 0 < multOf D α j + multOf D (2*Real.pi/3-α) j + multOf D (Real.pi/3) j := by
      intro j; by_contra hc; push_neg at hc
      have h0 : multOf D α j = 0 := by omega
      have h1 : multOf D (2*Real.pi/3-α) j = 0 := by omega
      have h2 : multOf D (Real.pi/3) j = 0 := by omega
      have := per_vertex_eq D hα hd j; rw [h0, h1, h2] at this; push_cast at this
      linarith [Tri.angleAt_pos' D.target j]
    have hTe0 : multOf D α 0 + multOf D (2*Real.pi/3-α) 0 + multOf D (Real.pi/3) 0 = 1 := by
      have p0 := hT_pos 0; have p1 := hT_pos 1; have p2 := hT_pos 2; omega
    have hTe1 : multOf D α 1 + multOf D (2*Real.pi/3-α) 1 + multOf D (Real.pi/3) 1 = 1 := by
      have p0 := hT_pos 0; have p1 := hT_pos 1; have p2 := hT_pos 2; omega
    have hTe2 : multOf D α 2 + multOf D (2*Real.pi/3-α) 2 + multOf D (Real.pi/3) 2 = 1 := by
      have p0 := hT_pos 0; have p1 := hT_pos 1; have p2 := hT_pos 2; omega
    -- Per-vertex angle value (which angle type is at each vertex)
    have hpv_val : ∀ j : Fin 3,
        (multOf D α j = 1 → D.target.angleAt j = α) ∧
        (multOf D (2*Real.pi/3-α) j = 1 → D.target.angleAt j = 2*Real.pi/3-α) ∧
        (multOf D (Real.pi/3) j = 1 → D.target.angleAt j = Real.pi/3) := by
      intro j
      have hTj : multOf D α j + multOf D (2*Real.pi/3-α) j + multOf D (Real.pi/3) j = 1 := by
        fin_cases j; exact hTe0; exact hTe1; exact hTe2
      have hpv := per_vertex_eq D hα hd j
      refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
      · have h1 : multOf D (2*Real.pi/3-α) j = 0 := by omega
        have h2 : multOf D (Real.pi/3) j = 0 := by omega
        rw [hpv, h, h1, h2]; push_cast; ring
      · have h0 : multOf D α j = 0 := by omega
        have h2 : multOf D (Real.pi/3) j = 0 := by omega
        rw [hpv, h0, h, h2]; push_cast; ring
      · have h0 : multOf D α j = 0 := by omega
        have h1 : multOf D (2*Real.pi/3-α) j = 0 := by omega
        rw [hpv, h0, h1, h]; push_cast; ring
    -- Model σ from SixtyData
    obtain ⟨σ, hσα, hσα_len, hσ23, hσ23_len, hσ13, hσ13_len⟩ := hd
    -- oppLen ratio helper: sin cancels to give oppLen ratio equality
    have oppLen_ratio : ∀ (τ : Equiv.Perm (Fin 3)) (k : Fin 3),
        (∀ j : Fin 3, D.target.angleAt j = D.model.angleAt (τ j)) →
        D.target.oppLen k * D.model.oppLen (τ 0) = D.target.oppLen 0 * D.model.oppLen (τ k) := by
      intro τ k hangle
      have hls_t : Real.sin (D.model.angleAt (τ 0)) * D.target.oppLen k =
          Real.sin (D.model.angleAt (τ k)) * D.target.oppLen 0 := by
        have := Tri.lawSin D.target 0 k; rw [hangle 0, hangle k] at this; exact this
      have hls_m : Real.sin (D.model.angleAt (τ 0)) * D.model.oppLen (τ k) =
          Real.sin (D.model.angleAt (τ k)) * D.model.oppLen (τ 0) :=
        Tri.lawSin D.model (τ 0) (τ k)
      have hsin0 : 0 < Real.sin (D.model.angleAt (τ 0)) :=
        Real.sin_pos_of_pos_of_lt_pi (Tri.angleAt_pos' D.model (τ 0)) (cornerAngle_lt_pi D.model (τ 0))
      have step : Real.sin (D.model.angleAt (τ 0)) * (D.target.oppLen k * D.model.oppLen (τ 0)) =
          Real.sin (D.model.angleAt (τ 0)) * (D.target.oppLen 0 * D.model.oppLen (τ k)) :=
        calc Real.sin (D.model.angleAt (τ 0)) * (D.target.oppLen k * D.model.oppLen (τ 0))
            = Real.sin (D.model.angleAt (τ 0)) * D.target.oppLen k * D.model.oppLen (τ 0) := by ring
          _ = Real.sin (D.model.angleAt (τ k)) * D.target.oppLen 0 * D.model.oppLen (τ 0) := by rw [hls_t]
          _ = D.target.oppLen 0 * (Real.sin (D.model.angleAt (τ k)) * D.model.oppLen (τ 0)) := by ring
          _ = D.target.oppLen 0 * (Real.sin (D.model.angleAt (τ 0)) * D.model.oppLen (τ k)) := by rw [hls_m]
          _ = Real.sin (D.model.angleAt (τ 0)) * (D.target.oppLen 0 * D.model.oppLen (τ k)) := by ring
      exact mul_left_cancel₀ (ne_of_gt hsin0) step
    -- Construct SimilarTM by case-splitting on which vertex has α
    have hα_case : (multOf D α 0 = 1 ∧ multOf D α 1 = 0 ∧ multOf D α 2 = 0) ∨
        (multOf D α 0 = 0 ∧ multOf D α 1 = 1 ∧ multOf D α 2 = 0) ∨
        (multOf D α 0 = 0 ∧ multOf D α 1 = 0 ∧ multOf D α 2 = 1) := by omega
    -- For each α case, determine 23 case and build τ
    have build_similar : ∀ (τ : Equiv.Perm (Fin 3)),
        (∀ j : Fin 3, D.target.angleAt j = D.model.angleAt (τ j)) → SimilarTM D := by
      intro τ hangle
      exact ⟨D.target.oppLen 0 / D.model.oppLen (τ 0), τ, fun k => ⟨hangle k, by
        rcases Nat.eq_zero_or_pos k.val with hk | hk
        · have : k = 0 := by ext; exact hk
          subst this; simp [div_mul_cancel₀, ne_of_gt (Tri.oppLen_pos D.model (τ 0))]
        · have hrat := oppLen_ratio τ k hangle
          have hpos := Tri.oppLen_pos D.model (τ 0)
          field_simp [ne_of_gt hpos]; linarith [hrat]⟩⟩
    rcases hα_case with ⟨hα0, hα10, hα20⟩ | ⟨hα00, hα1, hα20⟩ | ⟨hα00, hα10, hα2⟩
    · -- α at vertex 0
      have h23_02 : multOf D (2*Real.pi/3-α) 0 = 0 := by have := hTe0; omega
      have h13_02 : multOf D (Real.pi/3) 0 = 0 := by have := hTe0; omega
      have h23_case : (multOf D (2*Real.pi/3-α) 1 = 1 ∧ multOf D (2*Real.pi/3-α) 2 = 0) ∨
          (multOf D (2*Real.pi/3-α) 1 = 0 ∧ multOf D (2*Real.pi/3-α) 2 = 1) := by omega
      rcases h23_case with ⟨h231, h232⟩ | ⟨h231, h232⟩
      · -- α@0, 23@1, 13@2
        have h13_2 : multOf D (Real.pi/3) 2 = 1 := by have := hTe2; omega
        have hta0 := (hpv_val 0).1 hα0
        have hta1 := (hpv_val 1).2.1 h231
        have hta2 := (hpv_val 2).2.2 h13_2
        exact build_similar σ (fun k => by
          fin_cases k
          · simp [hta0, hσα]
          · simp [hta1, hσ23]
          · simp [hta2, hσ13])
      · -- α@0, 23@2, 13@1  →  τ = (swap 1 2).trans σ: τ0=σ0, τ1=σ2, τ2=σ1
        have h13_1 : multOf D (Real.pi/3) 1 = 1 := by have := hTe1; omega
        have hta0 := (hpv_val 0).1 hα0
        have hta1 := (hpv_val 1).2.2 h13_1
        have hta2 := (hpv_val 2).2.1 h232
        exact build_similar ((Equiv.swap (1:Fin 3) 2).trans σ) (fun k => by
          fin_cases k
          · change D.target.angleAt 0 = D.model.angleAt (σ 0); rw [hta0, hσα]
          · change D.target.angleAt 1 = D.model.angleAt (σ 2); rw [hta1, hσ13]
          · change D.target.angleAt 2 = D.model.angleAt (σ 1); rw [hta2, hσ23])
    · -- α at vertex 1
      have h23_12 : multOf D (2*Real.pi/3-α) 1 = 0 := by have := hTe1; omega
      have h13_12 : multOf D (Real.pi/3) 1 = 0 := by have := hTe1; omega
      have h23_case : (multOf D (2*Real.pi/3-α) 0 = 1 ∧ multOf D (2*Real.pi/3-α) 2 = 0) ∨
          (multOf D (2*Real.pi/3-α) 0 = 0 ∧ multOf D (2*Real.pi/3-α) 2 = 1) := by omega
      rcases h23_case with ⟨h230, h232⟩ | ⟨h230, h232⟩
      · -- α@1, 23@0, 13@2  →  τ = (swap 0 1).trans σ: τ0=σ1, τ1=σ0, τ2=σ2
        have h13_2 : multOf D (Real.pi/3) 2 = 1 := by have := hTe2; omega
        have hta0 := (hpv_val 0).2.1 h230
        have hta1 := (hpv_val 1).1 hα1
        have hta2 := (hpv_val 2).2.2 h13_2
        exact build_similar ((Equiv.swap (0:Fin 3) 1).trans σ) (fun k => by
          fin_cases k
          · change D.target.angleAt 0 = D.model.angleAt (σ 1); rw [hta0, hσ23]
          · change D.target.angleAt 1 = D.model.angleAt (σ 0); rw [hta1, hσα]
          · change D.target.angleAt 2 = D.model.angleAt (σ 2); rw [hta2, hσ13])
      · -- α@1, 23@2, 13@0  →  τ = ((swap 0 2).trans (swap 0 1)).trans σ: τ0=σ2, τ1=σ0, τ2=σ1
        have h13_0 : multOf D (Real.pi/3) 0 = 1 := by have := hTe0; omega
        have hta0 := (hpv_val 0).2.2 h13_0
        have hta1 := (hpv_val 1).1 hα1
        have hta2 := (hpv_val 2).2.1 h232
        exact build_similar (((Equiv.swap (0:Fin 3) 2).trans (Equiv.swap 0 1)).trans σ) (fun k => by
          fin_cases k
          · change D.target.angleAt 0 = D.model.angleAt (σ 2); rw [hta0, hσ13]
          · change D.target.angleAt 1 = D.model.angleAt (σ 0); rw [hta1, hσα]
          · change D.target.angleAt 2 = D.model.angleAt (σ 1); rw [hta2, hσ23])
    · -- α at vertex 2
      have h23_22 : multOf D (2*Real.pi/3-α) 2 = 0 := by have := hTe2; omega
      have h13_22 : multOf D (Real.pi/3) 2 = 0 := by have := hTe2; omega
      have h23_case : (multOf D (2*Real.pi/3-α) 0 = 1 ∧ multOf D (2*Real.pi/3-α) 1 = 0) ∨
          (multOf D (2*Real.pi/3-α) 0 = 0 ∧ multOf D (2*Real.pi/3-α) 1 = 1) := by omega
      rcases h23_case with ⟨h230, h231⟩ | ⟨h230, h231⟩
      · -- α@2, 23@0, 13@1  →  τ = ((swap 0 1).trans (swap 0 2)).trans σ: τ0=σ1, τ1=σ2, τ2=σ0
        have h13_1 : multOf D (Real.pi/3) 1 = 1 := by have := hTe1; omega
        have hta0 := (hpv_val 0).2.1 h230
        have hta1 := (hpv_val 1).2.2 h13_1
        have hta2 := (hpv_val 2).1 hα2
        exact build_similar (((Equiv.swap (0:Fin 3) 1).trans (Equiv.swap 0 2)).trans σ) (fun k => by
          fin_cases k
          · change D.target.angleAt 0 = D.model.angleAt (σ 1); rw [hta0, hσ23]
          · change D.target.angleAt 1 = D.model.angleAt (σ 2); rw [hta1, hσ13]
          · change D.target.angleAt 2 = D.model.angleAt (σ 0); rw [hta2, hσα])
      · -- α@2, 23@1, 13@0  →  τ = (swap 0 2).trans σ: τ0=σ2, τ1=σ1, τ2=σ0
        have h13_0 : multOf D (Real.pi/3) 0 = 1 := by have := hTe0; omega
        have hta0 := (hpv_val 0).2.2 h13_0
        have hta1 := (hpv_val 1).2.1 h231
        have hta2 := (hpv_val 2).1 hα2
        exact build_similar ((Equiv.swap (0:Fin 3) 2).trans σ) (fun k => by
          fin_cases k
          · change D.target.angleAt 0 = D.model.angleAt (σ 2); rw [hta0, hσ13]
          · change D.target.angleAt 1 = D.model.angleAt (σ 1); rw [hta1, hσ23]
          · change D.target.angleAt 2 = D.model.angleAt (σ 0); rw [hta2, hσα])


#check @lemmaPStatement
#print axioms lemmaPStatement

end Erdos634.Draft.LemmaPProof
