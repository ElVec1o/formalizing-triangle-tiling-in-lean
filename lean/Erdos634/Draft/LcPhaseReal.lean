-- Draft/LcPhaseReal.lean — THE L_c PHASE OF THEOREM H, composed ((private working notes, not included) §6,
-- "Induction claim I(k)"; steps k with L_c, and the chain end k = n), for REAL `m = 1` dissections:
-- from the apex patch `Π(1) = {T₂, T₃}` (APX, the frame fields), S4(k) + R9 iterated while the
-- `α`-tile at `kV` is `L_c`, and S5 + S5-M at `k = n`.  Conclusion: every such dissection turns — some
-- chain point `kV`, `1 ≤ k ≤ n − 1`, carries `L_b = B_k`, with `Π(k)` present.  What is left of
-- Theorem H is exactly Theorem L3M (the `L_b` subtree: base S(k+1), the march Λ3M, Terminal(k)),
-- which was NOT formalized when this file was written; it is now `L3MReal.l3m_theorem` (2026-09-30).  Imported directly by All.lean (stale "NOT imported" header corrected 2026-10-04).
--
-- Build (scratch oleans; never .lake): PatchCompleteReal olean in $S, then
--   lake env bash -c 'LEAN_PATH=$S:$LEAN_PATH lean Erdos634/Draft/LcPhaseReal.lean'
import Erdos634.Draft.PatchCompleteReal

namespace Erdos634.Draft.RowWallReal

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.Draft.HalfTurnR3R4
open Erdos634.Draft.HalfTurnR3R4Glue Erdos634.Draft.CornerAdjacency
open Erdos634.Draft.HalfTurnR3R4Order Erdos634.Draft.MirrorStripR2Real
open Erdos634.Draft.HalfTurnR4Real

variable {N : ℕ} {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ}
variable (F : HFrame D e f α β γ)

/-- **The patch `Π(K) = K·T₂ ∪ K·T₃`** (proof_H_empty.md §2.4): `T₂ + iV + tP′` (`i + t ≤ K − 1`),
`K + iV + tP′` (`i + t ≤ K − 2`), `T₃ + Λ(i,t)` (`i + t ≤ K − 1`), `Z₀ + Λ(i,t)` (`i + t ≤ K − 2`). -/
def PiK (F : HFrame D e f α β γ) (K : ℕ) : Prop :=
  (∀ i t, i + t + 1 ≤ K → Present D (T2c F i t)) ∧ (∀ i t, i + t + 2 ≤ K → Present D (Kc F i t)) ∧
    (∀ i t, i + t + 1 ≤ K → Present D (Up F i t)) ∧ (∀ i t, i + t + 2 ≤ K → Present D (Dn F i t))

/-- **`Π(1) = {T₂, T₃}`** (APX: thm:apexconfig, the frame fields `hT2`, `hT3`). -/
theorem pi_one : PiK F 1 := by
  refine ⟨fun i t hit => ?_, fun i t hit => by omega, fun i t hit => ?_, fun i t hit => by omega⟩
  · obtain ⟨rfl, rfl⟩ : i = 0 ∧ t = 0 := by omega
    have : T2c F 0 0 = {F.A, F.V, F.P} := by simp [T2c]
    rw [this]; exact F.hT2
  · obtain ⟨rfl, rfl⟩ : i = 0 ∧ t = 0 := by omega
    have : Up F 0 0 = {F.A, F.P, F.A + ((f : ℝ) ^ 2) • F.uL} := by
      simp only [Up, Nat.cast_zero, zero_add]
      rw [Lam_zero_zero, ← P_eq F]
      simp [Lam, vec, v]
    rw [this]; exact F.hT3

include F in
/-- **The chain length `n = n' + 1`**: `nc < fb < (n+1)c` (`n = ⌊fb/c⌋ ≥ 1`; strict on both sides
since `f ∤ e²`). -/
theorem chain_length : ∃ n' : ℕ,
    ((n' + 1 : ℕ) : ℝ) * (f : ℝ) ^ 2 < (f : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ∧
      (f : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) < ((n' + 2 : ℕ) : ℝ) * (f : ℝ) ^ 2 := by
  have he := F.he
  have hef := F.hef
  obtain ⟨b, hb⟩ : ∃ b, b + e ^ 2 = f ^ 2 :=
    ⟨f ^ 2 - e ^ 2, Nat.sub_add_cancel (Nat.pow_le_pow_left (by omega) 2)⟩
  have hbR : (b : ℝ) = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
    have : ((b + e ^ 2 : ℕ) : ℝ) = ((f ^ 2 : ℕ) : ℝ) := by rw [hb]
    push_cast at this; linarith
  have hf4 : 4 ≤ f := by omega
  have hf2 : 0 < f ^ 2 := by positivity
  -- `f·b` is not a multiple of `f²` (else `f ∣ b`, so `f ∣ e²`)
  have hndvd : ∀ m : ℕ, m * f ^ 2 ≠ f * b := by
    intro m hm
    have h2 : m * f = b := by
      have : f * (m * f) = f * b := by rw [← hm]; ring
      exact Nat.eq_of_mul_eq_mul_left (by omega) this
    have h4 : e ^ 2 + m * f = f * f := by
      have : f ^ 2 = f * f := by ring
      omega
    have h5 : f ∣ e ^ 2 + m * f := by rw [h4]; exact dvd_mul_right f f
    have h3 : f ∣ e ^ 2 := by
      have := Nat.dvd_sub h5 (dvd_mul_left f m)
      simpa using this
    have hcop : Nat.Coprime f (e ^ 2) := Nat.Coprime.pow_right 2 F.hco.symm
    have := Nat.Coprime.eq_one_of_dvd hcop h3
    omega
  -- `f < b`, so `f² < f·b` and `n = ⌊fb/f²⌋ ≥ 1`
  have hfb : f < b := by
    have h1 : e ^ 2 + 4 * f ≤ f ^ 2 + 4 := by nlinarith
    omega
  have hCB : f ^ 2 < f * b := by
    calc f ^ 2 = f * f := by ring
      _ < f * b := Nat.mul_lt_mul_of_pos_left hfb (by omega)
  obtain ⟨n', hn'⟩ : ∃ n', (f * b) / f ^ 2 = n' + 1 := ⟨(f * b) / f ^ 2 - 1, by
    have : 1 ≤ (f * b) / f ^ 2 := (Nat.le_div_iff_mul_le hf2).mpr (by omega)
    omega⟩
  have hlo : (n' + 1) * f ^ 2 ≤ f * b := by rw [← hn']; exact Nat.div_mul_le_self _ _
  have hhi : f * b < (n' + 2) * f ^ 2 := by
    have := Nat.lt_div_mul_add (a := f * b) hf2
    rw [hn'] at this
    have e1 : (n' + 1) * f ^ 2 + f ^ 2 = (n' + 2) * f ^ 2 := by ring
    omega
  have hlt : (n' + 1) * f ^ 2 < f * b := lt_of_le_of_ne hlo (hndvd _)
  refine ⟨n', ?_, ?_⟩
  · have : (((n' + 1) * f ^ 2 : ℕ) : ℝ) < ((f * b : ℕ) : ℝ) := by exact_mod_cast hlt
    push_cast at this; rw [hbR] at this; push_cast; linarith
  · have : ((f * b : ℕ) : ℝ) < (((n' + 2) * f ^ 2 : ℕ) : ℝ) := by exact_mod_cast hhi
    push_cast at this; rw [hbR] at this; push_cast; linarith

set_option maxHeartbeats 1000000 in
/-- **THE `L_c` PHASE OF THEOREM H, frame form — PROVED (by composition).**  Let `n = n' + 1` be the
chain length (`nc < fb < (n+1)c`).  In the apex frame, some chain point `kV` with `1 ≤ k ≤ n − 1`
carries `L_b = B_k` (the swap `Sw k 0`), and `Π(k)` is present (it contains the `L_c` chain
`T₂ + jV`, `j < k`).  Proof: `I(1) = Π(1)` (APX, `pi_one`); while the `α`-tile at `kV` is `L_c`,
S4(k) + R9 give `Π(k+1)` (`s4_frame`, `chain_alpha`, `r9_frame`; at `k = 1` S4 contains R2: the tile
across `VP′` is `K`, the mirror `M₁ = N₁` being killed by PK·a(1)); at `k = n`, S5 + S5-M
(`s5_frame`) is a contradiction. -/
theorem lc_phase (L : LFrame F) (n' : ℕ)
    (hnc : ((n' + 1 : ℕ) : ℝ) * (f : ℝ) ^ 2 < (f : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2))
    (hnc1 : (f : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) < ((n' + 2 : ℕ) : ℝ) * (f : ℝ) ^ 2) :
    ∃ k' : ℕ, k' < n' ∧ PiK F (k' + 1) ∧ Present D (Sw F ((k' : ℝ) + 1) 0) := by
  by_contra hno
  push Not at hno
  obtain ⟨-, hb0, hc0, -, -⟩ := consts F
  have hnf : n' + 2 ≤ f := by
    have h1 : ((n' + 1 : ℕ) : ℝ) * (f : ℝ) ^ 2 < (f : ℝ) * (f : ℝ) ^ 2 := by
      have : (f : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) < (f : ℝ) * (f : ℝ) ^ 2 := by
        have : (0 : ℝ) < (e : ℝ) ^ 2 := by
          have : (2 : ℝ) ≤ e := by exact_mod_cast F.he
          positivity
        have : (0 : ℝ) < f := f_pos' F
        nlinarith
      linarith
    have h2 : ((n' + 1 : ℕ) : ℝ) < f := lt_of_mul_lt_mul_right h1 (by positivity)
    have : n' + 1 < f := by exact_mod_cast h2
    omega
  have key : ∀ k', k' ≤ n' → PiK F (k' + 1) := by
    intro k'
    induction k' with
    | zero => intro _; exact pi_one F
    | succ k ih =>
      intro hk
      obtain ⟨hT2, hK2, hUp, hDn⟩ := ih (by omega)
      have hKc : ((k + 1 : ℕ) : ℝ) * (f : ℝ) ^ 2 < (f : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) := by
        have : ((k + 1 : ℕ) : ℝ) ≤ ((n' + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : k + 1 ≤ n' + 1)
        nlinarith
      obtain ⟨hAD, -, -, -⟩ := s4_frame F L k (by omega) hKc hT2 hK2 hUp hDn
      rcases chain_alpha F L k (fun i hi => hT2 i 0 (by omega)) (hAD k 0 (by omega)) with h | h
      · exact r9_frame F L k (by omega) hKc hT2 hK2 hUp hDn h
      · exact absurd h (hno k (by omega) ⟨hT2, hK2, hUp, hDn⟩)
  obtain ⟨hT2, hK2, hUp, -⟩ := key n' le_rfl
  exact s5_frame F L n' hnc hnc1 hT2 hK2 (hUp n' 0 (by omega))

/-- **THE `L_c` PHASE OF THEOREM H FOR EVERY REAL `m = 1` DISSECTION — PROVED.**  Every congruent
dissection of the `m = 1` base-β target (coprime `2 ≤ e ≤ f − 2`, `M1Data`) carries its apex frame `F`,
and in it some chain point `kV`, `1 ≤ k ≤ n − 1`, carries `L_b = B_k`, with `Π(k)` present.  (Theorem H
is this plus Theorem L3M(k): no `m = 1` dissection contains `Π(k)` and `B_k` — now `L3MReal.l3m_theorem`.) -/
theorem lc_phase_real {kk : Fin 3} (h : ApexFrameReal.M1Data D e f α β γ kk) :
    ∃ F : HFrame D e f α β γ, ApexPlacement.FrameCoords F ∧ ∃ n' : ℕ,
      ((n' + 1 : ℕ) : ℝ) * (f : ℝ) ^ 2 < (f : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ∧
      (f : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) < ((n' + 2 : ℕ) : ℝ) * (f : ℝ) ^ 2 ∧
      ∃ k' : ℕ, k' < n' ∧ PiK F (k' + 1) ∧ Present D (Sw F ((k' : ℝ) + 1) 0) := by
  obtain ⟨F, FC⟩ := ApexLegWord.exists_hframe_coords_m1 D h.hco h.he h.hef h.hM h.hAng kk
    h.hcorner h.hβ1 h.hβ2 h.hleg1 h.hleg2 h.hbase
  obtain ⟨n', hnc, hnc1⟩ := chain_length F
  exact ⟨F, FC, n', hnc, hnc1, lc_phase F (lframe_real F h FC) n' hnc hnc1⟩

end Erdos634.Draft.RowWallReal

#print axioms Erdos634.Draft.RowWallReal.pi_one
#print axioms Erdos634.Draft.RowWallReal.chain_length
#print axioms Erdos634.Draft.RowWallReal.lc_phase
#print axioms Erdos634.Draft.RowWallReal.lc_phase_real
