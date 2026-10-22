-- Draft/LaczFormalRG12GExcHelp.lean -- Laczkovich (DCG 48 (2012)), Sect. 6.2, Gamma_except, lemma L1 (`gexc_start_of_kite`): the HELPERS.
-- (a) `arm_start_eq` / `arm_end_eq`: if a tile has a left step starting (ending) at the corner `U` of a sector, the far end of the step is the `p`-arm (the `q`-arm) of the sector.
-- (b) `grunEnd_exists`: a nonempty division whose first element has angle `gamma` at its head has a `gamma`-run end `H` (`GRunEnd`).
-- (c) `comb_B`: the cyclic label combinatorics of Fig. 5 (B): six labels (two of each), no three consecutive distinct, a `beta beta` block and an `alpha alpha` block are `2` apart (mod 6).
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.2, Fig. 5), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalRG12GExcWalk

open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ}

/-- The period-6 sequence with values `a0, .., a5`. -/
abbrev gF (a0 a1 a2 a3 a4 a5 : Fin 3) (n : ℕ) : Fin 3 := (![a0, a1, a2, a3, a4, a5] : Fin 6 → Fin 3) ⟨n % 6, Nat.mod_lt _ (by norm_num)⟩

set_option synthInstance.maxSize 4000 in
set_option maxRecDepth 100000 in
/-- Combinatorial core on one period (decided by kernel evaluation over the `3^6` sequences). -/
theorem comb_fin : ∀ a0 a1 a2 a3 a4 a5 : Fin 3, ∀ b < 6, ∀ c < 6,
    ((Finset.range 6).filter (fun i => gF a0 a1 a2 a3 a4 a5 i = 0)).card = 2 →
    ((Finset.range 6).filter (fun i => gF a0 a1 a2 a3 a4 a5 i = 1)).card = 2 →
    (∀ j < 6, ¬ (gF a0 a1 a2 a3 a4 a5 j ≠ gF a0 a1 a2 a3 a4 a5 (j + 1) ∧ gF a0 a1 a2 a3 a4 a5 j ≠ gF a0 a1 a2 a3 a4 a5 (j + 2) ∧
      gF a0 a1 a2 a3 a4 a5 (j + 1) ≠ gF a0 a1 a2 a3 a4 a5 (j + 2))) →
    gF a0 a1 a2 a3 a4 a5 b = 1 → gF a0 a1 a2 a3 a4 a5 (b + 1) = 1 → gF a0 a1 a2 a3 a4 a5 c = 0 → gF a0 a1 a2 a3 a4 a5 (c + 1) = 0 →
    (b + 2) % 6 = c ∨ (c + 2) % 6 = b := by
  decide +kernel

set_option synthInstance.maxSize 4000 in
set_option maxRecDepth 100000 in
/-- Two `gamma` corners: any two adjacent `gamma` pairs of a period-6 sequence with exactly two `2`s coincide. -/
theorem comb_fin2 : ∀ a0 a1 a2 a3 a4 a5 : Fin 3, ∀ a < 6, ∀ a' < 6,
    ((Finset.range 6).filter (fun i => gF a0 a1 a2 a3 a4 a5 i = 2)).card = 2 →
    gF a0 a1 a2 a3 a4 a5 a = 2 → gF a0 a1 a2 a3 a4 a5 (a + 1) = 2 → gF a0 a1 a2 a3 a4 a5 a' = 2 → gF a0 a1 a2 a3 a4 a5 (a' + 1) = 2 → a = a' := by
  decide +kernel

set_option synthInstance.maxSize 40000 in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
/-- Three adjacent pairs (`beta beta`, `alpha alpha`, `gamma gamma`) in a period-6 sequence with two of each label leave no three consecutive distinct labels. -/
theorem comb_fin3 : ∀ a0 a1 a2 a3 a4 a5 : Fin 3,
    (((Finset.range 6).filter (fun i => gF a0 a1 a2 a3 a4 a5 i = 0)).card = 2 ∧
    ((Finset.range 6).filter (fun i => gF a0 a1 a2 a3 a4 a5 i = 1)).card = 2 ∧
    ((Finset.range 6).filter (fun i => gF a0 a1 a2 a3 a4 a5 i = 2)).card = 2) →
    ∀ b < 6, ∀ c < 6, ∀ e < 6, ∀ j < 6,
    (gF a0 a1 a2 a3 a4 a5 b = 1 ∧ gF a0 a1 a2 a3 a4 a5 (b + 1) = 1 ∧ gF a0 a1 a2 a3 a4 a5 c = 0 ∧ gF a0 a1 a2 a3 a4 a5 (c + 1) = 0 ∧
    gF a0 a1 a2 a3 a4 a5 e = 2 ∧ gF a0 a1 a2 a3 a4 a5 (e + 1) = 2) →
    ¬ (gF a0 a1 a2 a3 a4 a5 j ≠ gF a0 a1 a2 a3 a4 a5 (j + 1) ∧ gF a0 a1 a2 a3 a4 a5 j ≠ gF a0 a1 a2 a3 a4 a5 (j + 2) ∧
      gF a0 a1 a2 a3 a4 a5 (j + 1) ≠ gF a0 a1 a2 a3 a4 a5 (j + 2)) := by
  decide +kernel

open scoped Classical Fin.NatCast

/-- The far end of a left step STARTING at the corner `U` of a sector is the `p`-arm of the sector. -/
theorem arm_start_eq {T : Tri} {d : V2} {U U' : Plane} (hS : TriStep T d U U') {p q : V2} (kk' : Fin 3) (fl : Bool) (hk' : T.pts kk' = U)
    (hp : p = toV2 (T.pts (armP kk' fl) - U)) (hq : q = toV2 (T.pts (armQ kk' fl) - U)) (hok : SecOK p q) :
    ∃ f, T.pts f = U' ∧ f = armP kk' fl := by
  have hS' := hS
  obtain ⟨kk, f, g, hk, hf, hfk, hgk, hgf, hpar, hleft⟩ := hS'
  have hkk : kk = kk' := T.indep.injective (hk.trans hk'.symm)
  subst hkk
  rcases arm_cases kk fl f hfk with h | h
  · exact ⟨f, hf, h⟩
  · exfalso
    have hqpar : Par q d := by rw [hq, ← h, hf]; exact hpar
    have hppar : Par p d := triStep_start hS kk fl hk' hp hq hok
    exact par_not_secok hok (hqpar.trans hppar.symm)

/-- The start of a left step ENDING at the corner `U'` of a sector is the `q`-arm of the sector. -/
theorem arm_end_eq {T : Tri} {d : V2} {U U' : Plane} (hS : TriStep T d U U') {p q : V2} (kk' : Fin 3) (fl : Bool) (hk' : T.pts kk' = U')
    (hp : p = toV2 (T.pts (armP kk' fl) - U')) (hq : q = toV2 (T.pts (armQ kk' fl) - U')) (hok : SecOK p q) :
    ∃ kk, T.pts kk = U ∧ kk = armQ kk' fl := by
  have hS' := hS
  obtain ⟨kk, f, g, hk, hf, hfk, hgk, hgf, hpar, hleft⟩ := hS'
  have hff : f = kk' := T.indep.injective (hf.trans hk'.symm)
  subst hff
  rcases arm_cases f fl kk hfk.symm with h | h
  · exfalso
    have hqpar : Par q (neg2 d) := triStep_end hS f fl hk' hp hq hok
    have hppar : Par p (neg2 d) := by
      rw [hp, ← h, hk]
      have : toV2 (U - U') = (-(toV2 (U' - U)).1, -(toV2 (U' - U)).2) := by unfold toV2; ext <;> simp
      rw [this]
      exact par_neg hpar
    exact par_not_secok hok (hqpar.trans hppar.symm)
  · exact ⟨kk, hk, h⟩

/-- Three distinct elements of `Fin 3` have value sum `3`. -/
theorem fin3_sum3 {u v w : Fin 3} (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) : u.val + v.val + w.val = 3 := by
  revert u v w; decide

/-- **A nonempty division whose first element has `gamma` at its head has a `gamma`-run end.** -/
theorem grunEnd_exists (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) {L : List (Fin N × Plane × Plane)} (hne : L ≠ [])
    (hh : ∀ e ∈ L.head?, GammaHead D idx e) : ∃ H, GRunEnd D idx L H := by
  classical
  obtain ⟨e1, L1, rfl⟩ := List.exists_cons_of_ne_nil hne
  have h1 : GammaHead D idx e1 := hh e1 (by simp)
  set p : Fin N × Plane × Plane → Bool := fun e => decide (GammaHead D idx e) with hp
  set L' := (e1 :: L1).takeWhile p with hL'
  have hL'ne : L' ≠ [] := by
    simp [hL', hp, h1]
  refine ⟨(L'.getLast hL'ne).2.2, L', (e1 :: L1).dropWhile p, (List.takeWhile_append_dropWhile).symm, hL'ne, ?_, ?_, L'.getLast hL'ne, List.getLast?_eq_some_getLast hL'ne, rfl⟩
  · intro x hx
    have := List.mem_takeWhile_imp hx
    simpa [hp] using this
  · intro e he
    have := List.head?_dropWhile_not p (e1 :: L1)
    rw [Option.mem_def.mp he] at this
    simpa [hp] using this

/-- **Fig. 5 (B), the label combinatorics.**  Labels `ℓ` of six cyclic sectors (period 6, two of each label), no three consecutive labels pairwise distinct (no straight line);
a `beta beta` block at `b, b+1` and an `alpha alpha` block at `c, c+1` (`b, c < 6`): the blocks are at distance `2` in one of the two cyclic directions. -/
theorem comb_B (ℓ : ℕ → Fin 3) (hper : ∀ n, ℓ (n + 6) = ℓ n) (h0 : ((Finset.range 6).filter (fun i => ℓ i = 0)).card = 2)
    (h1 : ((Finset.range 6).filter (fun i => ℓ i = 1)).card = 2)
    (hnt : ∀ j, ¬ (ℓ j ≠ ℓ (j + 1) ∧ ℓ j ≠ ℓ (j + 2) ∧ ℓ (j + 1) ≠ ℓ (j + 2))) {b c : ℕ} (hb : b < 6) (hc : c < 6)
    (hb1 : ℓ b = 1 ∧ ℓ (b + 1) = 1) (hc1 : ℓ c = 0 ∧ ℓ (c + 1) = 0) :
    (b + 2 = c ∨ b + 2 = c + 6) ∨ (c + 2 = b ∨ c + 2 = b + 6) := by
  have hm := per_mod ℓ hper
  have hk : ∀ k (hk : k < 6), (![ℓ 0, ℓ 1, ℓ 2, ℓ 3, ℓ 4, ℓ 5] : Fin 6 → Fin 3) ⟨k, hk⟩ = ℓ k := by
    intro k hk; interval_cases k <;> rfl
  have hg : ∀ n, gF (ℓ 0) (ℓ 1) (ℓ 2) (ℓ 3) (ℓ 4) (ℓ 5) n = ℓ n := by
    intro n
    rw [hm n]
    exact hk (n % 6) (Nat.mod_lt _ (by norm_num))
  have key := comb_fin (ℓ 0) (ℓ 1) (ℓ 2) (ℓ 3) (ℓ 4) (ℓ 5) b hb c hc
  simp only [hg] at key
  have r := key h0 h1 (fun j _ => hnt j) hb1.1 hb1.2 hc1.1 hc1.2
  omega

/-- **Two adjacent `gamma` corners are unique** (period 6, exactly two `gamma` corners). -/
theorem gamma_pair_unique (ℓ : ℕ → Fin 3) (hper : ∀ n, ℓ (n + 6) = ℓ n) (h2 : ((Finset.range 6).filter (fun i => ℓ i = 2)).card = 2) {a a' : ℕ}
    (ha : ℓ a = 2 ∧ ℓ (a + 1) = 2) (ha' : ℓ a' = 2 ∧ ℓ (a' + 1) = 2) : a % 6 = a' % 6 := by
  have hm := per_mod ℓ hper
  have hk : ∀ k (hk : k < 6), (![ℓ 0, ℓ 1, ℓ 2, ℓ 3, ℓ 4, ℓ 5] : Fin 6 → Fin 3) ⟨k, hk⟩ = ℓ k := by
    intro k hk; interval_cases k <;> rfl
  have hg : ∀ n, gF (ℓ 0) (ℓ 1) (ℓ 2) (ℓ 3) (ℓ 4) (ℓ 5) n = ℓ n := by
    intro n
    rw [hm n]
    exact hk (n % 6) (Nat.mod_lt _ (by norm_num))
  have key := comb_fin2 (ℓ 0) (ℓ 1) (ℓ 2) (ℓ 3) (ℓ 4) (ℓ 5) (a % 6) (Nat.mod_lt _ (by norm_num)) (a' % 6) (Nat.mod_lt _ (by norm_num))
  simp only [hg] at key
  have e1 : ℓ (a % 6) = ℓ a := (hm a).symm
  have e2 : ℓ (a % 6 + 1) = ℓ (a + 1) := by rw [hm (a % 6 + 1), hm (a + 1)]; congr 1; omega
  have e3 : ℓ (a' % 6) = ℓ a' := (hm a').symm
  have e4 : ℓ (a' % 6 + 1) = ℓ (a' + 1) := by rw [hm (a' % 6 + 1), hm (a' + 1)]; congr 1; omega
  exact key h2 (by rw [e1]; exact ha.1) (by rw [e2]; exact ha.2) (by rw [e3]; exact ha'.1) (by rw [e4]; exact ha'.2)

/-- **Fig. 5, no `gamma gamma` pair with a straight line.**  Two of each label, a `beta beta` block, an `alpha alpha` block and a `gamma gamma` block: no three consecutive labels are pairwise distinct. -/
theorem comb_noStraight (ℓ : ℕ → Fin 3) (hper : ∀ n, ℓ (n + 6) = ℓ n) (h0 : ((Finset.range 6).filter (fun i => ℓ i = 0)).card = 2)
    (h1 : ((Finset.range 6).filter (fun i => ℓ i = 1)).card = 2) (h2 : ((Finset.range 6).filter (fun i => ℓ i = 2)).card = 2) {b c e : ℕ}
    (hb1 : ℓ b = 1 ∧ ℓ (b + 1) = 1) (hc1 : ℓ c = 0 ∧ ℓ (c + 1) = 0) (he1 : ℓ e = 2 ∧ ℓ (e + 1) = 2) (j : ℕ) :
    ¬ (ℓ j ≠ ℓ (j + 1) ∧ ℓ j ≠ ℓ (j + 2) ∧ ℓ (j + 1) ≠ ℓ (j + 2)) := by
  have hm := per_mod ℓ hper
  have hk : ∀ k (hk : k < 6), (![ℓ 0, ℓ 1, ℓ 2, ℓ 3, ℓ 4, ℓ 5] : Fin 6 → Fin 3) ⟨k, hk⟩ = ℓ k := by
    intro k hk; interval_cases k <;> rfl
  have hg : ∀ n, gF (ℓ 0) (ℓ 1) (ℓ 2) (ℓ 3) (ℓ 4) (ℓ 5) n = ℓ n := by
    intro n
    rw [hm n]
    exact hk (n % 6) (Nat.mod_lt _ (by norm_num))
  have key := comb_fin3 (ℓ 0) (ℓ 1) (ℓ 2) (ℓ 3) (ℓ 4) (ℓ 5)
  simp only [hg] at key
  have sh : ∀ n k : ℕ, ℓ (n % 6 + k) = ℓ (n + k) := fun n k => by rw [hm (n % 6 + k), hm (n + k)]; congr 1; omega
  have s0 : ∀ n : ℕ, ℓ (n % 6) = ℓ n := fun n => (hm n).symm
  have := key ⟨h0, h1, h2⟩ (b % 6) (Nat.mod_lt _ (by norm_num)) (c % 6) (Nat.mod_lt _ (by norm_num))
    (e % 6) (Nat.mod_lt _ (by norm_num)) (j % 6) (Nat.mod_lt _ (by norm_num)) ⟨(by rw [s0]; exact hb1.1), (by rw [sh]; exact hb1.2), (by rw [s0]; exact hc1.1), (by rw [sh]; exact hc1.2),
    (by rw [s0]; exact he1.1), (by rw [sh]; exact he1.2)⟩
  rw [s0, sh, sh] at this
  exact this

/-! ## Witness and negative control for `comb_B` -/

theorem gF_mod (a0 a1 a2 a3 a4 a5 : Fin 3) (n : ℕ) : gF a0 a1 a2 a3 a4 a5 n = gF a0 a1 a2 a3 a4 a5 (n % 6) := by
  unfold gF; simp [Nat.mod_mod]

theorem gF_add_mod (a0 a1 a2 a3 a4 a5 : Fin 3) (n k : ℕ) : gF a0 a1 a2 a3 a4 a5 (n + k) = gF a0 a1 a2 a3 a4 a5 (n % 6 + k) := by
  unfold gF; simp [Nat.add_mod]

/-- **Witness (Fig. 5 (B)).**  The labels `1,1,2,2,0,0` (period 6) satisfy every hypothesis of `comb_B` (two of each label, no three consecutive distinct) with `b = 0`, `c = 4`; the conclusion is the `c + 2 = b + 6` alternative. -/
theorem comb_B_witness : ∃ ℓ : ℕ → Fin 3, (∀ n, ℓ (n + 6) = ℓ n) ∧ ((Finset.range 6).filter (fun i => ℓ i = 0)).card = 2 ∧
    ((Finset.range 6).filter (fun i => ℓ i = 1)).card = 2 ∧ (∀ j, ¬ (ℓ j ≠ ℓ (j + 1) ∧ ℓ j ≠ ℓ (j + 2) ∧ ℓ (j + 1) ≠ ℓ (j + 2))) ∧
    ℓ 0 = 1 ∧ ℓ (0 + 1) = 1 ∧ ℓ 4 = 0 ∧ ℓ (4 + 1) = 0 := by
  refine ⟨gF 1 1 2 2 0 0, ?_, by decide, by decide, ?_, by decide, by decide, by decide, by decide⟩
  · intro n; unfold gF; simp [Nat.add_mod_right]
  · intro j
    rw [gF_mod 1 1 2 2 0 0 j, gF_add_mod 1 1 2 2 0 0 j 1, gF_add_mod 1 1 2 2 0 0 j 2]
    have hj : j % 6 < 6 := Nat.mod_lt _ (by norm_num)
    generalize j % 6 = r at hj ⊢
    interval_cases r <;> decide

/-- **Negative control (Fig. 5 (A)).**  The labels `1,1,2,0,0,2` have the distinct triple `(1, 2, 0)` at `j = 1`: the hypothesis `hnt` of `comb_B` is exactly what excludes pattern (A). -/
theorem comb_A_control : ¬ ∀ j, ¬ (gF 1 1 2 0 0 2 j ≠ gF 1 1 2 0 0 2 (j + 1) ∧ gF 1 1 2 0 0 2 j ≠ gF 1 1 2 0 0 2 (j + 2) ∧
    gF 1 1 2 0 0 2 (j + 1) ≠ gF 1 1 2 0 0 2 (j + 2)) := by
  intro h
  exact h 1 (by decide)

/-- **Witness for `comb_noStraight` / `gamma_pair_unique`** (pattern (B), `1,1,2,2,0,0`): two of each label, `beta beta` at 0, `alpha alpha` at 4, `gamma gamma` at 2. -/
theorem comb_noStraight_witness : ((Finset.range 6).filter (fun i => gF 1 1 2 2 0 0 i = 0)).card = 2 ∧ ((Finset.range 6).filter (fun i => gF 1 1 2 2 0 0 i = 1)).card = 2 ∧
    ((Finset.range 6).filter (fun i => gF 1 1 2 2 0 0 i = 2)).card = 2 ∧ (gF 1 1 2 2 0 0 0 = 1 ∧ gF 1 1 2 2 0 0 (0 + 1) = 1) ∧
    (gF 1 1 2 2 0 0 4 = 0 ∧ gF 1 1 2 2 0 0 (4 + 1) = 0) ∧ (gF 1 1 2 2 0 0 2 = 2 ∧ gF 1 1 2 2 0 0 (2 + 1) = 2) := by
  decide

/-- **Negative control for L3 (pattern (A), `1,1,2,0,0,2`)**: it has two of each label and the two kite blocks, but NO adjacent `gamma gamma` pair (the `gamma`s are at 2 and 5), so no edge of Gamma_except can arrive. -/
theorem comb_A_no_gamma_pair : ((Finset.range 6).filter (fun i => gF 1 1 2 0 0 2 i = 2)).card = 2 ∧ ∀ e < 6, ¬ (gF 1 1 2 0 0 2 e = 2 ∧ gF 1 1 2 0 0 2 (e + 1) = 2) := by
  decide

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.arm_start_eq
#print axioms Erdos634.Draft.LaczFormal.RG.arm_end_eq
#print axioms Erdos634.Draft.LaczFormal.RG.grunEnd_exists
#print axioms Erdos634.Draft.LaczFormal.RG.comb_B
#print axioms Erdos634.Draft.LaczFormal.RG.comb_B_witness
#print axioms Erdos634.Draft.LaczFormal.RG.comb_A_control
#print axioms Erdos634.Draft.LaczFormal.RG.gamma_pair_unique
#print axioms Erdos634.Draft.LaczFormal.RG.comb_noStraight
#print axioms Erdos634.Draft.LaczFormal.RG.comb_noStraight_witness
#print axioms Erdos634.Draft.LaczFormal.RG.comb_A_no_gamma_pair
