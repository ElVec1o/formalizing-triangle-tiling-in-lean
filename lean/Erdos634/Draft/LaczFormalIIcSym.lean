-- Draft/LaczFormalIIcSym.lean -- Laczkovich (DCG 48 (2012)), Sect. 6.3, two exceptional points, central symmetry: assembly.
-- `central_symmetry_of_spokes`: under the Case IIc block of `spokes_angle` (all corners (1,1,0), P = M = 2k, GExc edges W_j, S7 interiority) and the INDEX SPLIT hypothesis `hI` (after a cyclic shift s0, the first k corners have W = E and the last k have W = F;
-- this is step 7 of IIC_STRN.md Sect. 4, G10, NOT proved here: it needs the disjointness of the spokes (L8 `gexc_disjoint`) and the cyclic-interval lemma), the polygon is centrally symmetric: P.side i = P.side (i + k).
-- Uses `spokes_angle` (Spoke5), `caseII_polyvertex` / `caseII_exc_count` (angle pi - gamma at every corner, M gamma = 2 pi) and the pure-geometry core `central_symmetry_core` (SymB).
-- NOTE, UNAUDITED.  CONDITIONAL on `hI` (and on the Case IIc hypothesis block, this block is witnessed by GenWitK (204-tile octagon, genTiling_thm21) and IsoWitM).  Credit: Laczkovich (DCG 48 (2012), Sect. 6.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcSpoke5
import Erdos634.Draft.LaczFormalIIcSymB

open scoped Classical Fin.NatCast
open EuclideanGeometry Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ}

/-- At every corner of type (1,1,0) the polygon angle is `pi - gamma`, and `M gamma = 2 pi` when all corners are of this type. -/
theorem corner_angles_gamma [NeZero M] (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hC : CaseC D idx) (h1 : D.model.angleAt 2 < Real.pi / 2) (h3 : D.model.angleAt 2 ≠ Real.pi / 3)
    (hcor : ∀ j : Fin M, cnt D idx (P.v j) 0 = 1 ∧ cnt D idx (P.v j) 1 = 1 ∧ cnt D idx (P.v j) 2 = 0) :
    (∀ i : Fin M, P.angle i = Real.pi - D.model.angleAt 2) ∧ (M : ℝ) * D.model.angleAt 2 = 2 * Real.pi := by
  constructor
  · intro i
    have := caseII_polyvertex D P hreg idx hC.hidxA hC.hregc h1 (i - 1)
    rw [sub_add_cancel] at this
    rcases this with ⟨-, -, h⟩ | ⟨h0, -, -⟩
    · exact h
    · have := (hcor i).1; omega
  · obtain ⟨hRP, hMP, hexc, hang⟩ := caseII_exc_count D P hreg idx hC.hidxA hC.hregc h1 h3
    have hsumP : cntP0 D idx P = ∑ j : Fin M, cnt D idx (P.v j) 0 :=
      Equiv.sum_comp (Equiv.addRight (1 : Fin M)) (fun j => cnt D idx (P.v j) 0)
    have hsumR : cntR2 D idx P = ∑ j : Fin M, cnt D idx (P.v j) 2 :=
      Equiv.sum_comp (Equiv.addRight (1 : Fin M)) (fun j => cnt D idx (P.v j) 2)
    have hP : cntP0 D idx P = M := by
      rw [hsumP]; simp [fun j => (hcor j).1]
    have hR : cntR2 D idx P = 0 := by
      rw [hsumR]; simp [fun j => (hcor j).2.2]
    rw [hP, hR] at hang
    push_cast at hang
    linarith

theorem cross2_shift (x y z : Plane) : cross2 (y - x) (z - y) = cross2 (y - x) (z - x) := by
  unfold cross2; simp only [PiLp.sub_apply]; ring

set_option maxHeartbeats 6400000 in
/-- **Central symmetry of the two-exceptional-point polygon**, conditional on the index split `hI` (see the header). -/
theorem central_symmetry_of_spokes {k : ℕ} [NeZero (2 * k)] (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly (2 * k)) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hC : CaseC D idx) (h1 : D.model.angleAt 2 < Real.pi / 2) (h3 : D.model.angleAt 2 ≠ Real.pi / 3)
    (hcor : ∀ j : Fin (2 * k), cnt D idx (P.v j) 0 = 1 ∧ cnt D idx (P.v j) 1 = 1 ∧ cnt D idx (P.v j) 2 = 0) (hk : 3 ≤ k)
    (hint : ∀ E ∈ excVerts2 D idx P, E ∈ interior D.region) (W : Fin (2 * k) → Plane) (hW : ∀ j, GExc D idx (P.v j) (W j)) (E F : Plane)
    (hI : ∃ s0 : Fin (2 * k), ∀ i : Fin (2 * k), ((i - s0).val < k → W i = E) ∧ (k ≤ (i - s0).val → W i = F)) :
    ∀ i : Fin (2 * k), P.side i = P.side (i + (k : Fin (2 * k))) := by
  obtain ⟨a, b, hab, hsp⟩ := spokes_angle D P hreg idx hC h1 h3 hcor hint W hW
  obtain ⟨hang, hMγ⟩ := corner_angles_gamma D P hreg idx hC h1 h3 hcor
  obtain ⟨s0, hs0⟩ := hI
  have hpi := Real.pi_pos
  have hkγ : (k : ℝ) * D.model.angleAt 2 = Real.pi := by
    have : ((2 * k : ℕ) : ℝ) * D.model.angleAt 2 = 2 * Real.pi := hMγ
    push_cast at this; linarith
  have hγ0 := model_angle_pos' D 2
  have hαβγ : D.model.angleAt a + D.model.angleAt b + D.model.angleAt 2 = Real.pi := by
    have := angleAt_sum D.model
    rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact this
    · linarith
  have hab2 : a ≠ 2 ∧ b ≠ 2 := by
    rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  set ι : ℕ → Fin (2 * k) := fun n => (n : Fin (2 * k)) + s0 with hιdef
  have hι : ∀ n, ι (n + 1) = ι n + 1 := by
    intro n; simp only [hιdef]; rw [Nat.cast_succ, add_right_comm]
  have hι2 : ∀ n, ι (n + 2) = ι n + 2 := by
    intro n
    have h := hι (n + 1); rw [hι n] at h
    show ι (n + 1 + 1) = _
    rw [h, add_assoc, one_add_one_eq_two]
  set V : ℕ → Plane := fun n => P.v (ι n) with hV
  have hV1 : ∀ n, V (n + 1) = P.v (ι n + 1) := fun n => by simp only [hV]; rw [hι n]
  have hV2 : ∀ n, V (n + 2) = P.v (ι n + 2) := fun n => by simp only [hV]; rw [hι2 n]
  have hper : ∀ n, V (n + 2 * k) = V n := by
    intro n; simp only [hV, hιdef]; rw [Nat.cast_add]; simp
  have hval : ∀ n, n < 2 * k → ((ι n - s0).val = n) := by
    intro n hn
    simp only [hιdef, add_sub_cancel_right]
    rw [Fin.val_natCast]; exact Nat.mod_eq_of_lt hn
  have hWE : ∀ n, n < k → W (ι n) = E := fun n hn => (hs0 (ι n)).1 (by rw [hval n (by omega)]; exact hn)
  have hWF : ∀ n, k ≤ n → n < 2 * k → W (ι n) = F := fun n h1 h2 => (hs0 (ι n)).2 (by rw [hval n h2]; exact h1)
  have hcr : ∀ n, 0 < cross2 (V (n + 1) - V n) (V (n + 2) - V (n + 1)) := by
    intro n
    have hf := ConvPoly.fin_facts P.three_le (ι n)
    have := P.left (ι n) (ι n + 2) hf.2.1 hf.2.2.1
    rw [hV1 n, hV2 n, cross2_shift]
    exact this
  have hnc : 0 < cross2 (V k - V (k - 1)) (V 0 - V (k - 1)) := by
    obtain ⟨m, hm⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    have hk1 : k - 1 = m := by omega
    rw [hk1]
    have hVk : V k = P.v (ι m + 1) := (congrArg V hm).trans (hV1 m)
    rw [hVk]
    have h0 : V 0 = P.v s0 := by simp [hV, hιdef]
    rw [h0]
    have hne1 : s0 ≠ ι m := by
      intro h
      have h' : (m : Fin (2 * k)) = 0 := by
        have : (m : Fin (2 * k)) + s0 = 0 + s0 := by rw [zero_add]; exact h.symm
        exact add_right_cancel this
      have := (Fin.natCast_eq_zero).mp h'
      have := Nat.le_of_dvd (by omega) this
      omega
    have hne2 : s0 ≠ ι m + 1 := by
      intro h
      have h' : ((m + 1 : ℕ) : Fin (2 * k)) = 0 := by
        have : ((m + 1 : ℕ) : Fin (2 * k)) + s0 = 0 + s0 := by
          rw [zero_add, Nat.cast_succ, add_right_comm]; exact h.symm
        exact add_right_cancel this
      have := (Fin.natCast_eq_zero).mp h'
      have := Nat.le_of_dvd (by omega) this
      omega
    exact P.left (ι m) s0 hne1 hne2
  have hang' : ∀ n, ∠ (V n) (V (n + 1)) (V (n + 2)) = Real.pi - D.model.angleAt 2 := by
    intro n
    have := hang (ι n + 1)
    unfold ConvPoly.angle cornerAngle at this
    rw [add_sub_cancel_right] at this
    have hf := ConvPoly.fin_facts P.three_le (ι n)
    rw [hf.2.2.2.2.2] at this
    rw [hV1 n, hV2 n]
    exact this
  have hEa : ∀ n, n < k → ∠ (V (n + 1)) (V n) E = D.model.angleAt a := by
    intro n hn
    have := (hsp (ι n - 1)).1
    rw [sub_add_cancel] at this
    rw [hWE n hn] at this
    rw [hV1 n]
    exact this
  have hEb : ∀ n, n + 1 < k → ∠ (V n) (V (n + 1)) E = D.model.angleAt b := by
    intro n hn
    have := (hsp (ι n)).2
    have hw : W (ι n + 1) = E := by rw [← hι n]; exact hWE (n + 1) hn
    rw [hw] at this
    rw [hV1 n]
    exact this
  have hFa : ∀ n, k ≤ n → n < 2 * k → ∠ (V (n + 1)) (V n) F = D.model.angleAt a := by
    intro n h1 h2
    have := (hsp (ι n - 1)).1
    rw [sub_add_cancel] at this
    rw [hWF n h1 h2] at this
    rw [hV1 n]
    exact this
  have hFb : ∀ n, k ≤ n → n + 1 < 2 * k → ∠ (V n) (V (n + 1)) F = D.model.angleAt b := by
    intro n h1 h2
    have := (hsp (ι n)).2
    have hw : W (ι n + 1) = F := by rw [← hι n]; exact hWF (n + 1) (by omega) h2
    rw [hw] at this
    rw [hV1 n]
    exact this
  have key := central_symmetry_core hk V E F _ _ _ hper hcr hnc hang' (model_angle_pos' D a) (model_angle_pos' D b) hαβγ hγ0 hkγ hEa hEb hFa hFb
  intro i
  have hn : ((i - s0).val : ℕ) < 2 * k := (i - s0).isLt
  have e0 : ι ((i - s0).val) = i := by
    simp only [hιdef]; rw [Fin.cast_val_eq_self]; exact sub_add_cancel i s0
  have e1 : ι ((i - s0).val + k) = i + (k : Fin (2 * k)) := by
    simp only [hιdef]; rw [Nat.cast_add, Fin.cast_val_eq_self]; abel
  have e2 : ι ((i - s0).val + k + 1) = i + (k : Fin (2 * k)) + 1 := by rw [hι, e1]
  have e3 : ι ((i - s0).val + 1) = i + 1 := by rw [hι, e0]
  have := key (i - s0).val
  simp only [hV, e0, e1, e2, e3] at this
  unfold ConvPoly.side
  rw [this]

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.central_symmetry_of_spokes
