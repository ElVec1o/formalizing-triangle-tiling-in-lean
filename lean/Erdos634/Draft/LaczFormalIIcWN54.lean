-- Draft/LaczFormalIIcWN54.lean -- Laczkovich (DCG 48 (2012), Sect. 6.3), Lemma 6.2 (`IIcNoKites`), step (h), part 15:
-- `inv_step`: from a pocket one obtains a strictly smaller pocket (concave vertex in the pocket by `pocket_concave`; its chord ends inside the pocket by a winding
-- argument; sub-pocket by `sub_arc`).
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcWN53

open scoped Classical Fin.NatCast
open Complex Filter Topology

namespace Erdos634.Draft.LaczFormal.WN

variable {n : ℕ} [NeZero n]

theorem arcQ_ok {p : Fin n → ℂ} (hs : SimplePoly p) (hinj : Function.Injective p) (a : Fin n) {d : ℕ} (hd2 : 2 ≤ d) (hdn : d + 2 ≤ n)
    (hopen : ∀ s : ℝ, 0 < s → s < 1 → p (phi a d) + (s : ℂ) * (p a - p (phi a d)) ∉ edgeSet p) :
    SimplePoly (arcPoly p a d) ∧ Function.Injective (arcPoly p a d) := by
  have hc1 := chord_closed_sub hopen
  have hc1' : ∀ z ∈ segment ℝ (p (phi a d)) (p a), z ∈ edgeSet p → z = p a ∨ z = p (phi a d) :=
    fun z hz hE => (hc1 z hz hE).symm
  exact ⟨arc_simple hs hinj a hd2 hdn hc1', arc_inj hinj a (by omega)⟩

theorem inv_step {p : Fin n → ℂ} (hs : SimplePoly p) (hinj : Function.Injective p) (hn : 3 ≤ n) {σ : ℝ} (Op : OrientOK p σ)
    {J : Fin n → Fin n} (F : ChordFam p σ J) {a : Fin n} {d : ℕ} (hI : Inv p σ J a d) :
    ∃ a' d', d' < d ∧ Inv p σ J a' d' := by
  have hI' := hI
  obtain ⟨hd2, hdn, hcase, σQ, OQ, hσQ⟩ := hI'
  obtain ⟨hchQ, hdisQ⟩ := inv_data F hI
  have hopen := hchQ.1
  have hσ1 := Op.1.1
  obtain ⟨hSQ, hIQ⟩ := arcQ_ok hs hinj a hd2 hdn hopen
  obtain ⟨k, hk1, hk2, hkc⟩ := pocket_concave p a hd2 OQ hσQ
  have hch' : ExtChord p (p (phi a k)) (p (J (phi a k))) := F.chord _ hkc
  have hk'a : phi a k ≠ a := by
    intro h
    have h0 : phi a k = phi a 0 := by rw [h]; simp [phi]
    have := phi_inj_nat a (by omega) (by omega) h0
    omega
  have hk'd : phi a k ≠ phi a d := by
    intro h
    have := phi_inj_nat a (by omega) (by omega) h
    omega
  have hdis' := hdisQ _ hkc hk'a hk'd
  set k' := phi a k with hk'
  set j' := J k' with hj'
  have hjnot : p j' ∉ segment ℝ (p (phi a d)) (p a) := Set.disjoint_left.1 hdis' (right_mem_segment ℝ _ _)
  have hj_a : j' ≠ a := fun h => hjnot (by rw [h]; exact right_mem_segment ℝ _ _)
  have hj_d : j' ≠ phi a d := fun h => hjnot (by rw [h]; exact left_mem_segment ℝ _ _)
  have hjk : j' ≠ k' := (extChord_ne hch').1
  set i' := (j' - a).val with hi'
  have hphi : phi a i' = j' := by unfold phi; rw [Fin.cast_val_eq_self]; exact add_sub_cancel a j'
  have hi'n : i' < n := (j' - a).isLt
  have hi0 : i' ≠ 0 := by
    intro h; apply hj_a; rw [← hphi, h]; simp [phi]
  have hid : i' ≠ d := by
    intro h; apply hj_d; rw [← hphi, h]
  have hik : i' ≠ k := by
    intro h; apply hjk; rw [← hphi, h]
  -- the chord of the family at k' is off Q and disjoint from the pocket chord
  have hoffQ : ∀ s : ℝ, 0 < s → s < 1 → p k' + (s : ℂ) * (p j' - p k') ∉ edgeSet (arcPoly p a d) := by
    intro s hs0 hs1 hmem
    rcases edgeSet_arc_sub p a d hmem with h | h
    · exact hch'.1 s hs0 hs1 h
    · exact Set.disjoint_left.1 hdis' (chord_pt_mem _ _ hs0.le hs1.le) h
  -- (A) the chord ends in the pocket
  have hin : i' < d := by
    by_contra hge
    push Not at hge
    have hgt : d < i' := lt_of_le_of_ne hge (Ne.symm hid)
    obtain ⟨σ1, σ2, O1, O2⟩ := arc_pair_orient hs hinj a hd2 hdn hopen
    have hσ1Q : σ1 = σQ := orient_unique hSQ hIQ (by omega) O1 OQ
    have hsg := chord_signs hinj a hd2 hdn hopen O1.1 O2.1 hchQ.2
    have hσ2 : σ2 = σ := by
      have := hsg.1 rfl
      rw [hσ1Q, hσQ] at this
      linarith
    -- Q-value along the chord from k'
    obtain ⟨s0, hs0, hnear⟩ := arc_chord_near hs hinj hn a Op OQ k hk1 hk2 hch'
    set s1 : ℝ := min (s0 / 2) (1 / 2) with hs1
    have hs1pos : 0 < s1 := lt_min (by linarith) (by norm_num)
    have hs1lt : s1 < s0 := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hs1lt1 : s1 < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
    have hwQ1 : wind (arcPoly p a d) (p k' + (s1 : ℂ) * (p j' - p k')) = -σ := by
      have := (hnear s1 hs1pos hs1lt hs1lt1).2 hσQ
      rw [this, hσQ]
    -- B near j'
    set m := i' - d with hm
    have hm1 : 1 ≤ m := by omega
    have hm2 : m + 1 ≤ n - d := by omega
    have hjm : phi (phi a d) m = j' := by rw [phi_phi, ← hphi]; congr 1; omega
    have hyB : ExtChord p (p (phi (phi a d) m)) (p k') := by rw [hjm]; exact hch'.symm
    obtain ⟨t0, ht0, hnearB⟩ := arc_chord_near hs hinj hn (phi a d) Op O2 m hm1 hm2 hyB
    set t1 : ℝ := min (t0 / 2) (1 / 2) with ht1
    have ht1pos : 0 < t1 := lt_min (by linarith) (by norm_num)
    have ht1lt : t1 < t0 := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have ht1lt1 : t1 < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
    have hwB := (hnearB t1 ht1pos ht1lt ht1lt1).1 hσ2
    rw [hjm] at hwB
    -- the point z = p j' + t1 (p k' - p j')
    have hzeq : p j' + (t1 : ℂ) * (p k' - p j') = p k' + ((1 - t1 : ℝ) : ℂ) * (p j' - p k') := by push_cast; ring
    have hwQ : wind (arcPoly p a d) (p j' + (t1 : ℂ) * (p k' - p j')) = -σ := by
      rw [hzeq, ← hwQ1]
      exact (wind_const_on_chord _ hoffQ (by linarith) (by linarith) hs1pos hs1lt1)
    have hzE : p j' + (t1 : ℂ) * (p k' - p j') ∉ edgeSet p := by
      have := hch'.symm.1 t1 ht1pos ht1lt1
      exact this
    have hzC : p j' + (t1 : ℂ) * (p k' - p j') ∉ segment ℝ (p (phi a d)) (p a) := by
      rw [hzeq]
      exact fun h => Set.disjoint_left.1 hdis' (chord_pt_mem _ _ (by linarith) (by linarith)) h
    have hsplit := wind_split p a (by omega : d ≤ n) hzE hzC
    have hw0 : wind p (p j' + (t1 : ℂ) * (p k' - p j')) = 0 := hch'.symm.wind_zero ht1pos ht1lt1
    rw [hw0, hwQ, hwB] at hsplit
    rcases hσ1 with h | h <;> rw [h] at hsplit <;> norm_num at hsplit
  have hi1 : 1 ≤ i' := by omega
  -- (B) the sub-pocket
  rcases lt_or_gt_of_ne hik with hlt | hgt
  · -- i' < k : arc from j' to k'
    have hch2 : ExtChord p (p (phi a i')) (p (phi a k)) := by rw [hphi]; exact hch'.symm
    have hdis2 : ∀ z ∈ segment ℝ (p (phi a i')) (p (phi a k)), z ∉ segment ℝ (p (phi a d)) (p a) := by
      intro z hz
      rw [hphi, segment_symm] at hz
      exact Set.disjoint_left.1 hdis' hz
    obtain ⟨h2, σ', O', hσ'⟩ := sub_arc hs hinj hn Op a hd2 hdn hopen OQ hσQ hi1 hlt (by omega) hch2 hdis2
    refine ⟨phi a i', k - i', by omega, h2, by omega, Or.inr ⟨?_, ?_⟩, σ', O', hσ'⟩
    · rw [phi_phi, show i' + (k - i') = k by omega]; exact hkc
    · rw [phi_phi, show i' + (k - i') = k by omega, hphi]
  · -- k < i'
    have hch2 : ExtChord p (p (phi a k)) (p (phi a i')) := by rw [hphi]; exact hch'
    have hdis2 : ∀ z ∈ segment ℝ (p (phi a k)) (p (phi a i')), z ∉ segment ℝ (p (phi a d)) (p a) := by
      intro z hz
      rw [hphi] at hz
      exact Set.disjoint_left.1 hdis' hz
    obtain ⟨h2, σ', O', hσ'⟩ := sub_arc hs hinj hn Op a hd2 hdn hopen OQ hσQ hk1 hgt (by omega) hch2 hdis2
    refine ⟨phi a k, i' - k, by omega, h2, by omega, Or.inl ⟨hkc, ?_⟩, σ', O', hσ'⟩
    rw [phi_phi, show k + (i' - k) = i' by omega, hphi]

end Erdos634.Draft.LaczFormal.WN
