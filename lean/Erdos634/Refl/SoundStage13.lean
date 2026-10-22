import Erdos634.Refl.SoundStage12

/-! Stage 13: the assembled `checkNode_sound` (proved), with two hypotheses the skeleton lacked. -/

set_option linter.unusedSimpArgs false
open Erdos634.CertNode Erdos634.PlacementCompleteness Erdos634.SixPlacements
open Erdos634.Geometry (Plane)

namespace Refl

theorem unit_re (Dn : ℝ) (hD : 0 < Dn) (I : Inst) (hDn : (I.Dn : ℝ) = Dn) (d : Pt) (hdw : 0 < d.w)
    (hdu : d.x * d.x + I.Dn * d.y * d.y = d.w * d.w) :
    (d.re Dn) 0 ^ 2 + (d.re Dn) 1 ^ 2 = 1 := by
  have h := congrArg (fun z : Int => (z : ℝ)) hdu
  push_cast at h
  rw [hDn] at h
  have hw := Pt.w_pos d hdw
  show (rp Dn d.X d.Y) 0 ^ 2 + (rp Dn d.X d.Y) 1 ^ 2 = 1
  rw [rp_zero, rp_one, mul_pow, sr_sq hD]
  unfold Pt.X Pt.Y
  field_simp
  nlinarith [h]

theorem checkNode_sound (Dn : ℝ) (hD : 0 < Dn) (I : Inst) (hDn : (I.Dn : ℝ) = Dn)
    (M : Erdos634.Geometry.Tri)
    (hMa : dist (M.pts 0) (M.pts 1) = I.sides.1) (hMb : dist (M.pts 1) (M.pts 2) = I.sides.2.1)
    (hMc : dist (M.pts 0) (M.pts 2) = I.sides.2.2)
    (hI : I.ok = true) (hY : I.baseY = true) :
    ∀ (fuel : Nat) (cfg : List _root_.Tri) (n : Node), (∀ t ∈ cfg, t.ok = true) →
      checkNode I fuel cfg n = true → Sound Dn I M cfg := by
  obtain ⟨htok, hDpos, p1, p2, p3, p4, p5, p6, hpl, o1, o2, o3, o4, o5, o6⟩ := Inst_ok_facts I hI
  intro fuel
  induction fuel with
  | zero => intro cfg n _ h; simp [checkNode] at h
  | succ fuel ih =>
    intro cfg n hcfgok hchk N D htg hm hreal
    classical
    simp only [checkNode, Bool.and_eq_true] at hchk
    obtain ⟨hloc, hkills⟩ := hchk
    have F := nodeLocalOk_facts I cfg n hloc
    set S : Finset (Fin N) := Finset.univ.filter (fun i => ∃ t ∈ cfg, (D.tile i).carrier = t.carr Dn) with hSdef
    have hS : ∀ t ∈ cfg, ∃ i ∈ S, (D.tile i).carrier = t.carr Dn := by
      intro t ht
      obtain ⟨i, hi⟩ := hreal t ht
      exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, t, ht, hi⟩, hi⟩
    have hSt : ∀ i ∈ S, ∃ t ∈ cfg, (D.tile i).carrier = t.carr Dn := by
      intro i hi
      exact (Finset.mem_filter.mp hi).2
    have hyT : ∀ p ∈ D.target.carrier, 0 ≤ p 1 := by
      rw [htg]; exact tgt_y_nonneg Dn hD I htok hY
    have hlex := hlex_sound Dn hD I htok cfg hcfgok n F D htg S hS
    have hfree := hfree_sound Dn hD I hDn htok cfg hcfgok n F D htg S hSt
    have hblocked := hblocked_sound Dn hD I hDn cfg hcfgok n F D S hS (fun _ => hyT)
    have hunit := unit_re Dn hD I hDn n.d F.dw F.unit
    obtain ⟨j, hjS, k0, k1, k2, h01, h02, h12, hk0, ⟨c', hc', hk1⟩, hk2⟩ :=
      placement_completeness D.toDissection S (n.v.re Dn) (n.d.re Dn) hunit hlex hfree hblocked
    have hcong : (D.tile j).Congruent M := (D.tiles_congruent j).trans hm
    have hsix := six_placements hcong hMa hMb hMc hunit h01 h02 h12 hk0 hc' hk1 hk2
    -- the numerics of every placement
    have hpos : ∀ p ∈ I.pl, 0 < p.l1 ∧ 0 < p.pd ∧ 0 < p.qd ∧ 0 < p.qn := by
      intro p hp
      rw [hpl] at hp
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
      · have := placeOk_facts I _ _ _ _ o1; exact ⟨this.1, this.2.1, this.2.2.1, this.2.2.2.1⟩
      · have := placeOk_facts I _ _ _ _ o2; exact ⟨this.1, this.2.1, this.2.2.1, this.2.2.2.1⟩
      · have := placeOk_facts I _ _ _ _ o3; exact ⟨this.1, this.2.1, this.2.2.1, this.2.2.2.1⟩
      · have := placeOk_facts I _ _ _ _ o4; exact ⟨this.1, this.2.1, this.2.2.1, this.2.2.2.1⟩
      · have := placeOk_facts I _ _ _ _ o5; exact ⟨this.1, this.2.1, this.2.2.1, this.2.2.2.1⟩
      · have := placeOk_facts I _ _ _ _ o6; exact ⟨this.1, this.2.1, this.2.2.1, this.2.2.2.1⟩
    -- one of the six placements is realised by tile `j`
    have hrealj : ∃ p ∈ I.pl, (D.tile j).carrier = (placeTri I n.v n.d p).carr Dn := by
      have key := fun (l1 l2 l3 : Int) (p : Place) (hp : placeOk I l1 l2 l3 p = true)
          (h1 : (D.tile j).pts k1 = n.v.re Dn + (l1 : ℝ) • n.d.re Dn)
          (h2 : (D.tile j).pts k2 = placeThird (n.v.re Dn) (n.d.re Dn) l1 l2 l3) =>
        place_sound Dn hD I hDn n.v n.d F.vw F.dw F.unit l1 l2 l3 p hp (D.tile j) h01 h02 h12 hk0 h1 h2
      rcases hsix with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨p1, by simp [hpl], key _ _ _ p1 o1 h1 h2⟩
      · exact ⟨p2, by simp [hpl], key _ _ _ p2 o2 h1 h2⟩
      · exact ⟨p3, by simp [hpl], key _ _ _ p3 o3 h1 h2⟩
      · exact ⟨p4, by simp [hpl], key _ _ _ p4 o4 h1 h2⟩
      · exact ⟨p5, by simp [hpl], key _ _ _ p5 o5 h1 h2⟩
      · exact ⟨p6, by simp [hpl], key _ _ _ p6 o6 h1 h2⟩
    obtain ⟨pj, hpj, hjc⟩ := hrealj
    have hreal' : ∀ t ∈ cfg, ∃ i, i ≠ j ∧ (D.tile i).carrier = t.carr Dn := by
      intro t ht
      obtain ⟨i, hiS, hi⟩ := hS t ht
      exact ⟨i, fun h => hjS (h ▸ hiS), hi⟩
    refine killsSound Dn hD I hDn htok n.v n.d F.vw F.dw F.unit cfg hcfgok D htg j hreal'
      (fun c cfg' => checkNode I fuel cfg' c) n.kills I.pl n.children hpos ?_ hkills pj hpj hjc
    intro c p hp hrec hj
    obtain ⟨pl1, ppd, pqd, pqn⟩ := hpos p hp
    have htri := placeTri_ok I n.v n.d p F.vw F.dw F.unit hDpos pl1 ppd pqd pqn
    refine ih (cfg ++ [placeTri I n.v n.d p]) c ?_ hrec D htg hm ?_
    · intro t ht
      rcases List.mem_append.mp ht with h | h
      · exact hcfgok t h
      · simp only [List.mem_singleton] at h; subst h; exact htri
    · intro t ht
      rcases List.mem_append.mp ht with h | h
      · exact hreal t h
      · simp only [List.mem_singleton] at h; subst h; exact ⟨j, hj⟩

#print axioms Refl.checkNode_sound

theorem checkAll_sound (Dn : ℝ) (hD : 0 < Dn) (I : Inst) (hDn : (I.Dn : ℝ) = Dn)
    (M : Erdos634.Geometry.Tri)
    (hMa : dist (M.pts 0) (M.pts 1) = I.sides.1) (hMb : dist (M.pts 1) (M.pts 2) = I.sides.2.1)
    (hMc : dist (M.pts 0) (M.pts 2) = I.sides.2.2) (hY : I.baseY = true) (fuel : Nat) (n : Node)
    (h : I.checkAll fuel n = true) : Sound Dn I M [] := by
  unfold Inst.checkAll at h
  simp only [Bool.and_eq_true] at h
  exact checkNode_sound Dn hD I hDn M hMa hMb hMc h.1 hY fuel [] n (by simp) h.2

#print axioms Refl.checkAll_sound

end Refl
