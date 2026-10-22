-- Draft/LaczFormalIIcWN49.lean -- Laczkovich (DCG 48 (2012)), Sect. 6.3, Lemma 6.2 (`IIcNoKites`), step (h), part 10:
-- `ExtChord` (a chord whose open part misses the polygon and along which the winding number is 0, i.e. an exterior chord), its basic properties,
-- `chord_arc_param` (an exterior chord between two vertices is `p a -- p (a+d)` with 2 <= d <= n-2), and `arc_pair_orient` (both pieces of a chord split have orientations).
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcWN48

open scoped Classical Fin.NatCast
open Complex Filter Topology

namespace Erdos634.Draft.LaczFormal.WN

variable {n : ℕ} [NeZero n]

/-- `x -- y` is an exterior chord of `p`: its open part misses the polygon, and the winding number about its midpoint is 0. -/
def ExtChord (p : Fin n → ℂ) (x y : ℂ) : Prop :=
  (∀ s : ℝ, 0 < s → s < 1 → x + (s : ℂ) * (y - x) ∉ edgeSet p) ∧ wind p (x + ((1 / 2 : ℝ) : ℂ) * (y - x)) = 0

theorem ExtChord.symm {p : Fin n → ℂ} {x y : ℂ} (h : ExtChord p x y) : ExtChord p y x := by
  refine ⟨fun s hs0 hs1 => ?_, ?_⟩
  · have := h.1 (1 - s) (by linarith) (by linarith)
    have e : y + (s : ℂ) * (x - y) = x + ((1 - s : ℝ) : ℂ) * (y - x) := by push_cast; ring
    rw [e]; exact this
  · have e : y + ((1 / 2 : ℝ) : ℂ) * (x - y) = x + ((1 / 2 : ℝ) : ℂ) * (y - x) := by push_cast; ring
    rw [e]; exact h.2

theorem ExtChord.wind_zero {p : Fin n → ℂ} {x y : ℂ} (h : ExtChord p x y) {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    wind p (x + (s : ℂ) * (y - x)) = 0 := by
  have := wind_const_segment p (u := x + ((1 / 2 : ℝ) : ℂ) * (y - x)) (v := x + (s : ℂ) * (y - x)) (by
    intro z hz
    rw [segment_eq_image'] at hz
    obtain ⟨θ, ⟨hθ0, hθ1⟩, rfl⟩ := hz
    have e : x + ((1 / 2 : ℝ) : ℂ) * (y - x) + θ • (x + (s : ℂ) * (y - x) - (x + ((1 / 2 : ℝ) : ℂ) * (y - x))) =
        x + (((1 / 2 : ℝ) + θ * (s - 1 / 2) : ℝ) : ℂ) * (y - x) := by
      simp only [Complex.real_smul]; push_cast; ring
    beta_reduce
    rw [e]
    apply h.1
    · nlinarith
    · nlinarith)
  rw [← this]; exact h.2

theorem extChord_ne {p : Fin n → ℂ} {a b : Fin n} (h : ExtChord p (p a) (p b)) : b ≠ a ∧ b ≠ a + 1 ∧ a ≠ b + 1 := by
  refine ⟨?_, ?_, ?_⟩
  · rintro rfl
    apply h.1 (1 / 2) (by norm_num) (by norm_num)
    simpa using vertex_mem_edgeSet p b
  · rintro rfl
    apply h.1 (1 / 2) (by norm_num) (by norm_num)
    refine Set.mem_iUnion.2 ⟨a, ?_⟩
    rw [segment_eq_image']
    exact ⟨1 / 2, ⟨by norm_num, by norm_num⟩, by first | (simp only [Complex.real_smul]; push_cast; ring) | (simp only [Complex.real_smul]; push_cast) | simp only [Complex.real_smul]⟩
  · rintro rfl
    apply h.1 (1 / 2) (by norm_num) (by norm_num)
    refine Set.mem_iUnion.2 ⟨b, ?_⟩
    rw [segment_eq_image']
    exact ⟨1 / 2, ⟨by norm_num, by norm_num⟩, by first | (simp only [Complex.real_smul]; push_cast; ring) | (simp only [Complex.real_smul]; push_cast) | simp only [Complex.real_smul]⟩

theorem chord_arc_param {p : Fin n → ℂ} (hn : 3 ≤ n) {a b : Fin n} (h : ExtChord p (p a) (p b)) :
    ∃ d : ℕ, phi a d = b ∧ 2 ≤ d ∧ d + 2 ≤ n := by
  obtain ⟨h1, h2, h3⟩ := extChord_ne h
  have hone : (1 : Fin n).val = 1 := by rw [Fin.val_one']; exact Nat.mod_eq_of_lt (by omega)
  refine ⟨(b - a).val, ?_, ?_, ?_⟩
  · unfold phi; rw [Fin.cast_val_eq_self]; exact add_sub_cancel a b
  · by_contra hc
    have : (b - a).val = 0 ∨ (b - a).val = 1 := by omega
    rcases this with h0 | h0
    · apply h1
      have : b - a = 0 := Fin.ext (by simpa using h0)
      exact sub_eq_zero.1 this
    · apply h2
      have : b - a = 1 := Fin.ext (by rw [h0, hone])
      rw [sub_eq_iff_eq_add] at this
      rw [this, add_comm]
  · by_contra hc
    have hlt := (b - a).isLt
    have hd : (b - a).val = n - 1 := by omega
    apply h3
    have : b - a = -1 := by
      rw [← Fin.cast_val_eq_self (b - a), hd, cast_pred (by omega)]
    rw [sub_eq_iff_eq_add] at this
    rw [this]; abel

end Erdos634.Draft.LaczFormal.WN
