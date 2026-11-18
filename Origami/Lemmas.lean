import Origami.Tactics
import Origami.Geo

namespace Origami
open Line

theorem reflect_reflect (f : Line) (z : ℂ) : f.reflect (f.reflect z) = z := by
  line_auto

theorem reflect_eq_self_iff (f : Line) (z : ℂ) : f.reflect z = z ↔ z ∈ f := by
  line_facts
  rw [mem_iff_conj]
  unfold reflect
  conj_simp
  constructor
  · intro h
    field_simp at h
    linear_combination (-1 : ℂ) * h
  · intro h
    field_simp
    linear_combination (-1 : ℂ) * h

theorem par_refl (l : Line) : geo{l ∥ l} := by
  unfold Par
  to_re_im
  line_arith

theorem par_symm {l m : Line} (h : geo{l ∥ m}) : geo{m ∥ l} := by
  unfold Par at *
  to_re_im at *
  linarith

theorem par_trans {l m n : Line} (h₁ : geo{l ∥ m}) (h₂ : geo{m ∥ n}) : geo{l ∥ n} := by
  line_facts
  unfold Par at *
  to_re_im at *
  rcases m_ri with h | h <;>
  {apply (mul_left_cancel₀ h); simp; right; grind}

theorem mem_self (l : Line) : l.p ∈ l := by simp [Line.mem_def]

theorem same_symm {l m : Line} (h : l.Same m) : m.Same l := by
  obtain ⟨hp, hm⟩ := h
  constructor
  · exact par_symm hp
  · rw [mem_def] at *
    rw [Par] at hp
    rcases d_re_or_im m <;>
    {to_re_im at *; grind}

theorem same_trans {l m n : Line} (h₁ : l.Same m) (h₂ : m.Same n) : l.Same n := by
  obtain ⟨p₁, q₁⟩ := h₁
  obtain ⟨p₂, q₂⟩ := h₂
  refine ⟨par_trans p₁ p₂, ?_⟩
  line_facts
  unfold Line.Par at *
  rw [mem_def] at *
  to_re_im at *
  simp
  rcases m_ri with h | h <;>
  {apply mul_left_cancel₀ h; grind}

instance : Setoid Line where
  r := Line.Same
  iseqv := ⟨fun l => ⟨par_refl l, mem_self l⟩, same_symm, same_trans⟩

end Origami
