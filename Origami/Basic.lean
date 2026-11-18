import Mathlib

open ComplexConjugate

namespace Origami

structure Line where
  p : ℂ
  d : ℂ
  hd : d ≠ 0

namespace Line

instance : Membership ℂ Line where
  mem l z := ((z - l.p) * conj l.d).im = 0

def Par  (l m : Line) : Prop := (l.d * conj m.d).im = 0
def Perp (l m : Line) : Prop := (l.d * conj m.d).re = 0
def Same (l m : Line) : Prop := Par l m ∧ l.p ∈ m

noncomputable def reflect (f : Line) (z : ℂ) : ℂ :=
  f.p + (f.d / conj f.d) * conj (z - f.p)

noncomputable def reflectLine (f l : Line) : Line where
  p  := f.reflect l.p
  d  := (f.d / conj f.d) * conj l.d
  hd := mul_ne_zero (div_ne_zero f.hd ((map_ne_zero _).2 f.hd))
                    ((map_ne_zero _).2 l.hd)

theorem mem_def (l : Line) (z : ℂ) : z ∈ l ↔ ((z - l.p) * conj l.d).im = 0 := Iff.rfl

theorem mem_iff_conj (l : Line) (z : ℂ) :
    z ∈ l ↔ (z - l.p) * conj l.d = conj (z - l.p) * l.d := by
  rw [mem_def, Complex.ext_iff]
  simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
    Complex.sub_re, Complex.sub_im]
  constructor
  · intro h; exact ⟨by linarith, by linarith⟩
  · rintro ⟨-, h⟩; linarith

theorem d_re_or_im (l : Line) : l.d.re ≠ 0 ∨ l.d.im ≠ 0 := by
  by_contra h
  push Not at h
  exact l.hd (Complex.ext h.1 h.2)

end Line

end Origami
