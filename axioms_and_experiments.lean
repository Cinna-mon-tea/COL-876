import Mathlib
import SystemE.Theory.Sorts.Primitives
import SystemE.Theory.Relations

namespace LeanGeo

-- SystemE gives us: Point, Line, Circle, Point.onLine, between, collinear
-- We add origami-specific primitives on top:

axiom foldPoint : Line → Point → Point
axiom foldLine : Line → Line → Line
axiom isPerp : Line → Line → Prop

axiom length_symm (p q : Point) : length p q = length q p
axiom length_geq_zero (p q : Point) : length p q ≥ 0
axiom length_zero (p q : Point) : length p q = 0 ↔ p = q

axiom fold_fixes_Line (p : Point) (f : Line) :
  p.onLine f → foldPoint f p = p
axiom Line_fixes_fold (p : Point) (f : Line) :
  foldPoint f p = p → p.onLine f
axiom id_iff_onLine (p : Point) (f : Line) :
  foldPoint f p = p ↔ p.onLine f
axiom fold_involution_point (f : Line) (p : Point) :
  foldPoint f (foldPoint f p) = p
axiom fold_isometry (f : Line) (p q : Point) :
  length (foldPoint f p) (foldPoint f q) = length p q

axiom fold_perp (l f : Line) :
  isPerp f l ↔ foldLine l f = l

axiom O1 : Point → Point → Line → Prop
-- Given two points p1 and p2, we can fold a line connecting them
axiom O1_char (p q : Point) (f : Line):
  -- p.onLine (O1 p q) ∧ q.onLine (O1 p q)
  O1 p q f ↔ p.onLine f ∧ q.onLine f
axiom O1_ex (p q : Point):
  ∃ f : Line, O1 p q f

axiom O2 : Point → Point → Line → Prop
-- Given two points p1 and p2, we can fold p1 onto p2
axiom O2_char (p q : Point):
  -- foldPoint (O2 p q) p = q
  O2 p q f ↔ foldPoint f p = q
axiom O2_ex (p q : Point):
  ∃ f : Line, O2 p q f

axiom O3 : Line → Line → Line → Prop
-- Given two lines l1 and l2, we can fold line l1 onto l2
axiom O3_char (l m f : Line):
  -- foldLine l1 (O3 l1 l2) = l2
  O3 l m f ↔ foldLine l f = m
axiom O3_ex (l m f : Line):
  ∃ f : Line, O3 l m f

axiom O4 : Point → Line → Line → Prop
-- Given a point p1 and a line l1, we can make a fold
-- perpendicular to l1
-- passing through p1
axiom O4_char (p : Point) (l : Line):
  -- isPerp (O4 p l) l ∧ p.onLine (O4 p l)
  O4 p l f ↔ isPerp f l ∧ p.onLine f
axiom O4_ex (p : Point) (l : Line):
  ∃ f : Line, O4 p l f

axiom O5 : Point → Point → Line → Line → Prop
-- Given two points p1 and p2 and a line l1, we can make a fold that
-- places p1 onto l1
-- passes through p2
axiom O5_char (p q : Point) (l : Line):
  -- (foldPoint (O5 p q l) p).onLine l ∧ q.onLine (O5 p q l)
  O5 p q l f ↔ (foldPoint f p).onLine l ∧ q.onLine f
axiom O5_ex (p q : Point) (l : Line):
  ∃ f : Line, O5 p q l f

axiom O6 : Point → Point → Line → Line → Line → Prop
-- Given two points p1 and p2 and two lines l1 and l2, we can make a fold that
-- places p1 onto l1
-- places p2 onto l2
axiom O6_char (p q : Point) (l m : Line):
  -- (foldPoint (O6 p q l m) p).onLine l ∧ (foldPoint (O6 p q l m) q).onLine m
  O6 p q l m f ↔ (foldPoint f p).onLine l ∧ (foldPoint f q).onLine m
axiom O6_ex (p q : Point) (l m : Line):
  ∃ f : Line, O6 p q l m f

axiom O7 : Point → Line → Line → Line → Prop
-- Given a point p1 and two lines l1 and l2, we can make a fold
-- perpendicular to l2
-- places p1 onto l1
axiom O7_char (p : Point) (l m : Line):
  -- isPerp (O7 p l m) m ∧ (foldPoint (O7 p l m) p).onLine l
  O7 p l m f ↔ isPerp f m ∧ (foldPoint f p).onLine l
axiom O7_ex (p : Point) (l m : Line) :
  ∃ f : Line, O7 p l m f

inductive Alignment_1F : Type where
| A1 (p q : Point)          -- Fold point onto point
| A2 (l m : Line)           -- Fold line onto line
| A3 (l : Line)             -- Fold line onto itself
| A4 (p : Point) (l : Line) -- Fold point onto line
| A5 (p : Point)            -- Fold line through point

def Satisfies_1F (f : Line) (a : Alignment_1F) : Prop :=
match a with
| .A1 p q => foldPoint f p = q
| .A2 l m => foldLine l f = m
| .A3 l => isPerp f l
| .A4 p l => (foldPoint f p).onLine l
| .A5 p => p.onLine f

inductive HJAxiom : Type where
| O1 (p1 p2 : Point)
| O2 (p1 p2 : Point)
| O3 (l1 l2 : Line)
| O4 (p1 : Point) (l1 : Line)
| O5 (p1 p2 : Point) (l1 : Line)
| O6 (p1 p2 : Point) (l1 l2 : Line)
| O7 (p1 : Point) (l1 l2 : Line)

def SatisfiesHJA (f : Line) (ax : HJAxiom) : Prop :=
match ax with
| .O1 p1 p2 => Satisfies_1F f (.A5 p1) ∧ Satisfies_1F f (.A5 p2)
| .O2 p1 p2 => Satisfies_1F f (.A1 p1 p2)
| .O3 l1 l2 => Satisfies_1F f (.A2 l1 l2)
| .O4 p1 l1 => Satisfies_1F f (.A3 l1) ∧ Satisfies_1F f (.A5 p1)
| .O5 p1 p2 l1 => Satisfies_1F f (.A4 p1 l1) ∧ Satisfies_1F f (.A5 p2)
| .O6 p1 p2 l1 l2 => Satisfies_1F f (.A4 p1 l1) ∧ Satisfies_1F f (.A4 p2 l2)
| .O7 p1 l1 l2 => Satisfies_1F f (.A3 l2) ∧ Satisfies_1F f (.A4 p1 l1)

inductive AlignmentSet_1F : Type where
| single2Eq (a : Alignment_1F) : AlignmentSet_1F
| pair1Eq (a b : Alignment_1F) : AlignmentSet_1F

def SatisfiesSet (f : Line) (as : AlignmentSet_1F) : Prop :=
match as with
| .single2Eq a => Satisfies_1F f a
| .pair1Eq a b => Satisfies_1F f a ∧ Satisfies_1F f b

-- every HJA corresponds to a valid alignment set
theorem hja_to_alignment (hja : HJAxiom) (f : Line) :
SatisfiesHJA f hja → ∃ (s : AlignmentSet_1F), SatisfiesSet f s := by
  intro h
  cases hja with
  | O1 p q =>
    exact ⟨.pair1Eq (.A5 p) (.A5 q), h⟩
  | O2 p q =>
    exact ⟨.single2Eq (.A1 p q), h⟩
  | O3 l m =>
    exact ⟨.single2Eq (.A2 l m), h⟩
  | O4 p l =>
    exact ⟨.pair1Eq (.A3 l) (.A5 p), h⟩
  | O5 p q l =>
    exact ⟨.pair1Eq (.A4 p l) (.A5 q), h⟩
  | O6 p q l m =>
    exact ⟨.pair1Eq (.A4 p l) (.A4 q m), h⟩
  | O7 p l m =>
    exact ⟨.pair1Eq (.A3 m) (.A4 p l), h⟩

theorem alignment_to_hja (a : AlignmentSet_1F) (f : Line) :
SatisfiesSet f a → ∃ (hja : HJAxiom), SatisfiesHJA f hja := by
  intro h
  cases a with
  | single2Eq b =>
    cases b with
    | A1 p q =>
      rw [SatisfiesSet] at h
      rw [Satisfies_1F] at h
      exists HJAxiom.O2 p q
    | A2 l m =>
      rw [SatisfiesSet] at h
      rw [Satisfies_1F] at h
      exists HJAxiom.O3 l m
    | A3 l =>
      rw [SatisfiesSet] at h
      rw [Satisfies_1F] at h
      rw[fold_perp] at h
      exists HJAxiom.O3 l l
    | A4 p l =>
      rw [SatisfiesSet] at h
      rw [Satisfies_1F] at h
      let q := foldPoint f p
      exists HJAxiom.O2 p q
    | A5 p =>
      rw [SatisfiesSet] at h
      rw [Satisfies_1F] at h
      exists HJAxiom.O2 p p
      rw [SatisfiesHJA, Satisfies_1F, id_iff_onLine]
      assumption
  | pair1Eq b c =>
    cases b with
    | A1 p q =>
      rw [SatisfiesSet] at h
      obtain ⟨h1, h2⟩ := h
      rw [Satisfies_1F] at h1
      cases c with
      | A1 p1 q1 =>
        rw [Satisfies_1F] at h2
        obtain ⟨l, hl⟩ := O1_ex p p1
        obtain ⟨m, hm⟩ := O1_ex q q1
        exists HJAxiom.O3 l m
        sorry
      | A2 l1 m1 =>
        sorry
      | A3 l1 =>
        sorry
      | A4 p1 l1 =>
        sorry
      | A5 p1 =>
        sorry
    | A2 l m =>
      rw [SatisfiesSet] at h
      rw [Satisfies_1F] at h
      cases c with
      | A1 p1 q1 =>
        sorry
      | A2 l1 m1 =>
        sorry
      | A3 l1 =>
        sorry
      | A4 p1 l1 =>
        sorry
      | A5 p1 =>
        sorry
    | A3 l =>
      rw [SatisfiesSet] at h
      rw [Satisfies_1F] at h
      rw[fold_perp] at h
      cases c with
      | A1 p1 q1 =>
        sorry
      | A2 l1 m1 =>
        sorry
      | A3 l1 =>
        sorry
      | A4 p1 l1 =>
        sorry
      | A5 p1 =>
        sorry
    | A4 p l =>
      rw [SatisfiesSet] at h
      rw [Satisfies_1F] at h
      let q := foldPoint f p
      exists HJAxiom.O2 p q
    | A5 p =>
      rw [SatisfiesSet] at h
      rw [Satisfies_1F] at h
      cases c with
      | A1 p1 q1 =>
        sorry
      | A2 l1 m1 =>
        sorry
      | A3 l1 =>
        sorry
      | A4 p1 l1 =>
        sorry
      | A5 p1 =>
        sorry


theorem alignA1_symm (f : Line) (p1 p2 : Point) :
    foldPoint f p1 = p2 ↔ foldPoint f p2 = p1 := by
  constructor
  · intro h
    rw [← h]
    exact fold_involution_point f p1
  · intro h
    rw [← h]
    exact fold_involution_point f p2

theorem fold_preserves_dist
    (f : Line) (p q r : Point)
    (hfold : foldPoint f p = q)
    (hq : r.onLine f) : length r p = length r q := by
  nth_rw 2 [← fold_fixes_Line r f hq]
  rw [← fold_isometry f r p, hfold]

theorem fold_injective (f : Line) (p q : Point)
    (h : foldPoint f p = foldPoint f q) : p = q := by
  rw[
    alignA1_symm f p (foldPoint f q),
    fold_involution_point f q
  ] at h
  rw [eq_comm]
  assumption

-- right angle path: OA ⊥ AT
-- point lies between two others on a line
axiom onSegment (p a b : Point) : Prop  -- p between a and b on the line
axiom isParallel : Line → Line → Prop
-- a point is at a specific distance along a line from another point
axiom atDist (p q : Point) (l : Line) (d : ℝ) : Prop

-- 3 similar triangles with common sides give the cube root
-- X = (0, x) on y-axis, Y = (y, 0) on x-axis
-- OAX ~ OXY ~ OYB similar right triangles
-- |OA| = 1, |OB| = 2

theorem beloch_cube_root_coords (x y c : ℝ)
    (hx : x ≠ 0) (hy : y > 0)
    (h1 : x / 1 = y / x)      -- OAX ~ OXY
    (h2 : y / x = c / y) :    -- OXY ~ OYB
    x ^ 3 = c := by
  have hxy : y = x ^ 2 := by
    field_simp at h1
    rw [eq_comm]
    assumption
  have hx3 : x ^ 3 = c := by
    have : y ^ 2 = c * x := by
      field_simp at h2
      rw [mul_comm]
      assumption
    rw [hxy] at this
    field_simp at this
    assumption
  assumption

-- every point has coordinates
axiom coords : Point → ℝ × ℝ
axiom coords_injective (p q : Point) : coords p = coords q → p = q

-- every line has an equation
axiom lineEq : Line → (ℝ × ℝ × ℝ)  -- (a, b, c) for ax + by + c = 0

-- onLine in terms of coordinates
axiom onLine_coords (p : Point) (l : Line) :
  p.onLine l ↔
  let (a, b, c) := lineEq l
  let (x, y) := coords p
  a * x + b * y + c = 0

axiom len_coords (a b : Point):
  let ⟨xa, ya⟩ := coords a
  let ⟨xb, yb⟩ := coords b
  (length a b)^2 = (xa - xb)^2 + (ya - yb)^2

axiom foldPoint_coords (f : Line)
    (p1 p2 : Point)  -- two points determining the fold line f
    (hfp1 : p1.onLine f) (hfp2 : p2.onLine f) (hne : p1 ≠ p2)
    (pt : Point) :   -- the point being reflected
  let px := (coords p1).1; let py := (coords p1).2
  let qx := (coords p2).1; let qy := (coords p2).2
  let x  := (coords pt).1; let y  := (coords pt).2
  let dx := qx - px;       let dy := qy - py
  let d2 := dx^2 + dy^2
  let dot := dx*(x - px) + dy*(y - py)
  coords (foldPoint f pt) =
    (2*(px + dx*dot/d2) - x,
    2*(py + dy*dot/d2) - y)

theorem beloch_cube_root_from_O6 (c : ℝ)
    (A B X Y : Point)
    (r s f : Line)
    (hA : coords A = (-1, 0))
    (hB : coords B = (0, -c))
    (hX : (coords X).1 = 0)
    (hY : (coords Y).2 = 0)
    (hXpos : (coords X).2 ≠ 0)
    (hYpos : (coords Y).1 > 0)
    (hXf : X.onLine f)
    (hYf : Y.onLine f)
    (hXY : X ≠ Y)
    (hr : ∀ p : Point, p.onLine r ↔ (coords p).1 = 1) -- r' is the line x = 1
    (hs : ∀ p : Point, p.onLine s ↔ (coords p).2 = c) -- s' is the line y = c
    (hfold : O6 A B r s f) :
    (coords X).2 ^ 3 = c := by
  rw [O6_char] at hfold
  obtain ⟨hA_on_r, hB_on_s⟩ := hfold
  rw [hr] at hA_on_r
  rw [hs] at hB_on_s
  have hfA := foldPoint_coords f X Y hXf hYf hXY A
  have hfB := foldPoint_coords f X Y hXf hYf hXY B
  grind

theorem lill_cubic (a₂ a₁ a₀ : ℝ) (ha₀ : a₀ ≠ 0)
    (O T X Y : Point)

    (hO : coords O = (0, 0))
    (hT : coords T = (1 - a₁, a₂ - a₀))
    (hX : (coords X).1 = 1)
    (hY : (coords Y).2 = a₂)

    (r s f : Line)
    (hr  : ∀ p : Point, p.onLine r  ↔ (coords p).1 = 2)
    (hs  : ∀ p : Point, p.onLine s  ↔ (coords p).2 = a₂ + a₀)
    (hXf : X.onLine f) (hYf : Y.onLine f) (hXY : X ≠ Y)

    (hfold : O6 O T r s f) :

  let t := -(coords X).2
  t^3 + a₂ * t^2 + a₁ * t + a₀ = 0 := by

  intro t
  rw [O6_char] at hfold
  have hfO := foldPoint_coords f X Y hXf hYf hXY O
  have hfT := foldPoint_coords f X Y hXf hYf hXY T
  set y := (coords Y).1 with hy_def

  have hd : (y - 1) ^ 2 + (a₂ + t) ^ 2 ≠ 0 := by
    intro h
    have h1 : y - 1 = 0 := by nlinarith
    have h2 : a₂ + t = 0 := by nlinarith
    apply hXY
    apply coords_injective
    grind

  grind

inductive IsOrigamiConstructible : ℝ → Prop where
  | rat (q : ℚ) : IsOrigamiConstructible q
  | add {x y : ℝ} : IsOrigamiConstructible x → IsOrigamiConstructible y →
      IsOrigamiConstructible (x + y)
  | mul {x y : ℝ} : IsOrigamiConstructible x → IsOrigamiConstructible y →
      IsOrigamiConstructible (x * y)
  | neg {x : ℝ} : IsOrigamiConstructible x → IsOrigamiConstructible (-x)
  | inv {x : ℝ} : IsOrigamiConstructible x → IsOrigamiConstructible x⁻¹
  | sqrt {x : ℝ} : IsOrigamiConstructible x → IsOrigamiConstructible (Real.sqrt x)
  | cbrt {x : ℝ} : IsOrigamiConstructible x → IsOrigamiConstructible (x ^ ((1:ℝ)/3))

def OrigamiConstructible : Set ℝ := {x | IsOrigamiConstructible x}

lemma origami_zero : IsOrigamiConstructible 0 := by
  exact_mod_cast IsOrigamiConstructible.rat 0

lemma origami_one : IsOrigamiConstructible 1 := by
  exact_mod_cast IsOrigamiConstructible.rat 1

lemma origami_sub {x y : ℝ} (hx : IsOrigamiConstructible x)
    (hy : IsOrigamiConstructible y) : IsOrigamiConstructible (x - y) := by
  rw [sub_eq_add_neg]
  exact .add hx (.neg hy)

lemma origami_div {x y : ℝ} (hx : IsOrigamiConstructible x)
    (hy : IsOrigamiConstructible y) : IsOrigamiConstructible (x / y) := by
  rw [div_eq_mul_inv]
  exact .mul hx (.inv hy)

def origamiSubfield : Subfield ℝ where
  carrier := OrigamiConstructible
  add_mem' hx hy := .add hx hy
  mul_mem' hx hy := .mul hx hy
  neg_mem' hx := .neg hx
  inv_mem' _ hx := .inv hx
  one_mem' := origami_one
  zero_mem' := origami_zero

inductive isOrigamiConstructible : ℝ → Type where
  | rat (q : ℚ) : isOrigamiConstructible q
  | add {x y : ℝ} : isOrigamiConstructible x → isOrigamiConstructible y →
      isOrigamiConstructible (x + y)
  | mul {x y : ℝ} : isOrigamiConstructible x → isOrigamiConstructible y →
      isOrigamiConstructible (x * y)
  | neg {x : ℝ} : isOrigamiConstructible x → isOrigamiConstructible (-x)
  | inv {x : ℝ} : isOrigamiConstructible x → isOrigamiConstructible x⁻¹
  | sqrt {x : ℝ} : isOrigamiConstructible x → isOrigamiConstructible (Real.sqrt x)
  | cbrt {x : ℝ} : isOrigamiConstructible x → isOrigamiConstructible (x ^ ((1:ℝ)/3))

-- lemma origami_constructible_degree (x : ℝ) (hx : IsOrigamiConstructible x) :
--     ∃ (K : IntermediateField ℚ ℝ) (a b : ℕ),
--       x ∈ K ∧ Module.finrank ℚ K = 2^a * 3^b := by
--   induction hx with
--   | rat q =>
--     exact ⟨⊥, 0, 0, by exact_mod_cast IntermediateField.algebraMap_mem ⊥ q, by simp⟩

--   | add x y ihx ihy =>
--     obtain ⟨Kx, ax, bx, hxKx, hdx⟩ := ihx
--     obtain ⟨Ky, ay, by_, hyKy, hdy⟩ := ihy
--     refine ⟨Kx ⊔ Ky, ax + ay, bx + by_, ?_, ?_⟩
--     · apply IntermediateField.add_mem
--       · have h : Kx ≤ Kx ⊔ Ky := le_sup_left
--         exact h hxKx
--       · have h : Ky ≤ Kx ⊔ Ky := le_sup_right
--         exact h hyKy
--     · sorry -- degree of compositum divides lcm, still of form 2^a*3^b

--     | mul x y ihx ihy =>
--     obtain ⟨Kx, ax, bx, hxKx, hdx⟩ := ihx
--     obtain ⟨Ky, ay, by_, hyKy, hdy⟩ := ihy
--     refine ⟨Kx ⊔ Ky, ax + ay, bx + by_, ?_, ?_⟩
--     · apply IntermediateField.mul_mem
--       · have h : Kx ≤ Kx ⊔ Ky := le_sup_left
--         exact h hxKx
--       · have h : Ky ≤ Kx ⊔ Ky := le_sup_right
--         exact h hyKy
--     · sorry

--   | neg x ihx =>
--     obtain ⟨K, a, b, hxK, hd⟩ := ihx
--     exact ⟨K, a, b, IntermediateField.neg_mem _ hxK, hd⟩

--   | inv x ihx =>
--     obtain ⟨K, a, b, hxK, hd⟩ := ihx
--     exact ⟨K, a, b, IntermediateField.inv_mem _ hxK, hd⟩

--   | sqrt x ihx => sorry

--   | cbrt x ihx => sorry

end LeanGeo
