import Origami.Basic

namespace Origami

declare_syntax_cat geo

syntax ident                      : geo
syntax "(" term ")"               : geo

syntax:50 geo:51 " ∥ " geo:51     : geo
syntax:50 geo:51 " ⟂ " geo:51     : geo
syntax:50 geo:51 " ≡ " geo:51     : geo
syntax:50 geo:51 " ∈ " geo:51     : geo
syntax:50 geo:51 " ∉ " geo:51     : geo
syntax:max "¬ " geo:40            : geo
syntax:35 geo:36 " ∧ " geo:35     : geo

syntax "geo{" geo "}" : term

macro_rules
| `(geo{ $x:ident })    => `($x)
| `(geo{ ($t:term) })   => `($t)
| `(geo{ $a ∥ $b })     => `(Origami.Line.Par geo{$a} geo{$b})
| `(geo{ $a ⟂ $b })     => `(Origami.Line.Perp geo{$a} geo{$b})
| `(geo{ $a ≡ $b })     => `(Origami.Line.Same geo{$a} geo{$b})
| `(geo{ $a ∈ $b })     => `(Membership.mem geo{$b} geo{$a})
| `(geo{ $a ∉ $b })     => `(¬ Membership.mem geo{$b} geo{$a})
| `(geo{ ¬ $a })        => `(¬ geo{$a})
| `(geo{ $a ∧ $b })     => `(geo{$a} ∧ geo{$b})

def O1 (p q : ℂ) (f : Line) : Prop := p ∈ f ∧ q ∈ f
def O2 (p q : ℂ) (f : Line) : Prop := f.reflect p = q
def O3 (l m f : Line) : Prop := (f.reflectLine l).Same m
def O4 (p : ℂ) (l f : Line) : Prop := geo{ f ⟂ l ∧ p ∈ f }
def O5 (p q : ℂ) (l f : Line) : Prop := f.reflect p ∈ l ∧ q ∈ f
def O6 (p q : ℂ) (l m f : Line) : Prop :=
    f.reflect p ∈ l ∧ f.reflect q ∈ m
def O7 (p : ℂ) (l m f : Line) : Prop := geo{ f ⟂ m ∧ (f.reflect p) ∈ l }

mutual
inductive GeoConstrPt : ℂ → Prop
| zero : GeoConstrPt 0
| one  : GeoConstrPt 1
| inter {l m : Line} {z : ℂ} : GeoConstrLine l → GeoConstrLine m → ¬ l.Par m
    → z ∈ l → z ∈ m → GeoConstrPt z
| reflect {p : ℂ} {f : Line} : GeoConstrPt p → GeoConstrLine f → GeoConstrPt (f.reflect p)

inductive GeoConstrLine : Line → Prop
| o1 {p q : ℂ} {f : Line} :     -- line through p and q
    GeoConstrPt p → GeoConstrPt q → p ≠ q → O1 p q f → GeoConstrLine f
| o2 {p q : ℂ} {f : Line} :     -- line sending p to q
    GeoConstrPt p → GeoConstrPt q → p ≠ q → O2 p q f → GeoConstrLine f
| o3 {l m f : Line} :           -- angle bisector
    GeoConstrLine l → GeoConstrLine m → ¬ l.Same m → O3 l m f → GeoConstrLine f
| o4 {p : ℂ} {l f : Line} :     -- perp to l through p
    GeoConstrPt p → GeoConstrLine l → O4 p l f → GeoConstrLine f
| o5 {p q : ℂ} {l f : Line} :   -- send p to l, passing through q
    GeoConstrPt p → GeoConstrPt q → GeoConstrLine l → p ≠ q → O5 p q l f → GeoConstrLine f
| o6 {p q : ℂ} {l m f : Line} : -- send p to l and q to m
    GeoConstrPt p → GeoConstrPt q → GeoConstrLine l → GeoConstrLine m →
    p ∉ l → ¬ geo{l ∥ m} →
    O6 p q l m f → GeoConstrLine f
| o7 {p : ℂ} {l m f : Line} :   -- send p to l, perp to m
    GeoConstrPt p → GeoConstrLine l → GeoConstrLine m → ¬ geo{l ∥ m} →
    O7 p l m f → GeoConstrLine f
| same {f g : Line} : GeoConstrLine f → f.Same g → GeoConstrLine g
end

end Origami
