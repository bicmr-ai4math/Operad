import Mathlib.CategoryTheory.Groupoid
import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.BigOperators


set_option autoImplicit false

open CategoryTheory MonoidalCategory Limits
open scoped MonoidalCategory BigOperators

universe v u


noncomputable section temporary_fixes

namespace CategoryTheory.Limits

universe w w₁

variable {β : Type w}

variable {C : Type u} [Category.{v} C]

variable {γ : Type w₁} (ε : β ≃ γ) (f : γ → C)

section

variable [HasProduct f] [HasProduct (f ∘ ε)]

/-- Reindex a categorical product via an equivalence of the index types. -/
def Pi'.reindex : piObj (f ∘ ε) ≅ piObj f :=
  HasLimit.isoOfEquivalence (Discrete.equivalence ε) (Discrete.natIso fun _ => Iso.refl _)

@[reassoc (attr := simp)]
theorem Pi'.reindex_hom_π (b : β) : (Pi'.reindex ε f).hom ≫ Pi.π f (ε b) = Pi.π (f ∘ ε) b := by
  dsimp [Pi'.reindex]
  simp only [HasLimit.isoOfEquivalence_hom_π, Discrete.equivalence_inverse, Discrete.functor_obj,
    Function.comp_apply, Functor.id_obj, Discrete.equivalence_functor, Functor.comp_obj,
    Discrete.natIso_inv_app, Iso.refl_inv, Category.id_comp]
  exact limit.w (Discrete.functor (f ∘ ε)) (Discrete.eqToHom' (ε.symm_apply_apply b))

@[reassoc (attr := simp)]
theorem Pi'.reindex_inv_π (b : β) : (Pi'.reindex ε f).inv ≫ Pi.π (f ∘ ε) b = Pi.π f (ε b) := by
  simp [Iso.inv_comp_eq]

end

end CategoryTheory.Limits

end temporary_fixes


def PermCat := ℕ

namespace PermCat

instance (n : ℕ) : OfNat PermCat n := ⟨n⟩

instance : Groupoid PermCat where
  Hom (n m : ℕ) := Fin n ≃ Fin m
  id (n : ℕ) := .refl _
  comp := .trans
  inv := .symm

end PermCat

variable {ι : Type*} (V : Type u) [Category.{v} V] [MonoidalCategory V]
  [HasFiniteProducts V]

structure Operad extends PermCat ⥤ V where
  unit : 𝟙_ V ⟶ obj 1
  comp {k : ℕ} (n : Fin k → ℕ) :
    (obj k ⊗ ∏ (obj ∘ n)) ⟶ obj (∑ i, n i : ℕ)
  unit_comp (n : ℕ) : (λ_ (obj n)).inv ≫
    (unit ⊗ (productUniqueIso (obj ∘ ![n])).inv) ≫ comp ![n] = 𝟙 (obj n)
  comp_unit (n : ℕ) :
    (rightUnitor (obj n)).inv ≫ (𝟙 _ ⊗ (Pi.lift (fun _ ↦ unit))) ≫
      comp (fun _ : Fin n ↦ 1) ≫ eqToHom (by simp) = 𝟙 (obj n)
  equivariance {k : ℕ} (e : Fin k ≃ Fin k) (n : Fin k → ℕ) :
    (map e ⊗ 𝟙 _) ≫ comp n =
      (𝟙 _ ⊗ (Pi'.reindex e (obj ∘ n)).inv) ≫ comp (n ∘ e) ≫ eqToHom
      (congr_arg obj (Equiv.sum_comp e n))

