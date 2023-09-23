import Mathlib.CategoryTheory.Groupoid
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Sum.Basic
import Mathlib.Logic.Equiv.Fin
import Mathlib.Data.List.FinRange
import Mathlib.CategoryTheory.Limits.Preserves.Basic


set_option autoImplicit false

open CategoryTheory MonoidalCategory Limits
open scoped MonoidalCategory BigOperators

universe v u v₁ v₂ v₀ u₁ u₂ x

def PermCat := ℕ

namespace PermCat

instance (n : ℕ) : OfNat PermCat n := ⟨n⟩

instance : Groupoid PermCat where
  Hom (n m : ℕ) := Fin n ≃ Fin m
  id (n : ℕ) := .refl _
  comp := .trans
  inv := .symm

end PermCat

variable (V : Type u) [Category.{v} V] [HasFiniteProducts V]


noncomputable section temporary_fixes

namespace CategoryTheory.Limits

universe w w₁

variable {β : Type w}

variable {C : Type u} [Category.{v} C]

section

variable {γ : Type w₁} (ε : β ≃ γ) (f : γ → C)

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

@[simp]
theorem qaq (X : C) (Y : C) [inst : HasFiniteProducts C]
  : (∏ (pairFunction X Y)) = prod X Y := by rfl



instance {k : ℕ} : Finite (Fin k × WalkingPair)
  := by
  let q : Fin k × WalkingPair ≃ Fin k ⊕ Fin k
    := by
    let toFun (y : Fin k × WalkingPair) : Fin k ⊕ Fin k
      := match y with
      | ⟨x, WalkingPair.left⟩ => Sum.inl x
      | ⟨x, WalkingPair.right⟩ => Sum.inr x
    let invFun (x : Fin k ⊕ Fin k) : Fin k × WalkingPair 
      := match x with
      | Sum.inl y => ⟨y, WalkingPair.left⟩
      | Sum.inr y => ⟨y, WalkingPair.right⟩
    let left_inv x : (invFun (toFun x)) = x := by
      match x with
      | ⟨x, WalkingPair.left⟩ => rfl
      | ⟨x, WalkingPair.right⟩ => rfl
      
    let right_inv y : (toFun (invFun y)) = y := by
      match y with
      | Sum.inl y => rfl
      | Sum.inr y => rfl
    exact {toFun := toFun, invFun := invFun, left_inv := left_inv, right_inv := right_inv}
  exact (Finite.intro (Equiv.trans q finSumFinEquiv))

instance {k : ℕ} : Finite (WalkingPair × Fin k)
  := Finite.of_equiv (Fin k × WalkingPair) (Equiv.prodComm (Fin k) WalkingPair)


def lem1 {k : ℕ} (As : Fin k → C) (Bs : Fin k → C) [inst : HasFiniteProducts C]
  : ∏ (fun x => (As x) ⨯ (Bs x)) ≅
    ∏ (fun (p : (_ : Fin k) × WalkingPair) => (pairFunction (As p.fst) (Bs p.fst) p.snd))
  := piPiIso (fun _ => WalkingPair) (fun (j : Fin k) => (pairFunction (As j) (Bs j)))

def lem2 {k : ℕ} (As : Fin k → C) (Bs : Fin k → C) [inst : HasFiniteProducts C]
  : ∏ (fun (p : (_ : Fin k) × WalkingPair) => (pairFunction (As p.fst) (Bs p.fst) p.snd)) ≅
    ∏ (fun (p : (_ : WalkingPair) × Fin k) => (pairFunction (As p.snd) (Bs p.snd) p.fst))
  := Pi'.reindex
    (((Equiv.sigmaEquivProd (Fin k) WalkingPair).trans (Equiv.prodComm (Fin k) WalkingPair)).trans (Equiv.sigmaEquivProd WalkingPair (Fin k)).symm)
    (fun (p : (_ : WalkingPair) × Fin k) => (pairFunction (As p.snd) (Bs p.snd) p.fst))

def lem3 {k : ℕ} (As : Fin k → C) (Bs : Fin k → C) [inst : HasFiniteProducts C]
  : ∏ (fun x => ∏ fun y => pairFunction (As y) (Bs y) x) ≅
    ∏ (fun (p : (_ : WalkingPair) × Fin k) => (pairFunction (As p.snd) (Bs p.snd) p.fst))
  := piPiIso (fun _ => (Fin k)) (fun x => fun y => (pairFunction (As y) (Bs y) x))

@[simp]
theorem lem4 {k : ℕ} (As : Fin k → C) (Bs : Fin k → C) [inst : HasFiniteProducts C]
  (x : WalkingPair) : (∏ fun y => pairFunction (As y) (Bs y) x) = (WalkingPair.casesOn x (∏ fun y => (As y)) (∏ fun y => (Bs y)))
  := by
    match x with
    | WalkingPair.left =>
      dsimp
      simp
    | WalkingPair.right =>
      dsimp
      simp

def lem5 {k : ℕ} (As : Fin k → C) (Bs : Fin k → C) [inst : HasFiniteProducts C]
  : ∏ (fun x => ∏ fun y => pairFunction (As y) (Bs y) x) ≅
    (∏ As) ⨯ (∏ Bs)
  := by
    simp [lem4]
    rfl

def piProdIsoProdPi {k : ℕ} (As : Fin k → C) (Bs : Fin k → C) [inst : HasFiniteProducts C]
  : ∏ (fun x => (As x) ⨯ (Bs x)) ≅ (∏ As) ⨯ (∏ Bs)
  := (lem1 As Bs) ≪≫ (lem2 As Bs) ≪≫ (lem3 As Bs).symm ≪≫ (lem5 As Bs)

def lem6 {obj : PermCat → V} {k : ℕ} {j : Fin k → ℕ} (i : (s : Fin k) → Fin (j s) → ℕ) :
  ∏ (fun y => ∏ (obj ∘ (i y))) ≅ ∏ (fun (y : Σ i, Fin (j i)) => obj (i y.fst y.snd))
  := piPiIso (fun i => Fin (j i)) (fun x => fun y : Fin (j x) => obj (i x y))



end CategoryTheory.Limits

end temporary_fixes

-- by @Cloudifold
def sigmaFinSucc {k : ℕ} (f : Fin (k + 1) → Type u) : (Σ n, f n) ≃ Sum (f 0) (Σ n, f (Fin.succ n)) :=
  ⟨fun x =>
    @Sigma.casesOn (Fin (k + 1)) f (fun _ => Sum (f 0) (Σ n, f (Fin.succ n))) x fun n =>
      @Fin.cases k (fun i => f i → Sum (f 0) (Σn , f (Fin.succ n))) (fun x : f 0 => Sum.inl x)
        (fun (z : (Fin k)) (x : f z.succ) => Sum.inr ⟨z, x⟩) n,
    Sum.elim (Sigma.mk 0) (Sigma.map Fin.succ fun _ => id), by rintro ⟨n | n, x⟩ <;> rfl, by rintro (x | ⟨n, x⟩) <;> rfl⟩

def sigmaFinEquivFoldrSumFin : (k : ℕ) → (j : Fin k → ℕ) → (Σ i, Fin (j i)) ≃ (List.foldr (Sum) (Fin 0) (List.map Fin (Vector.toList (Vector.ofFn j))))
  := by 
  intro k
  intro j
  match k with
  | 0 => 
    let toFun (x : (Σ i, Fin (j i))) : (List.foldr (Sum) (Fin 0) (List.map Fin (Vector.toList (Vector.ofFn j))))
      := @finZeroElim (fun _ => (List.foldr (Sum) (Fin 0) (List.map Fin (Vector.toList (Vector.ofFn j))))) (Sigma.fst x)
    let invFun (x : (List.foldr (Sum) (Fin 0) (List.map Fin (Vector.toList (Vector.ofFn j))))) : (Σ i, Fin (j i))
      := ⟨(@finZeroElim (fun _ => Fin 0) x), (@finZeroElim (fun _ => Fin (j (@finZeroElim (fun _ => Fin 0) x))) x)⟩
    let left_inv x : (invFun (toFun x)) = x := by
      dsimp
      simp
    let right_inv y : (toFun (invFun y)) = y := by
      dsimp
      simp
    exact { toFun := toFun, invFun := invFun, left_inv := left_inv, right_inv := right_inv}
  | w + 1 => 
    let toFun (x : (Σ i, Fin (j i))) : (List.foldr (Sum) (Fin 0) (List.map Fin (Vector.toList (Vector.ofFn j))))
      := Sum.map id (sigmaFinEquivFoldrSumFin w (fun y => j (Fin.succ y))).toFun ((sigmaFinSucc (fun y => Fin (j y))).toFun x)
    let invFun (y : (List.foldr (Sum) (Fin 0) (List.map Fin (Vector.toList (Vector.ofFn j))))) : (Σ i, Fin (j i))
        := (sigmaFinSucc (fun z => Fin (j z))).invFun (Sum.map id (sigmaFinEquivFoldrSumFin w (fun z => j (Fin.succ z))).invFun y)
    let left_inv x : (invFun (toFun x)) = x := by
      dsimp
      simp
    let right_inv y : (toFun (invFun y)) = y := by
      dsimp
      simp
    exact {toFun := toFun, invFun := invFun, left_inv := left_inv, right_inv := right_inv}

def foldrSumFinEquivFinFoldrAdd : (v : List ℕ) → (List.foldr (Sum) (Fin 0) (List.map Fin v)) ≃ Fin (List.foldr Nat.add 0 v)
  := by
    intro v
    match v with
    | [] => dsimp; exact {toFun := id, invFun := id, left_inv := fun x => rfl, right_inv := fun x => rfl}
    | a :: l =>
      let toFun (x : Fin a ⊕ List.foldr Sum (Fin 0) (List.map Fin l)) : Fin (a + List.foldr Nat.add 0 l)
        := finSumFinEquiv.toFun (Sum.map id (foldrSumFinEquivFinFoldrAdd l).toFun x)
      let invFun (y : Fin (a + List.foldr Nat.add 0 l)) : Fin a ⊕ List.foldr Sum (Fin 0) (List.map Fin l)
        := Sum.map id (foldrSumFinEquivFinFoldrAdd l).invFun (finSumFinEquiv.invFun y)
      let left_inv x : (invFun (toFun x)) = x := by
        dsimp
        simp
      let right_inv y : (toFun (invFun y)) = y := by
        dsimp
        simp
      exact {toFun := toFun, invFun := invFun, left_inv := left_inv, right_inv := right_inv}
  
def piEquivFinToEquivSigmaFin {k : ℕ} (j : Fin k → ℕ) (τ : (s : Fin k) → Fin (j s) ≃  Fin (j s)) : (Σ i, Fin (j i)) ≃ Σ i, Fin (j i)
  :=
    let toFun : (Σ i, Fin (j i)) → (Σ i, Fin (j i))
      := fun ⟨a, b⟩ => ⟨a, (τ a).toFun b⟩
    let invFun : (Σ i, Fin (j i)) → (Σ i, Fin (j i))
      := fun ⟨a, b⟩ => ⟨a, (τ a).invFun b⟩
    let left_inv x : (invFun (toFun x)) = x := by
        dsimp
        simp
      let right_inv y : (toFun (invFun y)) = y := by
        dsimp
        simp
    {toFun := toFun, invFun := invFun, left_inv := left_inv, right_inv := right_inv}


def sigmaFinEquivFinFoldrAdd {k : ℕ} (j : Fin k → ℕ) : (Σ i, Fin (j i)) ≃ Fin (List.foldr Nat.add 0 (Vector.toList (Vector.ofFn j)))
  := Equiv.trans (sigmaFinEquivFoldrSumFin k j) (foldrSumFinEquivFinFoldrAdd (Vector.toList (Vector.ofFn j)))

@[simp]
theorem foldrAddEqsum {k : ℕ} (j : Fin k → ℕ) : List.foldr (fun x y => x + y) 0 (Vector.toList (Vector.ofFn j)) = ∑ i, j i
  := by
      simp [Vector.toList_ofFn]
      simp [Fin.univ_def]
      rw [←List.sum_eq_foldr]
      simp [List.ofFn_eq_map]


def finFoldrAddEquivFinsum {k : ℕ} (j : Fin k → ℕ) : Fin (List.foldr Nat.add 0 (Vector.toList (Vector.ofFn j))) ≃ Fin (∑ i, j i)
  := finCongr (foldrAddEqsum j)

def sigmaFinEquivFinsum {k : ℕ} {j : Fin k → ℕ} : (Σ i, Fin (j i)) ≃ Fin (∑ i, j i)
  := Equiv.trans (sigmaFinEquivFinFoldrAdd j) (finFoldrAddEquivFinsum j)

def piSymmActionOnFinsum {k : ℕ} {j : Fin k → ℕ} (τ : (s : Fin k) → Fin (j s) ≃  Fin (j s)) : Fin (∑ i, j i) ≃ Fin (∑ i, j i)
  := Equiv.trans (Equiv.trans (Equiv.symm sigmaFinEquivFinsum) (piEquivFinToEquivSigmaFin j τ)) sigmaFinEquivFinsum 
/--/
instance limPreserveLimits  {J : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁}     J] {C : Type u} [inst : CategoryTheory.Category.{v, u}    C] [inst : CategoryTheory.Limits.HasLimitsOfShape J C] 
  : CategoryTheory.Limits.PreservesLimitsOfSize.{v, u} CategoryTheory.Limits.lim
  := CategoryTheory.Adjunction.rightAdjointPreservesLimits CategoryTheory.Limits.constLimAdj
-/


def cc {k : ℕ} {j : Fin k → ℕ} (i : (s : Fin k) → Fin (j s) → ℕ) (x : Fin (∑ s, j s)) : ℕ
  := (Sigma.uncurry i) (sigmaFinEquivFinsum.symm x)

@[simp]
theorem ccDef {k : ℕ} {j : Fin k → ℕ} (i : (s : Fin k) → Fin (j s) → ℕ) (x : Fin (∑ s, j s)) :
  cc i x = (Sigma.uncurry i) (sigmaFinEquivFinsum.symm x)
  := by rfl
-- theorem haha {k : ℕ} {j : Fin k → ℕ} (i : (s : Fin k) → Fin (j s) → ℕ) :

@[simp]
theorem ha {k : ℕ} {j : Fin k → ℕ} (i : (s : Fin k) → Fin (j s) → ℕ) :
  (∑ s, (cc i s) : ℕ) = (∑ x, (cc i (sigmaFinEquivFinsum x)))
  := Fintype.sum_equiv sigmaFinEquivFinsum.symm (fun (y : Fin (∑ s, j s)) => ((cc i) y)) (fun x => (cc i (sigmaFinEquivFinsum x))) (by (intro x; simp))

@[simp]
theorem haa {k : ℕ} {j : Fin k → ℕ} (i : (s : Fin k) → Fin (j s) → ℕ) :
  (∑ x, (cc i (sigmaFinEquivFinsum x))) = (∑ x, Sigma.uncurry i x)
  := Fintype.sum_equiv (by rfl) (fun x => (cc i (sigmaFinEquivFinsum x))) (fun x => Sigma.uncurry i x)
    (by
      intro x
      dsimp
      simp
      )

@[simp]
theorem haha {k : ℕ} {j : Fin k → ℕ} (i : (s : Fin k) → Fin (j s) → ℕ) :
  (∑ x, Sigma.uncurry i x : ℕ) = (∑ x ,∑ y, i x y : ℕ)
  := Finset.sum_sigma Finset.univ (fun (_ : Fin k) => Finset.univ) (Sigma.uncurry i)

@[simp]
theorem hahaha {k : ℕ} {j : Fin k → ℕ} (i : (s : Fin k) → Fin (j s) → ℕ) :
  (∑ s, (cc i s) : ℕ) = (∑ x ,∑ y, i x y : ℕ)
  := by rw [ha, haa, haha]


section

variable (obj : PermCat → V) {k : ℕ} {j : Fin k → ℕ} (i : (s : Fin k) → Fin (j s) → ℕ)



noncomputable def finSumShuffleToProdPi :
  ∏ (obj ∘ (cc i)) ≅ ∏ (fun y => ∏ (obj ∘ (i y)))
  := (Pi'.reindex sigmaFinEquivFinsum.symm (fun (y : Σ i, Fin (j i)) => obj (i y.fst y.snd)))
    ≪≫ (piPiIso (fun s => Fin (j s)) (fun x => fun y : Fin (j x) => obj (i x y))).symm

  
noncomputable def prodPiShufflePiProd :
  (obj k) ⨯ ∏ (obj ∘ j) ⨯ ∏ (fun y => ∏ (obj ∘ (i y))) ≅ (obj k) ⨯ ∏ (fun x => (obj (j x)) ⨯ (∏ (obj ∘ (i x))))
  := prod.mapIso (CategoryTheory.Iso.refl _) (piProdIsoProdPi (obj ∘ j) (fun y => ∏ (obj ∘ (i y)))).symm

noncomputable def shuffle :
  (obj k) ⨯ ∏ (obj ∘ j) ⨯ ∏ (obj ∘ (cc i))
  ≅ (obj k) ⨯ ∏ (fun x => (obj (j x)) ⨯ (∏ (obj ∘ (i x))))
  := (prod.mapIso (CategoryTheory.Iso.refl _) (prod.mapIso (CategoryTheory.Iso.refl _) (finSumShuffleToProdPi V obj i)))
    ≪≫ prodPiShufflePiProd V obj i


noncomputable def m1 (comp : (k : ℕ) → (j : Fin k → ℕ) →  (obj k ⨯ ∏ (obj ∘ j)) ⟶ obj (∑ i, j i : ℕ)) :
  (obj k) ⨯ ∏ (obj ∘ j) ⨯ ∏ (obj ∘ (cc i)) ⟶ obj (∑ s, (cc i s) : ℕ)
  :=
  ((CategoryTheory.Limits.prod.associator (obj k) (∏ (obj ∘ j)) (∏ (obj ∘ (cc i)))).symm).hom
  ≫ (prod.map (comp k j) (𝟙 (∏ (obj ∘ (cc i)))))
  ≫ comp (∑ i, j i : ℕ) (cc i)


noncomputable def r1 (comp : (k : ℕ) → (j : Fin k → ℕ) →  (obj k ⨯ ∏ (obj ∘ j)) ⟶ obj (∑ i, j i : ℕ)) :
  (obj k) ⨯ ∏ (fun x => (obj (j x)) ⨯ (∏ (obj ∘ (i x)))) ⟶ obj (∑ x ,∑ y, i x y : ℕ)
  :=
  prod.map (𝟙 _) (CategoryTheory.Limits.Pi.map (fun x => comp (j x) (i x)))
  ≫ comp k (fun x => (∑ y, i x y : ℕ)) 

def i1 : obj (∑ x ,∑ y, i x y : ℕ) ≅ obj (∑ s, (cc i s) : ℕ)
  := by rw [hahaha]
  

end


structure Operad extends PermCat ⥤ V where
  point : obj 0 ≅ ⊤_ V
  unit : ⊤_ V ⟶ obj 1
  comp {k : ℕ} (j : Fin k → ℕ) :
    (obj k ⨯ ∏ (obj ∘ j)) ⟶ obj (∑ i, j i : ℕ)
  unit_comp (n : ℕ) : (prod.leftUnitor (obj n)).inv ≫
    (prod.map unit (productUniqueIso (obj ∘ ![n])).inv) ≫ comp ![n] = 𝟙 (obj n)
  comp_unit (n : ℕ) :
    (prod.rightUnitor (obj n)).inv ≫ (prod.map (𝟙 _) (Pi.lift (fun _ ↦ unit))) ≫
      comp (fun _ : Fin n ↦ 1) ≫ eqToHom (by simp) = 𝟙 (obj n)
  equivariance_sort {k : ℕ} (e : Fin k ≃ Fin k) (j : Fin k → ℕ) :
    (prod.map (map e) (𝟙 _)) ≫ comp j =
      (prod.map (𝟙 _) (Pi'.reindex e (obj ∘ j)).inv) ≫ comp (j ∘ e) ≫ eqToHom
      (congr_arg obj (Equiv.sum_comp e j))
  equivariance_comp {k : ℕ} (j : Fin k → ℕ) (τ : (s : Fin k) → Fin (j s) ≃  Fin (j s)) : 
    (prod.map (𝟙 _) (CategoryTheory.Limits.Pi.map (fun x => map (τ x)))) ≫ comp j = comp j ≫ (map (piSymmActionOnFinsum τ))
  associativity {k : ℕ} (j : Fin k → ℕ) (i : (s : Fin k) → Fin (j s) → ℕ) :
    (m1 V obj i @comp) = ((shuffle V obj i).hom ≫ (r1 V obj i @comp) ≫ (i1 V obj i).hom)
  

  
