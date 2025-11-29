/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yury Kudryashov, Kim Morrison
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Lift

/-!
# MonoidAlgebra.mapDomain

-/

@[expose] public section

assert_not_exists NonUnitalAlgHom AlgEquiv

open Function
open Finsupp hiding single mapDomain

noncomputable section

variable {R S M N O : Type*}

/-! ### Multiplicative monoids -/

namespace MonoidAlgebra
variable [Semiring R] [Semiring S] {f : M → N} {a : M} {r : R}

/-- Given a function `f : M → N` between magmas, return the corresponding map `R[M] → R[N]` obtained
by summing the coefficients along each fiber of `f`. -/
@[to_additive (attr := simps) /--
Given a function `f : M → N` between magmas, return the corresponding map `R[M] → R[N]` obtained
by summing the coefficients along each fiber of `f`. -/]
def mapDomain (f : M → N) (x : MonoidAlgebra R M) : MonoidAlgebra R N :=
  .ofCoeff <| Finsupp.mapDomain f x.coeff

@[to_additive (attr := simp)]
lemma mapDomain_zero (f : M → N) : mapDomain f (0 : MonoidAlgebra R M) = 0 := by ext; simp

@[to_additive]
lemma mapDomain_add (f : M → N) (x y : MonoidAlgebra R M) :
    mapDomain f (x + y) = mapDomain f x + mapDomain f y := by
  ext; simp [Finsupp.mapDomain_add]

@[to_additive]
lemma mapDomain_sum (f : M → N) (s : M →₀ S) (v : M → S → MonoidAlgebra R M) :
    mapDomain f (s.sum v) = s.sum fun a b ↦ mapDomain f (v a b) := by
  ext; simp [Finsupp.mapDomain_sum]

@[to_additive (relevant_arg := M) (attr := simp)]
lemma mapDomain_single : mapDomain f (single a r) = single (f a) r := by ext; simp

@[to_additive]
lemma mapDomain_injective (hf : Injective f) : Injective (mapDomain (R := R) f) :=
  ofCoeff_injective.comp <| (Finsupp.mapDomain_injective hf).comp coeff_injective

@[to_additive (dont_translate := R) (attr := simp) mapDomain_one]
theorem mapDomain_one [One M] [One N] {F : Type*} [FunLike F M N] [OneHomClass F M N] (f : F) :
    mapDomain f (1 : MonoidAlgebra R M) = (1 : MonoidAlgebra R N) := by
  simp [one_def]

@[to_additive (dont_translate := R) mapDomain_mul]
theorem mapDomain_mul [Mul M] [Mul N] {F : Type*} [FunLike F M N] [MulHomClass F M N] (f : F)
    (x y : MonoidAlgebra R M) : mapDomain f (x * y) = mapDomain f x * mapDomain f y := by
  simp [mul_def, mapDomain_sum, add_mul, mul_add, sum_mapDomain_index]

variable [Monoid M] [Monoid N] [Monoid O]

variable (R) in
/-- If `f : G → H` is a multiplicative homomorphism between two monoids, then
`Finsupp.mapDomain f` is a ring homomorphism between their monoid algebras. -/
@[to_additive (attr := simps) /--
If `f : G → H` is a multiplicative homomorphism between two monoids, then
`Finsupp.mapDomain f` is a ring homomorphism between their monoid algebras. -/]
def mapDomainRingHom {F : Type*} [FunLike F M N] [MonoidHomClass F M N] (f : F) :
    MonoidAlgebra R M →+* MonoidAlgebra R N where
  toFun := mapDomain f
  map_zero' := mapDomain_zero _
  map_add' := mapDomain_add _
  map_one' := mapDomain_one f
  map_mul' := mapDomain_mul f

attribute [local ext high] ringHom_ext

@[to_additive (dont_translate := R) (attr := simp)]
lemma mapDomainRingHom_id :
    mapDomainRingHom R (MonoidHom.id M) = .id (MonoidAlgebra R M) := by ext <;> simp

@[to_additive (dont_translate := R) (attr := simp)]
lemma mapDomainRingHom_comp (f : N →* O) (g : M →* N) :
    mapDomainRingHom R (f.comp g) = (mapDomainRingHom R f).comp (mapDomainRingHom R g) := by
  ext <;> simp

@[to_additive (dont_translate := R S)]
lemma mapRangeRingHom_comp_mapDomainRingHom (f : R →+* S) (g : M →* N) :
    (mapRangeRingHom N f).comp (mapDomainRingHom R g) =
      (mapDomainRingHom S g).comp (mapRangeRingHom M f) := by aesop

end MonoidAlgebra

namespace MulEquiv
variable [Semiring R] [Semiring S] [Monoid M] [Monoid N]

/-- Isomorphic monoids have isomorphic monoid algebras. -/
@[to_additive (dont_translate := R S)]
def monoidAlgebraCongrLeft (e : R ≃+* S) : MonoidAlgebra R M ≃+* MonoidAlgebra S M :=
  .ofRingHom (MonoidAlgebra.mapRangeRingHom M e) (MonoidAlgebra.mapRangeRingHom M e.symm)
    (by apply MonoidAlgebra.ringHom_ext <;> simp) (by apply MonoidAlgebra.ringHom_ext <;> simp)

/-- Isomorphic rings have isomorphic monoid algebras. -/
@[to_additive (dont_translate := R)]
def monoidAlgebraCongrRight (e : M ≃* N) : MonoidAlgebra R M ≃+* MonoidAlgebra R N :=
  .ofRingHom (MonoidAlgebra.mapDomainRingHom R e) (MonoidAlgebra.mapDomainRingHom R e.symm)
    (by apply MonoidAlgebra.ringHom_ext <;> simp) (by apply MonoidAlgebra.ringHom_ext <;> simp)

end MulEquiv

/-!
#### Conversions between `AddMonoidAlgebra` and `MonoidAlgebra`

We have not defined `k[G] = MonoidAlgebra k (Multiplicative G)`
because historically this caused problems;
since the changes that have made `nsmul` definitional, this would be possible,
but for now we just construct the ring isomorphisms using `RingEquiv.refl _`.
-/

variable (k G) in
/-- The equivalence between `AddMonoidAlgebra` and `MonoidAlgebra` in terms of
`Multiplicative` -/
protected def AddMonoidAlgebra.toMultiplicative [Semiring k] [Add G] :
    AddMonoidAlgebra k G ≃+* MonoidAlgebra k (Multiplicative G) where
  toFun x := .ofCoeff <| x.coeff.mapDomain .ofAdd
  invFun x := .ofCoeff <| x.coeff.mapDomain Multiplicative.toAdd
  left_inv x := by ext; simp
  right_inv x := by ext; simp
  map_add' x y := by simp [Finsupp.mapDomain_add]
  map_mul' x y := by
    classical
    ext
    simp [MonoidAlgebra.coeff_mul, AddMonoidAlgebra.coeff_mul, Finsupp.sum_mapDomain_index, add_mul,
      mul_add, ite_add_zero, Multiplicative.ext_iff]

variable (k G) in
/-- The equivalence between `MonoidAlgebra` and `AddMonoidAlgebra` in terms of `Additive` -/
protected def MonoidAlgebra.toAdditive [Semiring k] [Mul G] :
    MonoidAlgebra k G ≃+* AddMonoidAlgebra k (Additive G) where
  toFun x := .ofCoeff <| x.coeff.mapDomain .ofMul
  invFun x := .ofCoeff <| x.coeff.mapDomain Additive.toMul
  left_inv x := by ext; simp
  right_inv x := by ext; simp
  map_add' x y := by simp [Finsupp.mapDomain_add]
  map_mul' x y := by
    classical
    ext
    simp [MonoidAlgebra.coeff_mul, AddMonoidAlgebra.coeff_mul, Finsupp.sum_mapDomain_index, add_mul,
      mul_add, ite_add_zero, Additive.ext_iff]
