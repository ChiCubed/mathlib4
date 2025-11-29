/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yury Kudryashov, Kim Morrison
-/
module

public import Mathlib.Algebra.MonoidAlgebra.MapDomain
public import Mathlib.Algebra.Ring.Opposite
public import Mathlib.Data.Finsupp.Basic

/-!
# Monoid algebras and the opposite ring
-/

@[expose] public section

assert_not_exists NonUnitalAlgHom AlgEquiv

noncomputable section

open Finsupp hiding single

universe u₁ u₂ u₃ u₄

variable (k : Type u₁) (G : Type u₂) (H : Type*) {R S M : Type*}

/-! ### Multiplicative monoids -/

namespace MonoidAlgebra

variable {k G}

open Finsupp MulOpposite

variable [Semiring k]

/-- The opposite of a `MonoidAlgebra R I` equivalent as a ring to
the `MonoidAlgebra Rᵐᵒᵖ Iᵐᵒᵖ` over the opposite ring, taking elements to their opposite. -/
@[simps! +simpRhs apply symm_apply]
protected noncomputable def opRingEquiv [Mul G] :
    (MonoidAlgebra k G)ᵐᵒᵖ ≃+* MonoidAlgebra kᵐᵒᵖ Gᵐᵒᵖ where
  toAddEquiv := opAddEquiv.symm.trans <| opEquiv.monoidAlgebraCongrRight.trans
    opAddEquiv.monoidAlgebraCongrLeft
  map_mul' := by
    classical
    simp [-opEquiv_apply, coeff_mul, MonoidAlgebra.ext_iff, Finsupp.ext_iff, ← MulOpposite.unop_inj,
      sum_mapRange_index, sum_mapDomain_index, mul_add, add_mul, ite_add_zero, apply_ite op]
    simpa using fun _ _ _ ↦ Finsupp.sum_comm ..

theorem opRingEquiv_single [Mul G] (r : k) (x : G) :
    MonoidAlgebra.opRingEquiv (op (single x r)) = single (op x) (op r) := by ext; simp

theorem opRingEquiv_symm_single [Mul G] (r : kᵐᵒᵖ) (x : Gᵐᵒᵖ) :
    MonoidAlgebra.opRingEquiv.symm (single x r) = op (single x.unop r.unop) := by
  rw [← MulOpposite.unop_inj]; ext; simp

end MonoidAlgebra

/-! ### Additive monoids -/

namespace AddMonoidAlgebra

variable {k G H}

open Finsupp MulOpposite

variable [Semiring k]

/-- The opposite of an `R[I]` is ring equivalent to
the `AddMonoidAlgebra Rᵐᵒᵖ I` over the opposite ring, taking elements to their opposite. -/
@[simps! +simpRhs apply symm_apply]
protected noncomputable def opRingEquiv [AddCommMagma G] :
    k[G]ᵐᵒᵖ ≃+* kᵐᵒᵖ[G] where
  toAddEquiv := opAddEquiv.symm.trans opAddEquiv.addMonoidAlgebraCongrLeft
  map_mul' := by
    classical
    simp only [AddEquiv.toEquiv_eq_coe, Equiv.toFun_as_coe, EquivLike.coe_coe, AddEquiv.trans_apply,
      opAddEquiv_symm_apply, unop_mul, AddMonoidAlgebra.ext_iff,
      AddEquiv.addMonoidAlgebraCongrLeft_apply_coeff, opAddEquiv_apply, Finsupp.ext_iff,
      mapRange_apply, coeff_mul, op_finsuppSum, mul_zero, ite_self, implies_true,
      sum_mapRange_index, zero_mul, sum_zero, ← unop_inj, unop_finsuppSum, unop_op, apply_ite unop,
      unop_zero, «forall»]
    rintro x y a
    rw [Finsupp.sum_comm]
    simp [add_comm]

-- Not `@[simp]` because the LHS simplifies further.
-- TODO: the LHS simplifies to `Finsupp.single`, which implies there's some defeq abuse going on.
theorem opRingEquiv_single [AddCommMagma G] (r : k) (x : G) :
    AddMonoidAlgebra.opRingEquiv (op (single x r)) = single x (op r) := by ext; simp

theorem opRingEquiv_symm_single [AddCommMagma G] (r : kᵐᵒᵖ) (x : Gᵐᵒᵖ) :
    AddMonoidAlgebra.opRingEquiv.symm (single x r) = op (single x r.unop) := by
  rw [← MulOpposite.unop_inj]; ext; simp

end AddMonoidAlgebra
