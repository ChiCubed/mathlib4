module

public import Mathlib

@[expose] public section


open CategoryTheory Limits AlgebraicTopology

-- on mathlib master atm the Simplicial notation for geometric realisation
-- conflicts with so much stuff, including inductive function definitions...
-- so i `open scoped Simplicial` but skip that specifically.
-- (note i can't `open ⋯ in` this because the scope end kills the changes)
run_cmd do
  let ns := `Simplicial
  for ext in (← Lean.scopedEnvExtensionsRef.get) do
    if ext.descr.name == Lean.Parser.parserExtension.descr.name then
      let ext := Lean.Parser.parserExtension
      Lean.modifyEnv fun env =>
        ext.ext.modifyState (asyncMode := .local) env fun s =>
          { s with stateStack := s.stateStack.modifyHead fun top =>
            let activeScopes := top.activeScopes.insert ns
            let top := { top with activeScopes }
            if let some bs := s.scopedEntries.map.find? ns then Id.run do
              let mut state := top.state
              for b in bs do
                -- skip the bad notation
                if let .parser _ `Simplicial.«term|_|» _ _ _ := b then
                  continue
                state := ext.descr.addEntry state b
              { top with state }
            else
              top }
    else
      Lean.modifyEnv (ext.activateScoped · ns)

universe w v u


unif_hint {n m : ℕ} where n ≟ m ⊢ ⦋n⦌.len ≟ m


section misc

theorem TopCat.toSSet_obj_map
    (X : TopCat.{u}) {U V} (i : U ⟶ V) (f : (toSSet.obj X).obj U) :
    (toSSet.obj X).map i f = ULift.up ((SimplexCategory.toTop.op.map i).unop ≫ f.down) := by
  rfl

@[simps!] def ContinuousMap.codRestrict
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (s : Set Y) (h : ∀ x, f x ∈ s) : C(X, s) where
  toFun := s.codRestrict f h

@[elab_as_elim]
def SimplexCategory.Hom.rec {a b : SimplexCategory}
    {motive : (a ⟶ b) → Sort*}
    (h : (f : Fin (a.len + 1) →o Fin (b.len + 1)) → motive (mk f))
    (f : a ⟶ b) : motive f :=
  h f.toOrderHom

theorem SimplexCategory.δ_apply {n} (i : Fin (n + 2)) x :
    δ i x = Fin.succAbove i x := by
  rfl

end misc


namespace stdSimplex

variable
  {ι ι' : Type*} [Fintype ι] [Fintype ι']
  {R : Type*} [Semiring R] [PartialOrder R] [IsStrictOrderedRing R]

omit [IsStrictOrderedRing R] in
@[simp] theorem mk_apply x hx i :
    (⟨x, hx⟩ : stdSimplex R ι) i = x i := by
  rfl

noncomputable def toStdSimplex (p : stdSimplex R ι) : StdSimplex R ι where
  weights := Finsupp.equivFunOnFinite.symm p
  nonneg := p.property.left
  total := by simp [Finsupp.equivFunOnFinite_symm_sum]

variable
  {R : Type*} [Ring R] [PartialOrder R]
  {V : Type*} [AddCommGroup V] [Module R V]
  {P : Type*} [AddTorsor V P]

variable (R) in
/--
Convex combination as a map from `stdSimplex` to an `AddTorsor`, with vertices given by `f`.
-/
noncomputable def affineMap (f : ι → P) (p : stdSimplex R ι) : P :=
  Finset.univ.affineCombination R f p

section affineMap

@[simp] theorem affineMap_vertex [IsOrderedRing R] {_ : DecidableEq ι}
    (f : ι → P) i :
    affineMap R f (vertex (X := ι) i) = f i := by
  simp [affineMap, Finset.affineCombination_apply]

theorem comp_affineMap [IsOrderedRing R] (f : ι' → P) (i : ι → ι') :
    affineMap R (f ∘ i) = affineMap R f ∘ map i := by
  classical
  ext x
  dsimp [affineMap]
  simp_rw [Finset.affineCombination_apply, Finset.weightedVSubOfPoint_apply, Function.comp_apply,
    vadd_right_cancel_iff, FunOnFinite.linearMap_apply_apply]
  rw [← Finset.sum_fiberwise (g := i)]
  congr! 1 with j -
  rw [Finset.sum_smul]
  congr! with i hi; simpa using hi

theorem continuous_affineMap
    [TopologicalSpace R] [IsTopologicalRing R]
    [TopologicalSpace V] [ContinuousAdd V] [ContinuousSMul R V]
    [TopologicalSpace P] [IsTopologicalAddTorsor P]
    (f : ι → P) :
    Continuous (affineMap R f) := by
  suffices Continuous (Finset.univ.affineCombination R f) from
    this.comp continuous_subtype_val
  rw [← AffineMap.continuous_linear_iff, Finset.affineCombination_linear]
  apply LinearMap.continuous_on_pi

variable
  {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  {E : Type*} [AddCommGroup E] [Module R E] (f : ι → E)

theorem range_affineMap :
    Set.range (affineMap R f) = convexHull R (Set.range f) := by
  classical
  change Set.range (Finset.univ.affineCombination R f ∘ Subtype.val) = _
  rw [Set.range_comp, ← convexHull_rangle_single_eq_stdSimplex, Subtype.range_coe_subtype,
    Set.setOf_mem_eq, AffineMap.image_convexHull]
  congr
  simp_rw [← stdSimplex.vertex_coe]
  change (_ '' Set.range (Subtype.val ∘ vertex)) = _
  rw [Set.range_comp, Set.image_image]
  change affineMap R f '' Set.range vertex = Set.range f
  ext; simp

lemma affineMap_mem_convex
    {s : Set E} (hS : Convex R s) (h : Set.range f ⊆ s) :
    Set.range (affineMap R f) ⊆ s := by
  rw [range_affineMap, hS.convexHull_subset_iff]
  exact h

end affineMap

end stdSimplex


namespace CategoryTheory.Limits.Sigma

variable
  {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
  {β β' : Type w} [DecidableEq β] [DecidableEq β'] {f : β → C} {f' : β' → C}
  {A : C} (a b : A ⟶ ∐ f) (x : β)

omit [HasCoproducts.{w} C] [DecidableEq β] in
lemma desc_eq_sum
    [Fintype β] [DecidableEq β] [HasCoproduct f]
    {P} (p : ∀ b, f b ⟶ P) :
    desc p = ∑ i, π f i ≫ p i := by
  apply hom_ext
  simp [Preadditive.comp_sum, ι_desc, ι_π_assoc, apply_dite (· ≫ p _)]

omit [HasCoproducts.{w} C] [DecidableEq β] [DecidableEq β'] in
lemma map'_eq_sum
    [Fintype β] [DecidableEq β] [HasCoproduct f] [HasCoproduct f']
    p (q : ∀ b, f b ⟶ f' (p b)) :
    map' p q = ∑ i, π f i ≫ q i ≫ ι f' (p i) := by
  apply desc_eq_sum

def supp := { i | a ≫ π f i ≠ 0 }

@[local simp] theorem mem_supp : x ∈ supp a ↔ a ≫ π f x ≠ 0 := by
  rfl

theorem supp_ι_subset : supp (ι f x) ⊆ {x} := by
  simp +contextual [supp, ι_π]

@[simp] theorem supp_zero : supp (f := f) (A := A) 0 = ∅ := by
  ext; simp

theorem mem_supp_ι {x y} (hy : y ∈ supp (ι f x)) : y = x := by
  simpa using supp_ι_subset _ hy

theorem supp_add : supp (a + b) ⊆ supp a ∪ supp b := by
  intro x; contrapose
  simp +contextual [Preadditive.add_comp]

theorem supp_sum {ι : Type*}
    (t : Finset ι) (a : ι → (A ⟶ ∐ f)) :
    supp (∑ i ∈ t, a i) ⊆ ⋃ i ∈ t, supp (a i) := by
  intro x; contrapose
  simp +contextual [Preadditive.sum_comp]

theorem supp_const_zsmul_subset
    {A : C} (r : ℤ) (a : A ⟶ ∐ f) :
    supp (r • a) ⊆ supp a := by
  intro x; contrapose
  simp +contextual [smul_zero]

theorem supp_comp_subset_right
    {A B : C} (a : A ⟶ B) (b : B ⟶ ∐ f') :
    supp (a ≫ b) ⊆ supp b := by
  rw [← Set.compl_subset_compl]
  simp_rw [supp, Set.compl_def]
  simp +contextual

private lemma supp_subset_factor
    {p : Finset β} {b : A ⟶ ∐ fun x : p => f x}
    (h : a = b ≫ map' Subtype.val (fun _ => 𝟙 _)) :
    supp a ⊆ p := by
  grw [h, supp_comp_subset_right, map'_eq_sum, supp_sum]
  apply Set.iUnion₂_subset
  rintro i -
  grw [Category.id_comp, supp_comp_subset_right, supp_ι_subset]
  simp

variable
  {A : C} [IsFinitelyPresentable.{w} A] [HasFilteredColimitsOfSize.{w, w} C]
  (a : A ⟶ ∐ f) (b : ∐ f ⟶ ∐ f')

set_option backward.isDefEq.respectTransparency false in
omit [DecidableEq β] in
open CoproductsFromFiniteFiltered in
private lemma factor_thru_finset :
    ∃ p : Finset β, ∃ b : A ⟶ ∐ fun x : p => f x,
      a = b ≫ map' Subtype.val (fun _ => 𝟙 _) := by
  let a' := a ≫ liftToFinsetColimIso.inv.app _
  have ⟨p, b, hp⟩ := IsFinitelyPresentable.exists_hom_of_isColimit (colimit.isColimit _) a'
  simp only [a'] at hp
  replace hp := congr($hp ≫ liftToFinsetColimIso.hom.app _)
  simp_rw [Category.assoc, ← NatTrans.comp_app, Iso.inv_hom_id, NatTrans.id_app] at hp
  dsimp at hp
  exists p.map discreteEquiv.toEmbedding
  exists b ≫ map' (fun x => ⟨discreteEquiv.toEmbedding x, by simp [discreteEquiv]⟩) (fun _ => 𝟙 _)
  rw [Category.comp_id] at hp
  rw [← hp, Category.assoc]
  congr 1
  apply hom_ext
  intro i
  simp only [liftToFinset_obj_obj, Discrete.functor_obj_eq_as,
    Equiv.coe_toEmbedding, discreteEquiv_apply, ι_comp_map'_assoc, ι_comp_map', Category.id_comp]
  -- wtf is going on
  unfold liftToFinsetColimIso
  simp only [colim_obj, Functor.comp_obj, NatIso.ofComponents_hom_app, Iso.symm_hom]
  rw [← Category.assoc, Iso.comp_inv_eq]
  simp only [liftToFinset, colimit.isoColimitCocone_ι_hom, liftToFinsetColimitCocone_cocone_pt,
    Discrete.mk_as, liftToFinsetColimitCocone_cocone_ι_app, Discrete.functor_obj_eq_as]
  have :
      ι (fun x : p => f x.val.as) i =
      ι (fun x : ({i.val} : Finset _) => f x.val.as) ⟨i, by simp⟩
        ≫ (liftToFinsetObj (Discrete.functor f)).map (homOfLE <| by aesop) := by
    simp
  simp_rw [this, Category.assoc, colimit.w]

attribute [local gcongr] Set.Finite.subset in
theorem supp_finite :
    (supp a).Finite := by
  obtain ⟨p, a', ha'⟩ := factor_thru_finset a
  grw [supp_subset_factor a ha']
  apply Finset.finite_toSet

attribute [local gcongr] Set.Finite.subset in
theorem supp_comp :
    supp (a ≫ b) ⊆ ⋃ y ∈ supp a, supp (ι f y ≫ b) := by
  obtain ⟨p, a', ha'⟩ := factor_thru_finset a
  simp_rw [map'_eq_sum, Preadditive.comp_sum, Category.id_comp] at ha'
  rw (occs := [1]) [ha']
  simp_rw [Preadditive.sum_comp, Category.assoc]
  grw [supp_sum]
  simp_rw [Set.iUnion_subset_iff]
  rintro i -
  by_cases hi : ↑i ∈ supp a
  · grw [← Category.assoc, supp_comp_subset_right, ← Set.subset_iUnion₂ ↑i hi]
  · suffices a' ≫ π _ i = 0 by simp [reassoc_of% this]
    simp [ha', Preadditive.sum_comp, ι_π, comp_dite] at hi
    simpa using hi

theorem mem_supp_comp
    ⦃z⦄ (hz : z ∈ supp (a ≫ b)) : ∃ y ∈ supp a, z ∈ supp (ι f y ≫ b) := by
  grw [supp_comp] at hz
  simpa only [Set.mem_iUnion, exists_prop] using hz

lemma eq_sum_over_supp :
    a = ∑ i ∈ (supp_finite a).toFinset, a ≫ π f i ≫ ι f i := by
  classical
  obtain ⟨p, a', ha'⟩ := factor_thru_finset a
  rw [← Finset.sum_subtype_of_mem (p := (· ∈ p))
    (h := fun x hx => supp_subset_factor a ha' (by simpa using hx))]
  simp_rw [map'_eq_sum, Preadditive.comp_sum, Category.id_comp] at ha'
  convert ha' using 1
  apply Finset.sum_congr_of_eq_on_inter
  · simp
  · rintro i -
    simp [ha', Preadditive.sum_comp, ι_π, comp_dite]
    simp +contextual [← Category.assoc]
  · simp [ha', Preadditive.sum_comp, ι_π_assoc, dite_comp, comp_dite]

end CategoryTheory.Limits.Sigma


namespace AlgebraicTopology.SSet.SingularChainComplex

variable
  {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
  (R S : C)

scoped notation3 "𝒞[—; " R "]" => SSet.singularChainComplexFunctor _ |>.obj R
scoped notation3 "𝒞[" s "; " R "]" => 𝒞[—; R].obj s
scoped notation3 "∂[" s "; " R "]" => 𝒞[s; R].d

variable (s : SSet.{w})

-- this seems to help?
scoped instance (priority := high) {n} : HasCoproduct (fun _ : s _⦋n⦌ => R) :=
  inferInstance

-- generally seems best not to use this super directly, instead specialize to whatever
-- chain complexes
protected theorem d_eq {n} :
    ∂[s; R] (n + 1) n =
    ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • SimplicialObject.δ (s ⋙ sigmaConst.obj R) i := by
  simp [SSet.singularChainComplexFunctor, SimplicialObject.whiskering]

-- api transported from Limits.Sigma
section sigma

variable {R S s} {s' : SSet.{w}}

variable
  {n m : ℕ}
  {A : C} (f g : A ⟶ 𝒞[s; R].X n) (x : s _⦋n⦌)

noncomputable def ι : R ⟶ 𝒞[s; R].X n :=
  Sigma.ι (fun _ => _) x

open Classical in
noncomputable def π : 𝒞[s; R].X n ⟶ R :=
  Sigma.π (fun _ => _) x

open Classical in
@[reassoc (attr := simp)] theorem ι_π_eq_id :
    ι (R := R) x ≫ π x = 𝟙 _ :=
  Sigma.ι_π_eq_id ..

open Classical in
@[reassoc] theorem ι_π_of_ne {x y : s _⦋n⦌} (h : x ≠ y) :
    ι (R := R) x ≫ π y = 0 :=
  Sigma.ι_π_of_ne _ h

open Classical in
@[reassoc] theorem ι_π y :
    ι (R := R) x ≫ π y = if h : x = y then eqToHom (congrArg (fun _ => _) h) else 0 :=
  Sigma.ι_π ..

theorem hom_ext (g₁ g₂ : 𝒞[s; R].X n ⟶ A)
    (h : ∀ x, ι x ≫ g₁ = ι x ≫ g₂) : g₁ = g₂ :=
  Sigma.hom_ext g₁ g₂ h

noncomputable def desc (p : s _⦋n⦌ → (R ⟶ A)) :
    𝒞[s; R].X n ⟶ A :=
  Sigma.desc p

@[reassoc (attr := simp)]
theorem ι_desc (p : s _⦋n⦌ → (_ ⟶ A)) x :
    ι (R := R) x ≫ desc p = p x :=
  Sigma.ι_desc p x

noncomputable def map' (p : s _⦋n⦌ → s' _⦋m⦌) :
    𝒞[s; R].X n ⟶ 𝒞[s'; R].X m :=
  Sigma.map' p (fun _ => 𝟙 _)

theorem map'_eq_desc
    (p : s _⦋n⦌ → s' _⦋m⦌) :
    map' p = desc (fun x => ι (R := R) (p x)) := by
  simp [map', desc, Sigma.map']
  rfl

@[reassoc (attr := simp)]
theorem ι_comp_map' (p : s _⦋n⦌ → s' _⦋m⦌) x :
    ι (R := R) x ≫ map' p = ι (p x) := by
  erw [Sigma.ι_comp_map', Category.id_comp]
  rfl

@[reassoc (attr := simp)]
theorem ι_comp_map {s' : SSet.{w}} (f : s ⟶ s') :
    ι x ≫ (𝒞[—; R].map f).f n = ι (f.app (.op ⦋n⦌) x) :=
  ι_comp_map' ..

open Classical in
def supp := Sigma.supp f

open Classical in
theorem mem_supp : x ∈ supp f ↔ f ≫ π x ≠ 0 :=
  Sigma.mem_supp ..

open Classical in
@[simp] theorem supp_zero : supp (s := s) (n := n) (R := R) (A := A) 0 = ∅ :=
  Sigma.supp_zero ..

open Classical in
theorem supp_ι_subset : supp (R := R) (ι x) ⊆ {x} :=
  Sigma.supp_ι_subset ..

open Classical in
theorem mem_supp_ι {x y : s _⦋n⦌} (hy : y ∈ supp (R := R) (ι x)) : y = x :=
  Sigma.mem_supp_ι hy

open Classical in
theorem supp_add : supp (f + g) ⊆ supp f ∪ supp g :=
  Sigma.supp_add ..

open Classical in
theorem supp_sum {ι : Type*}
    (t : Finset ι) (f : ι → (A ⟶ 𝒞[s; R].X n)) :
    supp (∑ i ∈ t, f i) ⊆ ⋃ i ∈ t, supp (f i) :=
  Sigma.supp_sum ..

open Classical in
theorem supp_const_zsmul_subset
    {A : C} (a : ℤ) (f : A ⟶ 𝒞[s; R].X n) :
    supp (a • f) ⊆ supp f :=
  Sigma.supp_const_zsmul_subset ..

open Classical in
theorem supp_comp_subset_right
    {A B : C} (f : A ⟶ B) (g : B ⟶ 𝒞[s'; S].X m) :
    supp (f ≫ g) ⊆ supp g :=
  Sigma.supp_comp_subset_right ..

variable
  {A : C} [IsFinitelyPresentable.{w} A] [HasFilteredColimitsOfSize.{w, w} C]
  (f : A ⟶ 𝒞[s; R].X n)
  (g : 𝒞[s; R].X n ⟶ 𝒞[s'; S].X m)

open Classical in
theorem supp_finite : (supp f).Finite :=
  Sigma.supp_finite f

open Classical in
theorem supp_comp :
    supp (f ≫ g) ⊆ ⋃ y ∈ supp f, supp (ι y ≫ g) :=
  Sigma.supp_comp ..

open Classical in
theorem mem_supp_comp
    ⦃z⦄ (hz : z ∈ supp (f ≫ g)) : ∃ y ∈ supp f, z ∈ supp (ι y ≫ g) :=
  Sigma.mem_supp_comp f g hz

open Classical in
lemma eq_sum_over_supp :
    f = ∑ i ∈ (supp_finite f).toFinset, f ≫ π i ≫ ι i :=
  Sigma.eq_sum_over_supp ..

end sigma

theorem desc_comp_right
    {R₁ R₂ R₃ : C}
    {s₁ s₂ s₃ : SSet.{w}}
    {n m} (f : s₁ _⦋n⦌ → (R₁ ⟶ 𝒞[s₂; R₂].X m))
    (g : 𝒞[s₂; R₂] ⟶ 𝒞[s₃; R₃]) :
    desc (fun σ => f σ ≫ g.f m) = desc f ≫ g.f m := by
  apply hom_ext
  simp

namespace Lifting

set_option backward.isDefEq.respectTransparency false

local notation3 "Uℤ" => AddCommGrpCat.of <| ULift ℤ
local notation3 "∐[" σ "; " R "]" => (sigmaConst.obj R).obj σ

variable {σ τ ι : Type w}

noncomputable def liftSigmaConstMap
    (f : (sigmaConst.obj (C := Ab.{w}) Uℤ).obj σ ⟶ ∐[ι; Uℤ]) :
    ∐[σ; R] ⟶ ∐[ι; R] :=
  Sigma.desc fun i => Finsupp.linearCombination _ (Sigma.ι _)
    ((Sigma.ι _ i ≫ f ≫ Sigma.desc fun j => AddCommGrpCat.ofHom
      (Finsupp.lsingle (R := ℤ) j).toAddMonoidHom) 1)

@[simp] lemma liftSigmaConstMap_zero :
    liftSigmaConstMap R (σ := σ) (ι := ι) 0 = 0 := by
  aesop (add simp liftSigmaConstMap)

@[simp] lemma liftSigmaConstMap_id :
    liftSigmaConstMap R (𝟙 ∐[σ; Uℤ]) = 𝟙 ∐[σ; R] := by
  aesop (add simp liftSigmaConstMap)

@[simp] lemma liftSigmaConstMap_map (φ : σ → ι) :
    liftSigmaConstMap R ((sigmaConst.obj Uℤ).map φ) = (sigmaConst.obj R).map φ := by
  aesop (add simp liftSigmaConstMap)

@[simp] lemma liftSigmaConstMap_add (f g : ∐[σ; Uℤ] ⟶ ∐[ι; Uℤ]) :
    liftSigmaConstMap R (f + g) = liftSigmaConstMap R f + liftSigmaConstMap R g := by
  aesop (add simp liftSigmaConstMap)

@[simp] lemma liftSigmaConstMap_sum {α : Type*} (s : Finset α)
    (f : α → (∐[σ; Uℤ] ⟶ ∐[ι; Uℤ])) :
    liftSigmaConstMap R (∑ i ∈ s, f i) = ∑ i ∈ s, liftSigmaConstMap R (f i) := by
  classical
  induction s using Finset.induction_on with simp_all [- sigmaConst_obj_obj]

@[simp] lemma liftSigmaConstMap_smul
    (f : ∐[σ; Uℤ] ⟶ ∐[ι; Uℤ]) (a : ℤ) :
    liftSigmaConstMap R (a • f) = a • liftSigmaConstMap R f := by
  aesop (add simp liftSigmaConstMap)

@[simp] lemma liftSigmaConstMap_comp
    (f : ∐[σ; Uℤ] ⟶ ∐[τ; Uℤ]) (g : ∐[τ; Uℤ] ⟶ ∐[ι; Uℤ]) :
    liftSigmaConstMap R (f ≫ g) = liftSigmaConstMap R f ≫ liftSigmaConstMap R g := by
  -- stolen from andrew, idk what's going on but it works
  dsimp only [sigmaConst_obj_obj, liftSigmaConstMap, ULift.smul_def]
  ext i
  simp only [Category.assoc, Sigma.ι_desc, Sigma.ι_desc_assoc]
  refine .trans ?_ congr($(Finsupp.linearCombination_linear_comp _
    ((Preadditive.rightComp _ _).toIntLinearMap.restrictScalars _)) _)
  dsimp only [Function.comp_def, LinearMap.coe_restrictScalars, AddMonoidHom.coe_toIntLinearMap,
    CategoryTheory.Preadditive.rightComp, AddMonoidHom.mk'_apply]
  simp only [Sigma.ι_desc]
  rw [← Finsupp.linearCombination_linearCombination]
  congr 1
  refine .trans ?_ congr($(Finsupp.linearCombination_linear_comp _
    ((g ≫ Limits.Sigma.desc fun i ↦ AddCommGrpCat.ofHom (Finsupp.lsingle (R := ℤ) i).toAddMonoidHom)
    |>.hom.toIntLinearMap.restrictScalars (ULift ℤ))) _).symm
  dsimp
  congr 2
  have : (Limits.Sigma.desc fun i ↦ AddCommGrpCat.ofHom (Finsupp.lsingle (R := ℤ) i).toAddMonoidHom)
      ≫ AddCommGrpCat.ofHom (Finsupp.linearCombination (ULift.{w} ℤ) fun i ↦
        (Sigma.ι (fun x : τ ↦ AddCommGrpCat.of (ULift.{w} ℤ)) i).hom 1).toAddMonoidHom = 𝟙 _ := by
    ext; simp [← map_zsmul]; rfl
  exact congr($this _).symm


-- idk lol
@[local simp] lemma chainComplex_X (s : SSet.{w}) (R : C) n :
    𝒞[s; R].X n = ∐[s _⦋n⦌; R] :=
  rfl

variable {s s' : SSet.{w}}

@[local simp] lemma liftSigmaConstMap_singularChainComplexFunctor_d.aux {n} :
    liftSigmaConstMap R (∂[s; Uℤ] (n + 1) n) = ∂[s; R] (n + 1) n := by
  simp [- sigmaConst_obj_obj, - sigmaConst_obj_map, SSet.SingularChainComplex.d_eq,
    SimplicialObject.δ]

@[simp] lemma liftSigmaConstMap_singularChainComplexFunctor_d {i j} :
    liftSigmaConstMap R (∂[s; Uℤ] i j) = ∂[s; R] i j := by
  by_cases h : (ComplexShape.down ℕ).Rel i j
  · obtain rfl : j + 1 = i := by simpa using h
    simp
  · simp [HomologicalComplex.shape _ _ _ h]

noncomputable def liftChainMap
    (f : 𝒞[s; Uℤ] ⟶ 𝒞[s'; Uℤ]) :
    𝒞[s; R] ⟶ 𝒞[s'; R] where
  f n := liftSigmaConstMap R (f.f n)
  comm' i j hij := by
    simp only [chainComplex_X, ← liftSigmaConstMap_singularChainComplexFunctor_d (R := R)]
    -- defeq causing problems as usual
    rw [← liftSigmaConstMap_comp, ← liftSigmaConstMap_comp, f.comm' _ _ hij]

@[simp] lemma liftChainMap_id :
    liftChainMap R (𝟙 𝒞[s; Uℤ]) = 𝟙 𝒞[s; R] := by
  ext; simp [- sigmaConst_obj_obj, liftChainMap]

@[simp] lemma liftChainMap_map (f : s ⟶ s') :
    liftChainMap R (𝒞[—; Uℤ].map f) = 𝒞[—; R].map f := by
  aesop (add simp [SSet.singularChainComplexFunctor, liftChainMap, liftSigmaConstMap])

@[simp] lemma liftChainMap_comp
    {s s' s''} (f : 𝒞[s; Uℤ] ⟶ 𝒞[s'; Uℤ]) (g : 𝒞[s'; Uℤ] ⟶ 𝒞[s''; Uℤ]) :
    liftChainMap R (f ≫ g) = liftChainMap R f ≫ liftChainMap R g := by
  ext; simp [liftChainMap]

noncomputable def liftHomotopy
    {f g : 𝒞[s; Uℤ] ⟶ 𝒞[s'; Uℤ]}
    (h : _root_.Homotopy f g) :
    _root_.Homotopy (liftChainMap R f) (liftChainMap.{w} R g) where
  hom i j := liftSigmaConstMap R (h.hom i j)
  zero := by aesop (add simp h.zero)
  comm := by aesop (add simp [h.comm, liftChainMap, dNext, prevD]) (erase simp [sigmaConst_obj_obj])

noncomputable def liftHomotopyEquiv
    (e : HomotopyEquiv 𝒞[s; Uℤ] 𝒞[s'; Uℤ]) :
    HomotopyEquiv 𝒞[s; R] 𝒞[s'; R] where
  hom := liftChainMap R e.hom
  inv := liftChainMap R e.inv
  -- not very dataful fields but that's just fine for us
  -- (could make this a trans with ofEq on either side)
  homotopyHomInvId := by convert liftHomotopy R e.homotopyHomInvId <;> simp
  homotopyInvHomId := by convert liftHomotopy R e.homotopyInvHomId <;> simp

-- TODO: some stuff like `quasiIso_iff_mem_homotopyEquivalences`

end Lifting

end AlgebraicTopology.SSet.SingularChainComplex


namespace AlgebraicTopology

variable
  {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C] -- [CategoryWithHomology C]
  (R : C)

open SSet.SingularChainComplex

attribute [local simp] SimplexCategory.δ_apply


namespace BarycentricSubdivision

/-- The singular SSet. -/
scoped notation3 "𝒮" => TopCat.toSSet.obj
scoped notation3 "𝒮*" => TopCat.toSSet.map


namespace Affine

variable
  {V V' : Type w} [AddCommGroup V] [AddCommGroup V'] [Module ℝ V] [Module ℝ V']
  (K : Set V) (K' : Set V')
  (φ : V →ᵃ[ℝ] V') (hφ : K.MapsTo φ K')

@[simps! -isSimp] noncomputable def affineSSet : SSet.{w} where
  obj n := Fin (n.unop.len + 1) → K
  map f g := g ∘ f.unop.toOrderHom

variable {K K' φ} in
@[simps! -isSimp] noncomputable def affineSSet.map : affineSSet K ⟶ affineSSet K' where
  app | .op n => asHom <| fun a => hφ.restrict ∘ a

/-- The SSet of affine simplices. -/
scoped notation3 "𝒜" => affineSSet
scoped notation3 "𝒜*" => affineSSet.map


section main

local notation3 "𝒞" => 𝒞[𝒜 K; R]
local notation3 "𝒞* " hφ:max => 𝒞[—; R].map (𝒜* hφ)
local notation3 "∂" => ∂[𝒜 K; R]

omit [AddCommGroup V] [Module ℝ V] in
theorem chainComplex.d_eq n :
    ∂ (n + 1) n =
    ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • map' (· ∘ SimplexCategory.δ i) :=
  SSet.SingularChainComplex.d_eq ..

variable {K K'} {R}

noncomputable def cone.single (b : K) {n} : 𝒜 K _⦋n⦌ → 𝒜 K _⦋n + 1⦌ :=
  Fin.cons (α := fun _ => K) b

noncomputable def cone (b : K) n : (𝒞).X n ⟶ (𝒞).X (n + 1) :=
  map' (cone.single b)

omit [AddCommGroup V] [Module ℝ V] in
theorem d_cone_zero b : cone b 0 ≫ ∂ (0 + 1) 0 = 𝟙 _ - map' (fun _ => ![b]) := by
  apply hom_ext
  intro x
  rw [chainComplex.d_eq, cone, cone.single]
  simp only [Nat.reduceAdd, SimplexCategory.len_mk, Int.reduceNeg, Fin.sum_univ_two, Fin.isValue,
    Fin.coe_ofNat_eq_mod, Nat.zero_mod, pow_zero, one_smul, Nat.mod_succ, pow_one, neg_smul,
    ← sub_eq_add_neg, Preadditive.comp_sub, ι_comp_map'_assoc, ι_comp_map', Category.comp_id]
  congr 2
  funext i
  fin_cases i; simp

omit [AddCommGroup V] [Module ℝ V] in
theorem d_cone_succ b n : cone b (n + 1) ≫ ∂ (n + 1 + 1) (n + 1) = 𝟙 _ - ∂ _ _ ≫ cone b n := by
  apply hom_ext
  intro x
  simp_rw [chainComplex.d_eq, cone, cone.single]
  rw [Fin.sum_univ_succ]
  simp only [SimplexCategory.len_mk, Int.reduceNeg, Fin.coe_ofNat_eq_mod, Nat.zero_mod, pow_zero,
    one_smul, Fin.val_succ, Preadditive.comp_add, Preadditive.comp_sum, Linear.comp_smul,
    ι_comp_map'_assoc, ι_comp_map', Preadditive.sum_comp, Linear.smul_comp, Preadditive.comp_sub,
    Category.comp_id]
  simp_rw [pow_succ', mul_smul, ← Finset.smul_sum, ← zsmul_neg', one_zsmul, ← sub_eq_add_neg]
  congr! 4 with j -
  funext i
  cases i using Fin.cases <;> simp

variable [hK : Fact (Convex ℝ K)] [hK' : Fact (Convex ℝ K')]

@[simps] noncomputable def bary {n} (x : affineSSet K _⦋n⦌) : K where
  val := stdSimplex.affineMap ℝ (Subtype.val ∘ x) stdSimplex.barycenter
  property := by
    apply stdSimplex.affineMap_mem_convex (Subtype.val ∘ x) hK.out
      <;> simp [Set.range_subset_iff]

set_option linter.style.whitespace false in
unif_hint {n m : ℕ} where n ≟ m ⊢ n ≟ ⦋m⦌.len in
lemma bary_zero (x : affineSSet K _⦋0⦌) :
    bary x = x 0 := by
  have hx : x = fun _ => x 0 := by funext i; fin_cases i; dsimp
  rw (occs := [1]) [hx]
  ext
  simp [stdSimplex.affineMap]


noncomputable def S.Aux.f : ∀ n, End ((𝒞).X n)
  | 0     => 𝟙 _
  | n + 1 =>
    desc fun x =>
      ι x ≫ ∂ (n + 1) n ≫ f n ≫ cone (bary x) n

variable (R K) in
open S.Aux in
/--
The subdivision map on affine chains.
-/
noncomputable def S : End 𝒞 where
  f
  comm' := by
    simp only [ComplexShape.down_Rel]
    intro _ n rfl
    induction n using Nat.strongRec with | ind n ih
    apply hom_ext
    intro x
    simp_rw [f, ι_desc_assoc, Category.assoc]
    cases n with
    | zero =>
      simp_rw [Nat.reduceAdd, f, Category.id_comp, Category.comp_id, d_cone_zero]
      simp [chainComplex.d_eq]
    | succ n =>
      simp [d_cone_succ, Preadditive.comp_sub, reassoc_of% ih n (by valid)]

@[simp] theorem S.f_zero : (S R K).f 0 = 𝟙 _ := by rfl
@[simp] theorem S.f_succ {n} :
    (S R K).f (n + 1) =
    desc fun x =>
      ι x ≫ ∂ (n + 1) n ≫ (S R K).f n ≫ cone (bary x) n := by
  rfl


noncomputable def T.Aux.f : ∀ n, (𝒞).X n ⟶ (𝒞).X (n + 1)
  | 0     =>
    desc fun x =>
      ι x ≫ cone (bary x) 0
  | n + 1 =>
    desc fun x =>
      ι x ≫ (𝟙 _ - ∂ _ _ ≫ f n) ≫ cone (bary x) (n + 1)

variable (R K) in
open T.Aux in
noncomputable def T : Homotopy (𝟙 _) (S R K) where
  hom i j :=
    if h : i + 1 = j
      then h ▸ f i
      else 0
  comm n := by
    rw [dNext_nat, prevD_eq (j' := n + 1) (w := by simp)]
    simp only [show n - 1 + 1 = n ↔ ¬n = 0 by omega, dite_not, ↓reduceDIte,
      HomologicalComplex.id_f]
    suffices f n ≫ ∂ _ _ = 𝟙 _ - ∂ _ _ ≫ _ - (S R K).f _ by
      rw [this]; abel
    induction n using Nat.strongRec with | ind n ih
    apply hom_ext; dsimp
    intro x
    match n with
    | 0 =>
      suffices x = ![x 0] by simp [f, d_cone_zero, bary_zero, ← this]
      funext i
      fin_cases i; rfl
    | n + 1 =>
      specialize ih n (by valid)
      simp only [Nat.add_one_sub_one, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceDIte]
      simp_rw [f, ι_desc_assoc, Category.assoc, d_cone_succ]
      simp only [Preadditive.sub_comp, Preadditive.comp_sub, Category.comp_id, Category.id_comp,
        Category.assoc, sub_right_inj]
      simp [reassoc_of% ih]


-- do i even need these
omit hK hK' in
@[reassoc (attr := simp)] lemma chainComplex.map_desc {n}
    {A : C} {p : 𝒜 K' _⦋n⦌ → (R ⟶ A)} :
    (𝒞* hφ).f n ≫ desc p = desc (p ∘ (𝒜* hφ).app _) := by
  apply hom_ext; simp

omit hK hK' in
@[reassoc (attr := simp)] lemma chainComplex.map_map' {n m}
    {p : 𝒜 K' _⦋n⦌ → 𝒜 K' _⦋m⦌} :
    (𝒞* hφ).f n ≫ map' p = map' (p ∘ (𝒜* hφ).app _) := by
  apply hom_ext; simp

open chainComplex



omit hK hK' in
@[simp] lemma affineMap_of_map_apply {n} (x : 𝒜 K _⦋n⦌) p :
    dsimp% stdSimplex.affineMap ℝ (Subtype.val ∘ (𝒜* hφ).app (.op ⦋n⦌) x) p =
    φ (stdSimplex.affineMap ℝ (Subtype.val ∘ x) p) := by
  unfold stdSimplex.affineMap
  rw [Finset.map_affineCombination (hw := stdSimplex.sum_eq_one p)]
  simp [affineSSet.map_app, Function.comp_def]

@[simp] lemma bary.of_map {n} (x : 𝒜 K _⦋n⦌) :
    bary ((𝒜* hφ).app (.op ⦋n⦌) x) =
    hφ.restrict _ _ _ (bary x) := by
  ext
  simp [bary, SimplexCategory.len_mk, Set.MapsTo.val_restrict_apply]

omit hK hK' in
@[reassoc (attr := simp)] lemma cone.map_map_comm {m} (b : K) :
    (𝒞* hφ).f m ≫ cone (hφ.restrict _ _ _ b) m =
    cone b m ≫ (𝒞* hφ).f (m + 1) := by
  apply hom_ext
  intro x
  simp only [cone, affineSSet_obj, SimplexCategory.len_mk, single, map_map', ι_comp_map',
    Function.comp_apply, ι_comp_map'_assoc, ι_comp_map]
  apply congrArg
  funext i
  cases i using Fin.cases <;> simp [affineSSet.map, asHom]

@[reassoc (attr := simp)] lemma S.map_comm_of {n} :
    (𝒞* hφ).f n ≫ (S R K').f n =
    (S R K).f n ≫ (𝒞* hφ).f n := by
  induction n with
  | zero => simp
  | succ n ih
  apply hom_ext; simp [← ι_comp_map, reassoc_of% ih]

@[reassoc (attr := simp)] lemma T.map_comm_of {n} :
    (𝒞* hφ).f n ≫ (T R K').hom n (n + 1) =
    (T R K).hom n (n + 1) ≫ (𝒞* hφ).f (n + 1) := by
  simp only [T, ↓reduceDIte]
  induction n with
    ( unfold Aux.f
      apply hom_ext )
  | zero => simp [← ι_comp_map]
  | succ n ih => simp [← ι_comp_map, reassoc_of% ih]

end main


-- specialize to normed spaces, so we can talk about distances and continuity
section normedSpace

variable
  {V V' : Type w}
  [SeminormedAddCommGroup V] [SeminormedAddCommGroup V']
  [NormedSpace ℝ V] [NormedSpace ℝ V']
  {K : Set V} {K' : Set V'} [hK : Fact (Convex ℝ K)] [hK' : Fact (Convex ℝ K')]
  {φ : V →ᴬ[ℝ] V'} (hφ : K.MapsTo φ K')

local notation3 "𝒞" => 𝒞[𝒜 K; R]
local notation3 "𝒞* " hφ:max => 𝒞[—; R].map <| 𝒜* hφ
local notation3 "∂" => ∂[𝒜 K; R]


@[simps!] noncomputable def toSing.simplex {n} (s : 𝒜 K _⦋n⦌) :
    C(stdSimplex ℝ (Fin (n + 1)), K) :=
  (.codRestrict (s := K)
    ⟨stdSimplex.affineMap ℝ (Subtype.val ∘ s), stdSimplex.continuous_affineMap ..⟩
    fun x => by
      apply stdSimplex.affineMap_mem_convex (Subtype.val ∘ s) hK.out
        <;> simp [Set.range_subset_iff])

lemma toSing.map_simplex {n m} (x : 𝒜 K _⦋n⦌)
    (f : Fin (m + 1) → Fin (n + 1)) :
    simplex (x ∘ f) = (simplex x).comp ⟨_, stdSimplex.continuous_map f⟩ := by
  ext; simp [← Function.comp_assoc, stdSimplex.comp_affineMap]

noncomputable def toSing.sSet :
    𝒜 K ⟶ 𝒮 (.of K) where
  app n := asHom fun x =>
    ULift.up <| TopCat.ofHom <| (toSing.simplex x).comp ⟨_, continuous_uliftDown⟩
  naturality
  | .op n, .op m, .op f => by
    cases n using SimplexCategory.rec with | h n
    cases m using SimplexCategory.rec with | h m
    cases f using SimplexCategory.Hom.rec with | h f
    ext x
    dsimp only [affineSSet, asHom, types_comp_apply]
    rw [toSing.map_simplex]
    rfl

variable {R} in
noncomputable def toSing : 𝒞 ⟶ 𝒞[𝒮 (.of K); R] :=
  𝒞[—; R].map <| toSing.sSet


namespace toSing

variable {n} {x : 𝒜 K _⦋n⦌}
variable {R}

theorem range_eq_hull :
    Set.range (simplex x) = convexHull ℝ (Set.range (Subtype.val ∘ x)) := by
  simp_rw [simplex, ContinuousMap.codRestrict]
  simp only [SimplexCategory.len_mk, ContinuousMap.coe_mk, Set.range_codRestrict]
  rw [stdSimplex.range_affineMap, Subtype.image_preimage_coe, Set.inter_eq_right,
    hK.out.convexHull_subset_iff, Set.range_comp]
  apply Subtype.coe_image_subset

lemma range_eq_preimage_hull :
    Set.range (simplex x) = Subtype.val ⁻¹' convexHull ℝ (Set.range (Subtype.val ∘ x)) := by
  simp [← range_eq_hull]

lemma verts_subset :
    Set.range x ⊆ Set.range (simplex x) := by
  rw [range_eq_preimage_hull, ← Set.image_subset_iff, ← Set.range_comp]
  apply subset_convexHull

lemma subset_of_verts_subset {m} {y : 𝒜 K _⦋m⦌}
    (hy : Set.range x ⊆ Set.range (simplex y)) :
    Set.range (simplex x) ⊆ Set.range (simplex y) := by
  simp_rw [range_eq_preimage_hull] at *
  gcongr _ ⁻¹' ?_
  rw [Convex.convexHull_subset_iff (convex_convexHull ..), Set.range_comp]
  simpa using hy

lemma range_mono {m} {y : 𝒜 K _⦋m⦌}
    (hy : Set.range x ⊆ Set.range y) :
    Set.range (simplex x) ⊆ Set.range (simplex y) := by
  simp_rw [range_eq_preimage_hull, Set.range_comp]
  gcongr

-- lots of these are not really "toSing" lemmas...
omit [SeminormedAddCommGroup V] [NormedSpace ℝ V] hK in
lemma range_d {x y} (hy : y ∈ supp (ι x ≫ ∂ (n + 1) n)) :
    Set.range y ⊆ Set.range x := by
  simp_rw [chainComplex.d_eq, Preadditive.comp_sum, Preadditive.comp_zsmul, ι_comp_map'] at hy
  grw [supp_sum] at hy
  simp_rw [Finset.mem_univ, Set.mem_iUnion₂, exists_const] at hy
  rcases hy with ⟨i, hy⟩
  grw [supp_const_zsmul_subset, supp_ι_subset, Set.mem_singleton_iff] at hy
  subst hy
  apply Set.range_comp_subset_range

omit [SeminormedAddCommGroup V] [NormedSpace ℝ V] hK in
lemma range_cone.single b :
    Set.range (cone.single b x) = insert b (Set.range x) := by
  simp [cone.single]

omit [SeminormedAddCommGroup V] [NormedSpace ℝ V] hK in
lemma supp_cone {b y} (hy : y ∈ supp (ι x ≫ cone (R := R) b n)) :
    y = cone.single b x := by
  grw [cone, ι_comp_map', supp_ι_subset, Set.mem_singleton_iff] at hy
  rw [hy]

variable
  [IsFinitelyPresentable.{w} R] [HasFilteredColimitsOfSize.{w, w} C]

lemma range_S {x y} (hy : y ∈ supp (ι x ≫ (S R K).f n)) :
    Set.range y ⊆ Set.range (simplex x) := by
  induction n with dsimp [S, S.Aux.f] at hy
  | zero =>
    grw [Category.comp_id, supp_ι_subset, Set.mem_singleton_iff] at hy
    subst hy
    apply verts_subset
  | succ n ih =>
    rw [ι_desc] at hy
    rw [← Category.assoc] at hy; apply mem_supp_comp at hy
    rcases hy with ⟨u, hu, hy⟩
    rw [← Category.assoc] at hy; apply mem_supp_comp at hy
    rcases hy with ⟨v, hv, hy⟩
    apply supp_cone at hy
    grw [hy, range_cone.single]
    apply Set.insert_subset
    · rw [← Subtype.coe_injective.mem_set_image]
      simp only [bary_coe, simplex_apply_coe, SimplexCategory.len_mk, Set.mem_image, Set.mem_range,
        exists_exists_eq_and, exists_apply_eq_apply]
    · grw [ih hv, range_mono (range_d hu)]

lemma range_S_pow {k} {x y} (hy : y ∈ supp (ι x ≫ (S R K ^ k).f n)) :
    Set.range (simplex y) ⊆ Set.range (simplex x) := by
  induction k generalizing y with
  | zero =>
    simp only [pow_zero, End.one_def, HomologicalComplex.id_f, Category.comp_id] at hy
    grw [supp_ι_subset, Set.mem_singleton_iff] at hy
    subst hy; rfl
  | succ k ih =>
    rw [pow_succ', End.mul_def, HomologicalComplex.comp_f, ← Category.assoc] at hy
    apply mem_supp_comp at hy
    rcases hy with ⟨u, hu, hy⟩
    apply subset_of_verts_subset
    grw [← ih hu, range_S hy]

end toSing


section diam

variable
  {n} {x : 𝒜 K _⦋n⦌}
  {A} {f : A ⟶ 𝒞[𝒜 K; R].X n} -- this seems to break if i use the notation 𝒞 defined above?
variable {R}


variable (x) in
noncomputable abbrev ediam :=
  Metric.ediam (Set.range x)

theorem ediam_eq_ediam_toSing :
    ediam x = Metric.ediam (Set.range <| toSing.simplex x) := by
  rw [← isometry_subtype_coe.ediam_image, toSing.range_eq_hull, convexHull_ediam,
    Set.range_comp, isometry_subtype_coe.ediam_image]

omit [NormedSpace ℝ V] hK in
theorem ediam_d {x}
    {y} (hy : y ∈ supp (ι x ≫ ∂ (n + 1) n)) :
    ediam y ≤ ediam x :=
  Metric.ediam_mono <| toSing.range_d hy

/--
The shrinking factor for one step of barycentric subdivision.
-/
noncomputable def fac (n : ℕ) : NNReal := 1 - 1 / (n + 1)

lemma fac_lt_one {n} : fac n < 1 := by
  simp [fac]

@[simp] lemma coe_fac n : (fac n : ℝ) = 1 - 1 / (n + 1) := by
  simp [fac]

lemma edist_bary_le {p} (hp : p ∈ Set.range (toSing.simplex x)) :
    edist (bary x) p ≤ fac n * ediam x := by
  rcases p with ⟨p, hpK⟩
  simp_rw [toSing.range_eq_preimage_hull, Set.mem_preimage] at hp
  simp_rw [Subtype.edist_eq]
  have ⟨_, ⟨i, rfl⟩, hi⟩ := convexHull_exists_dist_ge hp (bary x)
  rw [Function.comp_apply] at hi
  replace hi : edist p (bary x) ≤ edist (x i).val (bary x).val := by
    simp_rw [edist_dist]; gcongr
  grw [edist_comm, hi]; clear * - i; dsimp at i
  cases n with
  | zero => fin_cases i; simp [bary_zero]
  | succ n
  let b' := Finset.centerMass (R := ℝ) {i}ᶜ 1 (Subtype.val ∘ x)
  have : edist (x i).val (bary x).val = fac (n + 1) * edist ↑(x i) b' := by
    simp_rw [edist_nndist]
    norm_cast
    suffices bary x = AffineMap.lineMap ↑(x i) b' (fac (n + 1) : ℝ) by
      rw [this, nndist_left_lineMap, NNReal.nnnorm_eq]
    simp_rw [bary, b', stdSimplex.affineMap,
      affineCombination_eq_centerMass (stdSimplex.sum_eq_one _)]
    -- wtf is this...
    rw [stdSimplex.instFunLikeElemForall]; dsimp
    convert_to Finset.univ.centerMass (R := ℝ) 1 (Subtype.val ∘ x) = _
    · have hc : ((n + 2 : ℕ) : ℝ) ≠ 0 := by positivity
      rw [← Finset.centerMass_smul_left (hc := hc)]
      simp only [stdSimplex.barycenter, Fintype.card_fin, Pi.smul_def]
      simp_rw [smul_eq_mul, mul_inv_cancel₀ hc]
      rfl
    dsimp
    rw [← Finset.insert_compl_self i, Finset.centerMass_insert _ _ _ (by simp) (by simp)]
    simp_rw [Pi.one_apply, show ∑ x ∈ {i}ᶜ, (1 : ℝ) = n + 1 by simp [Finset.card_compl]]
    rw [AffineMap.lineMap_apply_module, coe_fac]
    grind only
  simp_rw [this, b']
  gcongr _ * ?_
  rw [ediam_eq_ediam_toSing, ← isometry_subtype_coe.ediam_image]
  apply Metric.edist_le_ediam_of_mem
  · apply Set.mem_image_of_mem
    apply toSing.verts_subset; simp
  · rw [toSing.range_eq_hull]
    have : Finset.Nonempty {i}ᶜ := by
      simp [← Finset.card_compl_lt_iff_nonempty]
    apply Finset.centerMass_mem_convexHull <;> simp [this]

variable
  [HasFilteredColimitsOfSize.{w, w} C]
  [IsFinitelyPresentable.{w} R] [IsFinitelyPresentable.{w} A]

theorem ediam_S.single
    {y} (hy : y ∈ supp (ι x ≫ (S R K).f n)) :
    ediam y ≤ fac n * ediam x := by
  induction n with
  | zero =>
    suffices (Set.range y).Subsingleton by
      simp [ediam, Metric.ediam_subsingleton this]
    dsimp; apply Set.subsingleton_range
  | succ n ih =>
    dsimp only [S, S.Aux.f] at hy
    rw [ι_desc] at hy
    rw [← Category.assoc] at hy; apply mem_supp_comp at hy
    rcases hy with ⟨u, hu, hy⟩
    rw [← Category.assoc] at hy; apply mem_supp_comp at hy
    rcases hy with ⟨v, hv, hy⟩
    apply toSing.supp_cone at hy
    subst hy
    calc
      ediam (cone.single (bary x) v)
        = max (⨆ i, edist (bary x) (v i)) (ediam v)      := ?_
      _ ≤ max (fac (n + 1) * ediam x) (ediam v)          := ?_
      _ ≤ max (fac (n + 1) * ediam x) (fac n * ediam x)  := by grw [ih hv, ediam_d hu]
      _ = fac (n + 1) * ediam x                          := max_eq_left ?_
    · rw [ediam, toSing.range_cone.single, Metric.ediam_insert, iSup_range]
    · gcongr max ?_ _
      apply iSup_le
      intro i
      apply edist_bary_le
      apply toSing.range_mono <| toSing.range_d hu
      apply toSing.range_S hv <| Set.mem_range_self i
    · unfold fac
      gcongr; omega

theorem ediam_S (d : ENNReal)
    (hf : ∀ x ∈ supp f, ediam x ≤ d)
    {y} (hy : y ∈ supp (f ≫ (S R K).f n)) :
    ediam y ≤ fac n * d := by
  apply mem_supp_comp at hy
  rcases hy with ⟨u, hu, hy⟩
  grw [ediam_S.single hy, hf _ hu]

/--
Main lemma of barycentric subdivision of a simplex:
if all simplices in a chain c have diameter at most d,
then all simplices in S^k c have diameter at most fac n ^ k * d.
-/
theorem ediam_S_pow (d : ENNReal)
    (h : ∀ x ∈ supp f, ediam x ≤ d) (k : ℕ)
    {y} (hy : y ∈ supp (f ≫ (S R K ^ k).f n)) :
    ediam y ≤ fac n ^ k * d := by
  induction k generalizing y with
  | zero => simp at hy; simpa using h y hy
  | succ k ih =>
    rw [pow_succ', End.mul_def, HomologicalComplex.comp_f, ← Category.assoc] at hy
    apply mem_supp_comp at hy
    rcases hy with ⟨u, hu, hy⟩
    rw [pow_succ', mul_assoc]
    apply ediam_S (hy := hy)
    intro x hx
    grw [supp_ι_subset, Set.mem_singleton_iff] at hx
    simpa [hx] using ih hu

variable (R x) in
/--
For any open cover and chain consisting of a single simplex, there exists an iterated barycentric
subdivision thereof which is subordinate to the cover.
-/
theorem exists_S_pow_subordinate.single
    {β : Type*} {U : β → Set K}
    (hopen : ∀ i, IsOpen (U i)) (hcover : ⋃ i, U i = Set.univ) :
    ∃ k, ∀ j ≥ k, ∀ y ∈ supp (ι x ≫ (S R K ^ j).f n),
      ∃ i, Set.range (toSing.simplex y) ⊆ U i := by
  have ⟨δ, δ_pos, h⟩ :=
    lebesgue_number_lemma_of_emetric
      (c := U) (s := Set.range (toSing.simplex x))
      (isCompact_range <| map_continuous _)
      hopen (by simp [hcover])
  have (eq := hd) d := ediam x
  lift d to NNReal
  · rw [hd, ← Metric.isBounded_iff_ediam_ne_top]
    apply Set.finite_range _ |>.isBounded
  have ⟨k, hk⟩ : ∃ k, fac n ^ k * d < δ := by
    by_cases hδ : δ = ⊤
    · exists 0; simp [hδ]
    lift δ to NNReal using hδ
    obtain rfl | hd := eq_zero_or_pos d
    · simp [δ_pos]
    norm_cast at δ_pos ⊢
    suffices ∃ k, fac n ^ k < δ / d from
      this.imp fun _ => NNReal.mul_lt_of_lt_div
    apply NNReal.exists_pow_lt_of_lt_one (by positivity) fac_lt_one
  have hj j (hjk : j ≥ k) : fac n ^ j * d < δ := by
    refine lt_of_le_of_lt ?_ hk
    gcongr ?_ * _
    apply pow_le_pow_of_le_one (by simp) (by exact_mod_cast fac_lt_one.le) hjk.le
  exists k
  intro j hjk y hy
  have hy0 : y 0 ∈ Set.range (toSing.simplex y) :=
    toSing.verts_subset (by simp)
  specialize h (y 0) (toSing.range_S_pow hy hy0)
  peel h with i h
  grw [← h]
  have : ediam y < δ :=
    ediam_S_pow d (fun _ h => by simp [mem_supp_ι h, hd]) j hy |>.trans_lt (hj j hjk)
  rw [ediam_eq_ediam_toSing] at this
  clear * - hy0 this
  intro x hx
  grw [Metric.mem_eball, Metric.edist_le_ediam_of_mem hx hy0]
  exact this

end diam

end normedSpace

end Affine


/-
transporting it to regular chain groups now
-/

section prep

variable
  {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
  (R : C)

variable (X Y : TopCat.{w})

local notation3 "𝒞" => 𝒞[𝒮 X; R]
local notation3 "𝒞* " f:max => 𝒞[—; R].map (𝒮* f)
local notation3 "∂" => ∂[𝒮 X; R]


theorem chainComplex.d_eq {n} :
    ∂ (n + 1) n =
    ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
      map' (ULift.up <| SimplexCategory.toTop.map (SimplexCategory.δ i) ≫ ULift.down ·) :=
  SSet.SingularChainComplex.d_eq ..

open chainComplex


namespace Affine.toSing

variable
  {V V' : Type w}
  [SeminormedAddCommGroup V] [SeminormedAddCommGroup V']
  [NormedSpace ℝ V] [NormedSpace ℝ V']
  {K : Set V} {K' : Set V'} [hK : Fact (Convex ℝ K)] [hK' : Fact (Convex ℝ K')]
  {φ : V →ᴬ[ℝ] V'} (hφ : K.MapsTo φ K')

-- wtf is this proof
@[reassoc (attr := simp)] lemma sSet.map_comm {n} :
    (𝒜* hφ).app n ≫ toSing.sSet.app n =
    toSing.sSet.app n ≫ (𝒮* <| TopCat.ofHom ⟨hφ.restrict, φ.continuous.restrict hφ⟩).app n := by
  rcases n with ⟨n⟩
  cases n using SimplexCategory.rec with | h n
  ext x
  simp only [TopCat.toSSet, sSet, asHom, Functor.op_obj, SimplexCategory.toTop_obj, yoneda_obj_obj,
    SimplexCategory.toTop₀_obj, types_comp_apply, Presheaf.restrictedULiftYoneda_map_app]
  erw [← TopCat.ofHom_comp]
  congr
  ext p
  dsimp
  rw [affineMap_of_map_apply]
  dsimp

@[reassoc (attr := simp)] lemma map_comm {n} :
    (𝒞[—; R].map <| 𝒜* hφ).f n
      ≫ toSing.f n =
    toSing.f n
      ≫ (𝒞[—; R].map <| 𝒮* <| TopCat.ofHom (⟨hφ.restrict, φ.continuous.restrict hφ⟩)).f n := by
  unfold toSing
  simp_rw [← HomologicalComplex.comp_f]
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 2
  ext n : 1
  apply sSet.map_comm

end Affine.toSing


scoped notation3 "Δₜ[" n "]" => stdSimplex ℝ <| Fin (n + 1)
scoped notation3 "ΔₜU[" n "]" => stdSimplex ℝ <| ULift <| Fin (n + 1)

local instance {n} : Fact (Convex ℝ ΔₜU[n]) :=
  ⟨convex_stdSimplex ..⟩

variable {R X}
open scoped Affine

noncomputable def induceFromAffine.shuffleULift {n} : ΔₜU[n] ≃ₜ ULift.{w} Δₜ[n] :=
  .trans
    { toFun := stdSimplex.map ULift.down
      invFun := stdSimplex.map ULift.up.{w}
      left_inv x := by rw [stdSimplex.map_comp_apply]; apply stdSimplex.map_id_apply
      right_inv x := by rw [stdSimplex.map_comp_apply]; apply stdSimplex.map_id_apply
      continuous_toFun := stdSimplex.continuous_map _
      continuous_invFun := stdSimplex.continuous_map _ }
    Homeomorph.ulift.symm

noncomputable def induceFromAffine.sSet {n} (σ : 𝒮 X _⦋n⦌) :
    𝒜 ΔₜU[n] ⟶ 𝒮 X :=
  Affine.toSing.sSet
    ≫ 𝒮* (TopCat.ofHom ⟨_, shuffleULift.continuous⟩)
    ≫ 𝒮* σ.down

noncomputable def induceFromAffine {n} (σ : 𝒮 X _⦋n⦌) :
    𝒞[𝒜 ΔₜU[n]; R] ⟶ 𝒞[𝒮 X; R] :=
  𝒞[—; R].map <| induceFromAffine.sSet σ


noncomputable def faceCAM {n} (i : Fin (n + 2)) :
    ((ULift.{w} <| Fin (n + 1)) → ℝ) →ᴬ[ℝ] ((ULift.{w} <| Fin (n + 2)) → ℝ) :=
  FunOnFinite.linearMap ℝ ℝ (ULift.map <| i.succAboveOrderEmb)
    |>.toContinuousLinearMap.toContinuousAffineMap

lemma faceCAM.mapsTo {n} (i : Fin (n + 2)) :
    Set.MapsTo (faceCAM i) ΔₜU[n] ΔₜU[n + 1] :=
  fun ⦃_⦄ h => stdSimplex.image_linearMap _ <| Set.mem_image_of_mem _ h

@[local simp] theorem faceCAM.apply_eq {n} (i : Fin (n + 2)) p :
    (faceCAM.mapsTo i).restrict _ _ _ p = stdSimplex.map (ULift.map <| i.succAboveOrderEmb) p := by
  rfl


abbrev vertex' n : Fin (n + 1) → ΔₜU[n] := stdSimplex.vertex ∘ ULift.up

namespace induceFromAffine

variable {X Y : TopCat.{w}} (f : X ⟶ Y) {n} (σ : 𝒮 X _⦋n⦌)

set_option backward.isDefEq.respectTransparency false in
@[simp] lemma sSet.app_vertex :
    (sSet σ).app (.op ⦋n⦌) (vertex' n) = σ := by
  -- this is so garbage
  simp only [sSet]
  suffices
      ContinuousMap.comp
        ⟨_, shuffleULift.{w}.continuous⟩
        (TopCat.Hom.hom (Affine.toSing.sSet.app (Opposite.op ⦋n⦌) (vertex'.{w} n)).down) =
      ContinuousMap.id _ by
    erw [ULift.ext_iff, TopCat.hom_ext_iff]
    convert ContinuousMap.comp_id _
    rw [← this]; rfl
  dsimp [TopCat.uliftFunctor]
  ext x : 1
  rcases x with ⟨x⟩
  suffices stdSimplex.map ULift.down ((Affine.toSing.simplex (vertex' n)) x) = x by
    simpa [shuffleULift, Homeomorph.ulift, Affine.toSing.sSet]
  suffices Affine.toSing.simplex (vertex'.{w} n) x = stdSimplex.map ULift.up x by
    rw [this, stdSimplex.map_comp_apply, Function.comp_def]
    dsimp only
    apply stdSimplex.map_id_apply
  ext i
  simp only [Affine.toSing.simplex, ContinuousMap.codRestrict, SimplexCategory.len_mk,
    ContinuousMap.coe_mk, Set.codRestrict, stdSimplex.mk_apply, stdSimplex.map_coe,
    FunOnFinite.linearMap_apply_apply]
  simp only [stdSimplex.affineMap, stdSimplex.sum_eq_one,
    Finset.affineCombination_eq_linear_combination, Function.comp_apply, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul]
  simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite, Finset.sum_const_zero,
    add_zero]
  simp_rw [eq_comm (a := i)]

@[reassoc (attr := simp)] lemma ι_vertex :
    ι (vertex' n) ≫ (induceFromAffine (R := R) σ).f n = ι σ := by
  simp [induceFromAffine]

-- bleh
set_option backward.isDefEq.respectTransparency false in
lemma sSet.map_comm
    {n m} (σ : 𝒮 X _⦋m⦌)
    {φ : _ →ᴬ[ℝ] _} (hφ : Set.MapsTo φ ΔₜU[n] ΔₜU[m]) :
    𝒜* hφ ≫ sSet σ =
    sSet (.up <|
      TopCat.ofHom ⟨_, induceFromAffine.shuffleULift.continuous_invFun⟩
        ≫ TopCat.ofHom ⟨_, (map_continuous φ).restrict hφ⟩
        ≫ TopCat.ofHom ⟨_, induceFromAffine.shuffleULift.continuous⟩
        ≫ σ.down) := by
  ext m : 1
  simp only [sSet, NatTrans.comp_app, Affine.toSing.sSet.map_comm_assoc]
  simp_rw [← NatTrans.comp_app, ← Functor.map_comp]
  congr 3
  simp_rw [← Category.assoc]
  congr 2
  ext x : 1
  simp

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)] lemma sSet.map_face_comm
    (σ : 𝒮 X _⦋n + 1⦌) (i : Fin (n + 2)) :
    𝒜* (faceCAM.mapsTo i) ≫ sSet σ =
    (sSet <| .up <| SimplexCategory.toTop.map (SimplexCategory.δ i) ≫ σ.down) := by
  rw [sSet.map_comm]
  congr 2
  dsimp
  ext
  simp [TopCat.uliftFunctor, ULift.map, shuffleULift, Homeomorph.ulift, stdSimplex.map_comp_apply,
    Function.comp_def]
  rfl

@[reassoc (attr := simp)] lemma map_face_comm_of
    {m} (σ : 𝒮 X _⦋n + 1⦌) (i : Fin (n + 2)) :
    (𝒞[—; R].map <| 𝒜* (faceCAM.mapsTo i)).f m ≫ (induceFromAffine σ).f m =
    (induceFromAffine <| .up <|
      SimplexCategory.toTop.map (SimplexCategory.δ i) ≫ σ.down).f m := by
  simp [induceFromAffine, ← HomologicalComplex.comp_f, ← Functor.map_comp]

@[reassoc (attr := simp)] lemma sSet.comp_map :
    sSet σ ≫ 𝒮* f = sSet (.up <| σ.down ≫ f) := by
  simp [sSet, ← Functor.map_comp]
  rfl

@[reassoc (attr := simp)] lemma comp_map_of :
    (induceFromAffine σ).f n ≫ (𝒞* f).f n =
    (induceFromAffine (.up <| σ.down ≫ f)).f n := by
  simp [induceFromAffine,← HomologicalComplex.comp_f, ← Functor.map_comp]

end induceFromAffine


lemma bob {n} {i : Fin (n + 2)} :
    vertex' (n + 1) ∘ SimplexCategory.δ i =
    (𝒜* (faceCAM.mapsTo i) |>.app (.op ⦋n⦌) <| vertex' n) := by
  ext; simp [Affine.affineSSet.map_app, asHom]


variable (R X) in
/--
The barycentric subdivision functor on singular chains.
-/
noncomputable def S : End 𝒞 where
  f n :=
    desc fun σ =>
      ι (vertex' n)
        ≫ (Affine.S R _).f n
        ≫ (induceFromAffine σ).f n
  comm' := by
    simp only [ComplexShape.down_Rel]
    intro _ n rfl
    apply hom_ext
    intro σ
    simp only [Category.assoc, ι_desc_assoc,
      HomologicalComplex.Hom.comm, HomologicalComplex.Hom.comm_assoc]
    simp_rw [Affine.chainComplex.d_eq, chainComplex.d_eq, Preadditive.comp_sum_assoc,
      Preadditive.sum_comp, Linear.comp_smul, ι_comp_map', Linear.smul_comp, ι_desc]
    congr! 2 with i -
    simp [bob, ← ι_comp_map]

noncomputable def T.Aux.f n : (𝒞).X n ⟶ (𝒞).X (n + 1) :=
  desc fun σ =>
    ι (vertex' n)
      ≫ (Affine.T R _).hom n (n + 1)
      ≫ (induceFromAffine σ).f (n + 1)

set_option backward.isDefEq.respectTransparency false in
variable (R X) in
open T.Aux in
noncomputable def T : Homotopy (𝟙 _) (S R X) where
  hom i j :=
    if h : i + 1 = j
      then h ▸ f i
      else 0
  comm n := by
    rw [dNext_nat, prevD_eq (j' := n + 1) (w := by simp)] -- TODO do this stuff better
    apply hom_ext
    intro σ
    simp_rw [f, S]
    dsimp
    simp_rw [(Affine.T R ΔₜU[n]).symm.comm n]
    rw [dNext_nat, prevD_eq (j' := n + 1) (w := by simp)]
    simp only [show n - 1 + 1 = n ↔ ¬n = 0 by omega, dite_not, Homotopy.symm_hom,
      Preadditive.comp_neg, Preadditive.neg_comp, Preadditive.comp_add, Preadditive.add_comp,
      HomologicalComplex.id_f, HomologicalComplex.Hom.comm, Category.assoc, Category.id_comp,
      Category.comp_id, ι_desc, ι_desc_assoc]
    rw [← add_assoc, ← sub_eq_iff_eq_add, induceFromAffine.ι_vertex, sub_self]
    cases n with
    | zero =>
      simp
    | succ n =>
      simp only [Nat.add_one_sub_one, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceDIte,
        d_eq, Affine.chainComplex.d_eq, Preadditive.sum_comp, Preadditive.comp_sum,
        Linear.smul_comp, Linear.comp_smul, Category.assoc, Affine.T.map_comm_of_assoc,
        induceFromAffine.map_face_comm_of, ι_comp_map'_assoc, ι_desc, bob, ← ι_comp_map]
      abel


namespace S

variable {X Y : TopCat.{w}} (f : X ⟶ Y)

@[reassoc (attr := simp)] theorem map_comm_of {n} :
    (𝒞* f).f n ≫ (S R Y).f n = (S R X).f n ≫ (𝒞* f).f n := by
  apply hom_ext
  intro σ
  simp [S]
  rfl

/- would be nice to have SemiconjBy / Function.Semiconj for categories or whatever -/
@[reassoc (attr := simp)] theorem pow_map_comm_of {k n} :
    (𝒞* f).f n ≫ (S R Y ^ k).f n = (S R X ^ k).f n ≫ (𝒞* f).f n := by
  induction k with
  | zero => simp
  | succ _ ih => simp [pow_succ', reassoc_of% ih]

end S


variable
  [HasFilteredColimitsOfSize.{w, w} C]
  [IsFinitelyPresentable.{w} R]
  {A : C} [IsFinitelyPresentable.{w} A]


-- TODO these first two lemmas seem pretty useless

omit [HasFilteredColimitsOfSize.{w, w} C] [IsFinitelyPresentable.{w} R] in
lemma chainComplex.map.range_subset
    {X Y : TopCat.{w}} (f : X ⟶ Y)
    {n x y} (hy : y ∈ supp (ι x ≫ (𝒞* f).f n)) :
    Set.range y.down.hom ⊆ Set.range f := by
  grw [ι_comp_map, supp_ι_subset, Set.mem_singleton_iff] at hy
  subst hy
  erw [ContinuousMap.coe_comp] -- idk
  apply Set.range_comp_subset_range

lemma induceFromAffine.range_subset
    {n} (σ : 𝒮 X _⦋n⦌)
    {m x y} (hy : y ∈ supp (ι x ≫ (induceFromAffine (R := R) σ).f m)) :
    Set.range y.down.hom ⊆ Set.range σ.down.hom := by
  simp only [induceFromAffine, induceFromAffine.sSet,
    HomologicalComplex.comp_f, Functor.map_comp] at hy
  simp_rw [← Category.assoc] at hy
  apply mem_supp_comp at hy
  rcases hy with ⟨z, hz, hy⟩
  exact chainComplex.map.range_subset _ hy

lemma range_S.single
    {n x y} (hy : y ∈ supp (ι x ≫ (S R X).f n)) :
    Set.range y.down.hom ⊆ Set.range x.down.hom := by
  simp only [S, ι_desc] at hy
  rw [← Category.assoc] at hy
  apply mem_supp_comp at hy
  rcases hy with ⟨_, _, hy⟩
  exact induceFromAffine.range_subset _ hy

lemma range_T.single
    {i j x y} (hy : y ∈ supp (ι x ≫ (T R X).hom i j)) :
    Set.range y.down.hom ⊆ Set.range x.down.hom := by
  simp only [T] at hy
  split_ifs at hy with hij
  case neg => simp at hy
  subst hij; dsimp at hy
  simp only [T.Aux.f, ι_desc] at hy
  rw [← Category.assoc] at hy
  apply mem_supp_comp at hy
  rcases hy with ⟨_, _, hy⟩
  exact induceFromAffine.range_subset _ hy


-- oh no
noncomputable def tautoCAM {n m} (x : 𝒜 ΔₜU[n] _⦋m⦌) :
    (ULift.{w} (Fin (m + 1)) → ℝ) →ᴬ[ℝ] (ULift.{w} (Fin (n + 1)) → ℝ) where
  toAffineMap := Finset.univ.affineCombination ℝ (fun i => x i.down)
  cont := by
    dsimp
    rw [← AffineMap.continuous_linear_iff, Finset.affineCombination_linear]
    apply LinearMap.continuous_on_pi

theorem tautoCAM.mapsTo {n m} (x : 𝒜 ΔₜU[n] _⦋m⦌) :
    Set.MapsTo (tautoCAM x) ΔₜU[m] ΔₜU[n] := by
  intro y hy
  lift y to ΔₜU[m] using hy
  dsimp [tautoCAM]
  apply affineCombination_mem_convexHull
  · exact fun i _ => stdSimplex.zero_le y i
  · exact stdSimplex.sum_eq_one y
  · simp only [Set.le_eq_subset, Subtype.range_coe_subtype, Set.mem_setOf_eq, convex_stdSimplex,
      and_true]
    rw [Set.range_subset_iff]
    intro i
    apply Subtype.property

lemma tautoCAM.map_app {n m} (x : 𝒜 ΔₜU[n] _⦋m⦌) :
    (𝒜* (tautoCAM.mapsTo x)).app (.op ⦋m⦌) (vertex' m) = x := by
  rw [Affine.affineSSet.map_app]
  dsimp [asHom]
  apply funext
  intro i
  apply Subtype.ext
  simp [tautoCAM]
  rfl

set_option backward.isDefEq.respectTransparency false in
lemma tautoCAM.map_comp_induceFromAffine {n} (x : 𝒜 ΔₜU[n] _⦋n⦌) (σ : 𝒮 X _⦋n⦌) :
    𝒜* (tautoCAM.mapsTo x) ≫ induceFromAffine.sSet σ =
    induceFromAffine.sSet ((induceFromAffine.sSet σ).app (.op ⦋n⦌) x) := by
  rw [induceFromAffine.sSet.map_comm]
  congr 2
  simp only [Functor.op_obj, SimplexCategory.toTop_obj, TopCat.uliftFunctor, SimplexCategory.len_mk,
    yoneda_obj_obj, SimplexCategory.toTop₀_obj, Equiv.invFun_as_coe, Homeomorph.coe_symm_toEquiv,
    yoneda_map_app]
  ext m
  simp only [TopCat.hom_comp, TopCat.hom_ofHom, ContinuousMap.comp_assoc, ContinuousMap.comp_apply,
    ContinuousMap.coe_mk]
  congr 1
  unfold TopCat.toSSet
  simp only [Presheaf.restrictedULiftYoneda_map_app, SimplexCategory.toTop_obj,
    SimplexCategory.len_mk, TopCat.hom_comp, TopCat.hom_ofHom, ContinuousMap.comp_apply,
    ContinuousMap.coe_mk, EmbeddingLike.apply_eq_iff_eq]
  suffices
      tautoCAM x ↑(stdSimplex.map ULift.up m.down) =
      stdSimplex.affineMap ℝ (Subtype.val ∘ x) m.down by
    apply Subtype.ext
    simpa [Affine.toSing.sSet, induceFromAffine.shuffleULift, Homeomorph.ulift]
  -- this goal feels familiar...
  dsimp [tautoCAM, stdSimplex.affineMap]
  rw [← Finset.map_univ_equiv Equiv.ulift.{w, 0}, Finset.affineCombination_map]
  congr
  ext i
  simp [FunOnFinite.linearMap_apply_apply, ULift.ext_iff, Finset.filter_eq']

omit [HasFilteredColimitsOfSize.{w, w} C] [IsFinitelyPresentable R] in
lemma ι_S_pow_eq k {n} (σ : 𝒮 X _⦋n⦌) :
    ι σ ≫ (S R X ^ k).f n =
    ι (vertex' n) ≫ (Affine.S R _ ^ k).f n ≫ (induceFromAffine σ).f n := by
  induction k with
  | zero =>
    simp
  | succ k ih =>
    simp_rw [pow_succ', End.mul_def, HomologicalComplex.comp_f, Category.assoc,
      reassoc_of% ih]
    congrm _ ≫ _ ≫ ?_
    apply hom_ext
    intro x
    simp only [induceFromAffine, S, ι_comp_map_assoc, ι_desc]
    conv_rhs => rw [← tautoCAM.map_app x, ← ι_comp_map]
    simp only [Category.assoc, Affine.S.map_comm_of_assoc]
    congrm _ ≫ _ ≫ ?_
    rw [← HomologicalComplex.comp_f, ← Functor.map_comp, tautoCAM.map_comp_induceFromAffine]

lemma exists_of_supp_S_pow k
    {n x y} (hy : y ∈ supp (ι x ≫ (S R X ^ k).f n)) :
    ∃ z ∈ supp (ι (vertex' n) ≫ (Affine.S R _ ^ k).f n),
      y = (induceFromAffine.sSet x).app _ z := by
  rw [ι_S_pow_eq, ← Category.assoc] at hy
  apply mem_supp_comp at hy
  peel hy with z hz hy
  grw [induceFromAffine, ι_comp_map, supp_ι_subset] at hy
  simpa


set_option backward.isDefEq.respectTransparency false in
variable (R) in
theorem exists_S_pow_subordinate.single
    {β : Type*} {U : β → Set X}
    (hcover : ⋃ i, interior (U i) = Set.univ)
    {n} (x : 𝒮 X _⦋n⦌) :
    ∃ k, ∀ j ≥ k, ∀ y ∈ supp (ι x ≫ (S R X ^ j).f n),
      ∃ i, Set.range y.down.hom ⊆ U i := by
  let U' i : Set ΔₜU[n] :=
    (x.down.hom.comp ⟨_, induceFromAffine.shuffleULift.{w}.continuous⟩) ⁻¹' interior (U i)
  have hopen' i : IsOpen (U' i) :=
    isOpen_interior.preimage (map_continuous _)
  have hcover' : ⋃ i, U' i = Set.univ := by
    rw [← Set.preimage_iUnion, hcover, Set.preimage_univ]
  have ⟨k, hk⟩ :=
    Affine.exists_S_pow_subordinate.single R
      hopen' hcover'
      (n := n) (x := vertex' n)
  exists k
  peel hk with j hjk hk
  intro y hy
  apply exists_of_supp_S_pow at hy
  rcases hy with ⟨z, hz, hy⟩
  apply hk at hz
  peel hz with i hz
  rw [← Set.image_subset_iff] at hz
  grw [← interior_subset (s := U i), ← hz, hy]
  dsimp
  rw [Set.image_comp]
  unfold induceFromAffine.sSet
  dsimp [TopCat.toSSet, ContinuousMap.comp, ContinuousMap.coe_mk, Affine.toSing.sSet]
  simp_rw [Set.range_comp]
  apply_rules [Set.image_mono]
  simp


variable (R) in
theorem exists_S_pow_subordinate
    {β : Type*} {U : β → Set X}
    (hcover : ⋃ i, interior (U i) = Set.univ)
    {n} (f : A ⟶ (𝒞).X n) :
    ∃ k, ∀ y ∈ supp (f ≫ (S R X ^ k).f n),
      ∃ i, Set.range y.down.hom ⊆ U i := by
  have this (x : 𝒮 X _⦋n⦌) := exists_S_pow_subordinate.single R (x := x) hcover
  choose u hu using this
  obtain ⟨k, hk⟩ : ∃ k, ∀ x ∈ supp f, u x ≤ k := by
    exists (supp_finite f).toFinset.sup u
    simp +contextual [Finset.le_sup]
  exists k
  intro x hx
  apply mem_supp_comp at hx
  rcases hx with ⟨y, hy, hx⟩
  exact hu y k (hk _ hy).ge _ hx


variable (X) {β : Type*} (U : β → Set X)

/--
The singular simplicial set of `X`, restricted to simplices in at least one of the sets in `U`.
-/
noncomputable def restrictedSSet : (𝒮 X).Subcomplex where
  obj n := { σ | ∃ i, Set.range σ.down.hom ⊆ U i }
  map {A B} i := by
    intro f hf
    dsimp only [Set.mem_setOf_eq, Set.preimage_setOf_eq] at hf ⊢
    rw [TopCat.toSSet_obj_map, TopCat.hom_comp, ContinuousMap.coe_comp]
    peel hf with i u hf
    grind only [= Set.mem_range]

-- note this isnt actually of type … → SSet.{w}
-- (but it coerces (but you still might need/want to manually insert .toSSet))
scoped notation "𝒮ʳ" => restrictedSSet

local notation3 "𝒞ʳ" => 𝒞[𝒮ʳ X U; R]

variable (R) in
/--
The inclusion map from restricted chain complexes.
-/
noncomputable def restrictedChainComplex.toChainComplex : 𝒞ʳ ⟶ 𝒞 :=
  𝒞[—; R].map <| SSet.Subcomplex.ι _


local notation3 "∂ʳ" => (𝒞ʳ).d

scoped notation3 "ι♯[" U "; " R "]" => restrictedChainComplex.toChainComplex R _ U
local notation3 "ι♯" => ι♯[U; R]


section ForLater

set_option backward.isDefEq.respectTransparency false in
noncomputable def restrictedSSet.incl i :
    𝒮 (.of (U i)) ⟶ 𝒮ʳ X U :=
  let f := 𝒮* <| TopCat.ofHom <| .restrict (U i) (.id _)
  𝒮ʳ X U |>.lift f ?_
where finally
  rw [Subfunctor.le_def]
  rintro ⟨n⟩
  cases n using SimplexCategory.rec with | h n
  simp only [Subfunctor.range_obj, restrictedSSet, Functor.op_obj, SimplexCategory.toTop_obj,
    TopCat.uliftFunctor, yoneda_obj_obj, Set.range_subset_iff, ULift.forall,
    SimplexCategory.len_mk, Set.le_eq_subset, Set.mem_setOf_eq]
  intro x
  exists i
  intro y
  simp [f, TopCat.toSSet]

noncomputable def restrictedChainComplex.incl i :
    𝒞[𝒮 (.of (U i)); R] ⟶ 𝒞[𝒮ʳ X U; R] :=
  𝒞[—; R].map <| restrictedSSet.incl ..

@[simp] theorem restrictedSSet.incl_ι i :
    incl X U i ≫ (𝒮ʳ X U).ι =
    𝒮* (TopCat.ofHom <| .restrict (U i) (.id _)) := by
  simp [incl]

omit [HasFilteredColimitsOfSize C] [IsFinitelyPresentable R] in
@[simp] theorem restrictedChainComplex.incl_ι i :
    incl X U i ≫ ι♯ =
    𝒞[—; R].map (𝒮* (TopCat.ofHom <| .restrict (U i) (.id _))) := by
  simp [incl, restrictedChainComplex.toChainComplex, ← Functor.map_comp]

end ForLater


namespace restrictedChainComplex

instance {n} : Mono (ι♯.f n) := by
  dsimp [toChainComplex, SSet.singularChainComplexFunctor]
  apply MonoCoprod.mono_map'_of_injective
  apply Subtype.val_injective

instance : Mono ι♯ := by
  apply HomologicalComplex.mono_of_mono_f
  infer_instance

omit [HasFilteredColimitsOfSize.{w, w} C] [IsFinitelyPresentable R] in
@[reassoc (attr := simp)] theorem ι_toChainComplex
    {n} (σ : (𝒮ʳ X U).toSSet _⦋n⦌) :
    ι σ ≫ ι♯.f n = ι σ.val := by
  simp [toChainComplex]

variable {X U} in
lemma d_eq.aux {n} (σ : 𝒮ʳ X U _⦋n + 1⦌) (i : Fin (n + 2)) :
    ∃ j,
      Set.range
        (ULift.up.{w} <|
          SimplexCategory.toTop.map (SimplexCategory.δ i) ≫ σ.val.down).down.hom ⊆
      U j := by
  rcases σ with ⟨σ, i, hi⟩
  exists i
  grw [← hi]
  dsimp only [TopCat.hom_comp, ContinuousMap.comp]
  -- help
  unfold ContinuousMap.instFunLike
  dsimp only
  apply Set.range_comp_subset_range

-- seems pretty silly to be proving this but whatever
omit [HasFilteredColimitsOfSize.{w, w} C] [IsFinitelyPresentable R] in
theorem d_eq {n} :
    ∂ʳ (n + 1) n =
    ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
      map' (s := 𝒮ʳ X U) (s' := 𝒮ʳ X U) (fun σ =>
        ⟨ULift.up <| SimplexCategory.toTop.map (SimplexCategory.δ i) ≫ σ.val.down,
         d_eq.aux σ i⟩) :=
  SSet.SingularChainComplex.d_eq ..


set_option linter.unusedVariables false in
variable {X U} in
noncomputable def lift
    {n} (f : A ⟶ (𝒞).X n)
    (hf : ∀ x ∈ supp f, ∃ i, Set.range x.down.hom ⊆ U i) :
    A ⟶ 𝒞ʳ.X n :=
  f ≫ retract
where
  retract : (𝒞).X n ⟶ 𝒞ʳ.X n :=
    desc fun σ =>
      open scoped Classical in
      if hσ : ∃ i, Set.range σ.down.hom ⊆ U i
        then ι ⟨σ, hσ⟩
        else 0

omit [HasFilteredColimitsOfSize.{w, w, v, u} C] [IsFinitelyPresentable R] in
@[local simp] theorem lift.retract_spec {n} :
    ι♯.f n ≫ retract = 𝟙 _ := by
  apply hom_ext
  intro x
  simp_rw [ι_toChainComplex_assoc, Category.comp_id, retract, ι_desc, Subtype.coe_eta,
    dite_eq_left_iff]
  intro h
  apply h x.2 |>.elim

omit [IsFinitelyPresentable R] in
@[reassoc (attr := simp)] theorem lift_toChainComplex
    {n} (f : A ⟶ (𝒞).X n) hf :
    lift (U := U) f hf ≫ ι♯.f n = f := by
  rw [lift, eq_sum_over_supp f]
  simp_rw [Preadditive.sum_comp, Category.assoc]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Set.Finite.mem_toFinset] at hx
  rw [lift.retract, ι_desc_assoc, dite_cond_eq_true (by simpa using hf _ hx)]
  simp

variable {X U} in
theorem exists_S_pow_subordinate
    (hcover : ⋃ i, interior (U i) = Set.univ)
    {n} (f : A ⟶ (𝒞).X n) :
    ∃ k, ∃ f', f ≫ (S R X ^ k).f n = f' ≫ ι♯.f _ := by
  have ⟨k, hk⟩ := BarycentricSubdivision.exists_S_pow_subordinate R hcover f
  exists k, lift (f ≫ (S R X ^ k).f n) hk
  simp

end restrictedChainComplex


namespace S

variable (R) in
/--
S restricted to the restricted chain complex.
-/
noncomputable def restricted : End 𝒞ʳ where
  f n := desc fun σ =>
    restrictedChainComplex.lift (R := R)
      (ι (s := 𝒮 X) σ ≫ (S R X).f n)
      fun x hx => by
        rcases σ with ⟨σ, hσ⟩
        dsimp [restrictedSSet] at hσ hx
        peel hσ with i hσ
        grw [← hσ]
        apply range_S.single hx
  comm' := by
    simp only [ComplexShape.down_Rel]
    intro _ n rfl
    apply hom_ext
    intro σ
    rw [← cancel_mono (ι♯.f n)]
    simp only [ι_desc_assoc, Category.assoc]
    rw [← HomologicalComplex.Hom.comm, restrictedChainComplex.lift_toChainComplex_assoc,
      Category.assoc, HomologicalComplex.Hom.comm, chainComplex.d_eq, restrictedChainComplex.d_eq]
    simp [Preadditive.sum_comp, Preadditive.comp_sum]

@[reassoc (attr := simp)] theorem restricted.map_comm_of {n} :
    ι♯.f n ≫ (S R X).f n =
    (S.restricted R X U).f n ≫ ι♯.f n := by
  apply hom_ext
  intro x
  simp [restricted]

@[reassoc (attr := simp)] theorem restricted.pow_map_comm_of {k n} :
    ι♯.f n ≫ (S R X ^ k).f n =
    (S.restricted R X U ^ k).f n ≫ ι♯.f n := by
  induction k with
  | zero => simp
  | succ _ ih => simp [pow_succ', reassoc_of% ih]

end S

namespace T

variable (R) {X} in
noncomputable def restricted : Homotopy (𝟙 _) (S.restricted R X U) where
  hom i j := desc fun σ =>
    restrictedChainComplex.lift (R := R)
      (ι (s := 𝒮 X) σ ≫ (T R X).hom i j)
      fun x hx => by
        rcases σ with ⟨σ, hσ⟩
        dsimp [restrictedSSet] at hσ hx
        peel hσ with i hσ
        grw [← hσ]
        apply range_T.single hx
  zero i j h := by
    apply hom_ext
    simp [restrictedChainComplex.lift, (T R X).zero i j h]
  comm n := by
    apply hom_ext
    intro σ
    rw [← cancel_mono (ι♯.f n)]
    -- what am i even looking at
    simp_rw [Preadditive.comp_add, Preadditive.add_comp, Category.assoc,
      ← dNext_comp_right, ← prevD_comp_right, ← desc_comp_right, ← S.restricted.map_comm_of]
    simp only [HomologicalComplex.id_f, Category.id_comp, restrictedChainComplex.ι_toChainComplex,
      Subfunctor.toFunctor_obj, restrictedChainComplex.lift_toChainComplex,
      restrictedChainComplex.ι_toChainComplex_assoc]
    convert congr(ι σ.val ≫ $((T R X).comm n)) using 1
    · simp
    simp_rw [Preadditive.comp_add]
    congrm ?_ + ?_ + _
    -- helpppp
    · cases n with
      | zero => simp
      | succ n
      iterate 2 rw [dNext_eq (i' := n) (w := by simp)]
      simp [restrictedChainComplex.d_eq, chainComplex.d_eq,
        Preadditive.sum_comp, Preadditive.comp_sum]
    · iterate 2 rw [prevD_eq (j' := n + 1) (w := by simp)]
      simp

end T


private noncomputable def homotopy_iter
    {s : SSet.{w}}
    {S : End 𝒞[s; R]}
    (T : Homotopy (𝟙 _) S) :
    ∀ k : ℕ, Homotopy (𝟙 _) (S ^ k)
  | 0 => .refl _
  | k + 1 =>
    .trans (homotopy_iter T k)
      <| .trans (.ofEq (by simp))
      <| .trans (T.compRight <| S ^ k)
      <| .ofEq (by simp [pow_succ])

end prep


namespace restrictedChainComplex.toChainComplex

namespace Aux

/-
TODO:
you're going to want to extract some of this out for mayer-vietoris.
but in what form?
i guess there's only one way to find out huh
-/

-- for convenience we lock down the universe levels here,
-- we'll open them back up when we do the transport step.
variable
  {C : Type u} [Category.{v} C] [Abelian C]
  [HasCoproducts.{v} C] [HasFilteredColimitsOfSize.{v, v} C]
  (R : C) [IsFinitelyPresentable.{v} R]

variable (X : TopCat.{v}) {β : Type*} (U : β → Set X)

-- for the initial quasi-iso.
-- the assumption that R is a generator is stronger than we need,
-- we just need C to be locally compact. but we are only going to apply this
-- for R := ℤ anyway and this is more convenient
variable
  (hR : IsSeparator R)
  (hcover : ⋃ i, interior (U i) = Set.univ)

local notation3 "𝒞" => 𝒞[𝒮 X; R]
local notation3 "∂" => ∂[𝒮 X; R]

local notation3 "𝒞ʳ" => 𝒞[𝒮ʳ X U; R]
local notation3 "∂ʳ" => 𝒞ʳ.d
local notation3 "ι♯" => ι♯[U; R]

open HomologicalComplex ComplexShape

set_option backward.isDefEq.respectTransparency false in
variable {R X U} in
include hR hcover in
theorem quasiIso_of_coeffs_compact_generator :
    QuasiIso ι♯ where
  quasiIsoAt n := by
    constructor
    rw [ShortComplex.quasiIso_iff, isIso_iff_mono_and_epi]
    constructor
    · rw [ShortComplex.mono_homologyMap_iff_up_to_refinements]
      dsimp
      intro B x₂ hx₂ y₁ h
      suffices
          ∀ i : R ⟶ B, ∃ x₁ : R ⟶ (𝒞ʳ).X ((down ℕ).prev n),
          i ≫ x₂ = x₁ ≫ ∂ʳ _ _ by
        choose! x₁ hx₁ using this
        exists _, _, isSeparator_iff_epi R |>.mp hR B, Sigma.desc x₁
        apply Sigma.hom_ext
        simpa [Sigma.ι_desc_assoc] using hx₁
      intro i
      have ⟨k, x₁, hx₁⟩ := exists_S_pow_subordinate (R := R) (U := U) hcover (i ≫ y₁)
      have Tk : Homotopy (𝟙 _) (S.restricted R X U ^ k) := homotopy_iter (T.restricted ..) k
      exists x₁ + i ≫ x₂ ≫ Tk.hom _ _
      rw [← cancel_mono (f := ι♯.f _)]
      simp_rw [Preadditive.add_comp, Category.assoc, ← ι♯.comm,
        h, ← reassoc_of% hx₁, HomologicalComplex.Hom.comm, ← h, ← reassoc_of% h,
        S.restricted.pow_map_comm_of]
      rw [Tk.symm.comm]
      simp [reassoc_of% hx₂, fromNext, toPrev]
    · rw [ShortComplex.epi_homologyMap_iff_up_to_refinements]
      dsimp
      intro B y₂ hy₂
      suffices
          ∀ i : R ⟶ B,
          ∃ (x₂ : R ⟶ (𝒞ʳ).X n) (hx₂ : x₂ ≫ ∂ʳ n ((down ℕ).next n) = 0)
            (y₁ : R ⟶ (𝒞).X ((down ℕ).prev n)),
          i ≫ y₂ = x₂ ≫ ι♯.f n + y₁ ≫ ∂ _ _ by
        choose! x₂ hx₂ y₁ h using this
        refine ⟨_, _, isSeparator_iff_epi R |>.mp hR B, Sigma.desc x₂, ?_, Sigma.desc y₁, ?_⟩
        all_goals
          apply Sigma.hom_ext
        · simpa [Sigma.ι_desc_assoc] using hx₂
        · simpa [Sigma.ι_desc_assoc] using h
      intro i
      have ⟨k, x₂, hx₂⟩ := exists_S_pow_subordinate (R := R) (U := U) hcover (i ≫ y₂)
      have Tk : Homotopy (𝟙 _) (S R X ^ k) := homotopy_iter (T ..) k
      refine ⟨x₂, ?_, i ≫ y₂ ≫ (Tk.hom _ _), ?_⟩
      · rw [← cancel_mono (f := ι♯.f _)]
        simp_rw [Category.assoc, ← ι♯.comm, ← reassoc_of% hx₂, HomologicalComplex.Hom.comm,
          reassoc_of% hy₂]
        simp
      · rw [← hx₂, Tk.symm.comm]
        simp [reassoc_of% hy₂, fromNext, toPrev]


/-
next we use abstract nonsense to upgrade our quasi-iso to a (chain) homotopy equivalence
(we could also have proven this directly e.g. following Hatcher, but I wanna see how this turns out.
and it's nice for Mayer-Vietoris setup (TODO))
-/

variable {R X U}

set_option backward.isDefEq.respectTransparency false in
noncomputable def cokernel_X_iso {n} :
    (cokernel ι♯).X n ≅ (sigmaConst.obj R).obj {a : 𝒮 X _⦋n⦌ // a ∉ (𝒮ʳ X U).obj (.op ⦋n⦌)} :=
  open scoped Classical in
  letI F := sigmaConst.obj R
  have _ : F.IsLeftAdjoint := (sigmaConstAdj R).isLeftAdjoint
  let A : Type v := 𝒮ʳ X U _⦋n⦌
  let B : Type v := {a : 𝒮 X _⦋n⦌ // a ∉ (𝒮ʳ X U).obj (.op ⦋n⦌)}
  let C : Type v := 𝒮 X _⦋n⦌
  let e : A ⊕ B ≃ C := Equiv.sumCompl _
  have he {i} : e (.inl i) = i := by simp +zetaDelta
  calc
    _ ≅ HomologicalComplex.eval _ _ n |>.obj <| cokernel ι♯ :=
      .refl _
    _ ≅ cokernel (ι♯.f n) :=
      PreservesCokernel.iso _ _
    _ ≅ cokernel (biprod.inl (X := F.obj A) (Y := F.obj B)) :=
      -- TODO: extract some/all of this out
      -- (idk what the best way to do that is though)
      .symm <| cokernel.mapIso _ _
        (.refl _)
        (calc
          _ ≅ F.obj A ⨿ F.obj B := biprod.isoCoprod _ _
          _ ≅ F.obj (A ⨿ B) := PreservesColimitPair.iso _ _ _
          _ ≅ F.obj C := F.mapIso (Types.binaryCoproductIso _ _ ≪≫ e.toIso))
        <| by
          simp only [Iso.trans_def, Functor.mapIso_trans, Iso.trans_assoc, Iso.trans_hom,
            biprod_isoCoprod_hom, PreservesColimitPair.iso_hom, Functor.mapIso_hom, Equiv.toIso_hom,
            biprod.inl_desc_assoc, coprodComparison_inl_assoc, Iso.refl_hom, Category.id_comp]
          simp_rw [← F.map_comp]
          change F.map _ = F.map _
          congr 1
          ext; simpa using he
    _ ≅ F.obj B := cokernelBiprodInlIso

local instance cokernel_X_projective {n} [Projective R] :
    Projective (cokernel ι♯ |>.X n) := by
  rw [Projective.iso_iff cokernel_X_iso]
  apply Projective.instSigmaObj

local instance cokernel_shortExact :
    (ShortComplex.cokernelSequence ι♯).ShortExact where
  exact := ShortComplex.cokernelSequence_exact _
  mono_f := inferInstanceAs (Mono ι♯)

local notation3 "F" => embeddingDownNat.extendFunctor C
local notation3 "FQ" => (F).obj (cokernel ι♯)
local notation3 "FS" => ShortComplex.cokernelSequence ι♯ |>.map F

-- TODO: we could instead prove that F PreservesHomology in much the same way
-- and then combine with preservesFiniteLimits_of_preservesHomology etc.
-- so:
-- move this out, and maybe also extract out lemmas about composing eval
-- with extendFunctor.
local instance cokernel_shortExact' :
    (FS).ShortExact := by
  rw [shortExact_iff_degreewise_shortExact]
  intro n
  rw [← ShortComplex.map_comp]
  by_cases! hn : ∃ i, embeddingDownNat.f i = n
  · rcases hn with ⟨i, hi⟩
    apply ShortComplex.shortExact_of_iso _ <|
      cokernel_shortExact (X := X) (U := U) (R := R) |>.map_of_exact (eval _ _ i)
    apply ShortComplex.mapNatIso
    exact NatIso.ofComponents (.symm <| extendXIso · _ hi) (by simp [extendMap_f _ _ hi])
  · -- bleh
    open ZeroObject in
    have _ := Functor.preservesLimitsOfSize_of_isZero
      (0 : ChainComplex C ℕ ⥤ C) (Limits.isZero_zero _)
    have _ := Functor.preservesColimitsOfSize_of_isZero
      (0 : ChainComplex C ℕ ⥤ C) (Limits.isZero_zero _)
    apply ShortComplex.shortExact_of_iso _ <|
      cokernel_shortExact (X := X) (U := U) (R := R) |>.map_of_exact 0
    apply ShortComplex.mapNatIso
    exact NatIso.ofComponents (.symm <| isZero_extend_X · _ _ hn |>.iso (by simp)) <|
      by simp [extendMap_f_eq_zero _ _ _ hn]

local notation3 "hFS" => cokernel_shortExact' (R := R) (U := U)

open DerivedCategory in
include hR hcover in
theorem cokernel'_acyclic :
    (FQ).Acyclic := by
  have _ := HasDerivedCategory.standard C
  have hι : QuasiIso ι♯ := quasiIso_of_coeffs_compact_generator hR hcover
  have : QuasiIso ((F).map ι♯) := instQuasiIsoExtendMap ..
  let t := triangleOfSES hFS
  have ht : t ∈ distTriang _ := triangleOfSES_distinguished _
  erw [← isIso_Q_map_iff_quasiIso, ← t.isZero₃_iff_isIso₁ ht] at this
  change IsZero (Q.obj FQ) at this
  -- TODO: maybe separate this out into a theorem?
  intro n
  rw [exactAt_iff_isZero_homology]
  exact homologyFunctor C n |>.map_isZero this |>.of_iso <|
    homologyFunctorFactors C n |>.app FQ |>.symm

local instance cokernel'_X_projective [Projective R] {n} :
    Projective (FQ |>.X n) := by
  dsimp
  -- this feels a little bit silly but seems intended
  by_cases! hn : ∃ i, embeddingDownNat.f i = n
  · rcases hn with ⟨i, hi⟩
    rw [Projective.iso_iff <| extendXIso _ _ hi]
    apply cokernel_X_projective
  · apply isZero_extend_X _ _ _ hn |>.projective

include hR hcover in
theorem cokernel'_contractible [Projective R] :
    Nonempty (Homotopy (𝟙 FQ) 0) := by
  have _ : CochainComplex.IsStrictlyLE FQ 0 :=
    inferInstanceAs <|
      CochainComplex.IsStrictlyLE (extend _ embeddingDownNat) 0
  apply CochainComplex.isKProjective_of_projective FQ 0 |>.nonempty_homotopy_zero
  apply cokernel'_acyclic <;> assumption

open HomotopyCategory

include hR hcover in
lemma is_homotopy_iso' [Projective R] :
    IsIso (quotient _ _ |>.map <| (F).map ι♯) := by
  let t := CochainComplex.trianglehOfDegreewiseSplit FS
    fun n => by
      have _ : Projective ((FS).map (eval _ _ n)).X₃ := cokernel'_X_projective ..
      exact (hFS).map_of_exact (eval _ _ n) |>.splittingOfProjective
  have ht : t ∈ distTriang _ :=
    distinguished_iff_iso_trianglehOfDegreewiseSplit t |>.mpr <| ⟨_, _, ⟨Iso.refl _⟩⟩
  have h₃ : IsZero t.obj₃ := by
    dsimp [t]
    rw [isZero_quotient_obj_iff]
    apply cokernel'_contractible <;> assumption
  exact t.isZero₃_iff_isIso₁ ht |>.mp h₃

include hR hcover in
theorem is_homotopy_iso [Projective R] :
    IsIso (quotient _ _ |>.map ι♯) := by
  let F' := embeddingDownNat.extendHomotopyFunctor C
  have : IsIso (F'.map <| quotient _ _ |>.map ι♯) := is_homotopy_iso' hR hcover
  convert F'.preimageIso (@asIso _ _ _ _ _ this) |>.isIso_hom
  simp

noncomputable def homotopyEquiv [Projective R] :
    HomotopyEquiv 𝒞ʳ 𝒞 :=
  let e := homotopyEquivOfIso <| @asIso _ _ _ _ _ (is_homotopy_iso hR hcover)
  let φ : Homotopy e.hom ι♯ := homotopyOutMap ..
  { hom := ι♯
    inv := e.inv
    homotopyHomInvId := φ.symm.compRight _ |>.trans e.homotopyHomInvId
    homotopyInvHomId := φ.symm.compLeft  _ |>.trans e.homotopyInvHomId }

end Aux

variable
  {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
  (R : C)
  {X : TopCat.{w}} {β : Type*} {U : β → Set X}
  (hcover : ⋃ i, interior (U i) = Set.univ)

-- TODO: move this setup stuff somewhere else

local notation3 "Uℤ" => AddCommGrpCat.of <| ULift ℤ

def coyonedaOpUℤIsoForget : coyoneda.obj (Opposite.op Uℤ) ≅ forget _ :=
  NatIso.ofComponents fun X => Equiv.toIso <|
    { toFun f := f.hom 1
      invFun x := AddCommGrpCat.ofHom <| uliftZMultiplesHom _ x
      left_inv f := by
        apply AddCommGrpCat.ext
        simp [AddEquiv.ulift, ← map_zsmul, ← ULift.up_intCast]
      right_inv x := by simp [AddEquiv.ulift] }

local instance : IsFinitelyPresentable.{w, w} Uℤ := by
  rw [isFinitelyPresentable_iff_preservesFilteredColimits]
  -- maybe take out a `preservesFilteredColimits_of_natIso` or something
  constructor
  exact fun _ _ => preservesColimitsOfShape_of_natIso coyonedaOpUℤIsoForget.symm

local instance : Projective Uℤ := by
  rw [Projective.projective_iff_preservesEpimorphisms_coyoneda_obj]
  apply Functor.preservesEpimorphisms.of_natTrans coyonedaOpUℤIsoForget.inv

open AddCommGrpCat in
lemma sep : IsSeparator Uℤ := by
  rw [isSeparator_iff_faithful_coyoneda_obj]
  apply Functor.Faithful.of_iso coyonedaOpUℤIsoForget.symm

include hcover in
open Lifting in
/--
`restrictedChainComplex.toChainComplex` and some homotopy inverse thereof,
bundled into a HomotopyEquiv.
-/
noncomputable def homotopyEquiv : HomotopyEquiv 𝒞[𝒮ʳ X U; R] 𝒞[𝒮 X; R] :=
  let e := liftHomotopyEquiv R (Aux.homotopyEquiv sep.{w} hcover)
  let φ : Homotopy e.hom ι♯[U; R] := .ofEq <| by
    simp_rw [e, liftHomotopyEquiv, Aux.homotopyEquiv]
    apply liftChainMap_map
  -- TODO: generalize this out together with the other definition's use of it
  { hom := ι♯[U; R]
    inv := e.inv
    homotopyHomInvId := φ.symm.compRight _ |>.trans e.homotopyHomInvId
    homotopyInvHomId := φ.symm.compLeft  _ |>.trans e.homotopyInvHomId }

include hcover in
/--
Main consequence of barycentric subdivision: the inclusion from
chains subordinate to a family whose interiors cover X
to chains is a quasi-iso.
-/
theorem quasiIso
    [∀ i, 𝒞[𝒮ʳ X U; R].HasHomology i] [∀ i, 𝒞[𝒮 X; R].HasHomology i] :
    QuasiIso ι♯[U; R] :=
  homotopyEquiv R hcover |>.quasiIso_hom

end restrictedChainComplex.toChainComplex

end BarycentricSubdivision

end AlgebraicTopology
