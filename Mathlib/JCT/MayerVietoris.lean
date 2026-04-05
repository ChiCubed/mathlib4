module

public import Mathlib.JCT.BarycentricSubdivision

@[expose] public section


universe w v u

open CategoryTheory Limits
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


-- TODO try use these everywhere they're used
-- (which is lots of places, including in BarycentricSubdivision)
namespace TopCat.Subspace

variable {X Y : TopCat.{u}}

noncomputable abbrev ι (A : Set X) : of A ⟶ X :=
  ofHom <| .restrict A (.id _)

noncomputable abbrev homOfLE {A B : Set X} (h : A ⊆ B) : of A ⟶ of B :=
  ofHom <| .inclusion h

noncomputable abbrev restrict (f : X ⟶ Y)
    {A : Set X} {B : Set Y} (h : f '' A ⊆ B) :
    of A ⟶ of B :=
  ofHom <| .codRestrict (.restrict A f.hom) B (by aesop)

instance (A : Set X) : Mono (ι A) := by
  simp [TopCat.mono_iff_injective]

instance {A B : Set X} (h : A ⊆ B) : Mono (homOfLE h) := by
  simp [TopCat.mono_iff_injective, ContinuousMap.inclusion, Set.inclusion_injective]

theorem mono_restrict (f : X ⟶ Y) {A B} (h : f '' A ⊆ B) (hf : Set.InjOn f A) :
    Mono (restrict f h) := by
  simp [TopCat.mono_iff_injective, ContinuousMap.codRestrict, Set.MapsTo.restrict,
    Function.Injective, Subtype.map]
  grind [Set.InjOn]

instance (f : X ⟶ Y) [Mono f] {A B} (h : f '' A ⊆ B) : Mono (restrict f h) :=
  mono_restrict f h <| TopCat.mono_iff_injective f |>.mp inferInstance |>.injOn

end TopCat.Subspace


-- TODO move this
namespace CategoryTheory.Limits

universe v' u'
variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C]

-- we cant use an adjunction because of mismatched universes
private noncomputable def mappy
    {J : Type u'} [hJ : Category.{v'} J]
    {K : J ⥤ Type w} {c : Cocone K} (hc : IsColimit c) {X : C} :
    IsColimit ((sigmaConst.obj X).mapCocone c) :=
  have _ : HasColimit K := .mk ⟨c, hc⟩
  let i : c.pt ≅ (colimit.cocone K).pt :=
    hc.coconePointUniqueUpToIso (colimit.isColimit K)
  -- this equivalence is awesome i love it
  let e : c.pt ≃ K.ColimitType :=
    i.toEquiv.trans <| Types.colimitEquivColimitType _
  have hi j k : i.hom (c.ι.app j k) = colimit.ι K j k := by
    change (c.ι.app j ≫ i.hom) k = _
    rw [hc.comp_coconePointUniqueUpToIso_hom]
    simp
  have he j k : e (c.ι.app j k) = K.ιColimitType j k := by
    simp [e, hi, Functor.ιColimitType]
  let f (t : Cocone (K ⋙ sigmaConst.obj X)) : K.ColimitType → (X ⟶ t.pt) :=
    K.descColimitType <|
      { pt := X ⟶ t.pt
        ι j k := Sigma.ι (fun _ => X) k ≫ t.ι.app j
        ι_naturality {j j'} f := funext fun x => by
          have : (K ⋙ sigmaConst.obj X).map f ≫ t.ι.app j' = t.ι.app j := by
            rw [t.ι.naturality]
            simp
          simp [← this] }
  { desc t := Sigma.desc <| f t ∘ e
    fac s j := by
      apply Sigma.hom_ext
      simp [Sigma.ι_desc, f, he]
    uniq s m h := by
      replace h j k :
          Sigma.ι (fun _ : c.pt => X) (c.ι.app j k) ≫ m =
          Sigma.ι (fun _ => X) k ≫ s.ι.app j :=
        by simpa using congr(Sigma.ι _ k ≫ $(h j))
      apply Sigma.hom_ext
      intro b
      obtain ⟨j, k, rfl⟩ := Types.jointly_surjective K hc b
      simp [Sigma.ι_desc, h, f, he] }

set_option linter.unusedVariables false in
instance (X : C) : PreservesColimitsOfSize.{v', u'} (sigmaConst.obj X) :=
  .mk fun {J} hJ => .mk fun {K} => .mk fun {c} hc => .intro <| mappy hc


section biproducts

universe w₁ w₂ v₁ v₂ u₁ u₂
variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
variable [HasZeroMorphisms C] [HasZeroMorphisms D]
variable (F : C ⥤ D) [F.PreservesZeroMorphisms]

set_option backward.isDefEq.respectTransparency false

-- i dont use this at all, but i would feel bad if i didn't prove it
namespace biproduct

variable
  {J : Type w₁}
  (f g : J → C) [HasBiproduct f] [HasBiproduct g]
  [PreservesBiproduct f F] [PreservesBiproduct g F]
  {W : C}

theorem map_map (p : ∀ b, f b ⟶ g b) :
    F.map (map p) =
    (F.mapBiproduct f).hom
      ≫ map (fun b => F.map (p b))
      ≫ (F.mapBiproduct g).inv := by
  classical
  rw [← Iso.inv_comp_eq, Iso.eq_comp_inv]
  ext i j
  rw [Functor.mapBiproduct_hom, Functor.mapBiproduct_inv]
  simp [← Functor.map_comp, ι_π_assoc]
  aesop

end biproduct

namespace biprod

variable
  (W X Y Z : C)
  [HasBinaryBiproduct W X] [PreservesBinaryBiproduct W X F]
  [HasBinaryBiproduct Y Z] [PreservesBinaryBiproduct Y Z F]

theorem map_map (f : W ⟶ Y) (g : X ⟶ Z) :
    F.map (map f g) =
    (F.mapBiprod W X).hom
      ≫ map (F.map f) (F.map g)
      ≫ (F.mapBiprod Y Z).inv := by
  rw [← Iso.inv_comp_eq, Iso.eq_comp_inv]
  ext <;> simp [Functor.mapBiprod, ← Functor.map_comp]

end biprod

end biproducts

end CategoryTheory.Limits


namespace CategoryTheory

namespace Square

variable {C : Type*} [Category* C] [Preadditive C]
  (sq : Square C) [HasBinaryBiproduct sq.X₂ sq.X₃]

@[simps!]
noncomputable abbrev shortComplex : ShortComplex C :=
  sq.commSq.shortComplex

@[simps]
noncomputable def shortComplex.map
    {s t : Square C} (f : s ⟶ t)
    [HasBinaryBiproduct s.X₂ s.X₃]
    [HasBinaryBiproduct t.X₂ t.X₃] :
    shortComplex s ⟶ shortComplex t where
  τ₁ := f.τ₁
  τ₂ := biprod.map f.τ₂ f.τ₃
  τ₃ := f.τ₄

end Square

end CategoryTheory


namespace AlgebraicTopology

section setup

variable {C : Type u} [Category.{v} C] [Preadditive C]
open HomologicalComplex (eval)

@[simp]
theorem AlternatingFaceMapComplex.comp_eval i :
    alternatingFaceMapComplex C ⋙ eval _ _ i = evaluation _ _ _⦋i⦌ :=
  rfl

namespace SSet.SingularChainComplex

variable
  [HasCoproducts.{w} C]
  (R : C)

@[simp]
theorem singularChainComplexFunctor_obj_comp_eval i :
    𝒞[—; R] ⋙ eval _ _ i = evaluation _ _ _⦋i⦌ ⋙ sigmaConst.obj R :=
  rfl

instance preservesMonos : 𝒞[—; R].PreservesMonomorphisms := by
  constructor
  intro X Y f hf
  dsimp [SSet.singularChainComplexFunctor]
  apply HomologicalComplex.mono_of_mono_f
  intro i
  dsimp [SSet.singularChainComplexFunctor]
  apply MonoCoprod.mono_map'_of_injective
  apply injective_of_mono

instance preservesColimitsOfSize.{v', u'} :
    PreservesColimitsOfSize.{v', u'} 𝒞[—; R] := by
  constructor
  intro J hJ
  apply HomologicalComplex.preservesColimitsOfShape_of_eval
  intro i
  rw [singularChainComplexFunctor_obj_comp_eval]
  apply comp_preservesColimitsOfShape

end SSet.SingularChainComplex

end setup


variable
  {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C]

open scoped BarycentricSubdivision SSet.SingularChainComplex

local notation3 "𝒞top[—; " R "]" => singularChainComplexFunctor _ |>.obj R
local notation3 "𝒞top[" X "; " R "]" => 𝒞top[—; R].obj X
local notation3 "∂top[" X "; " R "]" => 𝒞top[X; R].d


namespace TopCat.Square

-- some pre-definitions for mayer-vietoris
variable (R : C) (s : Square TopCat.{w})

-- TODO: extract out something like a functor `Square.toPushout`, and then functoriality is free.

@[simps! X₁ X₂ X₃ X₄ f₁₂ f₁₃ f₂₄ f₃₄]
noncomputable def complexPushoutSquare :
    Square (ChainComplex C ℕ) :=
  let s' := s.map 𝒞top[—; R]
  { s' with
    X₄ := pushout s'.f₁₂ s'.f₁₃
    f₂₄ := pushout.inl ..
    f₃₄ := pushout.inr ..
    fac := pushout.condition }

theorem isPushout_complexPushoutSquare :
    (complexPushoutSquare R s).IsPushout :=
  .of_isColimit' (complexPushoutSquare R s).commSq <| pushoutIsPushout ..

@[simps! X₁ X₂ X₃ f g]
noncomputable def pushoutShortComplex :
    ShortComplex (ChainComplex C ℕ) :=
  complexPushoutSquare R s |>.shortComplex

theorem shortExact_pushoutShortComplex_of_mono₁₂ [Mono s.f₁₂] :
    (pushoutShortComplex R s).ShortExact where
  -- very satisfying alignments :)
  exact := isPushout_complexPushoutSquare R s |>.exact_shortComplex
  epi_g := isPushout_complexPushoutSquare R s |>.epi_shortComplex_g
  mono_f := by
    dsimp [singularChainComplexFunctor]
    apply biprod.mono_lift_of_mono_left


variable {R} in
@[simps]
noncomputable def complexPushoutSquare.map
    {s t : Square TopCat.{w}} (f : s ⟶ t) :
    complexPushoutSquare R s ⟶ complexPushoutSquare R t :=
  let f' := 𝒞top[—; R].mapSquare.map f
  { f' with
    τ₄ := pushout.map _ _ _ _ f'.τ₂ f'.τ₃ f'.τ₁
            (by simp [f', ← Functor.map_comp])
            (by simp [f', ← Functor.map_comp])
    comm₂₄ := by simp [f', pushout.map, pushout.inl_desc]
    comm₃₄ := by simp [f', pushout.map, pushout.inr_desc] }

variable {R} in
@[simps! τ₁ τ₂ τ₃]
noncomputable def pushoutShortComplex.map
    {s t : Square TopCat.{w}} (f : s ⟶ t) :
    pushoutShortComplex R s ⟶ pushoutShortComplex R t :=
  Square.shortComplex.map <| complexPushoutSquare.map f

noncomputable abbrev pushoutShortComplex.ιX₃ : (pushoutShortComplex R s).X₃ ⟶ 𝒞top[s.X₄; R] :=
  pushout.desc (s.map 𝒞top[—; R]).f₂₄ (s.map 𝒞top[—; R]).f₃₄ (Square.fac _)

section constructors

variable
  {X Y : TopCat.{w}} (f : X ⟶ Y)
  (A B : Set X) (A' B' : Set Y)

/--
The square
```
  A ∩ B -----> A
    |          |
    |          |
    v          v
    B -------> X
```
where `A B : Set X` (note that the bottom right is `X` and not `A ∪ B`.)
-/
@[simps]
noncomputable def ofSubspaces :
    Square TopCat where
  X₁ := .of (A ∩ B :)
  X₂ := .of A
  X₃ := .of B
  X₄ := X
  f₁₂ := TopCat.Subspace.homOfLE (by simp)
  f₁₃ := TopCat.Subspace.homOfLE (by simp)
  f₂₄ := TopCat.Subspace.ι _
  f₃₄ := TopCat.Subspace.ι _
  fac := by aesop

section
-- weird that these fail without the set_option
set_option backward.isDefEq.respectTransparency false
instance : Mono (ofSubspaces A B).f₁₂ := by dsimp; infer_instance
instance : Mono (ofSubspaces A B).f₁₃ := by dsimp; infer_instance
instance : Mono (ofSubspaces A B).f₂₄ := by dsimp; infer_instance
instance : Mono (ofSubspaces A B).f₃₄ := by dsimp; infer_instance
end

noncomputable def ofSubspaces.map
    (hA : f '' A ⊆ A') (hB : f '' B ⊆ B') :
    ofSubspaces A B ⟶ ofSubspaces A' B' where
  τ₁ := TopCat.Subspace.restrict f (by grind)
  τ₂ := TopCat.Subspace.restrict f hA
  τ₃ := TopCat.Subspace.restrict f hB
  τ₄ := f

end constructors

end TopCat.Square

open TopCat.Square renaming ofSubspaces → squareOfSubspaces


namespace BarycentricSubdivision

section

variable
  {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
  {R : C} {X : TopCat.{w}} {β : Type*} (U : β → Set X)

instance restrictedSSet.instMonoIncl i : Mono (incl X U i) := by
  dsimp [incl]
  refine @mono_of_mono _ _ _ _ _ _ (𝒮ʳ X U).ι ?_
  simp only [SSet.Subcomplex.lift_ι]
  apply Functor.map_mono

instance restrictedChainComplex.instMonoIncl i : Mono (incl (R := R) X U i) := by
  unfold incl; infer_instance

end

namespace restrictedSSet

variable {X : TopCat.{w}} (A B : Set X)

open SSet SSet.Subcomplex

noncomputable abbrev inl : 𝒮 (.of A) ⟶ 𝒮ʳ X ![A, B] := incl X ![A, B] 0
noncomputable abbrev inr : 𝒮 (.of B) ⟶ 𝒮ʳ X ![A, B] := incl X ![A, B] 1

set_option backward.isDefEq.respectTransparency false in
noncomputable def singleIso :
    𝒮 (.of A) ≅ (𝒮ʳ X ![A]).toSSet :=
  let i := TopCat.Subspace.ι A
  have : Mono (TopCat.Subspace.ι A) := by
    simp [TopCat.mono_iff_injective]
  asIso (toRange (𝒮* i)) ≪≫ SSet.Subcomplex.eqToIso ?_
where finally
  -- this proof sucks
  ext n x
  rcases n with ⟨n⟩
  cases n using SimplexCategory.rec with | h n
  simp only [TopCat.toSSet, Subfunctor.range_obj, Functor.op_obj, SimplexCategory.toTop_obj,
    SimplexCategory.len_mk, yoneda_obj_obj, Set.mem_range, Presheaf.restrictedULiftYoneda_map_app,
    restrictedSSet, Nat.succ_eq_add_one, Nat.reduceAdd, Matrix.cons_val_fin_one, exists_const,
    Set.mem_setOf_eq]
  constructor
  · rintro ⟨y, rfl⟩
    dsimp
    grw [Set.range_comp_subset_range]
    simp [i]
  · intro h
    exists .up <| TopCat.ofHom <| x.down.hom.codRestrict A (by grind)

lemma bicartSq :
    BicartSq (X := 𝒮 X)
      (𝒮ʳ X ![A ∩ B])
      (𝒮ʳ X ![A])
      (𝒮ʳ X ![B])
      (𝒮ʳ X ![A, B]) := by
  constructor <;> ext n x <;> simp [restrictedSSet]

@[simps]
noncomputable def pushoutSquare : Square SSet where
  f₁₂ := 𝒮* (squareOfSubspaces A B).f₁₂
  f₁₃ := 𝒮* (squareOfSubspaces A B).f₁₃
  f₂₄ := inl _ _
  f₃₄ := inr _ _
  fac := rfl

set_option backward.isDefEq.respectTransparency false in
theorem isPushout_pushoutSquare :
    (pushoutSquare A B).IsPushout :=
  (bicartSq A B).isPushout.of_iso'
    (singleIso _) (singleIso _) (singleIso _) (.refl _)
    rfl rfl ?_ ?_
where finally all_goals
  rw [← cancel_mono (𝒮ʳ X _).ι]
  simp [singleIso, homOfLE_comp]

end restrictedSSet

namespace restrictedChainComplex

variable
  {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
  (R : C) {X : TopCat.{w}} (A B : Set X)

noncomputable abbrev inl : 𝒞top[.of A; R] ⟶ 𝒞[𝒮ʳ X ![A, B]; R] := incl X ![A, B] 0
noncomputable abbrev inr : 𝒞top[.of B; R] ⟶ 𝒞[𝒮ʳ X ![A, B]; R] := incl X ![A, B] 1

@[simps! X₁ X₂ X₃ X₄ f₁₂ f₁₃]
noncomputable def pushoutSquare : Square (ChainComplex C ℕ) :=
  restrictedSSet.pushoutSquare A B |>.map 𝒞[—; R]

@[simp] theorem pushoutSquare_f₂₄ : (pushoutSquare R A B).f₂₄ = inl R A B := rfl
@[simp] theorem pushoutSquare_f₃₄ : (pushoutSquare R A B).f₃₄ = inr R A B := rfl

theorem isPushout_pushoutSquare :
    (pushoutSquare R A B).IsPushout :=
  restrictedSSet.isPushout_pushoutSquare A B |>.map _

end BarycentricSubdivision.restrictedChainComplex


structure MayerVietorisSquare (R : C) extends Square TopCat.{w} where
  mono_f₁₂ : Mono f₁₂ := by infer_instance
  -- is_pushout : toSquare.IsPushout
  -- note that we could require this for ULift ℤ, and it automatically follows for
  -- any R in any (abelian?) C
  quasiIso' : QuasiIso <| TopCat.Square.pushoutShortComplex.ιX₃ R toSquare

namespace MayerVietorisSquare

variable {R : C} (s : MayerVietorisSquare R)

attribute [instance] mono_f₁₂

noncomputable abbrev shortComplex :=
  TopCat.Square.pushoutShortComplex R s.toSquare

theorem shortExact_shortComplex : s.shortComplex.ShortExact :=
  TopCat.Square.shortExact_pushoutShortComplex_of_mono₁₂ ..

noncomputable abbrev ιX₃ :=
  TopCat.Square.pushoutShortComplex.ιX₃ R s.toSquare

instance quasiIso : QuasiIso s.ιX₃ :=
  s.quasiIso'

-- this is slightly annoying for the user, but not awful I guess.
-- the main alternative idea would be to provide a distinguished triangle
-- with the third term adjusted to 𝒞top[s.X₄; R], but we would have to
-- map the shape to ℤ, which sounds more inconvenient
noncomputable def isoHomologyX₃ i :
    s.shortComplex.X₃.homology i ≅ 𝒞top[s.X₄; R].homology i :=
  asIso <| HomologicalComplex.homologyMap (ιX₃ s) i

section constructors

set_option backward.isDefEq.respectTransparency false in
@[simps! X₁ X₂ X₃ X₄ f₁₂ f₁₃ f₂₄ f₃₄]
noncomputable def ofUnionInterior
    (X : TopCat.{w}) (A B : Set X)
    (h : interior A ∪ interior B = Set.univ) :
    MayerVietorisSquare R where
  toSquare := squareOfSubspaces A B
  mono_f₁₂ := by
    rw [TopCat.mono_iff_injective]
    simpa [ContinuousMap.inclusion] using Set.inclusion_injective ..
  quasiIso' := by
    change QuasiIso <| pushout.desc _ _ (w := _)
    have hι : QuasiIso ι♯[![A, B]; R] :=
      BarycentricSubdivision.restrictedChainComplex.toChainComplex.quasiIso R <|
        (by convert h; ext; simp)
    have hp :=
      BarycentricSubdivision.restrictedChainComplex.isPushout_pushoutSquare R A B
    let e := hp.isoPushout
    rw [← quasiIso_iff_comp_left (φ := e.hom)]
    convert hι
    apply hp.hom_ext <;> simp [e, singularChainComplexFunctor]

set_option backward.isDefEq.respectTransparency false in
attribute [local instance] preservesBinaryBiproduct_of_preservesBiproduct in
open TopCat.Square in
noncomputable def comap
    (s : MayerVietorisSquare.{w} R)
    {t : Square TopCat}
    (f : t ⟶ s.toSquare) [Mono t.f₁₂]
    (h₁ : QuasiIso (𝒞top[—; R].map f.τ₁))
    (h₂ : QuasiIso (𝒞top[—; R].map f.τ₂))
    (h₃ : QuasiIso (𝒞top[—; R].map f.τ₃))
    (h₄ : QuasiIso (𝒞top[—; R].map f.τ₄)) :
    MayerVietorisSquare R where
  toSquare := t
  quasiIso' := by
    let sf : pushoutShortComplex R t ⟶ s.shortComplex := pushoutShortComplex.map f
    have : CommSq
        sf.τ₃ (pushoutShortComplex.ιX₃ R t)
        s.ιX₃ (𝒞top[—; R].map f.τ₄) := .mk <| by
      apply pushout.hom_ext
        <;> simp [sf, ιX₃, pushoutShortComplex.ιX₃, ← Functor.map_comp]
    have h₁₂ : QuasiIso sf.τ₃ := by
      unfold sf
      apply HomologicalComplex.HomologySequence.quasiIso_τ₃
      · apply shortExact_pushoutShortComplex_of_mono₁₂
      · apply s.shortExact_shortComplex
      · exact h₁
      · -- use that homology preserves finite biproducts
        simp_rw [quasiIso_iff, quasiIsoAt_iff_isIso_homologyMap] at h₂ h₃ ⊢
        intro i
        rw [← HomologicalComplex.homologyFunctor_map, pushoutShortComplex.map_τ₂, biprod.map_map,
          isIso_comp_left_iff, isIso_comp_right_iff]
        dsimp
        apply Balanced.isIso_of_mono_of_epi
    rw [← quasiIso_iff_comp_right (φ' := 𝒞top[—; R].map f.τ₄), ← this.w]
    infer_instance

@[simps! X₁ X₂ X₃ X₄ f₁₂ f₁₃ f₂₄ f₃₄]
noncomputable def ofQuasiIsoInclusionOfUnionInterior
    (X : TopCat.{w}) (A B : Set X)
    {U V : Set X} (hU : A ⊆ U) (hV : B ⊆ V)
    (hA : QuasiIso <| 𝒞top[—; R].map <| TopCat.Subspace.homOfLE hU)
    (hB : QuasiIso <| 𝒞top[—; R].map <| TopCat.Subspace.homOfLE hV)
    (hAB : QuasiIso <| 𝒞top[—; R].map <| TopCat.Subspace.homOfLE <|
      Set.inter_subset_inter hU hV)
    (h : interior U ∪ interior V = Set.univ) :
    MayerVietorisSquare R :=
  comap
    (ofUnionInterior X U V h)
    (TopCat.Square.ofSubspaces.map (𝟙 _) A B _ _ (by aesop) (by aesop))
    hAB
    hA
    hB
    (by
      apply +allowSynthFailures quasiIso_of_isIso
      simp [TopCat.Square.ofSubspaces.map, IsIso.id])

-- TODO: show that inclusion is a quasi-iso when we have a weak deformation retract

end constructors

end MayerVietorisSquare

end AlgebraicTopology
