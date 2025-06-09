Fredrik Bakke 2025

We define and study separated types, for a general notion of separatedness.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module TypeTopology.Separated where

open import MLTT.Spartan
open import Modal.Subuniverse
open import MLTT.Two-Properties
open import NotionsOfDecidability.Complemented
open import UF.Base
open import UF.DiscreteAndSeparated hiding (tight)
open import UF.Embeddings
open import UF.Equiv
open import UF.Yoneda
open import UF.Equiv-FunExt
open import UF.FunExt
open import UF.Hedberg
open import UF.LeftCancellable
open import UF.Lower-FunExt
open import UF.EquivalenceExamples
open import UF.NotNotStablePropositions
open import UF.PropTrunc
open import UF.Retracts
open import UF.Sets
open import UF.Sets-Properties
open import UF.SubtypeClassifier
open import UF.Subsingletons
open import UF.Subsingletons-FunExt

\end{code}

Given a type 𝒮 we can define a notion of _equality_ on an arbitrary type X by a
Leibniz principle with 𝒮-valued families:

\begin{code}

_＝₍_₎_ : {X : 𝓤 ̇ } → X → (𝒮 : 𝓥 ̇ ) → X → 𝓤 ⊔ 𝓥 ̇
x ＝₍ 𝒮 ₎ y = (p : type-of x → 𝒮) → p x ＝ p y

sep-ap : {X : 𝓤 ̇ } {Y : 𝓤' ̇ } (f : X → Y) (𝒮 : 𝓥 ̇ ) {x y : X}
       → x ＝₍ 𝒮 ₎ y → f x ＝₍ 𝒮 ₎ f y
sep-ap f 𝒮 α p = α (p ∘ f)

\end{code}

In topological models, maps into 𝟚 classify clopens, and so total
separatedness amounts to "the clopens separate the points" in the
sense that any two points with the same clopen neighbourhoods are
equal. This notion in topology is called total separatedness. Notice
that we are not referring to homotopical models in this discussion.

\begin{code}

refl-sep : (𝒮 : 𝓥 ̇ ) {X : 𝓤 ̇ } (x : X) → x ＝₍ 𝒮 ₎ x
refl-sep 𝒮 x p = refl

idtosep : (𝒮 : 𝓥 ̇ ) {X : 𝓤 ̇ } (x y : X) → x ＝ y → x ＝₍ 𝒮 ₎ y
idtosep 𝒮 x .x refl = refl-sep 𝒮 x

is-separated : (𝒮 : 𝓥 ̇ ) → 𝓤 ̇ → 𝓤 ⊔ 𝓥 ̇
is-separated 𝒮 X = {x y : X} → is-equiv (idtosep 𝒮 x y)

is-quasi-separated : (𝒮 : 𝓥 ̇ ) → 𝓤 ̇ → 𝓤 ⊔ 𝓥 ̇
is-quasi-separated 𝒮 X = {x y : X} → x ＝₍ 𝒮 ₎ y → x ＝ y

\end{code}

Every type is self-quasi-separated, but there doesn't seem to be a way to
conclude that this quasi-separation is unique in general.

\begin{code}

self-quasi-saparated : (𝒮 : 𝓥 ̇ ) → is-quasi-separated 𝒮 𝒮
self-quasi-saparated 𝒮 f = f id

compute-self-quasi-saparated :
  (𝒮 : 𝓥 ̇ ) {x y : 𝒮} → self-quasi-saparated 𝒮 ∘ idtosep 𝒮 x y ∼ id
compute-self-quasi-saparated 𝒮 refl = refl

\end{code}

We now define an alternative equivalent characterization of separatedness,
still using the equivalence relation `＝₍ 𝒮 ₎`.

\begin{code}

sep-component : (𝒮 : 𝓥 ̇ ) {X : 𝓤 ̇ } → X → 𝓤 ⊔ 𝓥 ̇
sep-component {𝓤} {𝓥} 𝒮 {X} x = (Σ y ꞉ X , x ＝₍ 𝒮 ₎ y)

sep-component-canonical-point : (𝒮 : 𝓥 ̇ )
                              → {X : 𝓤 ̇ } (x : X)
                              → sep-component 𝒮 x
sep-component-canonical-point 𝒮 x = (x , refl-sep 𝒮 x)

\end{code}

An alternative characterization of separatedness is that the sep-component of
any point is a subsingleton, and hence a singleton:

\begin{code}

is-separated₁ : (𝒮 : 𝓥 ̇ ) → 𝓤 ̇ → 𝓤 ⊔ 𝓥 ̇
is-separated₁ 𝒮 X =
 (x : X) → is-prop (sep-component 𝒮 x)

separated-gives-separated₁ : Fun-Ext
                           → (𝒮 : 𝓥 ̇ )
                           → {X : 𝓤 ̇ }
                           → is-separated 𝒮 X
                           → is-separated₁ 𝒮 X
separated-gives-separated₁ fe 𝒮 {X} ts x =
  singletons-are-props (Yoneda-Theorem-back x (idtosep 𝒮 x) λ y → ts)

separated₁-gives-separated : (𝒮 : 𝓥 ̇ ) {X : 𝓤 ̇ }
                           → is-separated₁ 𝒮 X
                           → is-separated 𝒮 X
separated₁-gives-separated {𝓤} 𝒮 {X} τ {x} {y} =
  Yoneda-Theorem-forth x (idtosep 𝒮 x)
    ( pointed-props-are-singletons (sep-component-canonical-point 𝒮 x) (τ x))
    ( y)

\end{code}

> A third formulation of the notion of total separatedness, as the
> tightness of a certain apartness relation, is given below.

The corresponding formulation of separatedness, given a subuniverse 𝒮, may be to
say that the identity types are elements of 𝒮, if 𝒮 is a subuniverse.

\begin{uncode}

discrete-types-are-totally-separated : {X : 𝓤 ̇ }
                                     → is-discrete X
                                     → is-totally-separated X
discrete-types-are-totally-separated {𝓤} {X} d {x} {y} α = g
 where
  p : X → 𝟚
  p = pr₁ (characteristic-function (d x))

  φ : (y : X) → (p y ＝ ₀ → x ＝ y) × (p y ＝ ₁ → ¬ (x ＝ y))
  φ = pr₂ (characteristic-function (d x))

  b : p x ＝ ₀
  b = different-from-₁-equal-₀ (λ s → pr₂ (φ x) s refl)

  a : p y ＝ ₀
  a = p y ＝⟨ (α p)⁻¹ ⟩
      p x ＝⟨ b ⟩
      ₀   ∎

  g : x ＝ y
  g = pr₁ (φ y) a

\end{uncode}

> The converse fails: by the results below, e.g. (ℕ → 𝟚) is totally
> separated, but its discreteness amounts to WLPO.

What is a corresponding counterexample for general separatedness?

𝒮-quasi-separated types are closed under retracts, and more generally under
left cancellable maps:

\begin{code}

left-cancellable-reflects-quasi-separated : {𝒮 : 𝓥 ̇ } {X : 𝓤 ̇ } {Y : 𝓤' ̇ }
                                          → (Y ↣ X)
                                          → is-quasi-separated 𝒮 X
                                          → is-quasi-separated 𝒮 Y
left-cancellable-reflects-quasi-separated (f , lc) τ {y} {y'} α = lc h
 where
  h : f y ＝ f y'
  h = τ (sep-ap f _ α)

retract-of-quasi-separated : {𝒮 : 𝓥 ̇ } {X : 𝓤 ̇ } {Y : 𝓤' ̇ }
                             → retract Y of X
                             → is-quasi-separated 𝒮 X
                             → is-quasi-separated 𝒮 Y
retract-of-quasi-separated (r , s , rs) = left-cancellable-reflects-quasi-separated
                                           (s , section-lc s (r , rs))

equiv-to-quasi-separated : {𝒮 : 𝓥 ̇ } {X : 𝓤 ̇ } {Y : 𝓤' ̇ }
                           → X ≃ Y
                           → is-quasi-separated 𝒮 X
                           → is-quasi-separated 𝒮 Y
equiv-to-quasi-separated 𝕗 = retract-of-quasi-separated (≃-gives-▷ 𝕗)

\end{code}

𝒮-separated types are closed under embeddings.

-- ! This proof is erroneous. It might not follow that x ＝₍𝒮₎ y → f x ＝₍𝒮₎ f y is an equivalence.

Proof. Given two elements y and y of Y and an embedding f : Y ↪ X into an
𝒮-separated type X, have a commuting diagram of shape

    x ＝ y ─────────→ x ＝₍𝒮₎ y
      │                  │
      │                  │
      │                  │
      ↓                  ↓
  f x ＝ f y ─────→ f x ＝₍𝒮₎ f y,

and we wish to prove that the top horizontal map is an equivalence. The left
vertical map is an equivalence since f is an embedding, and the bottom
horizontal map is an equivalence since X is 𝒮-separated. Finally, the right
vertical map is an equivalence by the postcomposition property of embeddings
and so the top horizontal map must also necessarily be an equivalence. ∎

-- ! This proof is erroneous. It might not follow that x ＝₍𝒮₎ y → f x ＝₍𝒮₎ f y is an equivalence.

\begin{code}

embedding-into-separated : FunExt → {𝒮 : 𝓥 ̇ } {X : 𝓤 ̇ } {Y : 𝓤' ̇ }
                             → Y ↪ X
                             → is-separated 𝒮 X
                             → is-separated 𝒮 Y
embedding-into-separated fe {𝒮} (f , H) τ {x} {y} =
  equiv-closed-under-∼
  {!   !}
  (idtosep 𝒮 x y)
  ( ≃-2-out-of-3-left
    { g = sep-ap f 𝒮}
    {! dprecomp-is-equiv ? ? ? (ap f) (embedding-gives-embedding' f H x y)  !}
    -- {!  equiv-post ? ? (ap f) (embedding-gives-embedding' f H x y) !}
    ( ∘-is-equiv (embedding-gives-embedding' f H x y) (τ {f x} {f y})))
  {!   !}


equiv-to-separated : FunExt
                   → {𝒮 : 𝓥 ̇ } {X : 𝓤 ̇ } {Y : 𝓤' ̇ }
                   → Y ≃ X
                   → is-separated 𝒮 X
                   → is-separated 𝒮 Y
equiv-to-separated fe 𝕗 = embedding-into-separated fe (≃-gives-↪ 𝕗)

\end{code}

Recall that a type is called ¬¬-separated if the doubly negated equality
of any two element implies their equality, and that such a type is a
set.

TODO: double negation stable propositions classify double negation separated types.

\begin{code}

quasi-separated-types-are-¬¬-separated : {𝒮 : 𝓥 ̇ } {X : 𝓤 ̇ }
                                       → is-¬¬-separated 𝒮
                                       → is-quasi-separated 𝒮 X
                                       → is-¬¬-separated X
quasi-separated-types-are-¬¬-separated {𝓤} {𝓥} {𝒮} {X} s τ = g
 where
  g : (x y : X) → ¬¬ (x ＝ y) → x ＝ y
  g x y φ  = τ h
   where
    a : (p : X → 𝒮) → ¬¬ (p x ＝ p y)
    a p = ¬¬-functor (ap p) φ

    h : (p : X → 𝒮) → p x ＝ p y
    h p = s (p x) (p y) (a p)

quasi-separated-types-of-quasi-separated-types : {𝒮 : 𝓥 ̇ } {𝒯 : 𝓦 ̇ } {X : 𝓤 ̇ }
                                               → is-quasi-separated 𝒯 𝒮
                                               → is-quasi-separated 𝒮 X
                                               → is-quasi-separated 𝒯 X
quasi-separated-types-of-quasi-separated-types {𝓤} {𝓥} {𝓦} {𝒮} {𝒯} {X} s τ {x} {y} = g
 where
  g : x ＝₍ 𝒯 ₎ y → x ＝ y
  g φ = τ h
   where
    a : (p : X → 𝒮) → (p x ＝₍ 𝒯 ₎ p y)
    a p q = φ (q ∘ p)

    h : x ＝₍ 𝒮 ₎ y
    h p = s (a p)

-- totally-separated-types-are-sets : funext 𝓤 𝓤₀
--                                  → (X : 𝓤 ̇ )
--                                  → is-totally-separated X
--                                  → is-set X
-- totally-separated-types-are-sets fe X t =
--  ¬¬-separated-types-are-sets fe (totally-separated-types-are-¬¬-separated X t)

\end{code}

> The converse fails: the type of propositions is a set, but its total
> separatedness implies excluded middle. In fact, its ¬¬-separatedness
> already implies excluded middle:

TODO: This should already follow from the statement that the type of De Morgan
propositions is ¬¬-separated.

\begin{uncode}

open import UF.ClassicalLogic

Ω-separated-gives-DNE : propext 𝓤
                      → funext 𝓤 𝓤
                      → is-¬¬-separated (Ω 𝓤)
                      → DNE 𝓤
Ω-separated-gives-DNE {𝓤} pe fe Ω-is-¬¬-separated P P-is-prop not-not-P = d
 where
  p : Ω 𝓤
  p = (P , P-is-prop)

  b : ¬¬ (p ＝ ⊤)
  b = ¬¬-functor (holds-gives-equal-⊤ pe fe p) not-not-P

  c : p ＝ ⊤
  c = Ω-is-¬¬-separated p ⊤ b

  d : P
  d = equal-⊤-gives-holds p c

Ω-separated-gives-EM : propext 𝓤
                     → funext 𝓤 𝓤
                     → is-¬¬-separated (Ω 𝓤)
                     → EM 𝓤
Ω-separated-gives-EM {𝓤} pe fe Ω-is-¬¬-separated =
 DNE-gives-EM (lower-funext 𝓤 𝓤 fe) (Ω-separated-gives-DNE pe fe Ω-is-¬¬-separated)

Ω-totally-separated-gives-EM : propext 𝓤
                             → funext 𝓤 𝓤
                             → is-totally-separated (Ω 𝓤)
                             → EM 𝓤
Ω-totally-separated-gives-EM {𝓤} pe fe Ω-is-totally-separated =
 Ω-separated-gives-EM pe fe
  (totally-separated-types-are-¬¬-separated (Ω 𝓤) Ω-is-totally-separated)

\end{uncode}

The need to define f and g in the following proof arises because the
function Π-is-prop requires a dependent function with explicit
arguments, but total separatedness is defined with implicit
arguments. The essence of the proof is that of p in the where clause.

\begin{code}

being-separated-is-prop : FunExt
                        → (𝒮 : 𝓥 ̇ ) (X : 𝓤 ̇ )
                        → is-prop (is-separated 𝒮 X)
being-separated-is-prop {𝓤} {𝓥} fe 𝒮 X =
 Π-is-prop' (fe 𝓥 (𝓤 ⊔ 𝓥)) λ x →
 Π-is-prop' (fe 𝓥 (𝓤 ⊔ 𝓥)) λ y →
 being-equiv-is-prop fe (idtosep 𝒮 x y)

\end{code}

As discussed above, we don't have general closure under Σ, but we have
the following particular cases:

\begin{uncode}

×-totally-separated : (X : 𝓤 ̇ ) (Y : 𝓥 ̇ )
                    → is-totally-separated X
                    → is-totally-separated Y
                    → is-totally-separated (X × Y)
×-totally-separated X Y t u {a , b} {x , y} φ =
 to-×-＝
   (t (λ (p : X → 𝟚) → φ (λ ((x , y) : X × Y) → p x)))
   (u (λ (q : Y → 𝟚) → φ (λ ((x , y) : X × Y) → q y)))

Σ-is-totally-separated-if-index-type-is-discrete :

    (X : 𝓤 ̇ ) (Y : X → 𝓥 ̇ )
  → is-discrete X
  → ((x : X) → is-totally-separated (Y x))
  → is-totally-separated (Σ Y)

Σ-is-totally-separated-if-index-type-is-discrete X Y d t {a , b} {x , y} φ = γ
 where
  r : a ＝ x
  r = discrete-types-are-totally-separated d (λ p → φ (λ z → p (pr₁ z)))

  s₂ : transport Y r b ＝₂ y
  s₂ q = g
   where
    f : {u : X} → (u ＝ x) + ¬ (u ＝ x) → Y u → 𝟚
    f (inl m) v = q (transport Y m v)
    f (inr _) v = ₀ --<-- What we choose here is irrelevant.

    p : Σ Y → 𝟚
    p (u , v) = f (d u x) v

    g = q (transport Y r b)    ＝⟨ (ap (λ - → f - b) (discrete-inl d a x r))⁻¹ ⟩
        p (a , b)              ＝⟨ φ p ⟩
        p (x , y)              ＝⟨ ap (λ - → f - y) (discrete-inl d x x refl) ⟩
        q (transport Y refl y) ∎

  s : transport Y r b ＝ y
  s = t x s₂

  γ : (a , b) ＝ (x , y)
  γ = to-Σ-＝ (r , s)

\end{uncode}

Maybe this can be further generalized by replacing the discreteness of X
with the assumption that

  (x : X) (q : Y x → 𝟚) → Σ p ꞉ Σ Y → 𝟚 , (y : Y x) → q y ＝ p (x , y).

Then the previous few functions would be a particular case of this.

See also the module SigmaDiscreteAndTotallySeparated.

The following can also be considered as a special case of Σ (indexed
by the type 𝟚):

\begin{uncode}

+-totally-separated : (X : 𝓤 ̇ ) (Y : 𝓥 ̇ )
                    → is-totally-separated X
                    → is-totally-separated Y
                    → is-totally-separated (X + Y)
+-totally-separated X Y t u {inl x} {inl x'} φ =
    ap inl (t (λ p → φ (cases p (λ (_ : Y) → ₀))))
+-totally-separated X Y t u {inl x} {inr y} φ =
    𝟘-elim (zero-is-not-one (φ (cases (λ _ → ₀) (λ _ → ₁))))
+-totally-separated X Y t u {inr y} {inl x} φ =
    𝟘-elim (zero-is-not-one (φ (cases (λ _ → ₁) (λ _ → ₀))))
+-totally-separated X Y t u {inr y} {inr y'} φ =
    ap inr (u (λ p → φ (cases (λ (_ : X) → ₀) p)))

\end{uncode}

Closure under /-extensions defined in the module
InjectiveTypes. Notice that j doesn't need to be an embedding (in
which case the extension is merely a Kan extension rather than a
proper extension).

\begin{uncode}

module _ (fe : FunExt)  where

 private
  fe' : Fun-Ext
  fe' {𝓤} {𝓥} = fe 𝓤 𝓥

 open import InjectiveTypes.Blackboard fe

 /-is-totally-separated : {X : 𝓤 ̇ } {A : 𝓥 ̇ }
                          (j : X → A)
                          (Y : X → 𝓦 ̇ )
                        → ((x : X) → is-totally-separated (Y x))
                        → (a : A) → is-totally-separated ((Y / j) a)
 /-is-totally-separated {𝓤} {𝓥} {𝓦} j Y t a =
  Π-is-totally-separated fe' (λ (σ : fiber j a) → t (pr₁ σ))

\end{uncode}

We now characterize the totally separated types X as those such that
the map eval X defined below is an embedding, in order to construct
totally separated reflections.

The proof should follow from computing the fibers of `eval`.

\begin{code}
module _ (𝒮 : 𝓥 ̇ ) where

 eval : (X : 𝓤 ̇ ) → X → ((X → 𝒮) → 𝒮)
 eval X x p = p x

 is-separated₂ : 𝓤 ̇ → 𝓤 ⊔ 𝓥 ̇
 is-separated₂ X = is-embedding (eval X)

--  separated-gives-separated₂ : FunExt
--                             → {X : 𝓤 ̇ }
--                             → is-separated X
--                             → is-separated₂ X
--  separated-gives-separated₂ fe {X} τ φ (x , p) (y , q) = ?
  -- where
  --  s : eval X x ＝ eval X y
  --  s = eval X x  ＝⟨ p ⟩
  --       φ        ＝⟨ q ⁻¹ ⟩
  --       eval X y ∎

--    t : x ＝ y
--    t = τ (happly s)

--    r : transport (λ - → eval X - ＝ φ) t p ＝ q
--    r = totally-separated-types-are-sets fe
--         ((X → 𝟚) → 𝟚)
--         (Π-is-totally-separated fe (λ p → 𝟚-is-totally-separated))
--         (transport (λ - → eval X - ＝ φ) t p)
--         q

--    γ : (x , p) ＝ (y , q)
--    γ = to-Σ-＝ (t , r)

--  totally-separated₂-gives-totally-separated : funext 𝓤 𝓤₀
--                                             → {X : 𝓤 ̇ }
--                                             → is-totally-separated₂ X
--                                             → is-totally-separated X
--  totally-separated₂-gives-totally-separated fe {X} i {x} {y} e = ap pr₁ q
--   where
--    φ : (X → 𝟚) → 𝟚
--    φ = eval X x

--    h : is-prop (fiber (eval X) φ)
--    h = i φ

--    g : eval X y ＝ φ
--    g = dfunext fe (λ p → (e p)⁻¹)

--    q : x , refl ＝ y , g
--    q = h (x , refl) (y , g)

\end{code}

Now, if a type X is not (necessarily) separated, we can
consider the image of the map eval X, and this gives the totally
separated reflection, with the corestriction of eval X to its image as
its reflector.

\begin{code}

module separated-reflection
         (fe : FunExt)
         (pt : propositional-truncations-exist)
         (𝒮 : 𝓥 ̇ )
 where

 private
  fe' : Fun-Ext
  fe' {𝓤} {𝓥} = fe 𝓤 𝓥

 open PropositionalTruncation pt
 open import UF.ImageAndSurjection pt

\end{code}

We construct the reflection as the image of the evaluation map.

TODO: It is easy to show that 𝕋 X is separated₂, since the image inclusion is an
embedding.

\begin{code}

 𝕋 : 𝓤 ̇ → 𝓤 ⊔ 𝓥 ̇
 𝕋 X = image (eval 𝒮 X)

--  τ₂ : {X : 𝓤 ̇ } → is-separated₂ 𝒮 (𝕋 X)
--  τ₂ f = {!   !}

 quasi-τ : {X : 𝓤 ̇ } → is-quasi-separated 𝒮 (𝕋 X)
 quasi-τ {𝓤} {X} {φ , s} {γ , t} = g
  where
   f : (e : (q : 𝕋 X → 𝒮) → q (φ , s) ＝ q (γ , t)) (p : X → 𝒮) → φ p ＝ γ p
   f e p = e (λ (x' : 𝕋 X) → pr₁ x' p)

   g : (e : (q : 𝕋 X → 𝒮) → q (φ , s) ＝ q (γ , t)) → (φ , s) ＝ (γ , t)
   g e = to-subtype-＝ (λ _ → ∥∥-is-prop) (dfunext fe' (f e))

\end{code}

Then the reflector is the corestriction of the evaluation map. The
induction principle for surjections gives an induction principle for
the reflector.

\begin{code}

 η : {X : 𝓤 ̇ } → X → 𝕋 X
 η {𝓤} {X} = corestriction (eval 𝒮 X)

 η-is-surjection : {X : 𝓤 ̇ } → is-surjection η
 η-is-surjection {𝓤} {X} = corestrictions-are-surjections (eval 𝒮 X)

 η-induction :  {X : 𝓤 ̇ } (P : 𝕋 X → 𝓦 ̇ )
             → ((x' : 𝕋 X) → is-prop (P x'))
             → ((x : X) → P (η x))
             → (x' : 𝕋 X) → P x'
 η-induction = surjection-induction η η-is-surjection

\end{code}

\begin{uncode}

 separated-reflection : {X : 𝓤 ̇ } {A : 𝓦 ̇ }
                      → is-separated 𝒮 A
                      → (f : X → A)
                      → ∃! f⁻ ꞉ (𝕋 X → A) , f⁻ ∘ η ＝ f
 separated-reflection {𝓤} {𝓥} {X} {A} τ f = TODO  -- δ

  -- where
  --  A-is-set : is-set A
  --  A-is-set = totally-separated-types-are-sets fe' A τ

  --  ie : (γ : (A → 𝟚) → 𝟚) → is-prop (Σ a ꞉ A , eval A a ＝ γ)
  --  ie = totally-separated-gives-totally-separated₂ fe' τ

  --  h : (φ : (X → 𝟚) → 𝟚)
  --    → (∃ x ꞉ X , eval X x ＝ φ)
  --    → Σ a ꞉ A , eval A a ＝ (λ q → φ (q ∘ f))
  --  h φ = ∥∥-rec (ie γ) u
  --   where
  --    γ : (A → 𝟚) → 𝟚
  --    γ q = φ (q ∘ f)

  --    u : (Σ x ꞉ X , (λ p → p x) ＝ φ) → Σ a ꞉ A , eval A a ＝ γ
  --    u (x , r) = f x , dfunext fe' (λ q → happly r (q ∘ f))

  --  h' : (x' : 𝕋 X) → Σ a ꞉ A , eval A a ＝ (λ q → pr₁ x' (q ∘ f))
  --  h' (φ , s) = h φ s

  --  f⁻ : 𝕋 X → A
  --  f⁻ (φ , s) = pr₁ (h φ s)

  --  b : (x' : 𝕋 X) (q : A → 𝟚) → q (f⁻ x') ＝ pr₁ x' (q ∘ f)
  --  b (φ , s) = happly (pr₂ (h φ s))

  --  r : f⁻ ∘ η ＝ f
  --  r = dfunext fe' (λ x → τ (b (η x)))

  --  c : (σ : Σ f⁺ ꞉ (𝕋 X → A) , f⁺ ∘ η ＝ f) → (f⁻ , r) ＝ σ
  --  c (f⁺ , s) = to-Σ-＝ (t , v)
  --   where
  --    w : f⁻ ∘ η ∼ f⁺ ∘ η
  --    w = happly (f⁻ ∘ η  ＝⟨ r ⟩
  --                f       ＝⟨ s ⁻¹ ⟩
  --                f⁺ ∘ η ∎ )

  --    t : f⁻ ＝ f⁺
  --    t = dfunext fe' (η-induction _ (λ _ → A-is-set) w)

  --    u : f⁺ ∘ η ＝ f
  --    u = transport (λ - → - ∘ η ＝ f) t r

  --    v : u ＝ s
  --    v = Π-is-set fe' (λ _ → A-is-set) u s

  --  δ : ∃! f⁻ ꞉ (𝕋 X → A) , f⁻ ∘ η ＝ f
  --  δ = (f⁻ , r) , c

\end{uncode}

We package the above as follows for convenient use elsewhere
(including the module CompactTypes).

\begin{uncode}

 separated-reflection' : {X : 𝓤 ̇ } {A : 𝓦 ̇ }
                               → is-separated 𝒮 A
                               → is-equiv (λ (f⁻ : 𝕋 X → A) → f⁻ ∘ η)
 separated-reflection' τ =
  vv-equivs-are-equivs _ (separated-reflection τ)

 separated-reflection'' : {X : 𝓤 ̇ } {A : 𝓥 ̇ }
                                → is-separated 𝒮 A
                                → (𝕋 X → A) ≃ (X → A)
 separated-reflection'' τ = ((λ f⁻ → f⁻ ∘ η) , separated-reflection' τ)

\end{uncode}

In particular, because 𝟚 is totally separated, 𝕋 X and X have the same
boolean predicates (which we exploit in the module CompactTypes).

The notion of total separatedness (or 𝟚-separatedness) is analogous to
the T₀-separation axiom (which says that any two points with the same
open neighbourhoods are equal).

\begin{code}

is-sober : 𝓥 ̇  → 𝓦 ̇ → 𝓤 ⁺ ⊔ 𝓥 ⊔ 𝓦 ̇
is-sober {𝓥} {𝓦} {𝓤} 𝒮 A = is-separated 𝒮 A
                          × ((X : 𝓤 ̇ )
                             (e : A → X) → is-equiv (dual 𝒮 e) → is-equiv e)

\end{code}

TODO: example of 𝟚-separated type that fails to be 𝟚-sober, 𝟚-sober
reflection (or 𝟚-sobrification).

TODO: most of what we said doesn't depend on the type 𝟚, and total
separatedness can be generalized to S-separatedness for an arbitrary
type S, where 𝟚-separatedness is total separatedness. Then, for
example, Prop-separated is equivalent to is-set, all types in U are U
separated, Set-separatedness (where Set is the type of sets) should be
equivalent to is-1-groupoid, etc.

An interesting case is when S is (the total space of) a dominance,
generalizing the case S=Prop. Because the partial elements are defined
in terms of maps into S, the S-lifting of a type X should coincide
with the S-separated reflection of the lifting of X, and hence, in
this context, it makes sense to restrict our attention to S-separated
types.

Another useful thing is that in any type X we can define an apartness
relation x♯y by ∃ p : X→𝟚 , p x ‌≠p y, which is tight iff X is totally
separated, where tightness means ¬ (x ♯ y)→ x = y. Part of the following
should be moved to another module about apartness, but I keep it here
for the moment.

Added 26 January 2018.

We now show that a type is totally separated iff a particular
apartness relation _♯₂ is tight:

\begin{uncode}

module total-separatedness-via-apartness
        (pt : propositional-truncations-exist)
       where

 open PropositionalTruncation pt
 open import Apartness.Definition
 open Apartness pt

 _♯₂_ : {X : 𝓤 ̇ } → X → X → 𝓤 ̇
 x ♯₂ y = ∃ p ꞉ (type-of x → 𝟚), p x ≠ p y

 ♯₂-is-apartness : {X : 𝓤 ̇ } → is-apartness (_♯₂_ {𝓤} {X})
 ♯₂-is-apartness {𝓤} {X} = a , b , c , d
  where
   a : is-prop-valued _♯₂_
   a x y = ∥∥-is-prop

   b : is-irreflexive _♯₂_
   b x = ∥∥-rec 𝟘-is-prop g
    where
     g : ¬ (Σ p ꞉ (X → 𝟚) , p x ≠ p x)
     g (p , u) = u refl

   c : is-symmetric _♯₂_
   c x y = ∥∥-functor g
    where
     g : (Σ p ꞉ (X → 𝟚) , p x ≠ p y) → Σ p ꞉ (X → 𝟚) , p y ≠ p x
     g (p , u) = p , ≠-sym u

   d : is-cotransitive _♯₂_
   d x y z = ∥∥-functor g
    where
     g : (Σ p ꞉ (X → 𝟚) , p x ≠ p y) → (x ♯₂ z) + (y ♯₂ z)
     g (p , u) =
       h (discrete-types-are-cotransitive 𝟚-is-discrete {p x} {p y} {p z} u)
      where
       h : (p x ≠ p z) + (p z ≠ p y) → (x ♯₂ z) + (y ♯₂ z)
       h (inl u) = inl ∣ p , u ∣
       h (inr v) = inr ∣ p , ≠-sym v ∣

 is-totally-separated₃ : 𝓤 ̇ → 𝓤 ̇
 is-totally-separated₃ {𝓤} X = is-tight (_♯₂_ {𝓤} {X})

 totally-separated₃-gives-totally-separated : {X : 𝓤 ̇ }
                                            → is-totally-separated₃ X
                                            → is-totally-separated X
 totally-separated₃-gives-totally-separated {𝓤} {X} τ {x} {y} α = γ
  where
   h : ¬ (Σ p ꞉ (X → 𝟚) , p x ≠ p y)
   h (p , u) = u (α p)

   γ : x ＝ y
   γ = τ x y (∥∥-rec 𝟘-is-prop h)

 totally-separated-gives-totally-separated₃ : {X : 𝓤 ̇ }
                                            → is-totally-separated X
                                            → is-totally-separated₃ X
 totally-separated-gives-totally-separated₃ {𝓤} {X} τ x y na = τ α
  where
   h : ¬ (Σ p ꞉ (X → 𝟚) , p x ≠ p y)
   h (p , u) = na ∣ p , u ∣

   α : (p : X → 𝟚) → p x ＝ p y
   α p = 𝟚-is-¬¬-separated (p x) (p y) (λ u → h (p , u))

 ♯₂-is-tight = totally-separated-gives-totally-separated₃

 tight-relation-contained-in-♯₂-gives-total-separatedness
  : {X : 𝓤 ̇ }
  → (_♯_ : X → X → 𝓥 ̇ )
  → ((x y : X) → x ♯ y → x ♯₂ y)
  → is-tight _♯_
  → is-totally-separated X
 tight-relation-contained-in-♯₂-gives-total-separatedness _♯_ ϕ t =
  totally-separated₃-gives-totally-separated
   (finner-than-tight-is-tight _♯_ _♯₂_ ϕ t)

 tight-apartness-contained-in-♯₂-gives-total-separatedness
  : {X : 𝓤 ̇ }
  → ((_♯_ , _) : Tight-Apartness X 𝓥)
  → ((x y : X) → x ♯ y → x ♯₂ y)
  → is-totally-separated X
 tight-apartness-contained-in-♯₂-gives-total-separatedness (_♯_ , _ , t) ϕ
  = tight-relation-contained-in-♯₂-gives-total-separatedness _♯_ ϕ t

\end{uncode}
