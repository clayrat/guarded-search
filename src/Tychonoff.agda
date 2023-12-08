{-# OPTIONS --guarded #-}
module Tychonoff where

open import Prelude
open import Data.Empty
open import Data.Unit
open import Data.Bool
open import Data.Dec renaming (elim to elimᵈ)
open import Data.Sum

open import Later
open import ClIrr
open import Clocked.Stream
open import Clocked.Stream.Eta
open import Clocked.Stream.Quantifiers
open import Clocked.Conat
open import Clocked.Conat.Arith
open import Clocked.Conat.Stream

private variable
  ℓ : Level
  X : 𝒰 ℓ
  k : Cl

𝓟 : 𝒰 ℓ → 𝒰 (ℓsuc 0ℓ ⊔ ℓ)
𝓟 X = X → 𝒰

-- decidable predicate
d-predicate : 𝒰 ℓ → 𝒰 (ℓsuc 0ℓ ⊔ ℓ)
d-predicate {ℓ} X = Σ[ p ꞉  𝓟 X ] (Decidable p)

trivial-predicate : d-predicate X
trivial-predicate = (λ _ → ⊤) , (λ _ → yes tt)

searchable : 𝒰 ℓ → 𝒰 (ℓsuc 0ℓ ⊔ ℓ)
searchable X = Π[ (p , _) ꞉ d-predicate X ] (Σ[ x ꞉ X ] (Σ X p → p x))

searchable-types-are-inhabited : searchable X → X
searchable-types-are-inhabited S = S trivial-predicate .fst

Bool-is-searchable : searchable Bool
Bool-is-searchable (p , d) = γ (d true)
  where
  γ : Dec (p true) → Σ[ x₀ ꞉ Bool ] (Σ Bool p → p x₀)
  γ (yes prf) = true , λ _ → prf
  γ (no ctra) = false , λ where
                            (false , pf) → pf
                            (true  , pt) → absurd (ctra pt)

LPO : 𝒰
LPO = Π[ s ꞉ Stream Bool ] (Any (_＝ true) s) ⊎ (All (_＝ false) s)

LPO' : 𝒰₁
LPO' = Π[ (p , d) ꞉ d-predicate ℕ ] (Σ ℕ p) ⊎ (Π[ n ꞉ ℕ ] (¬ (p n)))

ℕ-searchable→LPO : searchable ℕ → LPO'
ℕ-searchable→LPO S (p , d) =
  elimᵈ (inl ∘ left) (inr ∘ right) (d x₀)
  where
  x₀ : ℕ
  x₀ = S (p , d) .fst
  left : p x₀ → Σ ℕ p
  left px₀ = x₀ , px₀
  right : ¬ (p x₀) → (x : ℕ) → ¬ p x
  right ¬px₀ x px = ¬px₀ (S (p , d) .snd (x , px))

LPO-implies-ℕ-searchable : LPO' → searchable ℕ
LPO-implies-ℕ-searchable L (p , d) = [ left , right ]ᵤ (L (p , d))
  where
  left : Σ ℕ p → Σ[ x ꞉ ℕ ] (Σ ℕ p → p x)
  left (x₀ , px₀) = x₀ , λ _ → px₀
  right : (∀ x → ¬ p x) → Σ[ x ꞉ ℕ ] (Σ ℕ p → p x)
  right f = 0 , (λ where (x , px) → absurd (f x px))

_≡⟦_⟧_ : {X : 𝒰 ℓ} → Stream X → ℕ → Stream X → 𝒰 ℓ
α ≡⟦ m ⟧ β = All≤ (λ ab → ab .fst ＝ ab .snd) m (zipˢ α β)

is-u-continuous-SB : 𝓟 (Stream Bool) → 𝒰
is-u-continuous-SB p = Σ[ m ꞉ ℕ ] ((α β : Stream Bool) → α ≡⟦ m ⟧ β → p α → p β)

record is-clofun {X : 𝒰 ℓ} (c : X → X → ℕ∞) : 𝒰 ℓ where
  field
    equal→inf-close : (x     : X) → c x x ＝ inftyᶜ
    inf-close→equal : (x y   : X) → c x y ＝ inftyᶜ → x ＝ y
    symmetricity    : (x y   : X) → c x y ＝ c y x
    ultrametric     : (x y z : X) → minᶜ (c x y) (c y z) ≤ᶜ c x z

-- discrete closeness

discrete-c' : (x y : X) → Dec (x ＝ y) → ℕ∞
discrete-c' x y (yes e) = inftyᶜ
discrete-c' x y (no ne) = zeᶜ

discrete-clofun : is-discrete X → X → X → ℕ∞
discrete-clofun d x y = discrete-c' x y (is-discrete-β d x y)

discrete-c'-eic : (x : X)
                → (dxx : Dec (x ＝ x))
                → discrete-c' x x dxx ＝ inftyᶜ
discrete-c'-eic x (yes e) = refl
discrete-c'-eic x (no ne) = absurd (ne refl)

discrete-c'-ice : (x y : X)
                → (dxy : Dec (x ＝ y))
                → discrete-c' x y dxy ＝ inftyᶜ → x ＝ y
discrete-c'-ice x y (yes e) ei = e
discrete-c'-ice x y (no ne) ei = absurd (inftyᶜ≠zeᶜ (sym ei))

discrete-c'-sym : (x y : X)
                → (dxy : Dec (x ＝ y))
                → (dyx : Dec (y ＝ x))
                → discrete-c' x y dxy ＝ discrete-c' y x dyx
discrete-c'-sym x y (yes exy) (yes eyx) = refl
discrete-c'-sym x y (yes exy) (no neyx) = absurd (neyx (sym exy))
discrete-c'-sym x y (no nexy) (yes eyx) = absurd (nexy (sym eyx))
discrete-c'-sym x y (no nexy) (no neyx) = refl

discrete-c'-ult : (x y z : X)
                → (dxy : Dec (x ＝ y))
                → (dyz : Dec (y ＝ z))
                → (dxz : Dec (x ＝ z))
                → minᶜ (discrete-c' x y dxy) (discrete-c' y z dyz) ≤ᶜ discrete-c' x z dxz
discrete-c'-ult x y z      dxy       dyz  (yes exz) = ≤ᶜ-infty (minᶜ (discrete-c' x y dxy) (discrete-c' y z dyz))
discrete-c'-ult x y z (yes exy) (yes eyz) (no nexz) = absurd (nexz (exy ∙ eyz))
discrete-c'-ult x y z (yes exy) (no neyz) (no nexz) = z≤ᶜn
discrete-c'-ult x y z (no nexy)      dyz  (no nexz) = z≤ᶜn

discrete-is-clofun : (ds : is-discrete X)
                   → is-clofun (discrete-clofun ds)
discrete-is-clofun ds .is-clofun.equal→inf-close x     =
  discrete-c'-eic x (is-discrete-β ds x x)
discrete-is-clofun ds .is-clofun.inf-close→equal x y   =
  discrete-c'-ice x y (is-discrete-β ds x y)
discrete-is-clofun ds .is-clofun.symmetricity    x y   =
  discrete-c'-sym x y (is-discrete-β ds x y) (is-discrete-β ds y x)
discrete-is-clofun ds .is-clofun.ultrametric     x y z =
  discrete-c'-ult x y z (is-discrete-β ds x y) (is-discrete-β ds y z) (is-discrete-β ds x z)

-- discrete stream closeness

discrete-seq-clofun : (ds : is-discrete X)
                    → is-clofun (closenessˢ ds)
discrete-seq-clofun ds .is-clofun.equal→inf-close x     = closenessˢ-refl ds x
discrete-seq-clofun ds .is-clofun.inf-close→equal x y   = close∞→equalˢ ds x y
discrete-seq-clofun ds .is-clofun.symmetricity    x y   = closenessˢ-comm ds x y
discrete-seq-clofun ds .is-clofun.ultrametric     x y z = closenessˢ-ultra ds x y z

-- closeness lemmas
{-
closeness→equality : (ds : is-discrete X)
                   → (α β : Stream X) → (n : ℕ)
                   → (fromℕᶜ (suc n)) ≤ᶜ closenessˢ ds α β
                   → α ≡⟦ n ⟧ β
closeness→equality ds = fix (go ds)
  where
  go : ∀ {X : 𝒰 ℓ}
     → (ds : is-discrete X)
     → ▹ k ((α β : Stream X) → (n : ℕ) → fromℕᶜ (suc n) ≤ᶜ closenessˢ ds α β → α ≡⟦ n ⟧ β)
     →      (α β : Stream X) → (n : ℕ) → fromℕᶜ (suc n) ≤ᶜ closenessˢ ds α β → α ≡⟦ n ⟧ β
  go ds ih▹ (cons a as▹) (cons b bs▹)  zero   l with (is-discrete-β ds a b)
  ... | yes e = All≤-nil e
  ... | no ne = absurd (¬s≤ᶜz (next coze) l)
  go ds ih▹ (cons a as▹) (cons b bs▹) (suc n) l with (is-discrete-β ds a b)
  go ds ih▹ (cons a as▹) (cons b bs▹) (suc n) l | yes e = ? {-with l
  go ds ih▹ (cons a as▹) (cons b bs▹) (suc n) l | yes e | s≤ᶜs l▹ =
    All≤-cons e λ α → subst (All≤ˢ (λ ab → ab .fst ＝ ab .snd) n)
                            (λ i → pfix (zipWithˢ-body (_,_)) (~ i) α (as▹ α) (bs▹ α)) $
                      ih▹ α (as▹ α) (bs▹ α) n $
                      transport (λ i → incᶜ (fromℕᶜ n) ≤ᶜ pfix (closenessˢ-body ds) i α (as▹ α) (bs▹ α)) $
                      l▹ α -}
  go ds ih▹ (cons a as▹) (cons b bs▹) (suc n) l | no ne = ? --absurd (¬s≤ᶜz (next (incᶜ (fromℕᶜ n))) l)

equality→closeness : (ds : is-discrete X)
                   → (α β : Stream X) → (n : ℕ)
                   → α ≡⟦ n ⟧ β
                   → (fromℕᶜ (suc n)) ≤ᶜ closenessˢ ds α β
equality→closeness ds = fix (go ds)
  where
  go : ∀ {X : 𝒰 ℓ}
     → (ds : is-discrete X)
     → ▹ ((α β : Stream X) → (n : ℕ) → α ≡⟦ n ⟧ β → fromℕᶜ (suc n) ≤ᶜ closenessˢ ds α β)
     →    (α β : Stream X) → (n : ℕ) → α ≡⟦ n ⟧ β → fromℕᶜ (suc n) ≤ᶜ closenessˢ ds α β
  go ds ih▹ (cons a as▹) (cons b bs▹) .zero    (All≤-nil p)         with (is-discrete-β ds a b)
  ... | yes e = s≤ᶜs (λ _ → z≤ᶜn)
  ... | no ne = absurd (ne p)
  go ds ih▹ (cons a as▹) (cons b bs▹) .(suc n) (All≤-cons {n} p a▹) with (is-discrete-β ds a b)
  ... | yes e = s≤ᶜs λ α → transport (λ i → incᶜ (fromℕᶜ n) ≤ᶜ pfix (closenessˢ-body ds) (~ i) α (as▹ α) (bs▹ α)) $
                           ih▹ α (as▹ α) (bs▹ α) n $
                           subst (All≤ˢ (λ ab → ab .fst ＝ ab .snd) n)
                                 (λ i → pfix (zipWithˢ-body (_,_)) i α (as▹ α) (bs▹ α)) $
                           a▹ α
  ... | no ne = absurd (ne p)
-}
-- no need for lemmas above
build-up : (ds : is-discrete X)
         → (xs ys : Stream X) → (δ : ℕ)
         → (fromℕᶜ δ) ≤ᶜ closenessˢ ds xs ys
         → (x : X)
         → (fromℕᶜ (suc δ)) ≤ᶜ closenessˢ ds (consˢ x xs) (consˢ x ys)
build-up ds xs ys δ l x with is-discrete-β ds x x
... | yes e = transport (λ i → ∀ k → cosu (λ α → fromℕᵏ δ) ≤ᵏ cosu (λ α → pfix (closenessᵏˢ-body ds) (~ i) α (xs k) (ys k))) (s≤ᶜs l)
... | no ne = absurd (ne refl)

-- uniform modulus
_is-u-mod-of_on_ : ℕ → 𝓟 X → (X → X → ℕ∞) → 𝒰 (level-of-type X)
_is-u-mod-of_on_ {X} δ p c = Π[ (x , y) ꞉ (X × X) ] ((fromℕᶜ δ) ≤ᶜ c x y → p x → p y)

u-continuous : (X → X → ℕ∞) → 𝓟 X → 𝒰 (level-of-type X)
u-continuous c p = Σ[ δ ꞉ ℕ ] (δ is-u-mod-of p on c)

-- uniformly continuous decidable predicate
uc-d-predicate : (X → X → ℕ∞) → 𝒰 (ℓsuc 0ℓ ⊔ level-of-type X)
uc-d-predicate {X} c = Σ[ (p , d) ꞉ d-predicate X ] u-continuous c p

trivial-uc-predicate : (c : X → X → ℕ∞) → uc-d-predicate c
trivial-uc-predicate c = trivial-predicate , 0 , λ _ _ _ → tt

c-searchable : (X → X → ℕ∞) → 𝒰 (ℓsuc 0ℓ ⊔ level-of-type X)
c-searchable {X} c = Π[ ((p , _) , _) ꞉ uc-d-predicate c ] (Σ[ x₀ ꞉ X ] (Σ X p → p x₀))

c-searchable-types-are-inhabited : (c : X → X → ℕ∞) → c-searchable c → X
c-searchable-types-are-inhabited c S = S (trivial-uc-predicate c) .fst

searchable→c-searchable : (c : X → X → ℕ∞) → searchable X → c-searchable c
searchable→c-searchable c S (pd , _ , _) = S pd

Bool-is-c-searchable : c-searchable (discrete-clofun bool-is-discrete)
Bool-is-c-searchable = searchable→c-searchable (discrete-clofun bool-is-discrete) Bool-is-searchable

all-discrete-predicates-are-continuous : (ds : is-discrete X)
                                       → d-predicate X
                                       → uc-d-predicate (discrete-clofun ds)
all-discrete-predicates-are-continuous {X} ds (p , d) =
  (p , d) , 1 , (λ where (x , y) → γ x y (is-discrete-β ds x y))
  where
  γ : (x y : X) → (q : Dec (x ＝ y)) → suᶜ zeᶜ ≤ᶜ discrete-c' x y q → p x → p y
  γ x y (yes e) l px = subst p e px
  γ x y (no ne) l px = absurd (¬s≤ᶜz zeᶜ l)

c-searchable-discrete→searchable : (ds : is-discrete X)
                                 → c-searchable (discrete-clofun ds)
                                 → searchable X
c-searchable-discrete→searchable ds S pd = S (all-discrete-predicates-are-continuous ds pd)

0-mod-always-satisfied : (c : X → X → ℕ∞)
                       → ((p , d) : d-predicate X)
                       → 0 is-u-mod-of p on c
                       → Σ X p → (x : X) → p x
0-mod-always-satisfied c (p , d) φ (x₀ , px₀) x = φ (x₀ , x) z≤ᶜn px₀

tail-predicate : (ds : is-discrete X)
               → ((p , d) : d-predicate (Stream X))
               → X → d-predicate (Stream X)
tail-predicate ds (p , d) x = (λ s → p (consˢ x s)) , (λ s → d (consˢ x s))

tail-predicate-reduce-mod : (ds : is-discrete X)
                          → ((p , d) : d-predicate (Stream X))
                          → (x : X) → (δ : ℕ)
                          → (suc δ) is-u-mod-of p on (closenessˢ ds)
                          →      δ  is-u-mod-of tail-predicate ds (p , d) x .fst
                                                  on (closenessˢ ds)
tail-predicate-reduce-mod ds (p , d) x δ φ (xs , ys) l =
  φ (consˢ x xs , consˢ x ys) (build-up ds xs ys δ l x)

→c-searchable' : (ds : is-discrete X) → searchable X
               → ((p , d) : d-predicate (Stream X))
               → (δ : ℕ) → δ is-u-mod-of p on (closenessˢ ds)
               → Σ[ s₀ ꞉ Stream X ] (Σ (Stream X) p → p s₀)
→c-searchable' {X} ds S (p , d)  zero   φ = α , γ
  where
  α : Stream X
  α = repeatˢ (searchable-types-are-inhabited S)
  γ : Σ (Stream X) p → p α
  γ sp = 0-mod-always-satisfied (closenessˢ ds) (p , d) φ sp α
→c-searchable' {X} ds S (p , d) (suc δ) φ = α , γ
  where
  𝓟ₜ : X → 𝓟 (Stream X)
  𝓟ₜ x = tail-predicate ds (p , d) x .fst
  IH-tail : (x : X) → Σ[ s₀ ꞉ Stream X ] (Σ (Stream X) (𝓟ₜ x) → 𝓟ₜ x s₀)
  IH-tail x = →c-searchable' ds S (tail-predicate ds (p , d) x) δ (tail-predicate-reduce-mod ds (p , d) x δ φ)
  𝓔xs : X → Stream X
  𝓔xs x = IH-tail x .fst
  γₜ : (x : X) → Σ (Stream X) (𝓟ₜ x) → 𝓟ₜ x (𝓔xs x)
  γₜ x = IH-tail x .snd
  head-predicate : d-predicate X
  head-predicate = (λ x → p (consˢ x (𝓔xs x))) , λ x → d (consˢ x (𝓔xs x))
  𝓟ₕ : 𝓟 X
  𝓟ₕ = head-predicate .fst
  S-head : Σ[ x ꞉ X ] (Σ X 𝓟ₕ → 𝓟ₕ x)
  S-head = S head-predicate
  x₁ : X
  x₁ = S-head .fst
  γₕ : Σ X 𝓟ₕ → 𝓟ₕ x₁
  γₕ = S-head .snd
  α : Stream X
  α = consˢ x₁ (𝓔xs x₁)
  γ : Σ (Stream X) p → p α
  γ (α₀ , pα₀) = step₆
    where
    x₀ : X
    x₀ = headˢ α₀
    xs₀ : Stream X
    xs₀ = tailˢ α₀
    step₁ : p (consˢ x₀ xs₀)
    step₁ = subst p (uncons-eqˢ α₀) pα₀
    step₂ : 𝓟ₜ x₀ xs₀
    step₂ = step₁
    step₃ : (𝓟ₜ x₀) (𝓔xs x₀)
    step₃ = γₜ x₀ (xs₀ , step₂)
    step₄ : 𝓟ₕ x₀
    step₄ = step₃
    step₅ : 𝓟ₕ x₁
    step₅ = γₕ (x₀ , step₄)
    step₆ : p (consˢ x₁ (𝓔xs x₁))
    step₆ = step₅
