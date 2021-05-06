{-
  Die Definition in dieser Datei sollen die Vorlesungsinhalte nachbilden.
  Wenn Agda auf eine Datei im gleichen Verzeichnis angewandt wird,
  kann man die Definition hier mit 'open import Vorlesung' importieren.
-}
module Vorlesung where

{-
  Funktionstypen sind in Agda direkt eingebaut, wir müssen die entsprechenden Regeln nicht angeben.
  Die Urteile "A : Set" kann man lesen als "A Typ".
  Ausdrücke "{A : Set}" bedeuten, dass Agda die so angegebenen Parameter bei Aufrufen berechnen soll.
  Im folgende erlaubt uns das, "f ∘ g" zu schreiben, ohne die Typen A,B,C anzugeben.
  Funktionsterme "x↦f(x)" werden in Agda "λ x → f(x)" geschrieben und Anwendungen "f x" statt "f(x)".
  Die Leerzeichen sind dabei wichtig.
-}
_∘_ : {A B C : Set} → (B → C) → (A → B) → (A → C)
g ∘ f = λ x → g(f(x))

{-
  Wir geben eine Definition an, die es uns erlaubt auch "Π B" für einen abhängigen Typ "B" zu schreiben,
  obwohl es bereits mit "(x : A) → B x" den Typ der abhängigen Funktionen gibt.
  Abhängige Typen "x:A ⊢ B(x)" schreibt man "B : A → Set".
-}

Π : (A : Set) (B : A → Set) → Set
Π A B = (x : A) → B x

{-
  das folgende erlaubt die Schreibweise 'Σ[ x ∈ A ] B' 
-}
infix 2 Π-syntax

Π-syntax : (A : Set) (B : A → Set) → Set
Π-syntax = Π

syntax Π-syntax A (λ x → B) = Π[ x ∈ A ] B

{-
  Natürliche Zahlen...
-}
data ℕ : Set where
  0ℕ : ℕ
  succℕ : ℕ → ℕ
{-
  Die Induktionsregel dafür gibt es bei Agda automatisch in der Gestalt von Pattern-Matching.
  Das können wir nutzen, um den Induktionsterm aus der Vorlesung zu definieren.
-}

ind= : {P : ℕ → Set} → (p₀ : P 0ℕ) → (pₛ : (n : ℕ) → P n → P (succℕ n)) → Π[ n ∈ ℕ ] (P n)
ind= p₀ pₛ 0ℕ = p₀
ind= p₀ pₛ (succℕ n) = pₛ  n (ind= p₀ pₛ n)

d : ℕ → ℕ
d 0ℕ = 0ℕ
d (succℕ n) = succℕ (succℕ (d n))

_+_ : ℕ → ℕ → ℕ
0ℕ + k = k
succℕ n + k = succℕ (n + k)

_·_ : ℕ → ℕ → ℕ
0ℕ · k = 0ℕ
succℕ n · k = (n · k) + k

{-
  Ein paar Induktive Typen
  (mit noch nicht so tollen Namen)
-}

{-
  1.3.3

  ∅ \0
-}

data ∅ : Set where

{-
  1.3.1
  ∗ \ast
-}

data Eins : Set where
  ∗ : Eins

{-
  1.3.4
-}

data Zwei : Set where
  0₂ : Zwei
  1₂ : Zwei

{-
  ⊔ \sqcup

  Koprodukt, 1.3.5
-}

data _⊔_ (A B : Set) : Set where
  ι₁ : A → A ⊔ B
  ι₂ : B → A ⊔ B

{-
  1.4.1
  Als Symbol für die Gleichheit verwenden wir:
  ≡           (\equiv \==)
  (damit sind die Symbole gegenüber der Vorlesung vertauscht)
  Gleichheit.
  Die beiden Parameter "x,y : A" können wir in Agda realisieren, indem wir einen
  induktiven Typ vom Typ "A → A → Set" definieren.
  mit der 'infixl' zeile legen wir fest, dass _≡_ eine niedrigere Priorität als default (=20) hat
-}
infixl 10 _≡_

data _≡_ {A : Set} : A → A → Set where
  refl : (x : A) → x ≡ x

{-
  Beispiel 1.4.2
-}

bsp1-4-2 : (x : Eins) → x ≡ ∗
bsp1-4-2 ∗ = refl ∗

{-
  1.4.3
  ⁻¹ \^-\^1
  mit der 'infixl' zeile legen wir fest, dass ⁻¹ ein höhere Priorität als default (=20) hat
-}
infixl 21 _⁻¹
_⁻¹ : {A : Set} {x y : A} → (x ≡ y) → (y ≡ x)
(refl x) ⁻¹ = refl x

{-
  ∙ \.
-}

_∙_ : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
(refl x) ∙ p = p

{-
  Beispiel 1.4.4
-}

bsp1-4-4 : (x y : Eins) → x ≡ y
bsp1-4-4 x y = bsp1-4-2 x ∙ (bsp1-4-2 y) ⁻¹

{-
  1.4.6, 1.4.7, 1.4.8
  Mit 'module _ {A : Set} where' öffnen wir einen durch Einrückung abgegrenzten Bereich,
  in dem alle Definitionen den Parameter '{A : Set}' ohne diesen jedesmal erwähnen zu müssen.
-}

module _ {A : Set} where
  reflLNeutral : {x y : A}
                 → (p : x ≡ y)
                 → (refl x) ∙ p ≡ p
  reflLNeutral (refl x) = refl (refl x)

  reflRNeutral : {x y : A}
                 → (p : x ≡ y)
                 → p ∙ (refl y) ≡ p
  reflRNeutral (refl x) = refl (refl x)

  ⁻¹RInv : {x y : A}
           → (p : x ≡ y)
           → p ∙ p ⁻¹ ≡ (refl x)
  ⁻¹RInv (refl x) = refl (refl x)

  ⁻¹LInv : {x y : A}
           → (p : x ≡ y)
           → p ⁻¹ ∙ p ≡ (refl y)
  ⁻¹LInv (refl x) = refl (refl x)

  ∙Assoziativ : {x y z w : A}
                → (p : x ≡ y) → (q : y ≡ z) → (r : z ≡ w)
                → (p ∙ q) ∙ r ≡ p ∙ (q ∙ r)
  ∙Assoziativ (refl x) q r = refl (q ∙ r)

{-
  1.4.11
-}

ap : {A B : Set} {x y : A}
     → (f : A → B)
     → (p : x ≡ y)
     → f x ≡ f y
ap f (refl x) = refl (f x)

{-
  1.4.10
-}

module macLane {A : Set} {x y z w u : A}
               (p : x ≡ y) (q : y ≡ z) (r : z ≡ w) (s : w ≡ u) where

       α₁ : ((p ∙ q) ∙ r) ∙ s ≡ (p ∙ (q ∙ r)) ∙ s
       α₁ = ap (λ t → t ∙ s) (∙Assoziativ p q r)

       α₂ : (p ∙ (q ∙ r)) ∙ s ≡ p ∙ ((q ∙ r) ∙ s)
       α₂ = ∙Assoziativ p (q ∙ r) s

       α₃ : p ∙ ((q ∙ r) ∙ s) ≡ p ∙ (q ∙ (r ∙ s))
       α₃ = ap (λ t → p ∙ t) (∙Assoziativ q r s)

       α₄ : ((p ∙ q) ∙ r) ∙ s ≡ (p ∙ q) ∙ (r ∙ s)
       α₄ = ∙Assoziativ (p ∙ q) r s

       α₅ : (p ∙ q) ∙ (r ∙ s) ≡ p ∙ (q ∙ (r ∙ s))
       α₅ = ∙Assoziativ p q (r ∙ s)

open macLane

bem1-4-10 : {A : Set} {x y z w u : A}
            (p : x ≡ y) (q : y ≡ z) (r : z ≡ w) (s : w ≡ u)
            → ((α₁ p q r s) ∙ (α₂ p q r s)) ∙ (α₃ p q r s) ≡ (α₄ p q r s) ∙ (α₅ p q r s)
bem1-4-10 (refl x) (refl x) (refl x) (refl x) = refl (refl (refl x))


{-
  1.5.1, 1.5.2
  Σ \Sigma
  'open Σ' lässt und die projektionen verwenden
  π₁ \pi\_1
-}

record Σ (A : Set) (B : A → Set) : Set where
  constructor _,_
  field
    π₁ : A
    π₂ : B π₁
open Σ
{-
  das folgende erlaubt die Schreibweise 'Σ[ x ∈ A ] B' 
-}
infix 2 Σ-syntax

Σ-syntax : (A : Set) (B : A → Set) → Set
Σ-syntax = Σ

syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B

{-
  1.5.3
  × \times
-}

_×_ : (A B : Set) → Set
A × B = Σ[ x ∈ A ] B

{-
  1.5.5
-}

curry : {A B C : Set}
        → ((A × B) → C) → (A → (B → C))
curry f = λ a b → f (a , b)

uncurry : {A B C : Set}
          → (A → (B → C)) → ((A × B) → C)
uncurry f = λ x → f (π₁ x) (π₂ x)

{-
  1.5.7
-}

_teilt_ : (a b : ℕ) → Set
a teilt b = Σ[ d ∈ ℕ ]  d · a ≡ b

{-
  1.5.8
-}

×Unique : {A B : Set} → (x : A × B) → x ≡ (π₁ x , π₂ x)
×Unique (x , y) = refl (x , y)

module _  {A B : Set} {a a' : A} {b b' : B} where
  pair= : ((a ≡ a') × (b ≡ b')) → (a , b) ≡ (a' , b')
  pair= ((refl a) , (refl b)) = refl (a , b)

  pair=⁻¹ : (a , b) ≡ (a' , b') → ((a ≡ a') × (b ≡ b'))
  pair=⁻¹ (refl (a , b)) = (refl a , refl b)

pair=⁻¹' : {A B : Set} {x y : A × B}
           → (p : x ≡ y) → ((π₁ x ≡ π₁ y) × (π₂ x ≡ π₂ y))
pair=⁻¹' p = ap π₁ p , ap π₂ p

