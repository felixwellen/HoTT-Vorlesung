{-# OPTIONS --without-K #-}
{-
  Hier kann man ganz unverfänglich Agda im Browser ausprobieren:

  https://agdapad.quasicoherent.io/

  (was aber evtl manchmal abgeschaltet ist)
  Mehr dazu, wie man an Agda rankommt, gibt es in der README.md
-}

{-
  Die Definition in dieser Datei sollen die Vorlesungsinhalte nachbilden.
  Wenn Agda auf eine Datei im gleichen Verzeichnis angewandt wird,
  kann man die Definition hier mit 'open import Vorlesung' importieren.
-}
module VorlesungMitUniversen where
{-
  Normalerweise gibt es in Agda eine Hierarchie von Universen die mit 'Set i' bezeichnet werden.
  Für i gibt es den Typ Level.
  Mit dem folgenden sagen wir Agda, dass es eine Hierarchie von Universen 'U i' geben soll.
-}

open import Agda.Primitive public
  using    ( Level )
  renaming ( lzero to ℓ-zero
           ; lsuc  to ℓ-suc
           ; _⊔_   to ℓ-max )

𝒰 : (i : Level) → Set(ℓ-suc i)
𝒰 i = Set i

𝒰₀ : 𝒰 (ℓ-suc ℓ-zero)
𝒰₀ = 𝒰 ℓ-zero

𝒰₁ : 𝒰 (ℓ-suc (ℓ-suc ℓ-zero))
𝒰₁ = 𝒰 (ℓ-suc ℓ-zero)

{-
  Es ist gängige Praxis, Universenlevel in Agda mit ℓ (\ell) zu bezeichnen.
  Wir werden dafür mit dem folgenden so etwas wie 'Hier seien stets ℓ, ℓ′ und ℓ″ Universenlevel':
-}

private
  variable
    ℓ ℓ′ ℓ″ : Level

{-
  Die Universenlevel können wir nun frei verwenden und Agda wird sie
  bei Bedarf in unsere Definitionen mit aufnehmen.
-}


{-
  Funktionstypen sind in Agda direkt eingebaut, wir müssen die entsprechenden Regeln nicht angeben.
  Die Urteile "A : Set" kann man lesen als "A Typ".
  Ausdrücke "{A : Set}" bedeuten, dass Agda die so angegebenen Parameter bei Aufrufen berechnen soll.
  Im folgende erlaubt uns das, "f ∘ g" zu schreiben, ohne die Typen A,B,C anzugeben.
  Funktionsterme "x↦f(x)" werden in Agda "λ x → f(x)" geschrieben und Anwendungen "f x" statt "f(x)".
  Die Leerzeichen sind dabei wichtig.
-}
_∘_ : {A : 𝒰 ℓ} {B : 𝒰 ℓ′} {C : 𝒰 ℓ″} → (B → C) → (A → B) → (A → C)
g ∘ f = λ x → g(f(x))

infixr 20 _∘_

{-
  Wir geben eine Definition an, die es uns erlaubt auch "Π B" für einen abhängigen Typ "B" zu schreiben,
  obwohl es bereits mit "(x : A) → B x" den Typ der abhängigen Funktionen gibt.
  Abhängige Typen "x:A ⊢ B(x)" schreibt man "B : A → U".
  Wir erlauben hier, dass A und B(x) in verschiedenen Universen liegen.
  Das Ergebnis liegt dann im größeren der beiden Universen 'U ℓ' und 'U'
-}

∏ : (A : 𝒰 ℓ) (B : A → 𝒰 ℓ′) → 𝒰 (ℓ-max ℓ ℓ′)
∏ A B = (x : A) → B x

{-
  das folgende erlaubt die Schreibweise '∏[ x ∈ A ] B'
-}
infix 2 ∏-syntax

∏-syntax : (A : 𝒰 ℓ) (B : A → 𝒰 ℓ′) → 𝒰 (ℓ-max ℓ ℓ′)
∏-syntax = ∏

syntax ∏-syntax A (λ x → B) = ∏[ x ∈ A ] B

{-
  Natürliche Zahlen...
-}
data ℕ : 𝒰₀ where
  0ℕ : ℕ
  succℕ : ℕ → ℕ
{-
  Die Induktionsregel dafür gibt es bei Agda automatisch in der Gestalt von Pattern-Matching.
  Das können wir nutzen, um den Induktionsterm aus der Vorlesung zu definieren.
-}

ind= : {P : ℕ → 𝒰₀} → (p₀ : P 0ℕ) → (pₛ : (n : ℕ) → P n → P (succℕ n)) → ∏[ n ∈ ℕ ] (P n)
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
-}

{-
  1.3.3

  ∅ \0
-}

data ∅ : 𝒰₀ where

{-
  1.3.1
  ∗ \ast
-}

data 𝟙 : 𝒰₀ where
  ∗ : 𝟙

{-
  1.3.4
-}

data 𝟚 : 𝒰₀ where
  0₂ : 𝟚
  1₂ : 𝟚

{-
  ∐ \coprod

  Koprodukt, 1.3.5
-}

data _∐_ (A B : 𝒰₀) : 𝒰₀ where
  ι₁ : A → A ∐ B
  ι₂ : B → A ∐ B

{-
  1.4.1
  Als Symbol für die Gleichheit verwenden wir:
  ≡           (\equiv \==)
  Damit sind die Symbole '≡' und '=' gegenüber der Vorlesung vertauscht.

  Die beiden Parameter "x,y : A" können wir in Agda realisieren, indem wir einen
  induktiven Typ vom Typ "A → A → U" definieren.
  Mit der 'infixl' zeile legen wir fest, dass _≡_ eine niedrigere Priorität als
  default (=20) hat. Damit lässt sich später etwa '(p ∙ q) ⁻¹ ≡ q ⁻¹ ∙ p ⁻¹' schreiben
  statt '((p ∙ q) ⁻¹) ≡ ((q ⁻¹) ∙ (p ⁻¹))' - vorausgesetzt für alle anderen operatoren
  werden auch sinnvolle Prioritäten gesetzt.
-}
infixl 4 _≡_

data _≡_ {A : 𝒰 ℓ} : A → A → 𝒰 ℓ where
  refl : (x : A) → x ≡ x



{-
  Beispiel 1.4.2
-}

bsp1-4-2 : (x : 𝟙) → x ≡ ∗
bsp1-4-2 ∗ = refl ∗

{-
  1.4.3
  ⁻¹ \^-\^1
  mit der 'infixl' zeile legen wir fest, dass ⁻¹ links assoziativ ist und eine höhere Priorität als default (=20) hat
-}
infixl 21 _⁻¹
_⁻¹ : {A : 𝒰₀} {x y : A} → (x ≡ y) → (y ≡ x)
(refl x) ⁻¹ = refl x

{-
  ∙ \.
-}

_∙_ : {A : 𝒰₀} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
(refl x) ∙ p = p

infixr 20 _∙_

{-
  Das folgende erlaubt es uns, Gleichungen in üblichem Stil
  aufzubauen.
-}
infixr 4 _≡⟨_⟩_
infixr 5 _≡∎

_≡⟨_⟩_ : {A : 𝒰₀} {y z : A} (x : A) (p : x ≡ y) (q : y ≡ z) → x ≡ z
x ≡⟨ p ⟩ q = p ∙ q

_≡∎ : {A : 𝒰₀} (x : A) → x ≡ x
x ≡∎ = refl x

{-
  Beispiel 1.4.4
-}

bsp1-4-4 : (x y : 𝟙) → x ≡ y
bsp1-4-4 x y = bsp1-4-2 x ∙ (bsp1-4-2 y) ⁻¹

{-
  1.4.6, 1.4.7, 1.4.8
  Mit 'module _ {A : U} where' öffnen wir einen durch Einrückung abgegrenzten Bereich,
  in dem alle Definitionen den Parameter '{A : U}' ohne diesen jedesmal erwähnen zu müssen.
-}

module _ {A : 𝒰₀} where
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

ap : {A B : 𝒰₀} {x y : A}
     → (f : A → B)
     → (p : x ≡ y)
     → f x ≡ f y
ap f (refl x) = refl (f x)

{-
  1.4.10
-}

module macLane {A : 𝒰₀} {x y z w u : A}
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

bem1-4-10 : {A : 𝒰₀} {x y z w u : A}
            (p : x ≡ y) (q : y ≡ z) (r : z ≡ w) (s : w ≡ u)
            → ((α₁ p q r s) ∙ (α₂ p q r s)) ∙ (α₃ p q r s) ≡ (α₄ p q r s) ∙ (α₅ p q r s)
bem1-4-10 (refl x) (refl x) (refl x) (refl x) = refl (refl (refl x))


{-
  1.5.1, 1.5.2
  ∑ \sum
  'open ∑' lässt ∑ und die Projektionen verwenden
  π₁ \pi\_1
-}

record ∑ (A : 𝒰 ℓ) (B : A → 𝒰 ℓ′) : 𝒰 (ℓ-max ℓ ℓ′) where
  constructor _,_
  field
    π₁ : A
    π₂ : B π₁
open ∑
{-
  Das Folgende erlaubt die Schreibweise 'Σ[ x ∈ A ] B'
-}
infix 2 ∑-syntax

∑-syntax : (A : 𝒰 ℓ) (B : A → 𝒰 ℓ′) → 𝒰 (ℓ-max ℓ ℓ′)
∑-syntax = ∑

syntax ∑-syntax A (λ x → B) = ∑[ x ∈ A ] B

{-
  1.4.13
  Transport (in B entlang von p)
-}

tr : {A : 𝒰 ℓ} (B : A → 𝒰 ℓ′) {x y : A} (p : x ≡ y) → B(x) → B(y)
tr B (refl _) = λ z → z

-- Lemma 1.4.14
tr-x≡a : {A : 𝒰₀} {a : A}
  → {x x' : A} (p : x ≡ x')
  → (λ { q → p ⁻¹ ∙ q }) ≡ tr (λ x → x ≡ a) (p)
tr-x≡a (refl _) = refl λ z → z

-- Lemma 1.4.15
tr-concat : {A : 𝒰₀} {B : A → 𝒰₀} {x y z : A} → ∏[ p ∈ x ≡ y ] ∏[ q ∈ y ≡ z ] tr B (q) ∘ tr B (p) ≡ tr B (p ∙ q)
tr-concat {_} {B} (refl w) q = refl (tr B q)

-- Lemma 1.5.9
∑= : ∀ {A : 𝒰₀} {x y : A} {B : A → 𝒰₀} {bx : B(x)} {by' : B(y)}
  → ∏[ p ∈ x ≡ y ] (  ( tr B (p)(bx) ≡ by' ) → ( (x , bx) ≡ (y , by') )  )
∑= (refl z) (refl w) = refl (z , w)

{-
  1.5.3
  × \times
-}

_×_ : (A B : 𝒰 ℓ) → 𝒰 ℓ
A × B = ∑[ x ∈ A ] B

{-
  1.5.4
-}
_inversZu_ : {A B : 𝒰₀} (f : A → B) (g : B → A) → 𝒰₀
f inversZu g = (∏[ x ∈ _ ] g(f x) ≡ x) × (∏[ y ∈ _ ] f(g y) ≡ y)

qinv : {A B : Set} (f : A → B) → Set
qinv f = ∑[ g ∈ (_ → _) ] g inversZu f

infix 6 _inversZu_

_hatInverse : {A B : 𝒰₀} (f : A → B) → 𝒰₀
f hatInverse = ∑[ g ∈ (_ → _) ] g inversZu f

{-
  1.5.5
-}

curry : {A B C : 𝒰₀}
        → ((A × B) → C) → (A → (B → C))
curry f = λ a b → f (a , b)

uncurry : {A B C : 𝒰₀}
          → (A → (B → C)) → ((A × B) → C)
uncurry f = λ x → f (π₁ x) (π₂ x)

{-
  1.5.7
-}

_teilt_ : (a b : ℕ) → 𝒰₀
a teilt b = ∑[ d ∈ ℕ ]  d · a ≡ b

{-
  1.5.8
-}

module lemma1-5-8 {A B : 𝒰₀} where
  u : {A B : 𝒰₀} → (x : A × B) → x ≡ (π₁ x , π₂ x)
  u (x , y) = refl (x , y)

  pair=⁻¹' : {x y : A × B}
             → (p : x ≡ y) → ((π₁ x ≡ π₁ y) × (π₂ x ≡ π₂ y))
  pair=⁻¹' p = ap π₁ p , ap π₂ p

  module _  {a a' : A} {b b' : B} where
    pair= : ((a ≡ a') × (b ≡ b')) → (a , b) ≡ (a' , b')
    pair= ((refl a) , (refl b)) = refl (a , b)

    pair=⁻¹ : (a , b) ≡ (a' , b') → ((a ≡ a') × (b ≡ b'))
    pair=⁻¹ p = pair=⁻¹' p

  lemma1-5-8-b :  {a a' : A} {b b' : B}
                  → pair= inversZu pair=⁻¹
  lemma1-5-8-b {a} {a'} {b} {b'} = teil1 , teil2
               where teil1 : ∏[ q ∈ _ ] pair=⁻¹ (pair= q) ≡ q
                     teil1 (refl _ , refl _) = refl _

                     teil2' : ∏[ p ∈ _ ] pair= (pair=⁻¹' p) ≡ (u _ ⁻¹ ∙ p) ∙ u _
                     teil2' (refl _) = refl _

                     teil2 : (p : (a , b) ≡ (a' , b')) → pair= (pair=⁻¹ p) ≡ p
                     teil2 p = (teil2' p) ∙ (reflRNeutral p)

{-
  1.6.1 Funktionsgleichheit
  ∼ \sim
-}

_∼_ : {A B : 𝒰 ℓ} (f : A → B) → (g : A → B) → 𝒰 ℓ
_∼_ {ℓ} {A} f g = ∏[ x ∈ A ] f(x) ≡ g(x)

infix 18 _∼_

∼sym : {A B : 𝒰₀} {f g : A → B} (H : f ∼ g) → (g ∼ f)
∼sym H = λ x → (H x)⁻¹

∼trans : {A B : 𝒰₀} {f g h : A → B} (H : f ∼ g) (G : g ∼ h) → f ∼ h
∼trans H G = λ x → (H x) ∙ (G x)

{-
  Das folgende erlaubt es uns, Verkettung von Homotopien in üblichem Stil
  aufzubauen.
-}
infixr 4 _∼⟨_⟩_
infixr 5 _∼∎

_∼⟨_⟩_ : {A B : 𝒰₀} {g h : A → B} (f : A → B) (H : f ∼ g) (K : g ∼ h) → f ∼ h
f ∼⟨ H ⟩ K = ∼trans H K

_∼∎ : {A B : 𝒰₀} (f : A → B) → f ∼ f
f ∼∎ = λ x → refl (f x)

{-
  1.6.2 Funktionsextensionalität
-}

postulate
  FunExt : {A B : 𝒰₀} (f g : A → B) → (∏[ x ∈ A ] f(x) ≡ g(x)) → f ≡ g

{-
  1.6.5
-}
-- A ist kontrahierbar / ein -2-Typ
isContr : (A : 𝒰₀) → 𝒰₀
isContr A = ∑[ c ∈ A ] ∏[ x ∈ A ] x ≡ c

-- A ist eine Aussage / ein -1-Typ
isProp : (A : 𝒰₀) → 𝒰₀
isProp A = ∏[ x ∈ A ] ∏[ y ∈ A ] x ≡ y

-- A ist eine Menge / ein 0-Typ
isSet : (A : 𝒰₀) → 𝒰₀
isSet A = ∏[ x ∈ A ] ∏[ y ∈ A ] ∏[ p ∈ x ≡ y ] ∏[ q ∈ x ≡ y ] p ≡ q


{-
  1.6.6
-}
-- 𝟙 ist kontrahierbar
𝟙isContr : isContr 𝟙
𝟙isContr = ∗ , helper
  where -- Mit Helper-Funktion, weil Patternmatching in Lamda-Ausdruck doof ist
    helper : (x : 𝟙) → x ≡ ∗
    helper ∗ = refl ∗

-- ∅ ist eine Aussage
∅isProp : isProp ∅
∅isProp = helper
  where
    helper : (a : ∅) → (b : ∅) → a ≡ b
    helper () ()

{-
  Ergebnis von Blatt 3, Aufgabe 3:
  Kontrahierbare Typen haben kontrahierbare Gleichheitstypen
-}
AisContr→≡isContr : ∀ {A : 𝒰₀} → isContr(A) → ∏[ x ∈ A ] ∏[ y ∈ A ] isContr(x ≡ y)
AisContr→≡isContr c x y = ( ((π₂ c) x) ∙ ((π₂ c) y) ⁻¹ ) , λ {(refl z) → (⁻¹RInv ( (π₂ c) z))⁻¹}


AisContr→AisProp : ∀ {A : 𝒰₀} → isContr(A) → isProp(A)
AisContr→AisProp c = λ x y → ((π₂ c) x) ∙ ((π₂ c) y) ⁻¹

{-
  2.1.1
-}
pre-whisker : ∀ {A B A' : 𝒰₀} {f g : A → B} (φ : A' → A) (H : f ∼ g) → f ∘ φ ∼ g ∘ φ
pre-whisker φ H = λ x → H (φ x)

post-whisker : ∀ {A B B' : 𝒰₀} {f g : A → B} (ψ : B → B') (H : f ∼ g) → ψ ∘ f ∼ ψ ∘ g
post-whisker ψ H = λ x → ap ψ (H x)

{-
  2.1.2
-}
id : (A : 𝒰 ℓ) → A → A
id A = λ a → a

LInv : {A B : 𝒰 ℓ} (f : A → B) → 𝒰 ℓ
LInv {ℓ} {A} {B} f = ∑[ g ∈ (B → A) ] g ∘ f ∼ (id A)

RInv : {A B : 𝒰 ℓ} (f : A → B) → 𝒰 ℓ
RInv {ℓ} {A} {B} f = ∑[ h ∈ (B → A) ] f ∘ h ∼ (id B)

LRInv : {A B : 𝒰 ℓ} (f : A → B) → 𝒰 ℓ
LRInv f = (LInv f) × (RInv f)

isEquiv : {A B : 𝒰 ℓ} (f : A → B) → 𝒰 ℓ
isEquiv f = LRInv f

_equivalentTo_ : (A B : 𝒰 ℓ) → 𝒰 ℓ
A equivalentTo B = ∑[ f ∈ (A → B) ] isEquiv f

-- Typ der Äquivalenzen (≃ – \simeq)
_≃_ : (A B : 𝒰 ℓ) → 𝒰 ℓ
A ≃ B = ∑[ f ∈ (A → B) ] isEquiv f

{-
  2.1.3 – Logische Äquivalenz
-}
_↔_ : (A B : 𝒰 ℓ) → 𝒰 ℓ
A ↔ B = (∑[ f ∈ (A → B)] 𝟙) × (∑[ g ∈ (B → A) ] 𝟙)

infixr 15 _↔_

{-
  Bemerkung 2.1.4: Seien A,B : 𝓤 und f : A → B. Die Typen LRInv(f) und qinv(f) sind logisch äquivalent
-}
bem-2-1-4 : {A B : 𝒰₀} (f : A → B) → ( (LRInv f) ↔ (qinv f) )
π₁ (bem-2-1-4 {A} {B} f) = (qinv-proof , ∗)
  where
    qinv-proof : LRInv f → qinv f
    qinv-proof lrinv = g , ginvf
      where
        g : B → A
        g = π₁ (π₁ lrinv)

        h : B → A
        h = π₁ (π₂ lrinv)

        g∼h : g ∼ h
        g∼h = g           ∼⟨ post-whisker g (∼sym (π₂ (π₂ lrinv))) ⟩
              g ∘ (f ∘ h)  ∼⟨ pre-whisker h (π₂ (π₁ lrinv)) ⟩
              h            ∼∎

        ginvf : g inversZu f
        ginvf = (f ∘ g   ∼⟨ post-whisker f g∼h ⟩
                 f ∘ h   ∼⟨ π₂ (π₂ lrinv) ⟩
                 id _    ∼∎)
                , π₂ (π₁ lrinv)

π₂ (bem-2-1-4 {A} {B} f) = lrinv-proof , ∗
  where
    lrinv-proof : qinv f → LRInv f
    lrinv-proof qinv = (g , H) , (g , K)
      where
        g : B → A
        g = π₁ qinv

        H : g ∘ f ∼ (id A)
        H = π₂ (π₂ qinv)

        K : f ∘ g ∼ (id B)
        K = π₁ (π₂ qinv)

{- Definition 1.6.13: Fasern, Injektivität, Surjektivität, Äquivalenz -}
fib : {A B : 𝒰₀} (f : A → B) (b : B) → 𝒰₀
fib {A} f b = ∑[ x ∈ A ] f(x) ≡ b

isInjective : {A B : 𝒰₀} (f : A → B) → 𝒰₀
isInjective {_} {B} f = ∏[ y ∈ B ] isProp(fib f y)

isSurjective : {A B : 𝒰₀} (f : A → B) → 𝒰₀
isSurjective {_} {B} f = ∏[ y ∈ B ] fib f y

isEquiv' : {A B : 𝒰₀} (f : A → B) → 𝒰₀
isEquiv' {_} {B} f = ∏[ y ∈ B ] isContr(fib f y)

{- Definition 2.3.3: Faserweise Abbildung induziert Abbildungen -}
-- ∑→ : \sum\to
∑→ : {A : 𝒰₀} {B B' : A → 𝒰₀}
  → (∏[ x ∈ A ] (B(x) → B'(x)))
  → ((∑[ x ∈ A ] B(x)) → (∑[ x ∈ A ] B'(x)))
∑→ f (x , bₓ) = x , f(x)(bₓ)
