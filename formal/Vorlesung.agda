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
  Natürliche Zahlen...
-}
data ℕ : Set where
  0ℕ : ℕ
  succℕ : ℕ → ℕ

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

data Eins : Set where
  ∗ : Eins

data Zwei : Set where
  0₂ : Zwei
  1₂ : Zwei

{-
  Gleichheit.
  Die beiden Parameter "x,y : A" können wir in Agda realisieren, indem wir einen
  induktiven Typ vom Typ "A → A → Set" definieren.
-}

data _≡_ {A : Set} : A → A → Set where
  refl : (x : A) → x ≡ x

{-
  Die Induktionsregel dafür gibt es bei Agda automatisch in der Gestalt von Pattern-Matching.
  Das können wir nutzen, um den Induktionsterm aus der Vorlesung zu definieren.
-}

ind= : {P : ℕ → Set} → (p₀ : P 0ℕ) → (pₛ : (n : ℕ) → P n → P (succℕ n)) → Π ℕ P
ind= p₀ pₛ 0ℕ = p₀
ind= p₀ pₛ (succℕ n) = pₛ  n (ind= p₀ pₛ n)
