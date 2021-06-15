{-# OPTIONS --without-K #-}

open import VorlesungMitUniversen

module Kreis where
module _ where
  private
    data #S¹ : 𝒰₀ where
      #base : #S¹
      
  S¹ : 𝒰₀
  S¹ = #S¹
  base : S¹
  base = #base
  
  postulate
    loop : base ≡ base
  
  S¹-induction : ∀ {i} {P : S¹ → 𝒰 i} (base* : P base)
           (loop* : tr P loop base* ≡ base*) → ((i : S¹) →  P i)
  S¹-induction base* loop* #base = base*

