{-# OPTIONS --without-K #-}

open import VorlesungMitUniversen

module Intervall where
module _ where
  private
    data #I : 𝒰₀ where
      #zero : #I
      #one : #I
      
  I : 𝒰₀
  I = #I
  a : I
  a = #zero
  b : I
  b = #one
  
  postulate
    seg : a ≡ b
  
  I-recursion : ∀ {i} {A : 𝒰 i} 
            → (a₀ : A) → (a₁ : A) → (aₛ : a₀ ≡ a₁) 
            → (I → A)
  I-recursion {i} {A} a₀ a₁ aₛ #zero = a₀
  I-recursion {i} {A} a₀ a₁ aₛ #one = a₁

  I-induction : ∀ {i} {P : I → 𝒰 i} (zero* : P a) (one* : P b)
           (seg* : tr P seg zero* ≡ one*) → ((i : I) →  P i)
  I-induction zero* one* seg* #zero = zero*
  I-induction zero* one* seg* #one = one*
                                       
I-isContr : isContr I
I-isContr = a , (I-induction
                  (refl _)
                  (seg ⁻¹)
                  (tr (λ x → x ≡ a) seg (refl a)    ≡⟨  ap (λ f → f (refl a)) (tr-x≡a seg ⁻¹) ⟩
                  (seg ⁻¹ ∙ (refl a))               ≡⟨ reflRNeutral (seg ⁻¹) ⟩ 
                  seg ⁻¹                            ≡∎))
