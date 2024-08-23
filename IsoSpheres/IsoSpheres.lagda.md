```agda
module IsoSpheres where

open import 1Lab.HLevel
open import 1Lab.Type
open import 1Lab.Equiv
open import 1Lab.Equiv.Biinv renaming (rinv to Brinv ; linv to Blinv)
open import 1Lab.Path
open import 1Lab.Type.Sigma
open import 1Lab.Univalence
open import 1Lab.Function.Embedding

open is-iso
```

## Pomožni rezultati

```agda
restrict-to-subtype : {ℓ₁ ℓ₂ : Level} {A : Type ℓ₁} {B P : A → Type ℓ₂}
                    → ((x : A) → is-prop (P x)) → ((x : A) → B x → P x)
                    → Σ A B ≃ (Σ[ t ∈ Σ A P ] B (t .fst))
restrict-to-subtype {A = A} {B = B} {P = P} Pprop f = Σ-ap-snd equiv-family ∙e Σ-assoc
  where

  equiv-family : (x : A) → B x ≃ Σ (P x) (λ _ → B x)
  equiv-family x = Iso→Equiv the-iso
    where

    the-iso : Iso _ _
    the-iso .fst        b      = (f x b) , b
    the-iso .snd .inv          = snd
    the-iso .snd .linv  _      = refl
    the-iso .snd .rinv (p , b) = Σ-path (Pprop x (f x b) p) (transport-refl b)

sigma-contr-base : {ℓ₁ ℓ₂ : Level} {A : Type ℓ₁} {B : A → Type ℓ₂}
                 → (c : is-contr A) → Σ A B ≃ B (centre c)
sigma-contr-base {B = B} c = Iso→Equiv the-iso
  where

  the-iso : Iso _ _
  the-iso .fst       (a , b) = subst B (sym (paths c a)) b
  the-iso .snd .inv       b  = (centre c) , b
  the-iso .snd .linv (a , b) = sym (Σ-path (sym (paths c a)) refl)
  the-iso .snd .rinv      b  =
    subst (λ p → subst B p b ≡ b)
          (is-contr→is-set c (centre c) (centre c) refl (sym (paths c (centre c))))
          (transport-refl b)
```

## Sfera

```agda
data S² : Type where
  base : S²
  surf : refl {x = base} ≡ refl

ap² : {ℓ₁ ℓ₂ : Level} {A : Type ℓ₁} {B : Type ℓ₂} (f : A → B) {x y : A} {p q : x ≡ y}
    → (s : p ≡ q) → ap f p ≡ ap f q
ap² f s i j = f (s i j)

universal-property-sphere : {ℓ : Level} {A : Type ℓ}
                          → (Σ[ x ∈ A ] (refl {x = x} ≡ refl)) ≃ (S² → A)
universal-property-sphere {ℓ} = Iso→Equiv the-iso
  where

  the-iso : Iso _ _
  the-iso .fst (a , s) base = a
  the-iso .fst (a , s) (surf i j) = s i j
  the-iso .snd .inv f = (f base) , ap² f surf
  the-iso .snd .linv (a , s) = refl
  the-iso .snd .rinv f = funext (λ { base → refl ; (surf i j) → refl})
```

## Konstrukcija

```agda
iso-is-looped-equiv : {ℓ : Level} {A B : Type ℓ}
                    → Iso A B ≃ (Σ[ e ∈ (A ≃ B)] (e ≡ e))
iso-is-looped-equiv {A = A} {B = B} =
  Iso A B                            ≃⟨ restrict-to-subtype-equiv ⟩
  Σ[ e ∈ (A ≃ B) ] (is-iso (e .fst)) ≃⟨ Σ-ap-snd equiv-family ⟩
  Σ[ e ∈ (A ≃ B) ] (e ≡ e)           ≃∎
  where

  restrict-to-subtype-equiv : _
  restrict-to-subtype-equiv =
    restrict-to-subtype is-equiv-is-prop (λ _ p → is-iso→is-equiv p)

  equiv-family : (e : A ≃ B) → is-iso (e .fst) ≃ (e ≡ e)
  equiv-family e =
    EquivJ (λ _ f → is-iso (f .fst) ≃ (f ≡ f))
           (lemma ∙e (Σ-prop-path≃ is-equiv-is-prop))
           (e)
    where

    lemma : is-iso id ≃ (id ≡ id)
    lemma =
      is-iso id                       ≃⟨ iso-assoc (id , id-equiv) ⟩
      Σ[ H ∈ Brinv id ] (H .fst ≡ id) ≃⟨ contract-sections ⟩
      id ≡ id                         ≃∎
      where

      iso-assoc : {ℓ : Level} {A B : Type ℓ} (e : A ≃ B)
                → is-iso (e .fst) ≃ (Σ[ H ∈ Brinv (e .fst) ] ((H . fst) ∘ (e .fst) ≡ id))
      iso-assoc {A = A} {B = B} e = Iso→Equiv the-iso
        where

        the-iso : Iso _ _
        the-iso .fst       p = (inv p , funext (rinv p)) , funext (linv p)
        the-iso .snd .inv  p = iso (p .fst .fst) (happly (p .fst .snd)) (happly (p .snd))
        the-iso .snd .rinv p = refl
        the-iso .snd .linv p = iso-eta p
          where

          iso-eta : {f : A → B} → (p : is-iso f) → iso (inv p) (rinv p) (linv p) ≡ p
          iso-eta p i .inv  = inv  p
          iso-eta p i .linv = linv p
          iso-eta p i .rinv = rinv p

      contract-sections : _
      contract-sections =
        sigma-contr-base (is-iso→is-contr-rinv (is-equiv→is-iso id-equiv))


isos-are-spheres : {ℓ : Level}
                 → (Σ[ A ∈ Type ℓ ] Σ[ B ∈ Type ℓ ] Iso A B) ≃ (S² → Type ℓ)
isos-are-spheres {ℓ} =
  Σ[ A ∈ Type ℓ ] Σ[ B ∈ Type ℓ ] Iso A B ≃⟨ Σ-ap-snd lemma ⟩
  Σ[ A ∈ Type ℓ ] (refl ≡ refl)           ≃⟨ universal-property-sphere ⟩
  (S² → Type ℓ)                           ≃∎
  where

  lemma : (A : Type ℓ) → (Σ[ B ∈ Type ℓ ] Iso A B) ≃ (refl ≡ refl)
  lemma A =
    Σ[ B ∈ Type ℓ ] Iso A B                           ≃⟨ Σ-ap-snd lemma2 ⟩
    Σ[ B ∈ Type ℓ ] Σ[ e ∈ A ≡ B ] (e ≡ e)            ≃⟨ Σ-assoc ⟩
    Σ[ E ∈ Σ[ B ∈ Type ℓ ] (A ≡ B)] (E .snd ≡ E .snd) ≃⟨ contract-Singleton ⟩
    refl ≡ refl                                       ≃∎
    where

    contract-Singleton : _
    contract-Singleton = sigma-contr-base (contr (A , refl) Singleton-is-contr)

    lemma2 : (B : Type ℓ) → Iso A B ≃ (Σ[ e ∈ (A ≡ B) ] (e ≡ e))
    lemma2 B =
      Iso A B                                      ≃⟨ iso-is-looped-equiv ⟩
      Σ[ e ∈ A ≃ B ] (e ≡ e)                       ≃˘⟨ Σ-ap-fst (Iso→Equiv Path≃Equiv) ⟩
      Σ[ e ∈ A ≡ B ] (path→equiv e ≡ path→equiv e) ≃˘⟨ cancel-path→equiv ⟩
      Σ[ e ∈ A ≡ B ] (e ≡ e)                       ≃∎
      where

      cancel-path→equiv : _
      cancel-path→equiv =
        Σ-ap-snd (λ _ → ap path→equiv , equiv→cancellable univalence)
```
