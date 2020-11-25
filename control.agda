module Control where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Bool using (true; false; if_then_else_) renaming (Bool to 𝔹)
open import Data.String using (String)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Product using (_,_; _×_; Σ)
open import Relation.Binary.PropositionalEquality
open Relation.Binary.PropositionalEquality.≡-Reasoning

-- Expression types
data Ty : Set

-- Trail types
data Tr : Set

data Ty where
  Nat   : Ty
  Bool  : Ty
  Str   : Ty
  _⇒_,_,_,_,_ : Ty → Ty → Tr → Ty → Tr → Ty → Ty

data Tr where
  ●     : Tr
  _⇨_,_ : (τ₁ τ₁' : Ty) → Tr → Tr

-- Compatibility relation
-- compatible μ₁ μ₂ μ₃ means concatenating μ₁ and μ₂ results in μ₃
compatible : Tr → Tr → Tr → Set
compatible ● μ₂ μ₃ = μ₂ ≡ μ₃
compatible (τ₁ ⇨ τ₁' , μ₁) ● μ₃ = (τ₁ ⇨ τ₁' , μ₁) ≡ μ₃
compatible (τ₁ ⇨ τ₁' , μ₁) (τ₂ ⇨ τ₂' , μ₂) ● = ⊥
compatible (τ₁ ⇨ τ₁' , μ₁) (τ₂ ⇨ τ₂' , μ₂) (τ₃ ⇨ τ₃' , μ₃) =
  τ₁ ≡ τ₃ × τ₁' ≡ τ₃' × compatible (τ₂ ⇨ τ₂' , μ₂) μ₃ μ₁

-- Identity trail check
-- A trail is identity when it is empty or requires no invocation contexts
is-id-trail : (τ τ' : Ty) → (μ : Tr) → Set
is-id-trail τ τ' ● = τ ≡ τ'
is-id-trail τ τ' (τ₁ ⇨ τ₁' , μ) = τ ≡ τ₁ × τ' ≡ τ₁' × μ ≡ ●

-- Expressions
-- e : Exp var τ μα α μβ β  means
--  * e has type τ
--  * e produces a value of type β when
--      - surrounded by a context that receives a trail of type μα
--        and returns a value of type α
--      - given a trail of type μβ
data Exp (var : Ty → Set) : Ty → Tr → Ty → Tr → Ty → Set where
  Var     : {τ α : Ty} {μα : Tr} →
            var τ → Exp var τ μα α μα α
  Num     : {α : Ty} {μα : Tr} →
            ℕ → Exp var Nat μα α μα α
  Bol     : {α : Ty} {μα : Tr} →
            𝔹 → Exp var Bool μα α μα α
  Abs     : {τ₁ τ₂ α β γ : Ty} {μα μβ μγ : Tr} →
            (var τ₁ → Exp var τ₂ μα α μβ β) →
            Exp var (τ₁ ⇒ τ₂ , μα , α , μβ , β) μγ γ μγ γ
  App     : {τ₁ τ₂ α β γ δ : Ty} {μα μβ μγ μδ : Tr} →
            Exp var (τ₁ ⇒ τ₂ , μα , α , μβ , β) μγ γ μδ δ →
            Exp var τ₁ μβ β μγ γ →
            Exp var τ₂ μα α μδ δ
  Plus    : {α β γ : Ty} {μα μβ μγ : Tr} →
            Exp var Nat μα α μβ β →
            Exp var Nat μγ γ μα α →
            Exp var Nat μγ γ μβ β
  Is0     : {α β : Ty} {μα μβ : Tr} →
            Exp var Nat μα α μβ β →
            Exp var Bool μα α μβ β
  B2S     : {α β : Ty} {μα μβ : Tr} →
            Exp var Bool μα α μβ β →
            Exp var Str μα α μβ β
  Control : {τ α β γ γ' t₁ t₂ : Ty} {μid μ₀ μ₁ μ₂ μα μβ : Tr} →
            is-id-trail γ γ' μid →
            compatible (t₁ ⇨ t₂ , μ₁) μ₂ μ₀ →
            compatible μβ μ₀ μα →
            (var (τ ⇒ t₁ , μ₁ , t₂ , μ₂ , α) →
             Exp var γ μid γ' ● β) →
            Exp var τ μα α μβ β
  Prompt  : {τ α β β' : Ty} {μid μα : Tr} →
            is-id-trail β β' μid →
            Exp var β μid β' ● τ →
            Exp var τ μα α μα α

-- CPS interpreter

-- Interpretation of types
〚_〛τ : Ty → Set
〚_〛μ : Tr → Set

〚 Nat 〛τ = ℕ
〚 Bool 〛τ = 𝔹
〚 Str 〛τ = String
〚 τ₂ ⇒ τ₁ , μα , α , μβ , β 〛τ =
  〚 τ₂ 〛τ → (〚 τ₁ 〛τ → 〚 μα 〛μ → 〚 α 〛τ) → 〚 μβ 〛μ → 〚 β 〛τ

〚 ● 〛μ = ⊤
〚 τ ⇨ τ' , μ 〛μ = 〚 τ 〛τ → 〚 μ 〛μ → 〚 τ' 〛τ

-- Trail composition (corresponds to _::_ and _@_)
compose-trail : {μ₁ μ₂ μ₃ : Tr} →
  compatible μ₁ μ₂ μ₃ → 〚 μ₁ 〛μ → 〚 μ₂ 〛μ → 〚 μ₃ 〛μ
compose-trail {●} refl tt t₂ = t₂
compose-trail {τ₁ ⇨ τ₁' , μ₁} {●} refl t₁ tt = t₁
compose-trail {τ₁ ⇨ τ₁' , μ₁} {τ₂ ⇨ τ₂' , μ₂} {.τ₁ ⇨ .τ₁' , μ₃}
              (refl , refl , c) t₁ t₂ =
  λ v t' → t₁ v (compose-trail c t₂ t')

-- Identity continuation
kid : {τ τ' : Ty} → {μ : Tr} →
     is-id-trail τ τ' μ →
     〚 τ 〛τ → 〚 μ 〛μ → 〚 τ' 〛τ
kid {μ = ●} refl v tt = v
kid {μ = τ₁ ⇨ τ₁' , .●} (refl , refl , refl) v k = k v tt

-- is0
is0 : ℕ → 𝔹
is0 zero    = true
is0 (suc _) = false

-- b2s
b2s : 𝔹 → String
b2s true = "true"
b2s false = "false"

-- Interpretation of terms
g : {var : Ty → Set} {τ α β : Ty} {μα μβ : Tr} →
    Exp 〚_〛τ τ μα α μβ β →
    (〚 τ 〛τ → 〚 μα 〛μ → 〚 α 〛τ) → 〚 μβ 〛μ → 〚 β 〛τ
g (Var x) k t = k x t
g (Num n) k t = k n t
g (Bol b) k t = k b t
g (Abs f) k t = k (λ x → g {var = 〚_〛τ} (f x)) t
g (App e₁ e₂) k t =
  g {var = 〚_〛τ} e₁
    (λ v₁ t₁ → g {var = 〚_〛τ} e₂ (λ v₂ t₂ → v₁ v₂ k t₂) t₁) t
g (Plus e₁ e₂) k t =
  g {var = 〚_〛τ} e₁
    (λ v₁ t₁ → g {var = 〚_〛τ} e₂ (λ v₂ t₂ → k (v₁ + v₂) t₂) t₁) t
g (Is0 e) k t = g {var = 〚_〛τ} e (λ v t' → k (is0 v) t') t
g (B2S e) k t = g {var = 〚_〛τ} e (λ v t' → k (b2s v) t') t
g (Control is-id c₁ c₂ f) k t =
  g {var = 〚_〛τ}
    (f (λ v k' t' → k v (compose-trail c₂ t (compose-trail c₁ k' t'))))
    (kid is-id) tt
g (Prompt is-id e) k t = k (g {var = 〚_〛τ} e (kid is-id) tt) t

-- Top-level evaluation
go : {τ : Ty} → Exp 〚_〛τ τ ● τ ● τ → 〚 τ 〛τ
go e = g {var = 〚_〛τ} e (λ z _ → z) tt

-- Examples and tests

-- No control
-- < 12 >
exp0 : {var : Ty → Set} {α : Ty} {μα : Tr} →
       Exp var Nat μα α μα α
exp0 =
  Prompt refl (Num 12)

test0 : go exp0 ≡ 12
test0 = refl

-- 1 control, 1 resumption
-- < 12 + Fk. k 2 >
exp1 : {var : Ty → Set} {α : Ty} {μα : Tr} →
       Exp var Nat μα α μα α
exp1 =
  Prompt (refl , refl , refl)
         (Plus (Num 12)
               (Control {μ₀ = Nat ⇨ Nat , ●}
                        refl refl refl
                        (λ k → App (Var k) (Num 2))))

test1 : go exp1 ≡ 14
test1 = refl

-- 1 control, 2 resumptions
-- 1 + < 2 + Fk. k (k 3) >
exp2 : {var : Ty → Set} {α : Ty} {μα : Tr} →
       Exp var Nat μα α μα α
exp2 =
  Plus (Num 1)
       (Prompt (refl , refl , refl)
               (Plus (Num 2)
                     (Control {μ₀ = Nat ⇨ Nat , ●}
                              refl refl refl
                              (λ k → App (Var k)
                                         (App (Var k) (Num 3))))))

test2 : go exp2 ≡ 8
test2 = refl

-- shift/reset -> 8, control/prompt -> 6,
-- shift0/reset0 -> 7, control0/prompt0 -> 5
-- < < 1 + < (λ x. Fh. x) (Fk. Fg. 2 + f 5) > > >
exp3 : {var : Ty → Set} {α : Ty} {μα : Tr} →
       Exp var Nat μα α μα α
exp3 =
  Prompt refl
    (Prompt refl
      (Plus (Num 1)
         (Prompt {β' = Nat} (refl , refl , refl)
                 (App (Abs (λ x →
                              Control {t₁ = Nat} {t₂ = Nat} {μ₁ = ●} {μ₂ = ●}
                                      refl refl (refl , refl , refl)
                                      (λ h → Var x)))
                       (Control {γ = Nat} (refl , refl , refl) refl refl
                                (λ f →
                                   Control {t₁ = Nat} {t₂ = Nat} {μ₁ = ●} {μ₂ = ●}
                                           (refl , refl , refl) refl refl
                                           (λ g →
                                              Plus (Num 2)
                                                   (App (Var f) (Num 5)))))))))
                                                                
test3 : go exp3 ≡ 6
test3 = refl

-- Trail-type modification
-- < (Fk₁. is0 (k₁ 5)) + (Fk₂. b2s (k₂ 8)) >
exp4 : {var : Ty → Set} {α : Ty} {μα : Tr} →
       Exp var Str μα α μα α
exp4 =
  Prompt {μid = Nat ⇨ Str , ●}
         (refl , refl , refl)
         (Plus (Control {μid = Bool ⇨ Str , ●}
                        {μ₀ = Nat ⇨ Str , (Bool ⇨ Str , ●)}
                        {μ₁ = Bool ⇨ Str , ●}
                        {μ₂ = ●}
                        {μα = Nat ⇨ Str , (Bool ⇨ Str , ●)}
                        {μβ = ●}
                        (refl , refl , refl) refl refl
                        (λ k₁ → Is0 (App (Var k₁) (Num 5))))
               (Control {μid = ●}
                        {μ₀ = Bool ⇨ Str , ●}
                        {μ₁ = ●}
                        {μ₂ = ●}
                        {μα = Nat ⇨ Str , ●}
                        {μβ = Nat ⇨ Str , (Bool ⇨ Str , ●)}
                        refl refl (refl , refl , refl)
                        (λ k₂ → B2S (App (Var k₂) (Num 8)))))

test4 : go exp4 ≡ "false"
test4 = refl

-- 2 control, 2 resumptions (non-terminating, ill-typed)
-- < (Fk₁. k₁ 1; k₁ 1); (Fk₂. k₂ 1; k₂ 1) >
exp5 : {var : Ty → Set} {α : Ty} {μα : Tr} →
       Exp var Nat μα α μα α
exp5 =
  Prompt {μid = Nat ⇨ Nat , ●} -- 1
         (refl , refl , refl)
         (App {μβ = Nat ⇨ Nat , ●} -- 2
              (Abs (λ a →
                Control {μid = ●} -- 3
                        {μ₀ = Nat ⇨ Nat , ●} -- 4
                        {μ₁ = ●} -- 5
                        {μ₂ = ●} -- 6
                        {μα = Nat ⇨ Nat , ●} -- 7
                        {μβ = Nat ⇨ Nat , ●} -- 8
                        refl
                        refl
                        (refl , refl , {!!})
                        (λ k₂ → App (Abs (λ c → App (Var k₂) (Num 1)))
                                    (App (Var k₂) (Num 1)))))
              (Control {μid = ●} -- 9
                       {μ₀ = Nat ⇨ Nat , ●} -- 10
                       {μ₁ = ●} -- 11
                       {μ₂ = ●} -- 12
                       {μα = Nat ⇨ Nat , ●} -- 13
                       {μβ = ●} -- 14
                       refl
                       refl
                       refl
                       (λ k₁ → App (Abs (λ b → App (Var k₁) (Num 1)))
                                   (App (Var k₁) (Num 1)))))

{-
Let eᵢ = kᵢ 1; kᵢ 1 where i = 1, 2.

a. By (Shift), initial trail type of eᵢ = ●.
   By (App), initial trail type of eᵢ = initial trail type of body of kᵢ.
   Therefore, 6 = 12 = ●.

b. By (App), final trail type of eᵢ = final answer type of body of kᵢ.
   Therefore, 3 = 5, 9 = 11.

c. By (App), final trail type of first kᵢ 1 = initial trail type of second kᵢ 1.
   Therefore, 5 = 6, 11 = 12.

d. By a, c, and compatible (t₁ ⇨ t₂ , μ₁) μ₂ μ₀, 4 = 10 = Nat ⇨ Nat , ●

e. By (Prompt), initial trail type of body of <> = ●.
   By (App), initial trail type of body of <> = initial trail type of Fk₁. e₁.
   Therefore, 14 = ●.

f. By compatible μβ μ₀ μα, 13 = Nat ⇨ Nat , ●.

g. By (App), final trail type of Fk₁. e₁ = initial trail type of Fk₂. e₂.
   Therefore, 8 = Nat ⇨ Nat , ●.

h. By (Prompt), final trail type of body of <> must satisfy is-id-trail.
   By (App), final trail type of body of <> = final trail type of Fk₂. e₂.
   Therefore, 7 = Nat ⇨ Nat , ●.

i. By d, g, and h, compatible μβ μ₀ μα does not hold for Fk₂. e₂.
-}

-- 2 control, 2/0 resumptions (terminating, ill-typed)
-- < (Fk₁. 1); (Fk₂. k₂ 1; k₂ 1) >
exp6 : {var : Ty → Set} {α : Ty} {μα : Tr} →
       Exp var Nat μα α μα α
exp6 =
  Prompt {μid = Nat ⇨ Nat , ●}
         (refl , refl , refl)
         (App {μβ = Nat ⇨ Nat , ●}
              (Abs (λ a →
                Control {μid = ●}
                        {μ₀ = Nat ⇨ Nat , ●}
                        {μα = Nat ⇨ Nat , ●}
                        {μβ = Nat ⇨ Nat , ●}
                        refl
                        (refl , refl , refl)
                        (refl , refl , {!!})
                        (λ k₂ → Num 1)))
              (Control {μid = ●}
                       {μ₀ = Nat ⇨ Nat , ●}
                       {μα = Nat ⇨ Nat , ●}
                       {μβ = ●}
                       refl
                       refl
                       refl
                       (λ k₁ → App (Abs (λ c → App (Var k₁) (Num 1)))
                                   (App (Var k₁) (Num 1)))))

-- 2 control, 0/2 resumptions (well-typed)
-- < Fk₁. 1; (Fk₂. k₂ 1; k₂ 1) >
exp7 : {var : Ty → Set} {α : Ty} {μα : Tr} →
        Exp var Nat μα α μα α
exp7 =
  Prompt {μid = Nat ⇨ Nat , ●}
         (refl , refl , refl)
         (App {τ₁ = Nat}
              {μβ = Nat ⇨ Nat , (Nat ⇨ Nat , ●)}
              (Abs (λ a →
                Control {μid = ●}
                        {μ₀ = Nat ⇨ Nat , ●}
                        {μα = Nat ⇨ Nat , ●}
                        {μβ = Nat ⇨ Nat , (Nat ⇨ Nat , ●)}
                        refl
                        refl
                        (refl , refl , refl)
                        (λ k₂ → App (Abs (λ c → App (Var k₂) (Num 1)))
                                    (App (Var k₂) (Num 1)))))
              (Control {t₁ = Nat}
                       {t₂ = Nat}
                       {μid = ●}
                       {μ₀ = Nat ⇨ Nat , (Nat ⇨ Nat , ●)}
                       {μ₁ = Nat ⇨ Nat , ●}
                       {μ₂ = Nat ⇨ Nat , (Nat ⇨ Nat , ●)}
                       {μα = Nat ⇨ Nat , (Nat ⇨ Nat , ●)}
                       {μβ = ●}
                       refl
                       (refl , refl , refl , refl , refl)
                       refl
                       (λ k₁ → Num 1)))

test7 : go exp7 ≡ 1
test7 = refl
