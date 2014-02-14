module Preliminaries where

-- levels

postulate Level : Set
postulate LZero : Level
postulate LSuc  : Level -> Level
postulate LMax  : Level -> Level -> Level

{-# BUILTIN LEVEL     Level #-}
{-# BUILTIN LEVELZERO LZero  #-}
{-# BUILTIN LEVELSUC  LSuc   #-}
{-# BUILTIN LEVELMAX  LMax #-}

-- natural numbers

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

{-# BUILTIN NATURAL Nat #-}
{-# BUILTIN ZERO zero #-}
{-# BUILTIN SUC suc #-}

-- propositional equality

infix 4 _==_ _~=~_

data _==_ {l}{A : Set l} (x : A) : A -> Set l where
  refl : x == x

{-# BUILTIN EQUALITY _==_ #-}
{-# BUILTIN REFL refl #-}  

-- utilities about equality

cong : forall {a b}{A : Set a}{B : Set b}(f : A -> B){x y}-> x == y -> f x == f y
cong f refl = refl

cong2 : forall {a b c}{A : Set a}{B : Set b}{C : Set c}
               (f : A -> B -> C){x y u v} -> x == y -> u == v -> f x u == f y v
cong2 f refl refl = refl

sym : forall {a}{A : Set a}{x y : A} -> x == y -> y == x
sym refl = refl

trans : forall {a}{A : Set a}{x y z : A} -> x == y -> y == z -> x == z
trans refl refl = refl

--heterogeneous equality 

data _~=~_ {a} {A : Set a}(x : A) : forall {b}{B : Set b} -> B -> Set where
  hrefl : x ~=~ x

~=~-to-== : forall {a}{A : Set a}{x y : A} -> x ~=~ y -> x == y
~=~-to-== hrefl = refl

==-to-~=~ : forall {a}{A : Set a}{x y : A} -> x == y -> x ~=~ y
==-to-~=~ refl = hrefl

-- unit type, hidden arguments and steroids.

data Unit : Set where
  unit : Unit

Hidden : forall {a} -> Set a -> Set a
Hidden A = Unit -> A

hide : forall {a b}{A : Set a}{B : A -> Set b} -> ((x : A) -> B x) -> ((x : A) -> Hidden (B x))
hide f x unit = f x

reveal : forall {a}{A : Set a} -> Hidden A -> A
reveal f = f unit

data Reveal_is_ {a} {A : Set a} (x : Hidden A) (y : A) : Set a where
  [_] : (eq : reveal x == y) -> Reveal x is y

inspect : forall {a b} {A : Set a} {B : A -> Set b}
          (f : (x : A) -> B x) (x : A) -> Reveal (hide f x) is (f x)
inspect f x = [ refl ]

-- products

infixr 4 _,_
infixr 2 _*_

record Sigma {a b}(A : Set a)(B : A -> Set b) : Set (LMax a b) where
  constructor _,_
  field
    fst : A
    snd : B fst

open Sigma public

exists : forall {a b} -> {A : Set a}(B : A -> Set b) -> Set (LMax a b)
exists = Sigma _

_*_ : forall {a b}(A : Set a)(B : Set b) -> Set (LMax a b)
A * B = Sigma A (\_ -> B)


sigmaInj : forall {a b}{A : Set a}{B : A -> Set b}{x x' : A}{y : B x}{y' : B x'} -> 
                  _==_ {A = Sigma A B} (x , y) (x' , y') -> 
                  (x ~=~ x') * (y ~=~ y')
sigmaInj refl = hrefl , hrefl

-- coproducts

data _+_ {a b}(A : Set a)(B : Set b) : Set (LMax a b) where
  inl : A -> A + B
  inr : B -> A + B

+-func : forall {a b c}{A : Set a}{B : Set b}{C : Set c} -> (A -> C) -> (B -> C) -> A + B -> C
+-func f g (inl a) = f a
+-func f g (inr b) = g b

-- negation

data Empty : Set where

not : forall {l}(A : Set l) -> Set l
not A = A -> Empty

exFalsum : forall {l}{A : Set l} -> Empty -> A
exFalsum ()

-- Lists

data List {l}(A : Set l) : Set l where
  []   : List A
  _::_ : A -> List A -> List A

infixl 4 _::_

-- foldr

foldr : forall {l}{A B : Set l} -> (A -> B -> B) -> B -> List A -> B
foldr f v [] = v
foldr f v (x :: xs) = f x (foldr f v xs)

-- List membership

infixl 3 _<-_

data _<-_ {A : Set} : A -> List A -> Set where
  here  : forall {x xs}   -> x <- (x :: xs)
  there : forall {x y ys} -> x <- ys -> x <- (y :: ys)

thereInj : forall {A}{x y : A}{xs : List A}{p : x <- xs}{q : x <- xs} -> there {y = y} p == there {y = y} q -> p == q
thereInj refl = refl

<-inv : forall {A}{x y : A}{xs : List A} -> x <- (y :: xs) -> (x == y) + (x <- xs)
<-inv here = inl refl
<-inv (there prf) = inr prf

-- decidability predicate

Rel : Set -> Set1
Rel A = A -> A -> Set

data Dec {a} (A : Set a) : Set a where
  yes : (p : A) -> Dec A
  no  : (p : not A) -> Dec A

<-Dec : forall {A : Set}(eq : forall (y z : A) -> Dec (y == z))(x : A)(xs : List A) -> Dec (x <- xs)
<-Dec eq x [] = no (λ ())
<-Dec eq x (y :: ys) with eq x y | <-Dec eq x ys 
<-Dec eq .y (y :: ys) | yes refl | r' = yes here
<-Dec eq x (y :: ys) | no p | yes p' = yes (there p')
<-Dec eq x (y :: ys) | no p | no p' = no (\ ctr -> +-func p p' (<-inv ctr))
