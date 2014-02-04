module Subst where

open import Preliminaries

-- kind definition

data Kind : Set where
  Star : Kind
  _=>_ : Kind -> Kind -> Kind

-- context for variables

VarCtx : Set
VarCtx = List Kind

-- context for type constructors

ConCtx : Set
ConCtx = List Kind

-- type definition

data Tau : VarCtx -> ConCtx -> Kind -> Set where
  var : forall {V C k} -> (x : k <- V) -> Tau V C k
  con : forall {V C k} -> (x : k <- C) -> Tau V C k
  app : forall {V C k k'} -> Tau V C (k => k') -> Tau V C k -> Tau V C k'

-- quantified types

data Rho : VarCtx -> ConCtx -> Kind -> Set where
  Forall  : forall {V C k k'} -> (t : Rho (k' :: V) C k) -> Rho V C k
  SimplyTau : forall {V C k} -> Tau V C k -> Rho V C k

SigmaType : ConCtx -> Set
SigmaType C = Rho [] C Star

-- removing a variable from a context

_-_ : forall {k} -> (V : VarCtx) -> (x : k <- V) -> VarCtx
[] - () 
(x :: V) - here = V
(x :: V) - there i = x :: (V - i)

-- weakening

weak : forall {V k k'}(x : k <- V)(v : k' <- (V - x)) -> k' <- V
weak here v = there v
weak (there x) here = here
weak (there x) (there v) = there (weak x v)

-- weakening a type

weakTau : forall {V C k k'}(v : k <- V)(t : Tau (V - v) C k') -> Tau V C k'
weakTau v (var x) = var (weak v x)
weakTau v (con c) = con c
weakTau v (app l r) = app (weakTau v l) (weakTau v r)

-- decidable equality test for variables

data EqVar {V : VarCtx} : {k k' : Kind} -> (x : k <- V)(v : k' <- V) -> Set where
  same : forall {k}{x : k <- V} -> EqVar x x
  diff : forall {k k'}(x : k <- V)(v : k' <- (V - x)) -> EqVar x (weak x v)

eq : forall {V k k'}(x : k <- V)(v : k' <- V) -> EqVar x v
eq here here = same
eq here (there v) = diff here v
eq (there x) here = diff (there x) here
eq (there x) (there v) with eq x v 
eq (there .v) (there v) | same = same
eq (there x) (there .(weak x v)) | diff .x v = diff (there x) (there v)

-- substitution, preserves kinds

substVar : forall {V C k k'}(v : k <- V)(x : k' <- V)(t : Tau (V - x) C k') -> Tau (V - x) C k
substVar v x t with eq x v 
substVar v .v t | same = t
substVar .(weak x v) x t | diff .x v = var v

-- t [u / x]

substTau : forall {V C k k'}(t : Tau V C k)(x : k' <- V)(u : Tau (V - x) C k') -> Tau (V - x) C k
substTau (var v) x u = substVar v x u
substTau (con c) x u = con c
substTau (app l r) x u = app (substTau l x u) (substTau r x u) 

-- idempotence stuff

weakInj : forall {k k' : Kind}{C : VarCtx}(p : k <- C)(v v' : k' <- C - p) -> weak p v == weak p v' -> v == v'
weakInj here .v' v' refl = refl
weakInj (there p) here here prf = refl
weakInj (there p) here (there v') () 
weakInj (there p) (there v) here () 
weakInj (there p) (there v) (there v') prf = cong there (weakInj p v v' (thereInj prf))

weakLeft : forall {k C}(p : k <- C)(q : k <- C - p) -> not (weak p q == p)
weakLeft here here () 
weakLeft here (there q) () 
weakLeft (there p) here ()
weakLeft (there p) (there q) prf = weakLeft p q (thereInj prf)

substWeakVar : forall {k k' V C}(p : k <- V)(v : k' <- V - p)(t : Tau (V - p) C k) -> var v == substTau (var (weak p v)) p t
substWeakVar p v t with weak p v | inspect (weak p) v | eq p (weak p v) 
substWeakVar .a v t | a | [ eq ] | same = exFalsum (weakLeft a v eq)
substWeakVar p v t | .(weak p v') | [ eq ] | diff .p v' = cong var (weakInj p v v' eq)

substLem : forall {k k' V C} (v : k <- V)(t : Tau (V - v) C k')(t' : Tau (V - v) C k) -> t == substTau (weakTau v t) v t' 
substLem v (var v') t' = substWeakVar v v' t'
substLem v (con c) t' = refl
substLem v (app l r) t' = cong2 app (substLem v l t') (substLem v r t')

substTauIdem : forall {V C k k'}(t : Tau V C k)(x : k' <- V)(u : Tau (V - x) C k') -> substTau t x u == substTau (weakTau x (substTau t x u)) x u
substTauIdem (var v) x u with eq x v
substTauIdem (var v) .v u | same = substLem v u u
substTauIdem (var .(weak x v)) x u | diff .x v = substWeakVar x v u
substTauIdem (con c) x u = refl
substTauIdem (app l r) x u = cong2 app (substTauIdem l x u) (substTauIdem r x u) 

-- associativity of substitutions

