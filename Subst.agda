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

-- variables and type constructors

Var : forall (k : Kind)(V : VarCtx) -> Set
Var k V = k <- V

Con : forall (k : Kind)(C : ConCtx) -> Set
Con k C = k <- C

-- type definition

data Tau : VarCtx -> ConCtx -> Kind -> Set where
  var : forall {V C k} -> (v : Var k V) -> Tau V C k
  con : forall {V C k} -> (c : Con k C) -> Tau V C k
  app : forall {V C k k'} -> Tau V C (k => k') -> Tau V C k -> Tau V C k'

-- removing a variable from a context

_-_ : forall {k} -> (V : VarCtx) -> (x : Var k V) -> VarCtx
[] - () 
(x :: V) - here = V
(x :: V) - there i = x :: (V - i)

-- weakening

weak : forall {V k k'}(x : Var k V)(v : Var k' (V - x)) -> Var k' V
weak here v = there v
weak (there x) here = here
weak (there x) (there v) = there (weak x v)

-- weakening a type

weakTau : forall {V C k k'}(v : Var k V)(t : Tau (V - v) C k') -> Tau V C k'
weakTau v (var x) = var (weak v x)
weakTau v (con c) = con c
weakTau v (app l r) = app (weakTau v l) (weakTau v r)

-- decidable equality test for variables

data EqVar {V : VarCtx} : {k k' : Kind} -> (x : Var k V)(v : Var k' V) -> Set where
  same : forall {k}{x : Var k V} -> EqVar x x
  diff : forall {k k'}(x : Var k V)(v : Var k' (V - x)) -> EqVar x (weak x v)

eq : forall {V k k'}(x : Var k V)(v : Var k' V) -> EqVar x v
eq here here = same
eq here (there v) = diff here v
eq (there x) here = diff (there x) here
eq (there x) (there v) with eq x v 
eq (there .v) (there v) | same = same
eq (there x) (there .(weak x v)) | diff .x v = diff (there x) (there v)

-- substitution, preserves kinds

substVar : forall {V C k k'}(v : Var k V)(x : Var k' V)(t : Tau (V - x) C k') -> Tau (V - x) C k
substVar v x t with eq x v 
substVar v .v t | same = t
substVar .(weak x v) x t | diff .x v = var v

-- t [u / x]

substTau : forall {V C k k'}(t : Tau V C k)(x : Var k' V)(u : Tau (V - x) C k') -> Tau (V - x) C k
substTau (var v) x u = substVar v x u
substTau (con c) x u = con c
substTau (app l r) x u = app (substTau l x u) (substTau r x u) 

-- idempotence stuff

weakInj : forall {k k' : Kind}{C : VarCtx}(p : Var k C)(v v' : Var k' (C - p)) -> weak p v == weak p v' -> v == v'
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

substWeakVar : forall {k k' V C}(p : Var k V)(v : Var k' (V - p))(t : Tau (V - p) C k) -> var v == substTau (var (weak p v)) p t
substWeakVar p v t with weak p v | inspect (weak p) v | eq p (weak p v) 
substWeakVar .a v t | a | [ eq ] | same = exFalsum (weakLeft a v eq)
substWeakVar p v t | .(weak p v') | [ eq ] | diff .p v' = cong var (weakInj p v v' eq)

substLem : forall {k k' V C} (v : Var k V)(t : Tau (V - v) C k')(t' : Tau (V - v) C k) -> t == substTau (weakTau v t) v t' 
substLem v (var v') t' = substWeakVar v v' t'
substLem v (con c) t' = refl
substLem v (app l r) t' = cong2 app (substLem v l t') (substLem v r t')

substTauIdem : forall {V C k k'}(t : Tau V C k)(x : Var k' V)(u : Tau (V - x) C k') -> substTau t x u == substTau (weakTau x (substTau t x u)) x u
substTauIdem (var v) x u with eq x v
substTauIdem (var v) .v u | same = substLem v u u
substTauIdem (var .(weak x v)) x u | diff .x v = substWeakVar x v u
substTauIdem (con c) x u = refl
substTauIdem (app l r) x u = cong2 app (substTauIdem l x u) (substTauIdem r x u) 

-- substitutions: 

data Subst (C : ConCtx) : VarCtx -> VarCtx -> Set where
  <>  : forall {V : VarCtx} -> Subst C V []
  _,,_ : forall {V V' : VarCtx}{k : Kind} -> Tau V C k -> Subst C V V' -> Subst C V (k :: V')

-- application

substVar1 : forall {V V' : VarCtx}{C : ConCtx}{k : Kind} -> Subst C V V' -> Var k V' -> Tau V C k
substVar1 <> ()
substVar1 (t ,, s) here = t
substVar1 (t ,, s) (there v) = substVar1 s v

-- by construction: substitution is kind preserving

substTau1 : forall {V V' : VarCtx}{C : ConCtx}{k : Kind} -> Subst C V V' -> Tau V' C k -> Tau V C k
substTau1 s (var v) = substVar1 s v
substTau1 s (con c) = con c
substTau1 s (app l r) = app (substTau1 s l) (substTau1 s r)

-- weakening substitutions

weakSubst : forall {k V V' C} -> Subst C V V' -> Subst C (k :: V) V'
weakSubst <> = <>
weakSubst (x ,, s) = (weakTau here x) ,, (weakSubst s)

-- extending a substitution

ext : forall {V V' C k} -> Subst C V V' -> Subst C (k :: V) (k :: V')
ext s = var here ,, weakSubst s  

substExt : forall {C V V' k}{s s' : Subst C V V'}{t t' : Tau V C k} -> s == s' -> t == t' ->  t ,, s == t' ,, s'
substExt refl refl = refl

-- identity substitution

id : forall {V : VarCtx}{C : ConCtx} -> Subst C V V
id {[]}{C}  = <>
id {x :: V} = ext id

-- composition

_o_ : forall {V V' V'' : VarCtx}{C : ConCtx} -> Subst C V V' -> Subst C V' V'' -> Subst C V V''
s o <> = <>
s o (t ,, s') = substTau1 s t ,, (s o s')

-- composition is equals to each substitution 

o-substTau1 : forall {V V' V'' : VarCtx}{C : ConCtx}{k : Kind}(s : Subst C V V')(s' : Subst C V' V'')(t : Tau V'' C k) -> 
              substTau1 (s o s') t == substTau1 s (substTau1 s' t)
o-substTau1 s <> (var ())
o-substTau1 s (x ,, s') (var here) = refl
o-substTau1 s (x ,, s') (var (there v)) = o-substTau1 s s' (var v)
o-substTau1 s s' (con c) = refl
o-substTau1 s s' (app l r) = cong2 app (o-substTau1 s s' l) (o-substTau1 s s' r)

-- composition is associative

o-assoc : forall {V V' V'' V''' : VarCtx}{C : ConCtx}(s : Subst C V V')(s' : Subst C V' V'')(s'' : Subst C V'' V''') -> 
                 s o (s' o s'') == (s o s') o s''
o-assoc s s' <> = refl
o-assoc s s' (t ,, s'') = substExt (o-assoc s s' s'') (sym (o-substTau1 s s' t))




