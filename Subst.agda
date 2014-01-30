module Subst where

open import Preliminaries

-- type definition

Vars : Set 
Vars = List Nat

data Ty (C : Vars) : Set where
  var : forall {x} -> x <- C -> Ty C
  app : forall (l r : Ty C) -> Ty C
  con : Nat -> Ty C

varInj : forall {C : Vars}{x y : Nat}{p : x <- C} {q : y <- C} -> var p == var q -> (x , p) == (y , q)
varInj refl = refl

conInj : forall {c c' : Nat}{C : Vars} -> con {C} c == con c' -> c == c'
conInj refl = refl

_-_ : forall {x} -> (C : Vars) -> (v : x <- C) -> Vars
[] - () 
(x :: c) - here = c
(x :: c) - (there p) = x :: (c - p)

weak : forall {x x' C} -> (p : x <- C) -> (p' : x' <- (C - p)) -> x' <- C
weak here p' = there p'
weak (there p) here = here
weak (there p) (there p') = there (weak p p')

infix 4 _<-==_

data _<-==_ {C} : forall {t t'} -> t <- C -> t' <- C -> Set where
  same : forall {t} (x : t <- C) -> x <-== x
  diff : forall {t t'} (x : t <- C ) (v : t' <- (C - x)) -> x <-== (weak x v) 

varDiff : forall {t t' C} -> (x : t <- C) (v : t' <- C) -> x <-== v
varDiff here here = same here
varDiff here (there v) = diff here v
varDiff (there x) here = diff (there x) here
varDiff (there x) (there v) with varDiff x v 
varDiff (there .v) (there v) | same .v = same (there v)
varDiff (there x) (there .(weak x v)) | diff .x v = diff (there x) (there v)

replace : forall {x C} -> (p : x <- C) -> (t : Ty (C - p)) -> Ty C -> Ty (C - p)
replace p t (var x) with varDiff p x 
replace .x₁ t (var x₁)        | same .x₁ = t
replace p t (var .(weak p v)) | diff .p v = var v
replace p t (app t' t'') = app (replace p t t') (replace p t t'')
replace p t (con x) = con x

weakTy : forall {x C} -> (p : x <- C) -> (t : Ty (C - p)) -> Ty C
weakTy p (var v) = var (weak p v)
weakTy p (app t t') = app (weakTy p t) (weakTy p t')
weakTy p (con c) = con c

weakVar : forall {x y C}{p : x <- C}{p' : y <- C}{t : Ty (C - p)} -> weakTy p t == var p' -> exists (\ v -> (t == var v) * (p' == weak p v))
weakVar {x} {y} {C} {p} {.(weak p v)} {var v} refl = v , (refl , refl)
weakVar {x} {y} {C} {p} {p'} {app l r} () 
weakVar {x} {y} {C} {p} {p'} {con c} () 

weakApp : forall {x C} -> (p : x <- C)(t : Ty (C - p))(t' t'' : Ty C) -> 
                 weakTy p t == (app t' t'') -> exists (\ a -> exists (\ b -> t == app a b))
weakApp p (var x₂) t' t'' () 
weakApp p (app t t₁) .(weakTy p t) .(weakTy p t₁) refl = t , (t₁ , refl)
weakApp p (con x₁) t' t'' ()

weakCon : forall {x c C}(p : x <- C)(t : Ty (C - p)) -> weakTy p t == con c -> t == con c
weakCon p (var v) () 
weakCon p (app l r) () 
weakCon {x} {c} p (con .c) refl = refl

weakInj : forall {x y : Nat}{C : Vars}(p : x <- C)(v v' : y <- C - p) -> weak p v == weak p v' -> v == v'
weakInj here .v' v' refl = refl
weakInj (there p) here here prf = refl
weakInj (there p) here (there v') () 
weakInj (there p) (there v) here () 
weakInj (there p) (there v) (there v') prf = cong there (weakInj p v v' (thereInj prf))

weakLeft : forall {x C}(p : x <- C)(q : x <- C - p) -> not (weak p q == p)
weakLeft here here () 
weakLeft here (there q) () 
weakLeft (there p) here ()
weakLeft (there p) (there q) prf = weakLeft p q (thereInj prf)

replaceWeakVar : forall {x y C} -> (p : x <- C)(v : y <- C - p)(t : Ty (C - p)) -> var v == replace p t (var (weak p v)) 
replaceWeakVar p v t with weak p v | inspect (weak p) v | varDiff p (weak p v)
replaceWeakVar .r v t | r | [ eq ] | same .r = exFalsum (weakLeft r v eq) 
replaceWeakVar p v t | .(weak p v₁) | [ eq ] | diff .p v₁ = cong var (weakInj p v v₁ eq) 

replaceLem : forall {x C} (v : x <- C)(t t' : Ty (C - v)) -> t == replace v t' (weakTy v t)
replaceLem v (var v') t' = replaceWeakVar v v' t'
replaceLem v (app l r) t' = cong2 app (replaceLem v l t') (replaceLem v r t')
replaceLem v (con c) t' = refl

replaceIdem : forall {x C} -> (v : x <- C) -> (t : Ty (C - v)) -> (t' : Ty C) -> replace v t t' == replace v t (weakTy v (replace v t t'))
replaceIdem p t (var v) with varDiff p v 
replaceIdem .v t (var v)          | same .v = replaceLem v t t 
replaceIdem p t (var .(weak p v)) | diff .p v = replaceWeakVar p v t
replaceIdem p t (app t' t'') = cong2 app (replaceIdem p t t') (replaceIdem p t t'')
replaceIdem p t (con c) = refl
