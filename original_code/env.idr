
data Ty = TyNat | TyBool | TyHandle Nat | TyUnit
        | TyLift #;

interpTy : Ty -> #;
interpTy TyNat = Nat;
interpTy TyBool = Bool;
interpTy (TyHandle h) = Fin h;
interpTy TyUnit = ();
interpTy (TyLift A) = A;

-- Return the biggest Fin we can
bound : Fin (S n);
bound {n=O} = fO;
bound {n=S k} = fS bound;

-- Generic environments, with R giving the type and iR giving the 
-- interpretation of the type.

data Env : (R:#) -> (iR:R->#) -> (xs:Vect R n) -> # where
   Empty : {iR:R->#} -> (Env R iR VNil)
 | Extend : {r:R} -> {iR:R->#} -> {xs:Vect R n} -> 
	    (res:(iR r)) -> (Env R iR xs) -> 
	    (Env R iR (VCons r xs));

envLookup : {iR:R->#} -> {xs:Vect R n} -> 
	    (i:Fin n) -> (Env R iR xs) -> (iR (vlookup i xs));
envLookup fO (Extend t env) = t;
envLookup (fS i) (Extend t env) = envLookup i env;

update : (i:Fin n) -> A -> (Vect A n) -> (Vect A n);
update fO v (VCons x xs) = VCons v xs;
update (fS i) v (VCons x xs) = VCons x (update i v xs);

updateEnv : {iR:R->#} -> {xs:Vect R n} -> {newR:R} ->
	    (Env R iR xs) ->
	    (i:Fin n) -> (iR newR) ->
	    (Env R iR (update i newR xs));
updateEnv (Extend t env) fO val = Extend val env;
updateEnv (Extend t env) (fS i) val = Extend t (updateEnv env i val);

snoc : (Vect A n) -> A -> (Vect A (S n));
snoc VNil a = VCons a VNil;
snoc (VCons x xs) a = VCons x (snoc xs a);

addEnd : {iR:R->#} -> {xs:Vect R n} ->
         (Env R iR xs) -> (r:iR ty) -> (Env R iR (snoc xs ty));
addEnd Empty i = Extend i Empty;
addEnd (Extend t env) i = Extend t (addEnd env i);

