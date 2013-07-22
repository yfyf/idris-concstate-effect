module ConcEnv

-- Return the biggest Fin we can
bound : Fin (S n)
bound {n=O} = fO
bound {n=S k} = fS bound

-- Generic environments, with t giving the type and iR giving the
-- interpretation of the type.

data Env : (t: Type) -> (iR: t -> Type) -> (xs:Vect t n) -> Type where
   Empty : {iR: t -> Type} -> (Env t iR Vect.Nil)
   Extend : {r:t} -> {iR:t->Type} -> {xs:Vect t n} ->
        (res:(iR r)) -> (Env t iR xs) ->
        (Env t iR (Vect.(::) r xs))

envLookup : {iR:t->Type} -> {xs:Vect t n} ->
        (i:Fin n) -> (Env t iR xs) -> (iR (index i xs))
envLookup fO (Extend t env) = t
envLookup (fS i) (Extend t env) = envLookup i env

updateEnv : {iR:t->Type} -> {xs:Vect t n} -> {newR:t} ->
        (Env t iR xs) ->
        (i:Fin n) -> (iR newR) ->
        (Env t iR (replaceAt i newR xs))
updateEnv (Extend t env) fO val = Extend val env
updateEnv (Extend t env) (fS i) val = Extend t (updateEnv env i val)

-- rev cons
snoc : (Vect a n) -> a -> (Vect a (S n))
snoc [] a =  a :: []
snoc (x :: xs) a = x :: (snoc xs a)

addEnd : {iR:t->Type} -> {xs:Vect t n} ->
         (Env t iR xs) -> (r:iR ty) -> (Env t iR (snoc xs ty))
addEnd Empty i = Extend i Empty
addEnd (Extend t env) i = Extend t (addEnd env i)

