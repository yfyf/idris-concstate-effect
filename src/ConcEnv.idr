module ConcEnv

-- Return the biggest Fin we can
bound : Fin (S n)
bound {n=O} = fO
bound {n=S k} = fS bound

-- Generic environments, with t giving the type and iR giving the
-- interpretation of the type.

data ConcEnv : (t: Type) -> (iR: t -> Type) -> (xs:Vect t n) -> Type where
   Empty : {iR: t -> Type} -> (ConcEnv t iR Vect.Nil)
   Extend : {r:t} -> {iR:t->Type} -> {xs:Vect t n} ->
        (res:(iR r)) -> (ConcEnv t iR xs) ->
        (ConcEnv t iR (Vect.(::) r xs))

envLookup : {iR:t->Type} -> {xs:Vect t n} ->
        (i:Fin n) -> (ConcEnv t iR xs) -> (iR (index i xs))
envLookup fO (Extend t env) = t
envLookup (fS i) (Extend t env) = envLookup i env

updateConcEnv : {iR:t->Type} -> {xs:Vect t n} -> {newR:t} ->
        (ConcEnv t iR xs) ->
        (i:Fin n) -> (iR newR) ->
        (ConcEnv t iR (replaceAt i newR xs))
updateConcEnv (Extend t env) fO val = Extend val env
updateConcEnv (Extend t env) (fS i) val = Extend t (updateConcEnv env i val)

-- rev cons
snoc : (Vect a n) -> a -> (Vect a (S n))
snoc [] a =  a :: []
snoc (x :: xs) a = x :: (snoc xs a)

addEnd : {iR:t->Type} -> {xs:Vect t n} ->
         (ConcEnv t iR xs) -> (r:iR ty) -> (ConcEnv t iR (snoc xs ty))
addEnd Empty i = Extend i Empty
addEnd (Extend t env) i = Extend t (addEnd env i)

