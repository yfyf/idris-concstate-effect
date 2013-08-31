module ConcEnv

-- Generic environments, with t giving the type and iR giving the
-- interpretation of the type.

data ConcEnv: (t: Type) -> (iR: t -> Type) -> (xs: Vect n t) -> Type where
   Empty:  {iR: t -> Type} -> ConcEnv t iR []
   Extend: {r: t} -> {iR: t -> Type} -> {xs: Vect n t} ->
                     (res: (iR r)) -> ConcEnv t iR xs ->
                     ConcEnv t iR (r::xs)

