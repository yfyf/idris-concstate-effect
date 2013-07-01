module LockLang

import Effect.State
import Effect.Exception
import Effect.Random
import Effect.StdIO

data Ty = TyInt | TyBool | TyString | TyUnit | TyFun Ty Ty |
          TyLift Type

interpTy : Ty -> Type
interpTy TyInt       = Int
interpTy TyBool      = Bool
interpTy TyUnit      = ()
interpTy (TyFun s t) = interpTy s -> interpTy t

-- STUBS ----
data IORef : Type -> Type where
    MkIORef : a -> IORef a
data Lock = MkLock
--------------

data ResState = RState Nat -- number of times it has been locked.
                       Ty; -- Type of resource

data Resource : ResState -> Type where
   MkResource : (IORef (interpTy a)) -> Lock -> (Resource (RState n a))

using (G : Vect Ty n)

  data Env : Vect Ty n -> Type where
      Nil  : Env Nil
      (::) : interpTy a -> Env G -> Env (a :: G)

  data HasType : (i : Fin n) -> Vect Ty n -> Ty -> Type where
      stop : HasType fO (t :: G) t
      pop  : HasType k G t -> HasType (fS k) (u :: G) t

  total
  lookup : HasType i G t -> Env G -> interpTy t
  lookup stop    (x :: xs) = x
  lookup (pop k) (x :: xs) = lookup k xs

  total
  update : HasType i G t -> Env G -> interpTy t -> Env G
  update stop (x :: xs) t    = (t :: xs)
  update (pop k) (x :: xs) t = x :: (update k xs t)

  data Expr : Vect Ty n -> Ty -> Type where
       Val : interpTy a -> Expr G a
       Var : HasType i G t -> Expr G t
       Op  : (interpTy a -> interpTy b -> interpTy c) ->
              Expr G a -> Expr G b -> Expr G c

  --total
  eval : Expr G t -> Eff IO [STATE (Env G)] (interpTy t)
  eval (Val a) = return a
  eval (Var v) = do env <- get
                    Effects.return $ lookup v env
  eval (Op op a b) = do
                        a' <- eval a
                        b' <- eval b
                        return (op a' b')

  data LockL : Vect Ty n -> Vect ResState rslin -> Vect ResState rslout -> Ty -> Type where
        {}
-- OLD CODE
--       (>>=): LockL G rsin rsfoo a -> (interpTy a -> LockL G rsfoo rsout b) -> LockL G rsin rsout b
--       Return: Expr G t -> LockL G [] [] t
--       Let    : Expr G t -> LockL (t :: G) u -> LockL G u

  --total
  interp : {rsin:Vect ResState rslin} -> {rsout:Vect ResState rslout} -> LockL G rsin rsout t -> EffM m
            [STATE (Env G), STATE (rsin), STDIO]
            [STATE (Env G), STATE (rsout), STDIO]
            (interpTy t)

  --OLD CODE
  --interp (Let e b) = do a <- eval e
  --                      -- @TODO: why doesn't updateM work here?
  --                      -- updateM ((::) a)
  --                      env <- get
  --                      putM (a :: env)
  --                      val <- interp b
  --                      -- @TODO: same here
  --                      -- updateM tail
  --                      (_ :: env') <- get
  --                      putM env'
  --                      return val
  --interp (imp >>= m) = do t <- interp imp
  --                        interp (m t)
  --interp (Return exp) = eval exp

  --main : IO ()
  --main = do
  --  putStrLn "Small example:"
  --  run [LockLang.Nil, (), ()] (interp small)
  --  return ()
