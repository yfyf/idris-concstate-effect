module Main

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

  infix 5 :=

  data LockL    : Vect Ty n -> Ty -> Type where
       Let    : Expr G t -> LockL (t :: G) u -> LockL G u
       (:=)   : HasType i G t -> Expr G t -> LockL G t
       Print  : Expr G TyInt -> LockL G TyUnit
       For    : LockL G i -> -- initialise
                LockL G TyBool -> -- test
                LockL G x -> -- increment
                LockL G t -> -- body
                LockL G TyUnit
       (>>=)  : LockL G a -> (interpTy a -> LockL G b) -> LockL G b
       Return : Expr G t -> LockL G t


  --total
  interp : LockL G t -> Eff IO [STATE (Env G), STDIO] (interpTy t)
  interp (Print e) = do val <- eval e
                        putStrLn (show val)
  interp (v := e) = do val <- eval e
                       State.update (\env => Main.update v env val)
                       return val
  interp (Let e b) = do a <- eval e
                        -- @TODO: why doesn't updateM work here?
                        -- updateM ((::) a)
                        env <- get
                        putM (a :: env)
                        val <- interp b
                        -- @TODO: same here
                        -- updateM tail
                        (_ :: env') <- get
                        putM env'
                        return val
  interp (imp >>= m) = do t <- interp imp
                          interp (m t)
  interp (Return exp) = eval exp
  interp (For i test inc b) = do
                            t <- interp i
                            bool <- interp test
                            if bool then do
                                        interp b
                                        interp (For inc test inc b)
                                else return ()

  small : LockL [] TyUnit
  small = Let (Val 42) (do
              Print (Var stop)
              stop := Op (+) (Var stop) (Val 1)
              Print $ Var stop)

  decent : LockL [] TyUnit
  decent = Let (Val 0) (
            For (stop := (Val 1))
                (Return (Op (<=) (Var stop) (Val 3)))
                (stop := (Op (+) (Var stop) (Val 1)))
                (Print (Var stop)))

  main : IO ()
  main = do
    putStrLn "Small example:"
    run [Main.Nil, (), ()] (interp small)
    putStrLn "Let's count to 3:"
    run [Main.Nil, (), ()] (interp decent)
    return ()
