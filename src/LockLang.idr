module LockLang

import Effect.State
import Effect.Exception
import Effect.Random
import Effect.StdIO
import Data.Vect

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
--data Ref = Nat
--------------

data ResState = RState Nat -- unique reference
                       Nat -- number of times it has been locked.
                       Ty; -- Type of resource

-- how to ensure resource uniqueness?
data Resource : ResState -> Type where
    MkResource : (IORef (interpTy a)) -> Lock -> (Resource (RState ind n a))

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

    -- Everything before i is unlocked
    data Unlocked : (i:Fin n) -> (xs:Vect ResState n) -> Type where
       UnlockedHere : {x:ResState} -> {xs:Vect ResState n} ->
             Unlocked fO (x :: xs)
       UnlockedThere : {i:Fin n} -> {xs:Vect ResState n} ->
             (Unlocked i xs) -> (Unlocked (fS i) ((RState ind O t) :: xs))

    data AllUnlocked : (xs: Vect ResState n) -> Type where
        AllUnlYes : AllUnlocked []
        AllUnlAlmost : {xs:Vect ResState n} -> AllUnlocked xs ->
            AllUnlocked ((RState ind O t) :: xs)

    -- Notes:
    -- * not dealing with resource creation/deletion for now, so parametrised
    --   over only one vector of resource states;
    -- * treat `Vect ResState n` as order set of `ResState`s, i.e. assume all resources
    --   are unique.
    data LockL : Vect ResState rescnt -> Ty -> Type where
        -- Read from a locked variable.
        READ : {tins:Vect ResState tin} ->
            (locked:Elem (RState ind (S k) ty) tins) ->
            LockL tins ty

        -- Write to a locked variable.
        WRITE : {tins:Vect ResState tin} -> (val:interpTy ty) ->
            (locked:Elem (RState ind (S k) ty) tins) ->
            (LockL tins TyUnit)

        -- Lock a shared variable.
        -- Must know that no lower priority items are locked, that is everything
        -- before 'i' in tins must be unlocked.
        LOCK : {tins:Vect ResState tin} ->
            (locked:Elem (RState ind k ty) tins) ->
            (priOK:Unlocked i tins) ->
            (LockL (replaceAt i (RState ind (S k) ty) tins) TyUnit)

        -- Unlock a shared variable. Must know it is locked at least once.
        -- TODO: why? it's safe to unlock an unlocked variable twice.
        UNLOCK : {tins:Vect ResState tin} ->
            (locked:Elem (RState ind (S k) ty) tins) ->
            (LockL (replaceAt i (RState ind k ty) tins) TyUnit)

        -- We allow forking only when all resources are unlocked, which is
        -- guaranteed to be safe
        FORK : {tins:Vect ResState tin} ->
            (AllUnlocked tins) ->
            (proc:LockL tins TyUnit) ->
            (LockL tins TyUnit)
