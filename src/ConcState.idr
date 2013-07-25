module ConcState

import Effects
import Data.Vect
import ConcEnv

data ResState = RState Nat -- number of times it has been locked.
                       Type; -- Type of resource

data Resource : ResState -> Type where
     resource : (l:Nat) -> (r:ty) -> (Resource (RState l ty));

data ResEnv : (xs:Vect ResState n) -> Type where
   Empty : (ResEnv Vect.Nil)
   Extend : {xs:Vect ResState n} -> (r:t) -> (k:Nat) -> (ResEnv xs) ->
        (ResEnv (Vect.(::) (RState k t) xs))

REnv : (xs:Vect ResState n) -> Type
REnv xs = ConcEnv ResState Resource xs

data LockLift: (Vect ResState n) -> Type where
    MkLockLift: (xs:Vect ResState n) -> LockLift xs

data ElemAtIs : (i: Fin n) -> a -> Vect a n -> Type where
  ElemAtIsHere : {x: a} -> {xs : Vect a n} -> ElemAtIs fO x (x::xs)
  ElemAtIsThere : {i : Fin n} -> {x: a} -> {xs : Vect a n} ->
                    ElemAtIs i x xs -> ElemAtIs (fS i) x (y::xs)

data PrevUnlocked : (i: Fin n) -> (rsin: Vect ResState n) -> Type where
   UnlockedHere : {x:ResState} -> {xs:Vect ResState n} ->
                     PrevUnlocked fO (x :: xs)
   UnlockedThere : {i:Fin n} -> {xs:Vect ResState n} ->
                     (PrevUnlocked i xs) -> (PrevUnlocked (fS i) ((RState O t) :: xs))

data AllUnlocked : (xs: Vect ResState n) -> Type where
    AllUnlYes : AllUnlocked []
    AllUnlAlmost : {xs:Vect ResState n} -> AllUnlocked xs ->
        AllUnlocked ((RState O t) :: xs)

using (rsin: Vect ResState n)

    envWrite : (REnv rsin) -> (i: Fin n) -> (val: ty) ->
        (ElemAtIs i (RState (S k) ty) rsin) -> (REnv rsin)
    envWrite (Extend (resource l r) rsin) f0 val ElemtAtIsHere ?=
        Extend (resource l val) rsin
    envWrite (Extend r rsin) (fS i) val (ElemAtIsThere foo) =
        Extend r (envWrite rsin i val foo)

    envRead : (REnv rsin) -> (i: Fin n) ->
        (ElemAtIs i (RState (S k) ty) rsin) -> ty
    envRead (Extend (resource _ r) _) f0 ElemtAtIsHere ?= r
    envRead (Extend r rsin) (fS i) (ElemAtIsThere foo) = envRead rsin i foo

    envLock : (REnv rsin) -> (i: Fin n) ->
        (prf:ElemAtIs i (RState k ty) rsin) ->
        (REnv (Vect.replaceAt i (RState (S k) ty) rsin))
    envLock (Extend (resource l r) rsin) f0 ElemtAtIsHere ?=
        Extend (resource (S l) r) rsin
    envLock (Extend r rsin) (fS i) (ElemAtIsThere foo) =
        Extend r (envLock rsin i foo)

    envUnlock : (REnv rsin) -> (i: Fin n) ->
        (prf:ElemAtIs i (RState (S k) ty) rsin) ->
        (REnv (Vect.replaceAt i (RState k ty) rsin))
    envUnlock (Extend (resource (S l) r) rsin) f0 ElemtAtIsHere ?=
        Extend (resource l r) rsin
    envUnlock (Extend r rsin) (fS i) (ElemAtIsThere foo) =
        Extend r (envUnlock rsin i foo)

    data ConcState : (m: Type -> Type) -> Effect where
        -- Lock a shared variable.
        -- Must know that no lower priority items are locked, that is everything
        -- before 'ind' in rsin must be unlocked.
        Lock: (ind: Fin n) -> (ElemAtIs ind (RState k ty) rsin) ->
              (PrevUnlocked ind tins) ->
              ConcState m (REnv rsin)
                        (REnv (Vect.replaceAt ind (RState (S k) ty) rsin))
                        ()
        -- Unlock a shared variable. Must know it is locked at least once.
        -- [TODO: why? it's safe to unlock an unlocked variable twice.]
        Unlock: (ind: Fin n) -> (ElemAtIs ind (RState (S k) ty) rsin) ->
              ConcState m (REnv rsin)
                        (REnv (Vect.replaceAt ind (RState k ty) rsin))
                        ()
        -- Read from a locked variable.
        Read: (ind: Fin n) -> (ElemAtIs ind (RState (S k) ty) rsin) ->
            ConcState m (REnv rsin) (REnv rsin) ty
        -- Write to a locked variable.
        Write: (ind: Fin n) ->
                (val:ty) -> (ElemAtIs ind (RState (S k) ty) rsin) ->
                ConcState m (REnv rsin) (REnv rsin) ()

        -- We allow forking only when all resources are unlocked, which is
        -- guaranteed to be safe
        Fork : {m: Type -> Type} -> (AllUnlocked rsin) ->
                (Eff m [MkEff (REnv rsin) (ConcState m)] ()) ->
                ConcState m (REnv rsin) (REnv rsin) ()


    instance Handler (ConcState m) m where
        handle env (Write ind val prf) k = do
            let newenv = envWrite env ind val prf
            k newenv ()
        handle env (Read ind prf) k = do
            let val = envRead env ind prf
            k env val
        handle env (Lock ind prf_elem prf_unlocked) k = do
            let newenv = envLock env ind prf_elem
            k newenv ()
        handle env (Unlock ind prf) k = do
            let newenv = envUnlock env ind prf
            k newenv ()
        handle env (Fork prf eff) k = do
            let newenv = env
            k newenv ()
