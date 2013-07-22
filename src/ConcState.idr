module ConcState

import Effects
import Data.Vect
import ConcEnv

data ResState = RState Nat -- number of times it has been locked.
                       Type; -- Type of resource

-- not used now -----
data Resource : ResState -> Type where
     resource : (l:Nat) -> (r:ty) -> (Resource (RState l ty));
---------------------

data ResEnv : (xs:Vect ResState n) -> Type where
   Empty : (ResEnv Vect.Nil)
   Extend : {xs:Vect ResState n} -> (r:t) -> (k:Nat) -> (ResEnv xs) ->
        (ResEnv (Vect.(::) (RState k t) xs))

REnv : (xs:Vect ResState n) -> Type
REnv xs = ResEnv xs

data Thread: (Vect ResState n) -> Type where
    MkThread: (xs: Vect ResState n) -> Thread xs

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
    envWrite (Extend r k rsin) f0 val ElemtAtIsHere           ?= Extend val k rsin
    envWrite (Extend r k rsin) (fS i) val (ElemAtIsThere foo)  = Extend r k (envWrite rsin i val foo)

    envRead : (REnv rsin) -> (i: Fin n) ->
        (ElemAtIs i (RState (S k) ty) rsin) -> ty
    envRead (Extend r k rsin) f0 ElemtAtIsHere           ?= r
    envRead (Extend r k rsin) (fS i) (ElemAtIsThere foo)  = envRead rsin i foo

    envLock : (REnv rsin) -> (i: Fin n) ->
        (prf:ElemAtIs i (RState k ty) rsin) ->
        (REnv (Vect.replaceAt i (RState (S k) ty) rsin))
    envLock (Extend val k rsin) f0 ElemtAtIsHere          ?= Extend val (S k) rsin
    envLock (Extend val k rsin) (fS i) (ElemAtIsThere foo) =
        Extend val k (envLock rsin i foo)

    envUnlock : (REnv rsin) -> (i: Fin n) ->
        (prf:ElemAtIs i (RState (S k) ty) rsin) ->
        (REnv (Vect.replaceAt i (RState k ty) rsin))
    envUnlock (Extend val (S k) rsin) f0 ElemtAtIsHere ?= Extend val k rsin
    envUnlock (Extend val k rsin) (fS i) (ElemAtIsThere foo) =
        Extend val k (envUnlock rsin i foo)

    data ConcState: Effect where
        -- Lock a shared variable.
        -- Must know that no lower priority items are locked, that is everything
        -- before 'ind' in rsin must be unlocked.
        Lock: (ind: Fin n) -> (ElemAtIs ind (RState k ty) rsin) ->
              (PrevUnlocked ind tins) ->
              ConcState (ResEnv rsin)
                        (ResEnv (Vect.replaceAt ind (RState (S k) ty) rsin))
                        ()
        -- Unlock a shared variable. Must know it is locked at least once.
        -- [TODO: why? it's safe to unlock an unlocked variable twice.]
        Unlock: (ind: Fin n) -> (ElemAtIs ind (RState (S k) ty) rsin) ->
              ConcState (ResEnv rsin)
                        (ResEnv (Vect.replaceAt ind (RState k ty) rsin))
                        ()
        -- Read from a locked variable.
        Read: (ind: Fin n) -> (ElemAtIs ind (RState (S k) ty) rsin) ->
            ConcState (ResEnv rsin) (ResEnv rsin) ty
        -- Write to a locked variable.
        Write: (ind: Fin n) -> (val:ty) -> (ElemAtIs ind (RState (S k) ty) rsin) ->
            ConcState (ResEnv rsin) (ResEnv rsin) ()
        -- We allow forking only when all resources are unlocked, which is
        -- guaranteed to be safe
        -- [TODO: How do I express this better?]
--        Fork : (AllUnlocked rsin) -> (Eff m [CONC_STATE (ResEnv rsin)] ()) ->
        Fork : (AllUnlocked rsin) ->
            ConcState (ResEnv rsin) (ResEnv rsin) (Thread rsin)

    instance Handler ConcState m where
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

CONC_STATE : Type -> EFFECT
CONC_STATE t = MkEff t ConcState
