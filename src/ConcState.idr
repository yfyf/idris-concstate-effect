module ConcState

import Effects
import ConcEnv

%default total

data ResState = RState Nat -- number of times it has been locked.
                       Type; -- Type of resource

data Resource : ResState -> Type where
     resource : (l:Nat) -> (r:ty) -> (Resource (RState l ty));

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
    envWrite (Extend (resource (S k) r) rsin) fO val ElemAtIsHere =
        Extend (resource (S k) val) rsin
    envWrite (Extend r rsin) (fS i) val (ElemAtIsThere foo) =
        Extend r (envWrite rsin i val foo)

    envRead : (REnv rsin) -> (i: Fin n) ->
        (ElemAtIs i (RState (S k) ty) rsin) -> ty
    envRead (Extend (resource _ r) _) fO ElemAtIsHere = r
    envRead (Extend r rsin) (fS i) (ElemAtIsThere foo) = envRead rsin i foo

    envLock : (REnv rsin) -> (i: Fin n) ->
        (prf:ElemAtIs i (RState k ty) rsin) ->
        (REnv (Vect.replaceAt i (RState (S k) ty) rsin))
    envLock (Extend (resource l r) rsin) fO ElemAtIsHere =
        Extend (resource (S l) r) rsin
    envLock (Extend r rsin) (fS i) (ElemAtIsThere foo) =
        Extend r (envLock rsin i foo)

    envUnlock : (REnv rsin) -> (i: Fin n) ->
        (prf:ElemAtIs i (RState (S k) ty) rsin) ->
        (REnv (Vect.replaceAt i (RState k ty) rsin))
    envUnlock (Extend (resource (S l) r) rsin) fO ElemAtIsHere =
        Extend (resource l r) rsin
    envUnlock (Extend r rsin) (fS i) (ElemAtIsThere foo) =
        Extend r (envUnlock rsin i foo)

    data ConcState : (m: Type -> Type) -> Effect where
        -- Lock a shared variable.
        -- Must know that no lower priority items are locked, that is everything
        -- before 'ind' in rsin must be unlocked.
        Lock: (ind: Fin n) -> (ElemAtIs ind (RState k ty) rsin) ->
              (PrevUnlocked ind rsin) ->
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


CONCSTATE : Vect ResState n -> (Type -> Type) -> EFFECT
CONCSTATE rsin m = MkEff (REnv rsin) (ConcState m)

instance (Applicative m) => Handler (ConcState m) m where
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
    handle env (Fork prf prog) k = do
        -- works only with a `let`, no idea why
        let _ = run [env] prog
        k env ()


write: (ind: Fin n) -> (val: ty) -> (ElemAtIs ind (RState (S k) ty) rsin) ->
            Eff m [(CONCSTATE rsin m)] ()
write i val el_prf = (Write i val el_prf)

read: (ind: Fin n) -> (ElemAtIs ind (RState (S k) ty) rsin) ->
            Eff m [(CONCSTATE rsin m)] ty
read i el_prf = (Read i el_prf)

lock: (ind: Fin n) -> (ElemAtIs ind (RState k ty) rsin) ->
          (PrevUnlocked ind rsin) ->
          EffM m [CONCSTATE rsin m] [CONCSTATE (replaceAt ind (RState (S k) ty) rsin) m] ()
lock i el_prf unl_prf = (Lock i el_prf unl_prf)

unlock: (ind: Fin n) -> (ElemAtIs ind (RState (S k) ty) rsin) ->
          EffM m [CONCSTATE rsin m] [CONCSTATE (replaceAt ind (RState k ty) rsin) m] ()
unlock i el_prf = (Unlock i el_prf)

fork: {rsin: Vect ResState n} -> (prf: AllUnlocked rsin) -> (Eff m [CONCSTATE rsin m] ()) ->
            Eff m [(CONCSTATE rsin m)] ()
fork prf prog = (Fork prf prog)
