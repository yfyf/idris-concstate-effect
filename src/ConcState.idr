module ConcState

import Effects
import Data.Vect

data ResState = RState Nat -- number of times it has been locked.
                       Type; -- Type of resource

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
    data ConcState: Effect where
        -- Lock a shared variable.
        -- Must know that no lower priority items are locked, that is everything
        -- before 'ind' in rsin must be unlocked.
        Lock: (ind: Fin n) -> (ElemAtIs ind (RState k ty) rsin) ->
              (PrevUnlocked ind tins) ->
              ConcState (LockLift rsin)
                        (LockLift (Vect.replaceAt ind (RState (S k) ty) rsin))
                        ty
        -- Unlock a shared variable. Must know it is locked at least once.
        -- [TODO: why? it's safe to unlock an unlocked variable twice.]
        Unlock: (ind: Fin n) -> (ElemAtIs ind (RState (S k) ty) rsin) ->
              ConcState (LockLift rsin)
                        (LockLift (Vect.replaceAt ind (RState k ty) rsin))
                        ty
        -- Read from a locked variable.
        Read: (ind: Fin n) -> (ElemAtIs ind (RState k ty) rsin) ->
            ConcState (LockLift rsin) (LockLift rsin) ty
        -- Write to a locked variable.
        Write: (ind: Fin n) -> (val:ty) -> (ElemAtIs ind (RState (S k) ty) rsin) ->
            ConcState (LockLift rsin) (LockLift rsin) ()
        -- We allow forking only when all resources are unlocked, which is
        -- guaranteed to be safe
        -- [TODO: How do I express this better?]
        Fork : (AllUnlocked rsin) ->
            ConcState (LockLift rsin) (LockLift rsin) (Thread rsin)


instance Handler ConcState IO where
    {}
