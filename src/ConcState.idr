module ConcState

import Effects
import ConcEnv
import IO

%default total

data ResState = RState Nat -- number of times it has been locked.
                       Type; -- Type of resource

data Resource : ResState -> Type where
     resource : (l:Nat) -> (r:ty) -> (Resource (RState l ty));

REnv : (xs:Vect n ResState) -> Type
REnv xs = ConcEnv ResState Resource xs

data LockLift: (Vect n ResState) -> Type where
    MkLockLift: (xs:Vect n ResState) -> LockLift xs

data ElemAtIs : (i: Fin n) -> a -> Vect n a -> Type where
  ElemAtIsHere : {x: a} -> {xs : Vect n a} -> ElemAtIs fZ x (x::xs)
  ElemAtIsThere : {i : Fin n} -> {x: a} -> {xs : Vect n a} ->
                    ElemAtIs i x xs -> ElemAtIs (fS i) x (y::xs)

data PrevUnlocked : (i: Fin n) -> (rsin: Vect n ResState) -> Type where
   UnlockedHere : {x:ResState} -> {xs:Vect n ResState} ->
                     PrevUnlocked fZ (x :: xs)
   UnlockedThere : {i:Fin n} -> {xs:Vect n ResState} ->
                     (PrevUnlocked i xs) -> (PrevUnlocked (fS i) ((RState Z t) :: xs))

data AllUnlocked : (xs: Vect n ResState) -> Type where
    AllUnlYes : AllUnlocked []
    AllUnlAlmost : {xs:Vect n ResState} -> AllUnlocked xs ->
        AllUnlocked ((RState Z t) :: xs)

using (rsin: Vect n ResState)

    envWrite : (REnv rsin) -> (i: Fin n) -> (val: ty) ->
        (ElemAtIs i (RState (S k) ty) rsin) -> (REnv rsin)
    envWrite (Extend (resource (S k) r) rsin) fZ val ElemAtIsHere =
        Extend (resource (S k) val) rsin
    envWrite (Extend r rsin) (fS i) val (ElemAtIsThere foo) =
        Extend r (envWrite rsin i val foo)

    envRead : (REnv rsin) -> (i: Fin n) ->
        (ElemAtIs i (RState (S k) ty) rsin) -> ty
    envRead (Extend (resource _ r) _) fZ ElemAtIsHere = r
    envRead (Extend r rsin) (fS i) (ElemAtIsThere foo) = envRead rsin i foo

    envLock : (REnv rsin) -> (i: Fin n) ->
        (prf:ElemAtIs i (RState k ty) rsin) ->
        (REnv (Vect.replaceAt i (RState (S k) ty) rsin))
    envLock (Extend (resource l r) rsin) fZ ElemAtIsHere =
        Extend (resource (S l) r) rsin
    envLock (Extend r rsin) (fS i) (ElemAtIsThere foo) =
        Extend r (envLock rsin i foo)

    envUnlock : (REnv rsin) -> (i: Fin n) ->
        (prf:ElemAtIs i (RState (S k) ty) rsin) ->
        (REnv (Vect.replaceAt i (RState k ty) rsin))
    envUnlock (Extend (resource (S l) r) rsin) fZ ElemAtIsHere =
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


CONCSTATE : Vect n ResState -> (Type -> Type) -> EFFECT
CONCSTATE rsin m = MkEff (REnv rsin) (ConcState m)

instance Handler (ConcState IO) IO where
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
        let _ = fork (run [env] prog)
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

ffork: {rsin: Vect n ResState} -> (prf: AllUnlocked rsin) ->
            Eff m [CONCSTATE rsin m] () -> Eff m [CONCSTATE rsin m] ()
ffork prf prog = (Fork prf prog)

-----------------------------------------

%assert_total
bump_first_val :  {rsin: Vect k ResState} ->
    Eff IO [(CONCSTATE ((RState l Nat) :: rsin) IO)] Nat
bump_first_val = do
    lock fZ ElemAtIsHere UnlockedHere
    val <- read fZ ElemAtIsHere
    --putStrLn ("val in thread:" ++ (show val))
    write fZ (val + 1) ElemAtIsHere
    val' <- read fZ ElemAtIsHere
    --putStrLn ("val' in thread:" ++ (show val'))
    unlock fZ ElemAtIsHere
    return val'

%assert_total
bump_single_val : Eff IO [CONCSTATE [(RState Z Nat)] IO] Nat
bump_single_val = do
    lock fZ ElemAtIsHere UnlockedHere
    val <- read fZ ElemAtIsHere
    --putStrLn ("Bump single val initial " ++ (show val))
    write fZ (val + 1) ElemAtIsHere
    val' <- read fZ ElemAtIsHere
    --putStrLn ("Bump single val final " ++ (show val'))
    unlock fZ ElemAtIsHere
    ffork (AllUnlAlmost AllUnlYes) (do _ <- bump_first_val; return ())
    lock fZ ElemAtIsHere UnlockedHere
    rez <- read fZ ElemAtIsHere
    --putStrLn ("Result: " ++ (show rez))
    unlock fZ ElemAtIsHere
    return rez

%assert_total
Main.main : IO ()
Main.main = do
    val <- run [(Extend (resource Z Z) Empty)] bump_single_val
    print val
