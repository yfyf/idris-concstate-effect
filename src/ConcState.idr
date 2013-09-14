module ConcState

import Effects
import ConcEnv
import IO
import Locks
import System

%default total

data ResState = RState Nat  -- number of times it has been locked.
                       Type -- type of resource

data ElemAtIs: (i: Fin n) -> a -> Vect n a -> Type where
  ElemAtIsHere:  {x: a} -> {xs: Vect n a} -> ElemAtIs fZ x (x::xs)
  ElemAtIsThere: {i: Fin n} -> {x: a} -> {xs: Vect n a} ->
                                ElemAtIs i x xs ->
                                ElemAtIs (fS i) x (y::xs)

prevUnlocked: Fin n -> Vect n ResState -> Bool
prevUnlocked fZ (x :: xs) = True
prevUnlocked (fS k) (RState Z t :: xs) = prevUnlocked k xs
prevUnlocked _ _ = False

allUnlocked: (xs: Vect n ResState) -> Bool
allUnlocked [] = True
allUnlocked ((RState Z t) :: xs) = allUnlocked xs
allUnlocked _ = False


bump_lock: (i: Fin n) -> Vect n ResState -> Vect n ResState
bump_lock fZ (RState l t :: xs) = (RState (S l) t :: xs)
bump_lock (fS k) (x :: xs) = x :: (bump_lock k xs)

GenREnv: (ResState -> Type) -> (xs:Vect n ResState) -> Type
GenREnv interp xs = ConcEnv ResState interp xs

mutual -- mutual due to Fork using CONCSTATE
 using (rsin: Vect n ResState)

    data GenConcState: (m: Type -> Type) -> (interp: ResState -> Type) ->
                        Effect where
        -- Lock a resource.
        -- Requires a proof that all resources ordered before it are unlocked.
        Lock: (ind: Fin n) ->
              (prevUnlocked ind rsin = True) ->
              GenConcState m interp (GenREnv interp rsin)
                        (GenREnv interp (bump_lock ind rsin))
                        ()

        -- Unlock a locked resource.
        -- Requires a proof it was locked.
        Unlock: (ind: Fin n) ->
                (ElemAtIs ind (RState (S k) ty) rsin) ->
                GenConcState m interp
                        (GenREnv interp rsin)
                        (GenREnv interp (replaceAt ind (RState k ty) rsin))
                        ()

        -- Read from locked a resource.
        -- Requires a proof it was locked.
        Read: (ind: Fin n) ->
                (ElemAtIs ind (RState (S k) ty) rsin) ->
                GenConcState m interp
                    (GenREnv interp rsin)
                    (GenREnv interp rsin)
                    ty

        -- Write to a locked resource.
        -- Requires a proof it was locked and
        -- matches the type of the value being written.
        Write: (ind: Fin n) ->
                (val:ty) ->
                (ElemAtIs ind (RState (S k) ty) rsin) ->
                GenConcState m interp
                    (GenREnv interp rsin)
                    (GenREnv interp rsin)
                    ()

        -- Fork a GEN_CONCSTATE program.
        -- Requires a proof that all resources are unlocked.
        Fork: {m: Type -> Type} ->
                (allUnlocked rsin = True) ->
                (Eff m [GEN_CONCSTATE interp rsin m] ()) ->
                GenConcState m interp
                    (GenREnv interp rsin)
                    (GenREnv interp rsin)
                    ()

    GEN_CONCSTATE: (ResState -> Type) ->
                        Vect n ResState ->
                        (Type -> Type) ->
                        EFFECT
    GEN_CONCSTATE interp rsin m =
        MkEff (GenREnv interp rsin) (GenConcState m interp)

-------------- "standard" CONCSTATE effect --------------

using (rsin: Vect n ResState)
    data Resource: ResState -> Type where
         resource: (l: Nat) -> LockRef -> (Resource (RState l Int))

    REnv: (xs:Vect n ResState) -> Type
    REnv xs = GenREnv Resource xs

    ConcState: (m: Type -> Type) -> Effect
    ConcState m = GenConcState m Resource

    CONCSTATE: Vect n ResState -> (Type -> Type) -> EFFECT
    CONCSTATE rsin m = GEN_CONCSTATE Resource rsin m

    envLookup: (REnv rsin) -> (i: Fin n) ->
        (ElemAtIs i (RState (S k) ty) rsin) -> LockRef
    envLookup (Extend (resource _ r) _) fZ ElemAtIsHere = r
    envLookup (Extend r rsin) (fS i) (ElemAtIsThere foo) = envLookup rsin i foo

    envLock: (ref: LockRef) -> (REnv rsin) -> (i: Fin n) ->
        (REnv (bump_lock i rsin))
    envLock newref (Extend (resource l _) rsin) fZ =
        Extend (resource (S l) newref) rsin
    envLock newref (Extend r rsin) (fS i) =
        Extend r (envLock newref rsin i)

    envUnlock: (REnv rsin) -> (i: Fin n) ->
        (prf: ElemAtIs i (RState (S k) ty) rsin) ->
        (REnv (replaceAt i (RState k ty) rsin))
    envUnlock (Extend (resource (S l) r) rsin) fZ ElemAtIsHere =
        Extend (resource l r) rsin
    envUnlock (Extend r rsin) (fS i) (ElemAtIsThere foo) =
        Extend r (envUnlock rsin i foo)

instance Cast (Fin n) Int where
  cast fZ    = 0
  cast (fS k) = 1 + cast k

instance Cast Nat Int where
  cast Z    = 0
  cast (S k) = 1 + cast k

instance Handler (ConcState IO) IO where
    handle env (Write ind val prf) k = do
        let lockref = envLookup env ind prf
        write lockref (believe_me val)
        k env ()
    handle env (Read ind prf) k = do
        let lockref = envLookup env ind prf
        val <- read lockref
        k env (believe_me val)
    handle env (Lock ind _) k = do
        ref <- get_lock (cast ind)
        let newenv = envLock ref env ind
        k newenv ()
    handle env (Unlock ind prf) k = do
        let lockref = envLookup env ind prf
        release_lock lockref
        let newenv = envUnlock env ind prf
        k newenv ()
    handle env (Fork _ prog) k = do
        _ <- fork (run [env] prog)
        k env ()

----------------------------------------------------------

write: (ind: Fin n) -> (val: ty) -> (ElemAtIs ind (RState (S k) ty) rsin) ->
            Eff m [(CONCSTATE rsin m)] ()
write i val el_prf = (Write i val el_prf)

read: (ind: Fin n) -> (ElemAtIs ind (RState (S k) ty) rsin) ->
            Eff m [(CONCSTATE rsin m)] ty
read i el_prf = (Read i el_prf)

lock: (ind: Fin n) ->
          {auto p: prevUnlocked ind rsin = True} ->
          EffM m [CONCSTATE rsin m]
                 [CONCSTATE (bump_lock ind rsin) m] ()
lock i {p} = (Lock i p)

unlock: (ind: Fin n) -> (ElemAtIs ind (RState (S k) ty) rsin) ->
          EffM m [CONCSTATE rsin m]
                 [CONCSTATE (replaceAt ind (RState k ty) rsin) m] ()
unlock i el_prf = (Unlock i el_prf)

efork: {rsin: Vect n ResState} -> {auto p: allUnlocked rsin = True} ->
            Eff m [CONCSTATE rsin m] () -> Eff m [CONCSTATE rsin m] ()
efork prog {p} = (Fork p prog)

-- Some tests ------------------------------------------------------------

UnlockedInt : ResState
UnlockedInt = RState Z Int

bump_elem: {rsin: Vect n ResState} -> {i: Fin n} ->
    ElemAtIs i (RState k Int) rsin ->
    ElemAtIs i (RState (S k) Int) (bump_lock i rsin)
bump_elem ElemAtIsHere = ElemAtIsHere
bump_elem (ElemAtIsThere ys) = ElemAtIsThere (bump_elem ys)

lckPreserve_prf: {rsin: Vect n ResState} ->
    ElemAtIs i (RState q Int) rsin ->
    replaceAt i (RState q Int) (bump_lock i rsin) = rsin
lckPreserve_prf ElemAtIsHere = refl
lckPreserve_prf (ElemAtIsThere ys) = cong (lckPreserve_prf ys)

concStateCng_prf: {rsin: Vect n ResState} ->
            (replaceAt i (RState q Int) (bump_lock i rsin) = rsin) -> (
            (CONCSTATE (replaceAt i (RState q Int) (bump_lock i rsin)) IO) =
                (CONCSTATE rsin IO))
concStateCng_prf p = ?concStateCng_prf

ConcState.concStateCng_prf1 = proof {
  intros;
  rewrite p;
  trivial;
}

bump_nth_val: {rsin: Vect n ResState} -> (i: Fin n) ->
    {auto p: prevUnlocked i rsin = True} ->
    (prf: ElemAtIs i (RState q Int) rsin) ->
    Eff IO [CONCSTATE rsin IO] ()
bump_nth_val i prf = do
    lock i
    val <- read i (bump_elem prf)
    write i (val + 1) (bump_elem prf)
    rewrite (sym (concStateCng_prf (lckPreserve_prf prf))) in
        unlock i (bump_elem prf)

bump_first_val: {rsin: Vect k ResState} ->
    Eff IO [CONCSTATE (RState l Int :: rsin) IO] ()
bump_first_val = bump_nth_val 0 ElemAtIsHere

%assert_total
wait_until_equals: {rsin: Vect k ResState} ->
                   Int ->
                   Eff IO [CONCSTATE (UnlockedInt :: rsin) IO] Int
wait_until_equals val = do
    lock fZ
    res <- read fZ ElemAtIsHere
    unlock fZ ElemAtIsHere
    if val == res
        then return val
        else wait_until_equals val


increment_first_val: {rsin: Vect k ResState} ->
    {auto p: allUnlocked rsin = True} ->
    (times: Nat) ->
    Eff IO [CONCSTATE (UnlockedInt :: rsin) IO] Int
increment_first_val times = do
    _ <- mapE efork $ replicate times bump_first_val
    wait_until_equals (cast times)

%assert_total
Main.main: IO ()
Main.main = do
    [lockref] <- init_locks [0]
    let res0 = resource 0 lockref
    val <- run [Extend res0 Empty] $ increment_first_val 1000
    putStr "The result is: "
    print val
