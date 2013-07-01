include "vect.idr";
include "env.idr";
include "member.idr";
include "locking.idr";

-- Carry the resource, and the lock associated with the resource.

data Resource : ResState -> # where
     resource : (IORef (interpTy a)) -> Lock -> (Resource (RState n a));

REnv : (xs:Vect ResState n) -> #;
REnv xs = Env ResState Resource xs;

getRef : (Resource r) -> (IORef (interpTy (getTy r)));
getRef (resource ref l) = ref;

getLock : (Resource r) -> Lock;
getLock (resource ref l) = l;

rlookup : {xs:Vect ResState rn} -> (p:ElemIs i (RState k ty) xs) ->
	  (REnv xs) ->
	  (IORef (interpTy ty));
rlookup first (Extend (resource v l) env) = v;
rlookup (later p) (Extend v env) = rlookup p env;

llookup : {xs:Vect ResState ln} -> (i:Fin ln) -> (REnv xs) -> Lock;
llookup i env = getLock (envLookup i env);

-- These are no-ops to convince the typechecker that the environment has
-- the right lock state.

lockEnv : {i:Fin ln} -> {xs:Vect ResState ln} ->
	  (ElemIs i (RState k ty) xs) ->
	  (REnv xs) ->
	  (REnv (update i (RState (S k) ty) xs));
lockEnv first (Extend (resource ref l) env) = Extend (resource ref l) env;
lockEnv (later p) (Extend r env) = Extend r (lockEnv p env);

unlockEnv : {i:Fin un} -> {xs:Vect ResState un} ->
	    (ElemIs i (RState (S k) ty) xs) ->
	    (REnv xs) ->
	    (REnv (update i (RState k ty) xs));
unlockEnv first (Extend (resource ref l) env) = Extend (resource ref l) env;
unlockEnv (later p) (Extend r env) = Extend r (unlockEnv p env);

showNat : Nat -> String;
showNat O = "O";
showNat (S k) = "s" ++ (showNat k);

data Lang : (Vect ResState tin)->(Vect ResState tout)->Ty-># where

-- Read from a shared variable. Must have the lock.

   READ : {tins:Vect ResState tin} ->
	  {i:Fin tin} ->
	  (locked:ElemIs i (RState (S k) ty) tins) ->
	  (Lang tins tins ty)

-- Write to a shared variable. Must have the lock.

 | WRITE : {tins:Vect ResState tin} ->
           {i:Fin tin} -> (val:interpTy ty) ->
	   (locked:ElemIs i (RState (S k) ty) tins) ->
	   (Lang tins tins TyUnit)

-- Lock a shared variable.
-- Must know that no lower priority items are locked, that is everything
-- before 'i' in tins must be unlocked.

 | LOCK : {tins:Vect ResState tin} ->
	  {i:Fin tin} ->
	  (locked:ElemIs i (RState k ty) tins) ->
	  (priOK:Unlocked i tins) ->
	  (Lang tins (update i (RState (S k) ty) tins) TyUnit)

-- Unlock a shared variable. Must know it is locked at least once.

 | UNLOCK : {tins:Vect ResState tin} ->
	    {i:Fin tin} ->
	    (locked:ElemIs i (RState (S k) ty) tins) ->
	    (Lang tins (update i (RState k ty) tins) TyUnit)

-- Create a new shared resource, and put it at the end of the list.
-- Leave it out for now until we work out the best way to represent handles.
{-
 | CREATE : {tins:Vect ResState tin} ->
	    (val:interpTy ty) ->
	    (Lang tins (snoc tins (RState O ty)) (TyHandle (S tin)))
-}

-- Some control structures; loop n times, and fork a new process

 | LOOP : {tins:Vect ResState tin} ->
	  (count:Nat) -> (body:Lang tins tins TyUnit) ->
	  (Lang tins tins TyUnit)
 | FORK : {tins:Vect ResState tin} ->
	  (AllUnlocked tins) ->
	  (proc:Lang tins tins TyUnit) ->
	  (Lang tins tins TyUnit)

-- The rest are useful for any language; dynamic checking, IO action and
-- binding variables.

 | CHECK : {tins:Vect ResState tin} -> {touts: Vect ResState tout} ->
	   (Maybe a) ->
	   (ifJ:a -> (Lang tins touts ty)) ->
	   (ifN:Lang tins touts ty) ->
	   (Lang tins touts ty)
 | CHOOSE : {tins:Vect ResState tin} -> {touts: Vect ResState tout} ->
	    (Either a b) ->
	    (ifLeft : a -> (Lang tins touts ty)) ->
	    (ifRight : b -> (Lang tins touts ty)) ->
	    (Lang tins touts ty)
 | ACTION : {tins:Vect ResState tin} ->
            (IO ()) -> (Lang tins tins TyUnit)
 | RETURN : {tins:Vect ResState tin} ->
	    (val:interpTy ty) -> (Lang tins tins ty)
 | BIND : {tins:Vect ResState tin} ->
	  {ts1:Vect ResState ts1n} ->
	  {touts:Vect ResState tout} ->
	  (code:Lang tins ts1 ty)->
	  (k:(interpTy ty)->(Lang ts1 touts tyout))->
	  (Lang tins touts tyout);

data I A B = MkPair A B;

fst : (I A B) -> A;
fst (MkPair a b) = a;

snd : (I A B) -> B;
snd (MkPair a b) = b;

interp : {ty:Vect ResState tin} -> {tyo:Vect ResState tout} -> {T:Ty} ->
         (REnv ty) -> (Lang ty tyo T) -> (IO (I (REnv tyo) (interpTy T)));

interpBind : {tyin:Vect ResState tin} -> {tyout:Vect ResState tout} ->
	     (I (REnv tyin) A) -> (A -> (Lang tyin tyout B)) ->
	     (IO (I (REnv tyout) (interpTy B)));
interpBind (MkPair env val) k = interp env (k val);

interpLoop : {tyin:Vect ResState tin} ->
	     (REnv tyin) ->
	     (count:Nat) -> (body:Lang tyin tyin TyUnit) ->
	     (IO (I (REnv tyin) ()));
interpLoop env O code = return (MkPair env II);
interpLoop env (S k) code = do { ires <- interp env code;
				 interpLoop (fst ires) k code;
			       };

interpCheck : {tyin:Vect ResState tin} -> {tyout:Vect ResState tout} ->
	      (env:REnv tyin) -> (Maybe a) ->
	      (ifJ : a -> (Lang tyin tyout ty)) ->
	      (ifN : Lang tyin tyout ty) ->
	      (IO (I (REnv tyout) (interpTy ty)));
interpCheck env Nothing ifJ ifN = interp env ifN;
interpCheck env (Just a) ifJ ifN = interp env (ifJ a);

interpChoose : {tyin:Vect ResState tin} -> {tyout:Vect ResState tout} ->
	       (env:REnv tyin) -> (Either a b) ->
	       (ifL : a -> (Lang tyin tyout ty)) ->
	       (ifL : b -> (Lang tyin tyout ty)) ->
	       (IO (I (REnv tyout) (interpTy ty)));
interpChoose env (Left a) ifL ifR = interp env (ifL a);
interpChoose env (Right b) ifL ifR = interp env (ifR b);

interp env (READ p) = do { val <- readIORef (rlookup p env);
			       return (MkPair env val);
			     };
interp env (WRITE v p) = do { val <- writeIORef (rlookup p env) v;
				  return (MkPair env II); };
interp env (LOCK {i} p pri) = do { lock (llookup i env);
			           return (MkPair (lockEnv p env) II); };
interp env (UNLOCK {i} p) = do { unlock (llookup i env);
			         return (MkPair (unlockEnv p env) II); };
interp env (ACTION io) = do { io;
			      return (MkPair env II); };
interp env (RETURN val) = return (MkPair env val);
interp env (CHECK m j n) = interpCheck env m j n;
interp env (CHOOSE m l r) = interpChoose env m l r;
interp env (LOOP n body) = interpLoop env n body;
-- Interpret the given process in a new thread, and carry on.
interp env (FORK _ proc)
       = do { fork (do { f <- interp env proc; return II; });
	      return (MkPair env II);
	    };
-- interp {tin} env CREATE = return (MkPair (addEnd env O) (bound {n=tin}));
interp env (BIND code k) = do { coderes <- interp env code;
				interpBind coderes k; };

