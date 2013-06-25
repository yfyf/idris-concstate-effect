include "vect.idr";
include "env.idr";
include "concdsl_dl.idr";

%latex {
       Nat = "\\Nat", O = "\\Z", S = "\\suc",
       fO = "\\fz", fS = "\\fs", 
       VNil = "\\Vnil", VCons = "\\Vcons",
       II = "()",
       IO = "\\IO"
}

showInt : Int -> String;

data Account = MkAcc Int;

accounts : (n:Nat) -> (Vect ResState n);
accounts O = VNil;
accounts (S k) = VCons (RState O (TyLift Account)) (accounts k);

mkAccounts : (n:Nat) -> (IO (REnv (accounts n)));
mkAccounts O = return Empty;
mkAccounts (S k) = do { kaccs <- mkAccounts k;
			aref <- newIORef (MkAcc 10000);
			alock <- newLock 1;
			return (Extend (resource aref alock) kaccs);
		      };

showAcc : Account -> String;
showAcc (MkAcc i) = "£" ++ (showInt i);

decrease : Int -> Account -> Account;
decrease sum (MkAcc v) = MkAcc (v-sum);

increase : Int -> Account -> Account;
increase sum (MkAcc v) = MkAcc (v+sum);

eq_resp_VCons : {xs,ys:Vect A n} ->
		(xs=ys) -> ((VCons x xs) = (VCons x ys));
eq_resp_VCons (refl xs) = refl (VCons _ xs);

revert : {i:Fin n} -> {xs:Vect A n} -> 
         (ElemIs i x xs) -> ((update i x (update i y xs))=xs);
revert first = refl _;
revert (later p) = eq_resp_VCons (revert p);

revertLock : {tins:Vect ResState tin} ->
	     {i:Fin tin} ->
	     (ElemIs i x tins) ->
	     (Lang (update i y tins) (update i x (update i y tins)) ty) ->
	     (Lang (update i y tins) tins ty);
revertLock {i} {y} {tins} {ty} p l 
        = rewrite {A=\ ts . Lang (update i y tins) ts ty} l (revert p);

-- if i<j, updating index i does not affect index j
stillElem : {i,j:Fin n} -> {xs:Vect A n} ->
	    (LTFin i j) -> (ElemIs i x xs) -> (ElemIs i x (update j y xs));
stillElem ltO first = first;
stillElem (ltS p) (later q) = later (stillElem p q);

updatedElemIs : {xs:Vect A n} -> 
		{i:Fin n} ->
	        (ElemIs i y (update i y xs));
updatedElemIs {i=fO} {xs=VCons x xs} = first;
updatedElemIs {i=fS k} {xs=VCons x xs} = later updatedElemIs;

updated2ElemIs : {xs:Vect A n} -> {x,w:A} ->  
	 	 {i,j:Fin n} -> (LTFin i j) ->
	         (ElemIs j x (update i w (update j x xs)));
updated2ElemIs ltO {xs=VCons x xs} = later updatedElemIs; 
updated2ElemIs (ltS p) {xs=VCons x xs} = later (updated2ElemIs p);

-- Take two locks, do the body, then unlock.
lockTwo : {tins:Vect ResState tin} ->
	  {r1,r2:Fin tin} -> 
	  (LTFin r1 r2) ->
	  (ElemIs r1 (RState k1 ty1) tins) ->
	  (ElemIs r2 (RState k2 ty2) tins) ->
	  (Unlocked r2 tins) ->
	  (body:Lang (update r1 (RState (S k1) ty1) 
			(update r2 (RState (S k2) ty2) tins))
		     (update r1 (RState (S k1) ty1) 
			(update r2 (RState (S k2) ty2) tins)) tyret) ->
	  (Lang tins tins tyret);
lockTwo {r1} {r2} lt l1 l2 pri body 
	 = BIND (LOCK l2 pri)
     (\u . BIND (LOCK (stillElem lt l1) (unlockEarlier lt (unlockedId pri)))
     (\u . BIND body
   (\ret . BIND (revertLock (stillElem lt l1) (UNLOCK updatedElemIs))
     (\u . BIND (revertLock l2 (UNLOCK updatedElemIs))
     (\u . RETURN ret)))));

-- All accounts are unlocked at the start
unlockedAcc : {i:Fin n} -> (Unlocked i (accounts n));
unlockedAcc {i=fO} = isFirst;
unlockedAcc {i=fS k} = isLater unlockedAcc;

accountIs : {i:Fin n} -> (ElemIs i (RState O (TyLift Account)) (accounts n));
accountIs {i=fO} = first;
accountIs {i=fS k} = later accountIs;

updateEq : {i:Fin n} -> {xs:Vect A n} -> {v:A} ->
	   ((vlookup i (update i v xs)) = v);
updateEq {i=fO} {v} {xs=VCons x xs} = refl _;
updateEq {i=fS k} {v} {xs=VCons x xs} = updateEq {i=k} {xs};

moveMoneyCmp : {sender,receiver:Fin n} ->
               (move:CmpFin sender receiver) ->	Int ->
               (Lang (accounts n) (accounts n) TyUnit);
moveMoneyCmp {sender} {receiver} (lSmall p) amount
    = lockTwo p accountIs accountIs unlockedAcc
             (BIND (READ {i=sender} updatedElemIs)
      (\send. BIND (READ {i=receiver} (updated2ElemIs p))
      (\recv. BIND (WRITE {i=sender} (decrease amount send) updatedElemIs)
         (\u. BIND (WRITE {i=receiver} (increase amount recv) 
                                        (updated2ElemIs p))
         (\u. ACTION (putStrLn "Moved money"))))));
moveMoneyCmp (finEq p) amount
    = RETURN II; -- same account!
moveMoneyCmp {sender} {receiver} (rSmall p) amount
    = lockTwo p accountIs accountIs unlockedAcc
             (BIND (READ {i=sender} (updated2ElemIs p))
      (\send. BIND (READ {i=receiver} updatedElemIs)
      (\recv. BIND (WRITE {i=sender} (decrease amount send) 
                          (updated2ElemIs p))
         (\u. BIND (WRITE {i=receiver} (increase amount recv) 
                                        updatedElemIs)
         (\u. ACTION (putStrLn "Moved money"))))));

moveMoney : (sender,receiver:Fin n) -> Int ->
            (Lang (accounts n) (accounts n) TyUnit);
moveMoney s r amount = moveMoneyCmp (cmpFin s r) amount;

runMove : (sender,receiver:Fin n) -> Int -> 
          (REnv (accounts n)) -> (IO (REnv (accounts n)));
runMove s r sum accs = do { env <- interp accs (moveMoney s r sum);
                            return (fst env); };

dumpAccs : Int -> (REnv (accounts n)) -> (IO ());
dumpAccs num Empty = return II;
{-
dumpAccs num (Extend (resource v l) env) = do { acc <- readIORef v;
                                     	        putStr ((showInt num)++" : ");
					        putStrLn (showAcc acc);
					        -- dumpAccs (num+1) env;
			};
-}

one = S O; two = S one; three = S two; four = S three; five = S four;
ten = mult two five;
twenty = mult two ten;
thirty = mult ten three;

test : IO ();
test = do { -- ten accounts with £100 each.
	    accs : (REnv (accounts ten)) <- mkAccounts ten; 
	    -- Move 50 from acct 1 to acct 0
	    accs <- runMove {n=ten} (fS fO) fO 50 accs; 
	    -- Move 120 from acct 0 to acct 2
	    accs <- runMove {n=ten} fO (fS (fS fO)) 120 accs;
	    return II;
	    };
