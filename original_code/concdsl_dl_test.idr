include "concdsl_dl.idr";

twoNats = VCons (RState O TyNat) (VCons (RState O TyNat) VNil);
mkNatEnv : IO (REnv twoNats);
mkNatEnv = do {
        r1 <- newIORef O;
        l1 <- newLock 1;
        r2 <- newIORef O;
        l2 <- newLock 1;
        return (Extend (resource r1 l1) 
               (Extend (resource r2 l2)
                Empty));
          };

one = S O; two = S one; three = S two; four = S three; five = S four;
ten = mult two five;
twenty = mult two ten;
thirty = mult ten three;

count : Nat -> String -> (Lang twoNats twoNats TyUnit);
count n pid 
          = LOOP n
           (BIND (LOCK (later first) (isLater isFirst))
      (\u . BIND (LOCK first isFirst)
      (\u . BIND (ACTION (putStrLn (pid ++ " in")))
      (\u . BIND (READ first)
   (\numa . BIND (WRITE (S numa) first)
      (\u . BIND (READ (later first))
   (\numb . BIND (WRITE (S numb) (later first))
      (\u . BIND (ACTION (putStrLn (pid ++ " out")))
      (\u.  BIND (UNLOCK (later first))
      (\u . BIND (UNLOCK first)
      (\u . ACTION (putStrLn (pid ++ " Val: " ++ (showNat (plus numa numb))))
      )))))))))));

threadcount : Lang twoNats twoNats TyUnit;
threadcount = BIND (FORK (consUn (consUn nilUn)) (count ten "thread"))
    (\u . count ten "__main");

runTest : IO ();
runTest = do { env <- mkNatEnv;
           putStrLn "Made Env";
           p <- interp env threadcount;
           return II;
    };
