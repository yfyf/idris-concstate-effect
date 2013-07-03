{- A resource is a shared variable, stored as an IORef. Resource
   states tell us whether they are locked or not, and resource handles,
   indexed over the resource state, store the IORef. -}

data ResState = RState Nat -- number of times it has been locked.
               Ty;  -- Type of resource

getTy : ResState -> Ty;
getTy (RState _ ty) = ty;

-- Everything before i is unlocked
data Unlocked : (i:Fin n) -> (xs:Vect ResState n) -> # where
   isFirst : {x:ResState} -> {xs:Vect ResState n} ->
         (Unlocked fO (VCons x xs))
 | isLater : {i:Fin n} -> {xs:Vect ResState n} ->
         (Unlocked i xs) -> (Unlocked (fS i) (VCons (RState O t) xs));

{- We need a way of taking two or more resource ids (Fins, perhaps) and
ordering them in such a way that we get a list of proofs (i.e. of type
Unlocked) that tells us the correct order to lock them. -}

data LTFin : (Fin n) -> (Fin n) -> # where
    ltO : {k:Fin n} -> (LTFin fO (fS k))
  | ltS : {x:Fin n} -> {y:Fin n} ->
      (LTFin x y) -> (LTFin (fS x) (fS y));

data CmpFin : (Fin n) -> (Fin n) -> # where
    lSmall : {x,y:Fin n} ->
         (LTFin x y) -> (CmpFin x y)
  | rSmall : {x,y:Fin n} -> 
         (LTFin y x) -> (CmpFin x y)
  | finEq : {x,y:Fin n} -> 
        (x=y) -> (CmpFin x y);

cmpFinS : {x,y:Fin n} -> (CmpFin x y) -> (CmpFin (fS x) (fS y));
cmpFinS (lSmall p) = lSmall (ltS p);
cmpFinS (rSmall p) = rSmall (ltS p);
cmpFinS (finEq (refl i)) = finEq (refl (fS i));

cmpFin : (x,y:Fin n) -> (CmpFin x y);
cmpFin fO fO = finEq (refl _);
cmpFin fO (fS k) = lSmall ltO;
cmpFin (fS k) fO = rSmall ltO;
cmpFin (fS x) (fS y) = cmpFinS (cmpFin x y);

-- if x<y, and everything before y is unlocked, then everything before
-- x must be unlocked

unlockEarlier : {i:Fin n} -> {j:Fin n} ->
            {xs:Vect ResState n} ->
        (LTFin i j) -> (Unlocked j xs) ->
        (Unlocked i xs);
unlockEarlier {xs=VCons _ _} ltO locked = isFirst;
unlockEarlier (ltS p) (isLater locked) = isLater (unlockEarlier p locked);

-- if everything before x is locked, then it's still locked even if we
-- change x.

unlockedId : {i:Fin n} -> {xs:Vect ResState n} -> {v:ResState} ->
         (Unlocked i xs) -> (Unlocked i (update i v xs));
unlockedId isFirst = isFirst;
unlockedId (isLater p) = isLater (unlockedId p);
