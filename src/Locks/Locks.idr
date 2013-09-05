module Locks

import System

%link C "locker"

data LockRef = MkLockRef Int

get_lock : Int -> IO LockRef
get_lock i = do
    x <- mkForeign (FFun "get_lock" [FInt] FInt) i
    return (MkLockRef x)

release_lock : LockRef -> IO ()
release_lock (MkLockRef h) = do
    _ <- mkForeign (FFun "release_lock" [FInt] FInt) h
    return ()

write : LockRef -> Int -> IO ()
write (MkLockRef h) val = do
    _ <- mkForeign (FFun "write_locked" [FInt, FInt] FInt) h val
    return ()

read : LockRef -> IO Int
read (MkLockRef h) = mkForeign (FFun "read_locked" [FInt] FInt) h

-- Some tests

frk_action : IO ()
frk_action = do
    _ <- fork ( do
        f <- get_lock 1
        putStrLn "    fork has lock"
        v <- read f
        write f (v+1)
        release_lock f
        putStrLn "    fork lock released"
        return ())
    return ()

test: IO ()
test = do
    h <- get_lock 1
    putStrLn "main has lock"
    frk_action
    frk_action
    frk_action
    usleep 100
    write h 1
    release_lock h
    putStrLn "main lock released"
    usleep 2000
    putStrLn "other things happened in between, we hope"
    h' <- get_lock 1
    v <- read h'
    print v
    return ()
