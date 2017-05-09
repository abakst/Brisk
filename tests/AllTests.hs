{-# LANGUAGE ScopedTypeVariables #-}
module AllTests where
import Brisk.Model.Rewrite -- (findRewrite, runRewrites, RWState(..), ProcessIdSpec(..), RewriteContext(..))
import Control.Exception
import Control.Monad.State
import Distribution.TestSuite
import qualified Brisk.Model.Types as T
import           Brisk.Model.IceT as I
import Brisk.Model.Env as Env

tests :: IO [Test]
tests = return $ [ Group { groupName    = "micro tests"
                         , concurrently = True
                         , groupTests   = posTests
                         }
                 ]
               
  where
    posTests = (Test . rewriteTest) <$> [
        test0
      , test1
      , test2
      , test3
      , test4
      , test5
      , test6
      , test7
      , test9
      , test10
      , test11
      , test12
      , test14
      , test15
      , test16
      -- Approaching reality:
      , workSteal0
      , workSteal
      , mapreduce0
      , mapreduce
      ]

fst3 (n,_,_) = n
snd3 (_,q,_) = q
thd3 (_,_,e) = e

rewriteTest :: RWAnnot s => (String, [RewriteContext s], [RewriteContext s]) -> TestInstance
rewriteTest (n, q, expected)
  = TestInstance { run = runTest `catch` (\(e :: ErrorCall) ->
                                           return (Finished (Distribution.TestSuite.Fail "")))
                 , name = n
                 , tags = []
                 , options = []
                 , setOption = \_ _ -> Right $ rewriteTest (n, q, expected)
                 }
  where
    runTest =
      if doTest (runRewrites (== expected) q) == expected then
        return (Finished Pass)
      else
        return (Finished (Distribution.TestSuite.Fail ""))


-- Quick tests go here:
tys   = [ T.TyVar ("T" ++ show i) | i <- [1..10] ]
t x   = T.TyVar ("T" ++ show x)
v x   = T.EVar x ()
p x   = T.EVal (Just (T.CPid x)) ()
pset x = T.EVal (Just (T.CPidSet x)) ()

send ti x y = Send (t ti) (p x) (v y)
sendv ti x y = Send (t ti) (v x) (v y)
sendb ti x y = Send (t ti) x y
c x   = Concrete x
u x y = Unfolded x y

recv ti x y = Recv (t ti) (Just (p x)) (Just y)
recvv ti x y = Recv (t ti) (Just (v x)) (Just y)
recvAny ti y = Recv (t ti) Nothing (Just y)

runTest t = map (consts . snd) $ runStateT t initState

test0 = ("test0", [One (c "p") (Send (tys !! 0) (p "q") (v "x"))], [])

test1 = ("test1",
         [ One (c "p")
          (Send (tys !! 0) (p "q") (v "x"))
        , One (c "q")
          (Recv (tys !! 0) (Just (p "p")) (Just "m"))
        ],
        [])

test2 = ( "test2"
        , [ One (c "p") $
            Seq [send 0 "q" "x", recv 1 "q" "y"]
          , One (c "q") $
            Seq [recv 0 "p" "m1", send 1 "p" "m2"]
          ]
        , []
        )

test2_state
  = [ One (c "p") $
          Seq [sendb 0 (p "q") (p "p"), recv 1 "q" "y"]
    , One (c "q") $
          Seq [recv 0 "p" "m1", sendv 1 "m1" "m2"]
    ]

test3 = ("test3", [ One (c "q") $ ForEach "x" (True, pset "xs") (Seq [send 0 "q" "mymsg", recv 0 "q" "foo"]) ], [])

test4 = ("test4", [ Par ["x"] (Singleton "xs") (One (c "q") (Seq [send 0 "q" "mymsg", recv 0 "q" "foo"])) ], [])

test5 = ("test5",
         [ Par ["x"] (Singleton "xs") $
              One (c "x") $
                  Seq [recv 0 "p" "foo", recv 1 "p" "goo"]
        , One (c "p") $
          ForEach "x" (True, pset "xs") (Seq [sendv 0 "x" "mymsg", sendv 1 "x" "amsg"])
        ], []
        )

test6 = ("test6", [
          One (c "q") $
            recv 1 "r" "qx"
        , One (c "r") $
            Seq [send 0 "p" "r", send 1 "q" "r"]
        , One (c "p") $
            recv 0 "r" "px"
        ], [])

test7 = ("test7", [ Par ["x"] (Singleton "xs") $
            One (c "x") $
             Seq [recv 0 "p" "foo", send 1 "q" "xgloop"]
        , Par ["x1"] (Singleton "xs") $
            One (c "p") $
              (sendv 0 "x1" "mymsg")
        , Par ["x2"] (Singleton "xs") $
            One (c "q") $
              (recvAny 1 "amsg")
        ], [])

test9 = ("test9", [ Par ["x"] (Singleton "xs") $
            One (c "x") $
             Seq [recv 0 "p" "foo", send 1 "q" "xgloop"]
        , One (c "p") $
            ForEach "x1" (True, pset "xs") (sendv 0 "x1" "mymsg")
        , One (c "q") $
            ForEach "x2" (True, pset "xs") (recvAny 1 "amsg")
        ], [])

test10 = ("test10", [ Par ["x"] (Singleton "xs") $
               One (c "x") $
                   Seq [recv 0 "q" "foo", send 1 "q" "xgloop"]
        , One (c "q") $
            Seq [ ForEach "x1" (True, pset "xs") (sendv 0 "x1" "mymsg")
                , ForEach "x2" (True, pset "xs") (recvAny 1 "floop")
                ]
        ], [])

test11 = ("test11", [ Par ["x"] (Singleton "xs") $
               One (Unfolded "x" "xs") $
                   Seq [recv 0 "q" "foo", sendv 1 "foo" "xgloop"]
        , One (c "q") $
            Seq [ ForEach "x1" (True, pset "xs") (sendb 0 (v "x1") (p "q"))
                , ForEach "x2" (True, pset "xs") (recvAny 1 "floop")
                ]
        ], [])

test12 = ("test12", [ Par ["x"] (Singleton "xs") $
               One (Unfolded "x" "xs") $
                   Seq [recv 0 "q" "foo", sendv 1 "foo" "xgloop"]
        , One (c "q") $
            ForEach "x1" (True, pset "xs") $
                    Seq [sendb 0 (v "x1") (p "q")
                        ,recvv 1 "x1" "floop"
                        ]
        ], [])

test13 = ("test13", [ Par ["x"] (Singleton "xs") $
             One (Unfolded "x" "xs") $
               While "bloop" $ Seq [ send 1 "q" "foo", Continue "bloop" ]
         , One (c "q") $
               recvAny 1 "blue"
         ], [])
test13Query = runRewrites (\ps -> null [ p | Just p <- contextPid <$> ps, p == (c "q")])
                          (snd3 test13)

test14 = ("test14", [ One (c "p") $
           While "bloop" $ Seq [ recv 0 "q" "what", recv 1 "q" "bloink" ]
         , One (c "q") $
           Seq [ sendb 0 (p "p") (v "abcd"), sendb 1 (p "p") (v "efgh") ]
         ], [])

test15 = ("test15", [ One (c "p") $
           Seq [ recv 0 "q" "what"
               , Case (v "what")
                   [ ( T.ECon "Left" [] ()
                     , Skip
                     )
                   , ( T.ECon "Right" [] ()
                     , I.Fail
                     )
                   ]
                   Nothing
               ]
         , One (c "q") $
           sendb 0 (p "p") (T.ECon "Left" [] ())
         ], [])

test16 = ("test16", [ One (c "p") $
           Seq [ recv 0 "q" "whom"
               , Case (v "whom")
                   [ ( T.ECon "Left" [T.EVar "x" ()] ()
                     , Seq [ recv 1 "q" "blorg"
                           , sendb 2 (v "x") (v "beepboop")
                           ]
                     )
                   , ( T.ECon "Right" [] ()
                     , I.Fail
                     )
                   ]
                   Nothing
               , sendb 1 (p "q") (p "p")
               ]
         , One (c "q") $
           Seq [ sendb 0 (p "p") (T.ECon "Left" [p "q"] ())
               , sendb 1 (p "p") (p "q")
               , recv 2 "p" "floop"
               ]
         ], [])

workSteal0 =
  ( "worksteal0-mini"
  , [ One (c "queue") $
      ForEach "x" (True, pset "xs") $
      Seq [ recvAny 1 "q"
          , sendb 0 (v "q") (T.ECon "Right" [] ())
          ]
      
    , Par ["x0"] (Singleton "xs") $
        One (Unfolded "x0" "xs") $
          While "loop0" $ Seq [
              sendb 1 (p "queue") (v "x0")
            , recv 0 "queue" "what"
            , Case (v "what")
              [ ( T.ECon "Left" [] ()
                , Continue "loop0"
                )
              , ( T.ECon "Right" [] ()
                , Skip
                )
              ] Nothing
            ]
    ]
  , []
  )

workSteal =
  ( "worksteal-mini"
  , [ One (c "queue") $
      Seq [ ForEach "i" (True, pset "is") $
            Seq [ recvAny 1 "x"
                , sendb 0 (v "x") (T.ECon "Left" [] ())
                ]
          , ForEach "x0" (True, pset "xs") $
            Seq [ recvAny 1 "x"
                , sendb 0 (v "x") (T.ECon "Right" [] ())
                ]
          ]
    , Par ["x1"] (Singleton "xs") $
        One (Unfolded "x1" "xs") $
          While "loop0" $ Seq [
              sendb 1 (p "queue") (v "x1")
            , recv 0 "queue" "what"
            , Case (v "what")
              [ ( T.ECon "Left" [] ()
                , Continue "loop0"
                )
              , ( T.ECon "Right" [] ()
                , Skip
                )
              ] Nothing
            ]
    ]
  , []
  )

friendLoop =
  ( "friendloop"
  , [ One (c "queue") $
        ForEach "i" (True, pset "is") $
          sendb 1 (p "m") (T.ECon "Left" [] ())
    , One (c "m") $
        ForEach "i1" (True, pset "is") $
          recv 1 "queue" "work"
    ]
  , []
  )

gloop = FinPar [ One (c "queue") $
                   Seq [ recvAny 1 "x"
                       , sendb 0 (v "x") (T.ECon "Left" [] ())
                       ]
               , One (c "m") $
                   recvAny 1 "work"
               ]

  
mapreduce0 =
  ( "mapreduce-mini0"
  , [ Par ["i0", "i1"] (Zipped 2 (Singleton "is")) $
        FinPar [ One (c "queue") $
                   Seq [ recvAny 1 "x"
                       , sendb 0 (v "x") (T.ECon "Left" [] ())
                       ]
               , One (c "m") $
                   recvAny 1 "work"
               ]
    , worker 
    ]
  , [worker]
  )
  where
    worker = Par ["x1"] (Singleton "xs") $
        One (Unfolded "x1" "xs") $
          While "loop0" $ Seq [
              sendb 1 (p "queue") (v "x1")
            , recv 0 "queue" "what"
            , Case (v "what")
              [ ( T.ECon "Left" [] ()
                , Seq [sendb 1 (p "m") (v "gloop"), Continue "loop0" ]
                )
              , ( T.ECon "Right" [] ()
                , Skip
                )
              ] Nothing
            ]

mapreduce =
  ( "mapreduce-mini"
  , [ One (c "queue") $
      Seq [ ForEach "i" (True, pset "is") $
            Seq [ recvAny 1 "x"
                , sendb 0 (v "x") (T.ECon "Left" [] ())
                ]
          , ForEach "x0" (True, pset "xs") $
            Seq [ recvAny 1 "x"
                , sendb 0 (v "x") (T.ECon "Right" [] ())
                ]
          ]
    , Par ["x1"] (Singleton "xs") $
        One (Unfolded "x1" "xs") $
          While "loop0" $ Seq [
              sendb 1 (p "queue") (v "x1")
            , recv 0 "queue" "what"
            , Case (v "what")
              [ ( T.ECon "Left" [] ()
                , Seq [sendb 1 (p "m") (v "gloop"), Continue "loop0" ]
                )
              , ( T.ECon "Right" [] ()
                , Skip
                )
              ] Nothing
            ]
    , One (c "m") $
      ForEach "i1" (True, pset "is") $ recvAny 1 "work"
    ]
  , []
  )

test8_shouldFail
  = [ Par ["x"] (Singleton "xs") $
            One (c "x") $
             Seq [recv 2 "p" "foo", recv 1 "q" "xgloop"]
        , One (c "p") $
            ForEach "x" (True, pset "xs") (send 0 "x" "mymsg")
        , One (c "q") $
            ForEach "x" (True, pset "xs") (send 1 "x" "amsg")
        ]


testState =
  initState { symSends = Env.fromList [(t 1, ["xs"])]
            }

doTest q = findRewrite q testState
