module Brisk.Model.Types where

data Stmt t b e a = Skip { annot :: a }

                  | Send { sendType    :: t
                         , sendMessage :: e
                         , stmtAnnot :: a
                         }

                  | Recv { recvType    :: t
                         , recvBind    :: Maybe b
                         , stmtAnnot   :: a
                         }
                  deriving (Eq, Show)

data Process p s a = Stmt { stmtStmt  :: s
                          , stmtProc  :: p
                          , procAnnot :: a
                          }
                   | Sequence { seqStmts  :: [s]
                              , procAnnot :: a
                              }
                   deriving (Eq, Show)
