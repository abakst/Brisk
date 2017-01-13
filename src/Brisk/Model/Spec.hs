{-# LANGUAGE FlexibleContexts #-}
module Brisk.Model.Spec where

import Data.Char
import Data.Functor.Identity
import Control.Monad.Trans
import Control.Exception (throw)
import Text.PrettyPrint.HughesPJ ((<+>), ($$), text, nest, (<>))
import Data.List
import Brisk.Model.Types (EffExpr(..), Id, Pred(..))
import Brisk.Pretty
import Text.ParserCombinators.Parsec hiding (try)
import Text.Parsec (Stream, ParsecT(..), runParserT)
import Text.Parsec.Error
import Text.Parsec.Prim
import Text.Parsec.Expr as PE
import Text.ParserCombinators.Parsec.Expr
import qualified Text.ParserCombinators.Parsec.Token as Token
import Text.ParserCombinators.Parsec.Language

{-
module spec Word where

effect Foo.Bar.Baz.n :=
  forall a. b. \x y z -> 

-}
{-
e := v | x | C <e> | \x.e | e e | return e | rec x. e | case e of ... | 
-}

data Spec = Spec [Id] Id BareExpr       

instance Pretty Spec where
  ppPrec _ (Spec ms i e) = text mod <> text "." <> text i
                       <+> text "<=" <+> nest 0 (pp e)
    where
      mod = intercalate "." ms

type BareExpr = EffExpr Id ()

type EffParser a = ParsecT String () IO a

testParse (Left  s) = text (show s)
testParse (Right f) = pp f                   

reserved_ = [ "in"
           , "rec" 
           , "spec"
           , "let"
           , "$spawn"
           , "$symSpawn"
           ]

lexer :: Token.GenTokenParser String () IO
lexer    = Token.makeTokenParser
                    haskellDef {
                          reservedNames = reserved_
                          ++ reservedNames haskellDef
                        , identStart = ioIfy (identStart haskellDef) 
                        , identLetter = ioIfy (identLetter haskellDef) 
                        , opLetter = ioIfy (opLetter haskellDef) 
                        , opStart  = ioIfy (opStart haskellDef)
                        }

ioIfy :: (Stream s Identity t)
      => (ParsecT s u Identity a)
      -> ParsecT s u IO a
ioIfy p = mkPT $ \u -> go $ runIdentity (runParsecT p u)
  where
    go :: Consumed (Identity a) -> IO (Consumed (IO a))
    go (Consumed v) = return (Consumed (return (runIdentity v)))
    go (Empty v)    = return (Empty (return (runIdentity v)))

reserved   = Token.reserved lexer
reservedOp = Token.reservedOp lexer

ident :: EffParser String
ident = Token.identifier lexer

symbol :: String -> EffParser String
symbol = Token.symbol lexer

parens :: EffParser a -> EffParser a
parens = Token.parens lexer

brackets = Token.brackets lexer

comma :: EffParser String
comma  = Token.comma lexer

-- X.Y.Bar <=  << eff >>
parseSpecFile :: String -> IO [Spec]
parseSpecFile fn = do input <- readFile fn
                      specs <- runParserT (specFile <* eof) () fn input
                      report specs
  where
    report (Left e)  = error (show e)
    report (Right s) = return s

name = Token.operator lexer <|> ident

specFile :: EffParser [Spec]
specFile = do reserved "module"
              reserved "spec"
              i <- name `sepBy1` Token.dot lexer
              reserved "where"
              many specLine
specLine = do i <- name `sepBy1` Token.dot lexer
              let mod = init i
                  id  = last i
              reserved "<="
              Token.braces lexer $ do
                e <- effExpr
                return $ Spec mod id e

effExpr :: EffParser BareExpr
effExpr = try effField <|> try opExpr <|> {- try effBind <|> -} effExpr'

effExpr' :: EffParser BareExpr
effExpr' = try effApp <|> effPrRec <|> effExpr''

effExpr'' :: EffParser BareExpr
effExpr'' = effLam
        <|> effRec
        <|> effReturn
        <|> effNil
        <|> effVar
        <|> effProcess
        <|> parens effExpr

effNil :: EffParser BareExpr
effNil = reserved "[]" >> return mkNil

opExpr :: EffParser BareExpr
opExpr = PE.buildExpressionParser opTab effExpr'
  where
    opTab = [ [ PE.Infix (reservedOp ":" >> return mkCons) PE.AssocLeft
              , PE.Infix (reservedOp ">>=" >> return mkBind) PE.AssocLeft
              ]
            ]

mkBind e1 e2 = EBind e1 e2 ()

mkCons e1 e2 = ECon { conId   = "Cons"
                    , conArgs = [e1,e2]
                    , annot   = ()
                    }

mkNil        = ECon { conId   = "Nil"
                    , conArgs = []
                    , annot   = ()
                    }

effField :: EffParser BareExpr
effField = do e <- effExpr''
              i <- read <$> brackets (many1 digit)
              return (EField e i ())

effRec :: EffParser BareExpr
effRec = do reserved "let"
            reserved "rec"
            i <- ident
            reserved "="
            e <- effExpr
            reserved "in"
            i' <- ident
            let foo = (ERec i e ())
            return foo

effPrRec :: EffParser BareExpr
effPrRec = do reserved "$R"
              parens $ do
                i <- ident
                comma
                j <- ident
                comma
                f <- effExpr
                comma
                e0 <- effExpr
                comma
                xs <- effExpr
                return (EPrRec i j f e0 xs ())

effProcess :: EffParser BareExpr      
effProcess = try send
         <|> try recv
         <|> try spawn
         <|> try self
         <|> try symSpawn
  where
    send = do reserved "$send"
              (t,p,m) <- triple effExpr
              return (Send t p m ())
    recv = do reserved "$recv"
              t <- parens effExpr
              return (Recv t ())
    spawn = do reserved "$spawn"
               p <- parens effExpr
               return (Spawn p ())
    self = do reserved "$self"
              return (Self ())
    symSpawn = do reserved "$symSpawn"
                  parens $ do
                    xs <- effExpr
                    comma
                    p  <- effExpr
                    return (SymSpawn xs p ())
                  

pair :: EffParser a -> EffParser (a,a)
pair p = parens $ do
  e1 <- p
  comma
  e2 <- p
  return (e1,e2)

triple :: EffParser a -> EffParser (a,a,a)
triple p = parens $ do
  e1 <- p
  comma
  e2 <- p
  comma
  e3 <- p
  return (e1, e2, e3)

effReturn :: EffParser BareExpr
effReturn = do reserved "return"
               e <- effExpr
               return (EReturn e ())

effVar :: EffParser BareExpr
effVar = flip EVar () <$> ident

effLam :: EffParser BareExpr
effLam = do symbol "\\"
            xs <- many1 ident
            symbol "->"
            e  <- effExpr
            return $ foldr go e xs
              where
                go x e = ELam x e ()

effBind :: EffParser BareExpr
effBind = do e1 <- effExpr'
             symbol ">>="
             e2 <- effExpr
             return (EBind e1 e2 ())--chainl1 effExpr (symbol ">>=" >> return go)

effApp :: EffParser BareExpr
effApp = do e:es <- many1 effExpr''
            return $
              case e of
                -- EVar c _ | isUpper (c !! 0) -> ECon c es ()
                _                           -> foldl' go e es
                where
                  go e e' = EApp e e' ()
