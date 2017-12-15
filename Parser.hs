module Parser where
import Type
import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Language
import Text.ParserCombinators.Parsec.Expr
import Data.Char
import Debug.Trace
import qualified Text.ParserCombinators.Parsec.Token as Tok

startData = do e <- datap
               whiteSpace
               eof
               return e

datap = do reserved "data"
           tcon <- tconp
           spaces
           tparams <- many tvar
           reserved "="
           dcons <- sepBy dcon $ reservedOp "|"
           return $ arange tcon tparams dcons

arange tcon tparams [] = []
arange tcon tparams ((dcon, dpar):ds) =
    dcon :>: foldr (-->) (foldl (|->) tcon tparams) dpar:arange tcon tparams ds

tvar = do x <- identifier
          return $ TVar x

tconp = do u <- upper
           x <- many letter
           return $ TCon (u:x)

dcon = do u <- upper
          x <- many letter
          spaces
          dparam <- sepBy tvar $ spaces
          return $ ((u:x), dparam)


start = do e <- term
           whiteSpace
           eof
           return e

term = do reserved "if"
          e1 <- term
          reserved "then"
          e2 <- term
          reserved "else"
          e3 <- term
          return (If e1 e2 e3)
          <|> do reservedOp "\\"
                 xs <- many1 identifier
                 reservedOp "."
                 e <- term
                 return (foldr Lam e xs)
         <|> do reserved "case"
                e <- term
                reserved "of"
                mcases <- sepBy cases $ reservedOp "|"
                return $ Case e mcases
         <|> expr
         <|> do true <- reserved "true"
                return (Lit (LitB True))
         <|> do false <- reserved "false"
                return (Lit (LitB False))
         <|> do reserved "let"
                x <- identifier
                reserved "="
                e1 <- term
                reserved "in"
                e2 <- term
                return $ Let (x, e1) e2


cases = do mpat <- pat
           reserved "->"
           e <- term
           return (mpat, e)

pat = do p <- pcon
         return p
      <|> do p <- parens pcon
             return p
      <|> do
          p <- pvar
          return p
      <|> do
          p <- plit
          return p

pcon = do u <- upper
          x <- many letter
          spaces
          p <- many pat
          return (PCon (u:x) p)

pvar = do x <- identifier
          return (PVar x)

plit = do x <- natural
          return (PLit (LitI (fromInteger x)))
          <|>
          do t <- reserved "true"
             return (PLit (LitB True))
          <|>
          do f <- reserved "false"
             return (PLit (LitB False))

apterm = do es<-many1 delterm
            return (foldl1 App es)

delterm = do x<-identifier
             return (Var x)
        <|> do n<-natural
               return (Lit (LitI (fromInteger n)))
        <|> parens term

expr :: Parser Expr
expr = buildExpressionParser table appl_expr
    where
        table = [ [Postfix ((reservedOp "+")  >> return (App (Var "+")))],
                  [Postfix ((reservedOp "-")  >> return (App (Var "-")))],
                  [Postfix ((reservedOp ">")  >> return (App (Var ">")))],
                  [Postfix ((reservedOp "<")  >> return (App (Var "<")))],
                  [Postfix ((reservedOp ">=") >> return (App (Var ">=")))],
                  [Postfix ((reservedOp "<=") >> return (App (Var "<=")))],
                  [Postfix ((reservedOp "==") >> return (App (Var "==")))],
                  [Postfix ((reservedOp "*")  >> return (App (Var "*")))],
                  [Postfix ((reservedOp "/")  >> return (App (Var "/")))],
                  [Infix (return (App)) AssocLeft] ]

appl_expr :: Parser Expr
appl_expr = do { es<-many1 delim_expr
               ; return (foldl1 App es)
               }

delim_expr :: Parser Expr
delim_expr = do { x<-identifier; return (Var x) }
             <|> do { n<-natural; return (Lit (LitI (fromInteger n))) }
             <|> parens term

defs = emptyDef { reservedNames   = ["if", "then", "else", "case", "of", "true", "false", "->", ".", "let", "in", "=", "data"],
                  reservedOpNames = ["\\", "+", "-", "*", "/", ">",
                                     "<", ">=", "<=", "==", "|"]
                }
lexer = Tok.makeTokenParser defs

reserved   = Tok.reserved   lexer
reservedOp = Tok.reservedOp lexer
identifier = Tok.identifier lexer
natural    = Tok.natural    lexer
parens     = Tok.parens     lexer
brackets   = Tok.brackets   lexer
whiteSpace = Tok.whiteSpace lexer
