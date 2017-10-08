module Parser where
import Type
import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Language
import Text.ParserCombinators.Parsec.Expr
import Data.Char
import qualified Text.ParserCombinators.Parsec.Token as Tok

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

cases = do mpat <- pat
           reserved "->"
           e <- term
           return (mpat, e)

pat = do p <- parens pcon
         return p
      <|> do
          p <- pvar
          return p
          <|> do
              p <- plit
              return p

pcon = do u <- upper
          x <- many1 letter
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
-- an application (e0 e1 e2 .. en)
-- where ei are self-delimited expressions
apterm = do es<-many1 delterm
            return (foldl1 App es)

-- self-delimited expressions:
-- identifiers, constants or parentesised terms
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

defs = emptyDef { reservedNames   = ["if", "then", "else", "case", "of", "true", "false", "->", "."],
                  reservedOpNames = ["\\", "+", "-", "*", "/", ">",
                                     "<", ">=", "<=", "==", "|"]
                }
lexer = Tok.makeTokenParser defs

reserved   = Tok.reserved   lexer
reservedOp = Tok.reservedOp lexer
identifier = Tok.identifier lexer
natural    = Tok.natural    lexer
parens     = Tok.parens     lexer
whiteSpace = Tok.whiteSpace lexer
