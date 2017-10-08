module Tests where
import Type
ex1 = Lam "f" (Lam "x" (App (Var "f") (Var "x")))
ex2 = Lam "x" (App (Var "x") (Var "x"))
ex3 = Lam "g" (Lam "f" (Lam "x" (App (Var "g") (App (Var "f") (Var "x")))))
true = Lit (LitB True)
ex4 = If (Lit (LitB False)) (Lit (LitI 10)) (App (Lam "x" (Var "x")) (Lit (LitI 20)))
ex5 = Lit (LitI 2)
-- ((\x.x)(\y.y))(True)
ex6 = ((App (App (Lam "x" (Var "x")) (Lam "y" (Var "y"))) (Lit (LitB True))))
ex7 = (App (Lam "x" (Var "x")) (If (Lit (LitB True)) (Lit (LitI 10)) (Lit (LitI 20))))
ex8 = (App (If (Lit (LitB True)) (Lit (LitI 10)) (Lit (LitI 20))) (Lam "x" (Var "x")))
exif = Lam "x" (If (Var "x") (Lit (LitI 1)) (Lit (LitI 0)))
exif2 = Lam "x" (Lam "y" (If (Var "x") (Var "y") (Lit (LitI 0))))
exif3 = Lam "x" (Lam "y" (Lam "z" (If (Var "x") (Var "y") (Var "z"))))
exif4 = Lam "x" (Lam "y" (If (App (App (Var "==") (Var "x")) (Var "y")) (Var "x") (Var "y")))
-- Case Examples --
ex1case = Lam "x" (Case (Var "x") [((PCon "Just" [PVar "x"]), (Lit (LitB True))), (PCon "Nothing" [], Lit (LitB False))])
ex2case = Lam "x" (Case (Var "x") [(PLit (LitB True), (Lit (LitI 1)))])
ex3case = Lam "x" (Case (Var "x") [((PCon "Just" [PVar "x"]), (Lit (LitB True)))])
ex4case = Lam "x" (Case (Var "x") [(PLit (LitI 1), Lit (LitB True)), (PLit (LitI 2), Lit (LitB True)), (PLit (LitI 0), Lit (LitB False))])

-- Shouldn't work
ex5case = Lam "x" (Case (Var "x") [((PCon "Just" [PVar "x"], (Lit (LitB True)))), ((PCon "Nothing" [], Lit (LitI 1)))])

-- Bin Ops --
suc = Lam "x" (App (App (Var "+") (Var "x")) (Lit (LitI 1)))
add = Lam "x" (Lam "y" (App (App (Var "+") (Var "x")) (Var "y")))
