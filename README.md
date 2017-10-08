# Types
Use `ghci Lambda.hs` to start the Haskell interpreter.

To infer types of a given lambda expression, use the function `hocuspocus`, i.e. `hocuspocus "\\x . x"`.

Some examples of expressions: 

| Expression 							   |        Result                  |
| :--------------------------------------------------------------- | :----------------------------- |
| \\\\x y . x + y						   | Int->Int->Int                  |
| \\\\x y. case x y of (Right ans) -> false \| (Left err) -> true  | (t1->"Either" a b)->t1->"Bool" |
| \\\\x . case x of (Just y) -> true \| (Nothing) -> true"         | ("Maybe" a)->"Bool"            |
| \\\\x y . if (x + y) > 0 then true else false 		   | (Int)->(Int)->Bool             |



