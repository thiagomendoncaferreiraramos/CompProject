{-# OPTIONS_GHC -fno-warn-tabs #-}
{- HLINT ignore "Use if" -}

module Imp where

type Id = String

type Prog = [Instr]

data Instr =   ASG (Id,Exp)
             | CASE Id [Branch]
			 | WHILE Id [Branch]
			 | LOCAL [Id] Prog
			 | POP -- para la implementacion
	deriving (Eq,Show)
	
type Branch = (Id,([Id],Prog))

data Exp =   V Id
           | C Id [Exp]
	deriving (Eq,Show)
	
data Val = K Id [Val]
			| Null -- para variables nuevas en el LOCAL
    deriving (Eq,Show)

val2exp :: Val -> Exp
val2exp (K id vs) = C id (map val2exp vs)

type Mem = [[(Id,Val)]]
push :: [(Id,Val)] -> Mem -> Mem
push = (:)

-- EXAMPLES------------------------------------------
-- VALORES Y MEMORIAS
zero :: Val
zero = K "0" []
one :: Val
one = K "S" [zero]
two :: Val
two = K "S" [one]
three :: Val
three = K "S" [two]
mem :: Mem
mem = [[("x",zero),("y",one)]]

mem1 :: Mem
mem1 = [("x",two)] : mem 

mem2 :: Mem
mem2 = [[("x",one),("y",two),("z",three),("w",zero)]]
-------------------------------------------------------
lkup :: Mem -> Id -> Val
lkup [] x = error ("lkup: variable " ++ x ++ " no inicializada")
lkup (f:fs) x = case lookup x f of
					Just v -> v
					Nothing -> lkup fs x		   
		   
upd :: (Id,Val) -> Mem -> Mem
upd p [f] = [p:f] 		-- se podría borrar el valor anterior
upd p (f:fs) = case elem (fst p) (map fst f) of		-- ver si la variable está en el primer frame
					True -> (p:f):fs 		-- se podría borrar el valor anterior
					False -> f : upd p fs

-- EXAMPLES------------------------------------------
-- LOOKUP Y UPDATE
ex1 :: Bool
ex1 = lkup mem "x" == zero
ex2 = lkup mem "y" == one
ex3 = lkup mem1 "x"  == two
ex4 = lkup mem1 "y" == one
ex5 = upd ("x",one) mem == [[("x",one),("x",zero),("y",one)]]
ex55 = upd ("x",zero) mem1 == [[("x",zero),("x",two)],
                              [("x",zero),("y",one)]] 
ex6 = upd ("y",zero) mem1 == [[("x",two)],
							 [("y",zero),("x",zero),("y",one)]]
ex7 = upd ("z",zero) mem == [[("z",zero),("x",zero),("y",one)]]
ex8 = upd ("z",zero) mem1 == [[("x",two)],
							 [("z",zero),("x",zero),("y",one)]]
ex9 = lkup (upd  ("x",one) mem) "x" == one
ex10 = lkup (upd  ("z",two) mem) "x" == zero
ex11 = (lkup (upd  ("z",two) mem1) "z") == two
-------------------------------------------------------

eval :: Mem -> Exp -> Val
eval m (V x) = lkup m x
eval m (C id exps) = K id (map (eval m) exps)
 
step :: (Mem,Prog) -> (Mem,Prog)
step (m, ASG (id,exp) :p') = (upd (id,eval m exp) m,p')
step (m, CASE x bs : p') = let K c vs = lkup m x in
                        	case lookup c bs of
								Just (xs,p) -> (push(zip xs vs) m, p ++ POP:p')
								Nothing -> error ("step: constructor " ++ c ++ " no considerado en ramas " ++ show(CASE x bs))					  
step (m, p@(WHILE x bs : p')) = let K c vs = lkup m x in
                               case lookup c bs of
						        	Just (xs,q) -> (push (zip xs vs) m , q ++ POP : p) 
							    	Nothing -> (m,p')
step (m, LOCAL xs p : p') =  (push(map (\x -> (x,Null)) xs) m, p ++ POP:p')
step (m, POP:p') = (tail m, p')
step (m,[]) = error "step: programa vacío"

-- 2 PASOS
step2  :: (Mem,Prog) -> (Mem,Prog)
step2 (m,p) = step(step (m,p))
-- 3 PASOS
step3 = step.step2
step6 = step3.step3
--- n steps: no da error con p = []
nnstep :: Int -> (Mem,Prog) -> (Mem,Prog) 
nnstep n (m,[]) = (m,[])
nnstep 0 (m,p) = (m,p)
nnstep n (m,p)= nnstep (n-1) (step (m,p))

--Examples------------------------------------------
-- PROGRAMAS
p1 = [ASG ("x",V "y")] -- x:=y
p2 = [ASG ("y",val2exp three)] -- y:=3
p3 = [ASG ("z",val2exp one)]  -- z:=1
ex12 = step (mem,p1) == ([[("x",one),("x",zero),("y",one)]],[])
ex13 = step (mem1,p1) == ([[("x",one),("x",two)],
                          [("x",zero),("y",one)]],
						[])
ex14 = step (mem1,p2) == ([[("x",two)],
						  [("y",one),("x",zero),("y",one)]],
						[])
ex15 = step (mem1,p3) == ([[("x",two)],
						  [("z",one),("x",zero),("y",one)]],
						[])
p4 = [CASE "x" [("0",([],p3)),("S",(["x1"],p2))]]
ex16 = step (mem,p4) == ([[],
						 [("x",K "0" []),("y",one)]],
						[ASG ("z",C "S" [C "0" []]),POP])
ex17 = step2 (mem,p4) == ([[],
                          [("z",one),("x",K "0" []),("y",one)]],
						 [POP])
ex18 = step3 (mem,p4) == ([[("z",one),("x",K "0" []),("y",one)]],
                         [])						
p5 = [WHILE "x" [("S",(["w"],[ASG ("x",V "w")]))]]
ex19 = step(mem1,p5) == ([[("w",one)],
						 [("x",two)],
						 [("x",K "0" []),("y",one)]],
						[ASG ("x",V "w"),POP,WHILE "x" [("S",(["w"],[ASG ("x",V "w")]))]])
ex20 = step2(mem1,p5) == ([[("w",one)],
						  [("x",one),("x",two)],
						  [("x",zero),("y",one)]],
						 [POP,WHILE "x" [("S",(["w"],[ASG ("x",V "w")]))]])
ex21 = step3(mem1,p5) == ([[("x",one),("x",two)],
                          [("x",zero),("y",one)]],
						[WHILE "x" [("S",(["w"],[ASG ("x",V "w")]))]])
ex22 = step6(mem1,p5) == ([[("x",zero),("x",one),("x",two)],
						  [("x",zero),("y",one)]],
						[WHILE "x" [("S",(["w"],[ASG ("x",V "w")]))]])
ex23 = step(step6(mem1,p5)) == ([[("x",zero),("x",one),("x",two)],
							    [("x",zero),("y",one)]],
							   [])	

add::(Id,Id) -> Prog  -- a:= a+b
add (a,b) = [LOCAL ["aux","i"]
				   [ASG ("aux",V b),ASG ("i",V a),
				    WHILE "i" [("S",(["x1"],[ASG ("i",V "x1"),ASG ("aux",C "S" [V "aux"])]))],
					ASG (a,V "aux")
				  ]
			]

add3::(Id,Id,Id) -> Prog  -- sab:= a+b
add3 (a,b,sab) = [LOCAL ["aux"]
				   [ASG (sab,V b),ASG ("aux",V a),
				    WHILE "aux" [("S",(["x1"],[ASG (sab,C "S" [V sab]),ASG ("aux",V "x1")]))]
				  ]
			]

			
prod::(Id,Id) -> Prog  -- a:= a*b
prod (a,b) = [LOCAL ["prod","i"]
			  		[ASG ("prod",val2exp zero),ASG("i",V a),
				    WHILE "i" [("S",(["k1"],ASG ("i",V "k1"):add("prod",b)))],
					ASG (a,V "prod")
				  ]
			]
ex24 = nnstep 20 (mem2,add("z","y")) == ([[("z",K "S" [K "S" [K "S" [K "S" [K "S" [K "0" []]]]]]),("z",K "0" []),("z",K "S" [K "0" []]),("z",K "S" [K "S" [K "0" []]]),("x",K "0" []),("y",K "S" [K "S" [K "0" []]]),("z",K "S" [K "S" [K "S" [K "0" []]]])]],[])
ex25 = nnstep 20 (mem2,add("z","z")) == ([[("z",K "S" [K "S" [K "S" [K "S" [K "S" [K "S" [K "0" []]]]]]]),("z",K "0" []),("z",K "S" [K "0" []]),("z",K "S" [K "S" [K "0" []]]),("x",K "0" []),("y",K "S" [K "S" [K "0" []]]),("z",K "S" [K "S" [K "S" [K "0" []]]])]],[])
ex26 = nnstep 20 (mem2,prod("z","y")) == ([[("z",K "S" [K "S" [K "S" [K "S" [K "S" [K "S" [K "0" []]]]]]]),("z",K "0" []),("z",K "S" [K "0" []]),("z",K "S" [K "S" [K "0" []]]),("x",K "0" []),("y",K "S" [K "S" [K "0" []]]),("z",K "S" [K "S" [K "S" [K "0" []]]])]],[])


rev:: (Id,Id) -> Prog
rev (l,rev) = [LOCAL ["aux","acum"]
		[ASG("aux",V l), ASG("acum",C "Nil" []),
		 WHILE "aux" 
		 	[("Cons",(["head","tail"],
					[ASG("acum",C "Cons" [V "head",V "acum"]),
					 ASG("aux",V "tail")]))],
					 ASG(rev,V "acum") ]
		]


l0 :: Val
l0 = K "Nil" [] -- l0 = []
l1 :: Val
l1 = K "Cons" [one,l0] -- l1 = [1]
l2 = K "Cons" [one,K "Cons" [two,l0]] -- l2 = [1,2]
l2R = K "Cons" [two,K "Cons" [one,l0]] -- l2R = [2,1]
l3 = K "Cons" [one,K "Cons" [two,K "Cons" [three,l0]]]  -- l3 = [1,2,3]
l3R = K "Cons" [three,K "Cons" [two,K "Cons" [one,l0]]]  -- l3 = [3,2,1]
mem3::Mem
mem3 = [[("l1",l1),("l2",l2),("l3",l3),("l2R",l2R)]]

ex27 = lkup(fst(nnstep 30 (mem3,rev("l3","rev")))) "rev" == l3R
ex28 = lkup(fst(nnstep 30 (mem3,rev("l2R","rev")))) "rev" == l2