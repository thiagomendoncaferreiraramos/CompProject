{-# OPTIONS_GHC -fno-warn-tabs #-}
{- HLINT ignore "Use if" -}

module Imp where

type Id = String

type Prog = [Instr]

data Instr =   ASS (Id,Exp)
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

--------Examples------------------------------------------
add::(Id,Id) -> Prog  -- a:= a+b
add (a,b) = [LOCAL ["aux","i"]
				   [ASS ("aux",V b),ASS ("i",V a),
				    WHILE "i" [("S",(["x1"],[ASS ("i",V "x1"),ASS ("aux",C "S" [V "aux"])]))],
					ASS (a,V "aux")
				  ]
			]

add3::(Id,Id,Id) -> Prog  -- sab:= a+b
add3 (a,b,sab) = [LOCAL ["aux"]
				   [ASS (sab,V b),ASS ("aux",V a),
				    WHILE "aux" [("S",(["x1"],[ASS (sab,C "S" [V sab]),ASS ("aux",V "x1")]))]
				  ]
			]

			
prod::(Id,Id) -> Prog  -- a:= a*b
prod (a,b) = [LOCAL ["prod","i"]
			  		[ASS ("prod",val2exp zero),ASS("i",V a),
				    WHILE "i" [("S",(["k1"],ASS ("i",V "k1"):add("prod",b)))],
					ASS (a,V "prod")
				  ]
			]

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

--------Examples------------------------------------------
e1 = lkup mem "x" == zero
e2 = lkup mem "y" == one
e3 = lkup mem1 "x"  == two
e4 = lkup mem1 "y" == one
e5 = upd ("x",one) mem == [[("x",one),("x",zero),("y",one)]]
e55 = upd ("x",zero) mem1 == [[("x",zero),("x",two)],
                              [("x",zero),("y",one)]] 
e6 = upd ("y",zero) mem1 == [[("x",two)],
							 [("y",zero),("x",zero),("y",one)]]
e7 = upd ("z",zero) mem == [[("z",zero),("x",zero),("y",one)]]
e8 = upd ("z",zero) mem1 == [[("x",two)],
							 [("z",zero),("x",zero),("y",one)]]
e9 = lkup (upd  ("x",one) mem) "x" == one
e10 = lkup (upd  ("z",two) mem) "x" == zero
e11 = (lkup (upd  ("z",two) mem1) "z") == two
-------------------------------------------------------

eval :: Mem -> Exp -> Val
eval m (V x) = lkup m x
eval m (C id exps) = K id (map (eval m) exps)
 
step :: (Mem,Prog) -> (Mem,Prog)
step (m, ASS (id,exp) :p') = (upd (id,eval m exp) m,p')
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

step2  :: (Mem,Prog) -> (Mem,Prog)
step2 (m,p) = step(step (m,p))
step3 = step.step2
step6 = step3.step3
nnstep :: Int -> (Mem,Prog) -> (Mem,Prog) --- no da error con p = []
nnstep n (m,[]) = (m,[])
nnstep 0 (m,p) = (m,p)
nnstep n (m,p)= nnstep (n-1) (step (m,p))
--Examples------------------------------------------
p1 = [ASS ("x",V "y")]
p2 = [ASS ("y",val2exp three)]
p3 = [ASS ("z",val2exp one)]
e12 = step (mem,p1) == ([[("x",one),("x",zero),("y",one)]],[])
e13 = step (mem1,p1) == ([[("x",one),("x",two)],
                          [("x",zero),("y",one)]],
						[])
e14 = step (mem1,p2) == ([[("x",two)],
						  [("y",one),("x",zero),("y",one)]],
						[])
e15 = step (mem1,p3) == ([[("x",two)],
						  [("z",one),("x",zero),("y",one)]],
						[])
p4 = [CASE "x" [("0",([],p3)),("S",(["x"],p2))]]
e16 = step (mem,p4) == ([[],
						 [("x",K "0" []),("y",one)]],
						[ASS ("z",C "S" [C "0" []]),POP])
e17 = step2 (mem,p4) == ([[],
                          [("z",one),("x",K "0" []),("y",one)]],
						 [POP])
e18 = step3 (mem,p4) == ([[("z",one),("x",K "0" []),("y",one)]],
                         [])						
p5 = [WHILE "x" [("S",(["w"],[ASS ("x",V "w")]))]]
e19 = step(mem1,p5) == ([[("w",one)],
						 [("x",two)],
						 [("x",K "0" []),("y",one)]],
						[ASS ("x",V "w"),POP,WHILE "x" [("S",(["w"],[ASS ("x",V "w")]))]])
e20 = step2(mem1,p5) == ([[("w",one)],
						  [("x",one),("x",two)],
						  [("x",zero),("y",one)]],
						 [POP,WHILE "x" [("S",(["w"],[ASS ("x",V "w")]))]])
e21 = step3(mem1,p5) == ([[("x",one),("x",two)],
                          [("x",zero),("y",one)]],
						[WHILE "x" [("S",(["w"],[ASS ("x",V "w")]))]])
e22 = step6(mem1,p5) == ([[("x",zero),("x",one),("x",two)],
						  [("x",zero),("y",one)]],
						[WHILE "x" [("S",(["w"],[ASS ("x",V "w")]))]])
e23 = step(step6(mem1,p5)) == ([[("x",zero),("x",one),("x",two)],
							    [("x",zero),("y",one)]],
							   [])	
e24 = nnstep 20 (mem2,add("z","y")) == ([[("z",K "S" [K "S" [K "S" [K "S" [K "S" [K "0" []]]]]]),("z",K "0" []),("z",K "S" [K "0" []]),("z",K "S" [K "S" [K "0" []]]),("x",K "0" []),("y",K "S" [K "S" [K "0" []]]),("z",K "S" [K "S" [K "S" [K "0" []]]])]],[])
e25 = nnstep 20 (mem2,add("z","z")) == ([[("z",K "S" [K "S" [K "S" [K "S" [K "S" [K "S" [K "0" []]]]]]]),("z",K "0" []),("z",K "S" [K "0" []]),("z",K "S" [K "S" [K "0" []]]),("x",K "0" []),("y",K "S" [K "S" [K "0" []]]),("z",K "S" [K "S" [K "S" [K "0" []]]])]],[])
e26 = nnstep 20 (mem2,prod("z","y")) == ([[("z",K "S" [K "S" [K "S" [K "S" [K "S" [K "S" [K "0" []]]]]]]),("z",K "0" []),("z",K "S" [K "0" []]),("z",K "S" [K "S" [K "0" []]]),("x",K "0" []),("y",K "S" [K "S" [K "0" []]]),("z",K "S" [K "S" [K "S" [K "0" []]]])]],[])
