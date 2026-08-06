open import TMtoIMP

loop-invariant : (t : TM1tape) → (m1 m2 : Mem) → (c1 : Config (TM1tape2TM t)) →
               (Fin2Exp (proj₁ c1)) ≡ val2exp (lkup m1 "q") →
               Fin2Exp (proj₁ (1-step (TM1tape2TM t) c1)) ≡ val2exp (lkup m2 "q") →
               lkup m1 "q" ≢ Zv → 
               (m1 , myTail (TM2IMP t)) ▸* (m2 , myTail (TM2IMP t))


loop-invariant = {!!}
