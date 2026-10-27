module

public import Certificates.Data.Kernel.Fi23Tw.Defs
public import Certificates.Kernel.Fi23K.Tabs
public import Certificates.Kernel.Fi23Cls.Data
public import Certificates.Kernel.Fi23Tw.Data

public section

namespace CFSG.KD.Fi23Tw

open CFSG.KC.Fi23Tw CFSG.KD.Fi23K CFSG.KD.Fi23Cls

@[expose] def w2 : List Nat := [4, 5, 2, 1]

@[expose] noncomputable def mat0 : Bool := matK G A L2 (nat_lit 0) (nat_lit 15)
@[expose] noncomputable def mat1 : Bool := matK G A L2 (nat_lit 15) (nat_lit 15)
@[expose] noncomputable def mat2 : Bool := matK G A L2 (nat_lit 30) (nat_lit 15)
@[expose] noncomputable def mat3 : Bool := matK G A L2 (nat_lit 45) (nat_lit 15)
@[expose] noncomputable def mat4 : Bool := matK G A L2 (nat_lit 60) (nat_lit 15)
@[expose] noncomputable def mat5 : Bool := matK G A L2 (nat_lit 75) (nat_lit 15)
@[expose] noncomputable def mat6 : Bool := matK G A L2 (nat_lit 90) (nat_lit 15)
@[expose] noncomputable def mat7 : Bool := matK G A L2 (nat_lit 105) (nat_lit 15)
@[expose] noncomputable def mat8 : Bool := matK G A L2 (nat_lit 120) (nat_lit 15)

@[expose] noncomputable def tw0 : Bool := twLoop A (nat_lit 1215) (nat_lit 0) T0
@[expose] noncomputable def tw1 : Bool := twLoop A (nat_lit 1215) (nat_lit 1215) T1
@[expose] noncomputable def tw2 : Bool := twLoop A (nat_lit 1215) (nat_lit 2430) T2
@[expose] noncomputable def tw3 : Bool := twLoop A (nat_lit 1215) (nat_lit 3645) T3
@[expose] noncomputable def tw4 : Bool := twLoop A (nat_lit 1215) (nat_lit 4860) T4
@[expose] noncomputable def tw5 : Bool := twLoop A (nat_lit 1215) (nat_lit 6075) T5
@[expose] noncomputable def tw6 : Bool := twLoop A (nat_lit 1215) (nat_lit 7290) T6
@[expose] noncomputable def tw7 : Bool := twLoop A (nat_lit 1215) (nat_lit 8505) T7
@[expose] noncomputable def tw8 : Bool := twLoop A (nat_lit 1215) (nat_lit 9720) T8
@[expose] noncomputable def tw9 : Bool := twLoop A (nat_lit 1215) (nat_lit 10935) T9
@[expose] noncomputable def tw10 : Bool := twLoop A (nat_lit 1215) (nat_lit 12150) T10
@[expose] noncomputable def tw11 : Bool := twLoop A (nat_lit 1215) (nat_lit 13365) T11
@[expose] noncomputable def tw12 : Bool := twLoop A (nat_lit 1215) (nat_lit 14580) T12
@[expose] noncomputable def tw13 : Bool := twLoop A (nat_lit 1215) (nat_lit 15795) T13
@[expose] noncomputable def tw14 : Bool := twLoop A (nat_lit 1215) (nat_lit 17010) T14
@[expose] noncomputable def pe : Bool := allL (fun e => bAnd(peK G L2 e, inTr L2 TR e)) PE
@[expose] noncomputable def key : Bool := keyK PE
@[expose] noncomputable def tri : Bool := allLL (trK G) TR
@[expose] noncomputable def trCm : Bool := cmAll G TR
@[expose] noncomputable def targ : Bool := allLL (tgK G w2 L2) TG

@[expose] noncomputable def rep0 : Bool := repAll G w2 TG R0
@[expose] noncomputable def rep1 : Bool := repAll G w2 TG R1
@[expose] noncomputable def rep2 : Bool := repAll G w2 TG R2
@[expose] noncomputable def rep3 : Bool := repAll G w2 TG R3
@[expose] noncomputable def rep4 : Bool := repAll G w2 TG R4
@[expose] noncomputable def rep5 : Bool := repAll G w2 TG R5
@[expose] noncomputable def rep6 : Bool := repAll G w2 TG R6
@[expose] noncomputable def rep7 : Bool := repAll G w2 TG R7
@[expose] noncomputable def rep8 : Bool := repAll G w2 TG R8
@[expose] noncomputable def rep9 : Bool := repAll G w2 TG R9
@[expose] noncomputable def rep10 : Bool := repAll G w2 TG R10
@[expose] noncomputable def rep11 : Bool := repAll G w2 TG R11

@[expose] noncomputable def covAll : Nat :=
  covU G w2 R11 (covU G w2 R10 (covU G w2 R9 (covU G w2 R8 (covU G w2 R7 (covU G w2 R6
    (covU G w2 R5 (covU G w2 R4 (covU G w2 R3 (covU G w2 R2 (covU G w2 R1
      (covU G w2 R0 (nat_lit 0))))))))))))

@[expose] noncomputable def cov : Bool :=
  Nat.beq covAll (Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 31671)) (nat_lit 1))

end CFSG.KD.Fi23Tw

end
