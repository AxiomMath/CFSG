module

public import Certificates.Data.Kernel.ThCentU.Defs
public import Certificates.Kernel.ThCentU.Data
public import Certificates.Kernel.ThCent.Data3C
public import CFSG.Certificates.Kernel.Th.S.Data.Sm_Sel
public import CFSG.Certificates.Kernel.Th.S.Data.Sm_const
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabThCensusInputs
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Each

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelThCentU

open CFSG.KC.Th CFSG.KC.ThCent CFSG.KC.ThCentU CFSG.KD CFSG.KD.ThCentU CFSG.KC.Misc.Clos

@[expose] noncomputable def AG (l : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) A2 A1 (Nat.beq l (nat_lit 0))

@[expose] noncomputable def ch17307P (k : Nat) : Bool :=
  Nat.beq (runPk ThS.c ThS.rm ThS.ONE CFSG.HardMathSupport.Dickson.I271.TabThNative.progU
    (initPk (ThS.RBf 1) (ThS.RBf 2) ThS.ONE) (Nat.add 20 k)) (MT (Nat.add 10 k))

#kc_each ch17307P 0 2

theorem ch17307W0 : Nat.beq (wordH ThS.c ThS.rm ThS.ONE (MT 10) (MT 11) w0) (MT 0) = true := by
  quickRfl
theorem ch17307W1 : Nat.beq (wordH ThS.c ThS.rm ThS.ONE (MT 10) (MT 11) w1) (MT 1) = true := by
  quickRfl
theorem ch17307W2 : Nat.beq (wordH ThS.c ThS.rm ThS.ONE (MT 10) (MT 11) w2) (MT 2) = true := by
  quickRfl
theorem ch17307W3 : Nat.beq (wordH ThS.c ThS.rm ThS.ONE (MT 10) (MT 11) w3) (MT 3) = true := by
  quickRfl
theorem ch17307W4 : Nat.beq (wordH ThS.c ThS.rm ThS.ONE (MT 10) (MT 11) w4) (MT 4) = true := by
  quickRfl

@[expose] noncomputable def ch17307S (i : Nat) : Bool :=
  CFSG.KC.Ord.andB (Nat.beq (mulB ThS.c ThS.rm (MT i) (MT i)) (MT (Nat.add 5 i)))
    (Nat.beq (mulB ThS.c ThS.rm (MT i) (MT (Nat.add 5 i))) ThS.ONE)

#kc_each ch17307S 0 5

@[expose] noncomputable def ch17307C (k : Nat) : Bool :=
  CFSG.KC.LQT.P.impB (Nat.blt (Nat.div k 5) (Nat.mod k 5))
    (Nat.beq (mulB ThS.c ThS.rm (MT (Nat.div k 5)) (MT (Nat.mod k 5)))
      (mulB ThS.c ThS.rm (MT (Nat.mod k 5)) (MT (Nat.div k 5))))

#kc_each ch17307C 0 25

@[expose] noncomputable def ch17307U (l : Nat) : Bool :=
  Nat.beq (mulB ThS.c ThS.rm ThCent.W3.Z3C (MT (Nat.add 10 l)))
    (mulB ThS.c ThS.rm (MT (Nat.add 10 l)) ThCent.W3.Z3C)

#kc_each ch17307U 0 2

@[expose] noncomputable def ch17307A (k : Nat) : Bool :=
  conjK ThS.c ThS.rm ThS.ONE MT (AG (Nat.div k 5)) (Nat.div k 5) (Nat.mod k 5)

#kc_each ch17307A 0 10

theorem ch17307V : Nat.blt (MT 12) (Nat.pow 2 248) = true := by
  quickRfl

@[expose] noncomputable def ch17307K (b : Nat) : Bool :=
  allR (Nat.mul 27 b) 27 fun c => Nat.beq (TB (Nat.add 2160 c)) (keyK ThS.rm MT c)

#kc_each ch17307K 0 9

theorem ch17307Q :
    allR 0 243 (sortAt 243 (fun c => TB (Nat.add 2160 c)) fun i => TB (Nat.add 2403 i)) = true := by
  quickRfl

@[expose] noncomputable def ch17307T (b : Nat) : Bool :=
  allR (Nat.mul 48 b) 48 (node5 AG 2 TB fun k => TB (Nat.add 720 k))

#kc_each ch17307T 0 15

theorem ch17307E : allR 0 720 (sortAt 720 TB fun i => TB (Nat.add 1440 i)) = true := by
  quickRfl

end CertificateChecks.KernelThCentU

end
