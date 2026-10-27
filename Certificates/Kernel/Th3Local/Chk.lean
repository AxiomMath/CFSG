module

public import Certificates.Data.Kernel.Th3Local.Defs
public import CFSG.Certificates.Kernel.Th.S.Data.Sm_Sel
public import CFSG.Certificates.Kernel.Th.S.Data.Sm_const
public import CFSG.HardMathSupport.Dickson.Sec6.Up34SporAux.ThThreeInputs
import CFSG.Certificates.Kernel.BabyMonster.Load

public section

namespace CFSG.KD.Th3Local

open CFSG.KC.Th CFSG.KC.Th.BigS CFSG.KC.ThCent CFSG.KC.Th3Local

@[expose] noncomputable def reg (r : Nat) : Nat :=
  runPk ThS.c ThS.rm ThS.ONE CFSG.HardMathSupport.Dickson.Sec6.Up34Th.ThThreeNative.prog3
    (initPk (ThS.RBf 1) (ThS.RBf 2) ThS.ONE) r

@[expose] noncomputable def ordB (r p : Nat) : Bool :=
  strictF (reg r) fun M => ordPk ThS.c ThS.rm ThS.ONE M p

@[expose] noncomputable def commB (r q : Nat) : Bool :=
  strictF (reg r) fun S => strictF (reg q) fun V => commPk ThS.c ThS.rm S V

#bm_bool CFSG.KD.Th3Local ord11 (ordB 11 3)
#bm_bool CFSG.KD.Th3Local ord12 (ordB 12 13)
#bm_bool CFSG.KD.Th3Local ord14 (ordB 14 7)
#bm_bool CFSG.KD.Th3Local comm14 (commB 11 14)
#bm_bool CFSG.KD.Th3Local comm12 (commB 11 12)

end CFSG.KD.Th3Local

end
