module

public import Certificates.Data.Kernel.LocalQT.LatM
public import Certificates.Data.Kernel.LocalQT.ChainInj
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListA7LatticeInputs
public import CFSG.Certificates.Kernel.LocalQTPermSound
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

public section

namespace CFSG.KD.LQT.C4083

open CFSG.KC.LQT.L CFSG.KC.LQT.S CFSG.KC.LQT.P CFSG.QuasithinUnique.Vol2Native.A312L.Seven

@[expose] def C : List Lvl :=
  [(0, [6614517792, 5574330369, 6614516738, 5574296579, 6613435396, 4499506181, 5506139142], [0, 1, 2, 3, 4, 5, 6], 7),
    (1, [0, 6614517792, 5574329408, 6614484064, 5573248128, 6579881120, 4465951936], [0, 0, 1, 2, 3, 4, 5], 6),
    (2, [0, 0, 6614517792, 5574298656, 6613438496, 4499510304, 5506144288], [0, 0, 0, 1, 2, 3, 4], 5),
    (3, [0, 0, 0, 6614517792, 5573314592, 6579980320, 4466083872], [0, 0, 0, 0, 1, 2, 3], 4),
    (4, [0, 0, 0, 0, 6614517792, 4501637152, 5509318688], [0, 0, 0, 0, 0, 1, 2], 3)]

theorem f1 : memIff7 C depth ((latGens.getD 10 []).map code)
    (fun x => Nat.beq (img x ((6 : Fin 7) : ℕ)) ((6 : Fin 7) : ℕ)) = true := by quickRfl
theorem f2 : memIff7 C depth ((latGens.getD 7 []).map code) (fun x => CFSG.KC.Ord.andB
    (CFSG.KC.Ord.orB (Nat.beq (img x ((4 : Fin 7) : ℕ)) ((4 : Fin 7) : ℕ))
      (Nat.beq (img x ((4 : Fin 7) : ℕ)) ((5 : Fin 7) : ℕ)))
    (CFSG.KC.Ord.orB (Nat.beq (img x ((5 : Fin 7) : ℕ)) ((4 : Fin 7) : ℕ))
      (Nat.beq (img x ((5 : Fin 7) : ℕ)) ((5 : Fin 7) : ℕ)))) = true := by quickRfl
theorem f3 : allL (dGens.map code) (even 7) = true := by quickRfl
theorem inj : chainInj 7 C = true := by quickRfl

end CFSG.KD.LQT.C4083

end
