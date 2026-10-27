module

public import Certificates.Data.Kernel.LocalQT.CoreS
public import Certificates.Kernel.LocalQT.Core.D4078h
import CFSG.Certificates.Kernel.Common.Harness
import Certificates.Kernel.Sporadic.ON.Gen

set_option maxRecDepth 100000
set_option Elab.async false

public section

namespace CFSG.KD.LQT.C4078h

open CFSG.KC.LQT.Syl CFSG.KC.LQT.W CFSG.KC.LQT.P CFSG.KC.LQT.L

noncomputable abbrev clP : Nat → Bool := fun s =>
  allL (nWL.map (evalWK 22 GL)) fun g => inC 22 C (chainF C) (mul 22 s g)

noncomputable abbrev hyP : Nat → Bool := hypAx 22 (eWL.map (evalWK 22 GL))

theorem hE : eK 22 (eWL.map (evalWK 22 GL)) = true := by quickRfl
theorem hC : chainOK 22 C = true := by quickRfl
theorem hg : allL (nWL.map (evalWK 22 GL)) (inC 22 C (chainF C)) = true := by quickRfl
theorem hw : wordsC 22 C (nWL.map (evalWK 22 GL)) W 21 = true := by quickRfl
theorem hL : chainF C = 5760 := by decide +kernel
theorem hN : normK 22 (eWL.map (evalWK 22 GL)) (nWL.map (evalWK 22 GL)) = true := by quickRfl
theorem hO : orbK 22 GL (eWL.map (evalWK 22 GL)) rTL 5760 443520 = true := by quickRfl

@[expose] noncomputable def clC (j : Nat) : Bool := chainChunk 22 C clP j

@[expose] noncomputable def hyC (j : Nat) : Bool := chainChunk 22 C hyP j

end CFSG.KD.LQT.C4078h

#kon_slices CFSG.KD.LQT.C4078h.clC 0 22
#kon_slices CFSG.KD.LQT.C4078h.hyC 0 22
#kon_join CFSG.KD.LQT.C4078h.clAll CFSG.KD.LQT.C4078h.clC 22
#kon_join CFSG.KD.LQT.C4078h.hyAll CFSG.KD.LQT.C4078h.hyC 22

end
