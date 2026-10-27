module

public import Certificates.Data.Kernel.LocalQT.CoreS
public import Certificates.Kernel.LocalQT.Core.D4074
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option Elab.async false

public section

namespace CFSG.KD.LQT.C4074

open CFSG.KC.LQT.Syl CFSG.KC.LQT.W CFSG.KC.LQT.P CFSG.KC.LQT.L

noncomputable abbrev clP : Nat → Bool := fun s =>
  allL (nWL.map (evalWK 23 GL)) fun g => inC 23 C (chainF C) (mul 23 s g)

noncomputable abbrev hyP : Nat → Bool := hypAx 23 (eWL.map (evalWK 23 GL))

theorem hE : eK 23 (eWL.map (evalWK 23 GL)) = true := by quickRfl
theorem hC : chainOK 23 C = true := by quickRfl
theorem hg : allL (nWL.map (evalWK 23 GL)) (inC 23 C (chainF C)) = true := by quickRfl
theorem hw : wordsC 23 C (nWL.map (evalWK 23 GL)) W 22 = true := by quickRfl
theorem hL : chainF C = 40320 := by decide +kernel
theorem hN : normK 23 (eWL.map (evalWK 23 GL)) (nWL.map (evalWK 23 GL)) = true := by quickRfl
theorem hO : orbK 23 GL (eWL.map (evalWK 23 GL)) rTL 40320 10200960 = true := by quickRfl

@[expose] noncomputable def clC (j : Nat) : Bool := chainChunk 23 C clP j

@[expose] noncomputable def hyC (j : Nat) : Bool := chainChunk 23 C hyP j

end CFSG.KD.LQT.C4074

end
