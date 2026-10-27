module

public import Certificates.Data.Kernel.LocalQT.Pairs
public import Certificates.Data.Kernel.LocalQT.Outer
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporM12Data
public import Certificates.Kernel.LocalQT.Pairs.D4093
import CFSG.Certificates.Kernel.Common.Harness
public import Mathlib.GroupTheory.Perm.Cycle.Type

set_option maxRecDepth 100000
set_option Elab.async false

public section

namespace CFSG.KD.LQT.C4093

open CFSG.KC.LQT.Pairs CFSG.KC.LQT.W CFSG.KC.LQT.P CFSG.KC.LQT.L CFSG.KC.Ord CFSG.KC.LQT.S
  CFSG.QuasithinUnique.Vol2Native.L239.M12Pairs

@[expose] def GC : List Nat := [184726996899603491, 365002956609719367]

noncomputable abbrev S0C : List Nat := clK 12 (List.map (evalZK 12 GC) s0Words) 6
noncomputable abbrev K1C : List Nat :=
  clK 12 (List.map (evalZK 12 GC) (s0Words ++ [tWords.getD 0 []])) 6
noncomputable abbrev K2C : List Nat :=
  clK 12 (List.map (evalZK 12 GC) (s0Words ++ [tWords.getD 1 []])) 6
noncomputable abbrev Q1C : List Nat := clK 12 (List.map (evalZK 12 GC) q1Words) 5
noncomputable abbrev Q2C : List Nat := clK 12 (List.map (evalZK 12 GC) q2Words) 7
noncomputable abbrev A1C : List Nat := centerK 12 S0C
noncomputable abbrev A2C : List Nat := centDK 12 S0C

theorem kS : subFacts 12 6 S0C = true := by quickRfl
theorem kA : andB (Nat.beq (lenL A1C) 2) (Nat.beq (lenL A2C) 16) = true := by quickRfl
theorem kK1 : andB (Nat.beq (lenL K1C) 192) (CFSG.KC.LQT.T2.distinctS K1C) = true := by quickRfl
theorem kK2 : andB (Nat.beq (lenL K2C) 192) (CFSG.KC.LQT.T2.distinctS K2C) = true := by quickRfl
theorem kN1 : allL K1C (nrmK 12 A1C (List.take 3 A1C)) = true := by quickRfl
theorem kN2 : allL K2C (nrmK 12 A2C (List.take 3 A2C)) = true := by quickRfl
theorem kQ1 : normFacts 12 5 6 K1C Q1C = true := by quickRfl
theorem kQ2 : normFacts 12 5 6 K2C Q2C = true := by quickRfl
@[expose] def JC : List Nat :=
  [257027720345619488, 372784167072859200, 75690421435869312, 152313533531523109,
    372996237422727200, 152211245531141121]
theorem kJ : allL JC (fun g => memL g (K1C ++ K2C)) = true := by quickRfl
theorem kC : chainOK 12 CFSG.KD.LQT.M12Chain.C = true := by quickRfl
theorem kg : allL GC (inC 12 CFSG.KD.LQT.M12Chain.C (chainF CFSG.KD.LQT.M12Chain.C)) = true := by
  quickRfl

noncomputable abbrev clP : Nat → Bool := fun s =>
  allL GC fun g => inC 12 CFSG.KD.LQT.M12Chain.C (chainF CFSG.KD.LQT.M12Chain.C) (mul 12 s g)

noncomputable abbrev cp1 : Nat → Bool := fun g =>
  impB (nrmK 12 A1C (List.take 3 A1C) g) (memL g K1C)

noncomputable abbrev cp2 : Nat → Bool := fun g =>
  impB (nrmK 12 A2C (List.take 3 A2C) g) (memL g K2C)

end CFSG.KD.LQT.C4093

end
