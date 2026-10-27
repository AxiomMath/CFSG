module

public import Certificates.Kernel.Sporadic.OddCore.RowsCmd
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.HeE8Check
public meta import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.HeE8Check

public section

namespace CFSG.KD.HeTab

open CFSG.Sporadic.He.Native CFSG.Sporadic.Th.Native CFSG.EvenSporadicStandard.Induction

meta def orbM : VOrbit := orbitData ()

meta def biM : Array Nat := Id.run do
  let mut r := Array.replicate 8330 0
  for i in [0:8330] do
    r := r.set! (orbM.beta[i]!).toNat i
  return r

meta def wordM (w : List Int) : Array Nat := (wordT 8330 (genTables orbM) w).map (·.toNat)

meta def wxM : Array Nat := wordM heWordE1
meta def wyM : Array Nat := wordM heWordE2
meta def wzM : Array Nat := wordM heWordE3

end CFSG.KD.HeTab

#krows CFSG.KD.HeTab.BI CFSG.KD.HeTab.biM
#krows CFSG.KD.HeTab.WX CFSG.KD.HeTab.wxM
#krows CFSG.KD.HeTab.WY CFSG.KD.HeTab.wyM
#krows CFSG.KD.HeTab.WZ CFSG.KD.HeTab.wzM

end
