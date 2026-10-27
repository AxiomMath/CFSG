module

public import CFSG.Sporadic.Recognition.J3MultiplierCover
public import CFSG.Certificates.CosetTablePresented
public import Certificates.Kernel.Bounds.Family
public import CFSG.Certificates.CosetTableShort
public import CFSG.Certificates.NativeSchreierCard
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.Open.Defs

open CFSG.CosetTable CFSG.Sporadic.Recognition.J3Multiplier

public section

#kb_family "data/J3U.json" 6525 17445354809841339518 (uhat := uhatWords)
  (uhatc := restrictWords (subsetOf 3 [1]) uhatWords)

end
