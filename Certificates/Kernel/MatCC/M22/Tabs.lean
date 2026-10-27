module

public import CFSG.Sporadic.Recognition.M22MultiplierInputs
public import CFSG.Certificates.CosetTablePresented
public import Certificates.Kernel.Bounds.Family
public import CFSG.Certificates.CosetTableShort
public import CFSG.Certificates.NativeSchreierCard
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.Open.Defs

open CFSG.CosetTable CFSG.Sporadic.Recognition.M22Multiplier

public section

#kb_family "data/M22.json.gz" 1569 5554640704730688663 (m22 := m22Rels)
  (m22b := restrictWords (subsetOf 2 [1]) m22Rels)

end
