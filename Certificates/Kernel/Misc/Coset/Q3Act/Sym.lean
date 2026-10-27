module

public import Certificates.Data.Kernel.Misc.Coset.CovActSym
public import Certificates.Kernel.Misc.Coset.Q3Act.Data
public import Certificates.Kernel.Misc.Coset.Q3Act.Rels
public import CFSG.Sporadic.Presentation.Common

public section

namespace CFSG.KAct.Q3

theorem sym : CFSG.KC.MiscCoset.CovAct.symOK 3 11 25 zs mac chk (wsQN CFSG.KD.OrdFi24p.rels) hint =
    true := by
  decide +kernel

end CFSG.KAct.Q3
