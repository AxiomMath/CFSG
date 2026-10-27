module

public import Certificates.Kernel.PhanD4Dce.CoverNData
public import Certificates.Kernel.PhanD4Dce.A3Codes
public import Certificates.Data.Kernel.TwistDce3.RelsNet

public section

namespace CFSG.KD.PhanD4Dce

open CFSG.KC.TwDce3

theorem omega_rels_net : relsN INVM NS 15 a3CodesL = true := by
  decide +kernel

end CFSG.KD.PhanD4Dce

end
