module

public import Certificates.Kernel.Sporadic.RawGenSplitP
public import Certificates.Kernel.Sporadic.Fi22.X2069PT
public meta import CFSG.Monster.B.Fischer.Fi22OrderCheckInputs
public meta import CFSG.Monster.B.Fischer.PinnedChainInputs

public section

set_option maxRecDepth 400000
set_option Elab.async false

#ks_rawchain_sl2_data CertificateChecks.KernelSpor.Fi22PC 3510 12 0 64
  CFSG.Monster.B.Fischer.fi22StrongArrs CFSG.Monster.B.Fischer.fi22BaseArr 19
  CertificateChecks.KernelSpor.Fi22X.nilD

end
