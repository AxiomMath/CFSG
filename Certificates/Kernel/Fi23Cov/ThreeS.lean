module

public import Certificates.Kernel.Fi23Cov.Three
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.SliceRange

set_option Elab.async false
public section

#kc_slice_range CFSG.KD.Fi23Cov.cS CFSG.KD.Fi23Cov.Ck.cS 0 13
#kc_slice_range CFSG.KD.Fi23Cov.dS CFSG.KD.Fi23Cov.Ck.dS 0 10

end
