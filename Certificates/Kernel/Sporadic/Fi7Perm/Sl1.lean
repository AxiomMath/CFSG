module

public import Certificates.Kernel.Sporadic.Fi7Perm.Data
import CFSG.Certificates.Kernel.Common.SliceRange

set_option Elab.async false

public section

#kc_slice_range CFSG.KD.Fi7Perm.slc CFSG.KD.Fi7Perm.Ck.slc 79 151

namespace CFSG.KD.Fi7Perm.Ck

theorem fEq_t : CFSG.KD.Fi7Perm.fEq = true := by quickRfl

theorem fNe_t : CFSG.KD.Fi7Perm.fNe = true := by quickRfl

end CFSG.KD.Fi7Perm.Ck

end
