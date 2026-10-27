module

import CFSG.Certificates.Kernel.Common.SliceRange
public import Certificates.Kernel.Sporadic.Fi24Seven.DataI

public section

set_option maxRecDepth 400000
set_option maxHeartbeats 0
set_option Elab.async false

namespace CFSG.KD.F24S

#kc_slice_range CK ck 107 108
#kc_slice_range CKI cki 108 109
#kc_slice_range CK ck 109 110
#kc_slice_range CKI cki 110 111
#kc_slice_range CK ck 111 112
#kc_slice_range CKI cki 112 113
#kc_slice_range CK ck 113 114
#kc_slice_range CKI cki 114 115

theorem gi_ok : GI = true := by quickRfl

end CFSG.KD.F24S
