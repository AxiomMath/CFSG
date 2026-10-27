module

public import Certificates.Data.Kernel.M24R.N8K
public import Certificates.Kernel.N8.Data

public section

set_option Elab.async false
set_option profiler true
set_option profiler.threshold 200

namespace CFSG.KC.N8K

open CFSG.KD.N8K in
theorem n8k_words : glFresh [W0, W1, W2, W3, W4, W5, W6, W7, W8, W9] 0 0 = true := by
  decide +kernel

end CFSG.KC.N8K

end
