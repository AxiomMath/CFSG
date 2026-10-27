module

public import Certificates.Data.Kernel.M24R.N8K

public section

set_option profiler true
set_option profiler.threshold 200

namespace CFSG.KC.N8K

theorem n8k_count : glCountK = true := by decide +kernel

end CFSG.KC.N8K

end
