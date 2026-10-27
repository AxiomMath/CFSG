module

public import Certificates.Kernel.Q7Bits.Data
public import CFSG.Certificates.Kernel.Q7BitsSound
import CFSG.Certificates.Kernel.Common.ForallChunks
import Certificates.Kernel.Q7Bits.R0
import Certificates.Kernel.Q7Bits.R1
import Certificates.Kernel.Q7Bits.R2
import Certificates.Kernel.Q7Bits.R3
import Certificates.Kernel.Q7Bits.R4
import Certificates.Kernel.Q7Bits.R5
import Certificates.Kernel.Q7Bits.R6
import Certificates.Kernel.Q7Bits.R7
import Certificates.Kernel.Q7Bits.R8
import Certificates.Kernel.Q7Bits.R9
import Certificates.Kernel.Q7Bits.R10
import Certificates.Kernel.Q7Bits.R11
import Certificates.Kernel.Q7Bits.R12
import Certificates.Kernel.Q7Bits.Neg
public import CFSG.Sporadic.Schreier.J4SOrder

public section

namespace CFSG.KD.Q7Bits

open CFSG.Certificates.Kernel.Q7Bits CFSG.ClassicalInvolution.PhanB3.S.Std.Q7

#kc_forall_chunks rowsOK (fun k => rowOK k = true) 91 CFSG.KD.Q7Bits.rowOK 1

theorem q7MuCheck_kernel : q7MuCheck = true :=
  q7MuCheck_of_rows (fun i => rt.getD i 0) (fun i => lv.getD i []) rowsOK

end CFSG.KD.Q7Bits
