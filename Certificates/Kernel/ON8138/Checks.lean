module

public import Certificates.Data.Kernel.ON8138.Defs
public import Certificates.Kernel.ON8138.Data
public import CFSG.RankThree.Native.ONTripleAutData
import CFSG.Certificates.Kernel.Common.Harness
public import Mathlib

public section

namespace CertificateChecks.KernelON8138

open CFSG.KC.ON8138 CFSG.KD.ON8138 CFSG.RankThree.Native.ONTriple

theorem r0 : r0OK R0K R0I R0codes = true := by quickRfl

theorem words : wordsOK R0words R0codes = true := by quickRfl

theorem mask : maskOK MK = true := by quickRfl

theorem cos : cosOK R0K TK TI TW = true := by quickRfl

end CertificateChecks.KernelON8138

end
