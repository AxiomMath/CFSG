module

public import Certificates.Kernel.Fi22Twist.Q01Each
public import Certificates.Kernel.Sporadic.HexNumsGen
public import Certificates.Data.Kernel.Fi22Rk.Defs
public import Certificates.Data.Fi22TwistData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelFi22Twist.Q0X CFSG.LocalAnalysis.GLTheoremA.H1017.Fi22TwistNative.qGensHex0
#ks_hexnums CertificateChecks.KernelFi22Twist.Q0X
  CFSG.LocalAnalysis.GLTheoremA.H1017.Fi22TwistNative.qGensHex0 3 12

#ks_chars CertificateChecks.KernelFi22Twist.Q1X CFSG.LocalAnalysis.GLTheoremA.H1017.Fi22TwistNative.qGensHex1
#ks_hexnums CertificateChecks.KernelFi22Twist.Q1X
  CFSG.LocalAnalysis.GLTheoremA.H1017.Fi22TwistNative.qGensHex1 3 12

namespace CertificateChecks.KernelFi22Twist

open CFSG.KC.Enum CFSG.KC.Fi22Rk CFSG.KD.Fi22Twist

theorem ch431009q0x : rowsK 3510 12 3 Q0X.F (fun k => KQ (Nat.succ k)) = true := by quickRfl

theorem ch431009q1x : rowsK 3510 12 3 Q1X.F (fun k => KQ1 (Nat.succ k)) = true := by quickRfl

theorem n431009q0x :
    Bool.not (rowsK 3510 12 3 Q0X.F (fun k => Nat.xor (KQ (Nat.succ k)) 1)) = true := by
  quickRfl

end CertificateChecks.KernelFi22Twist

end
