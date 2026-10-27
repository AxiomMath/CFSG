module

public import Certificates.Kernel.Mathieu.RootData
public import Certificates.Kernel.Mathieu.M11Chains
public import Certificates.Data.Kernel.Mathieu.SylowK
import CFSG.Certificates.Kernel.Common.Harness

namespace CertificateChecks.KernelMathieu

open CFSG.KD.Mathieu CFSG.Monster.B.Mathieu CFSG.KC.MathieuK CFSG.KS.M11

set_option maxRecDepth 400000

example : (!sylowB 11 4 7920 3 Root11.c0.LR Root11.c0.TRI Root11.c0.BP 4 (P11.S 0) (P11.LR 0)
    (P11.TR 0) (P11.TRI 0) (P11.BP 0) (P11.nb 0) (m11RecordK.sylows.getD 0 default)) = true := by
  quickRfl

example : (!sylowB 11 4 7920 4 Root11.c0.LR Root11.c0.TRI Root11.c0.BP 4 (P11.S 0) (P11.LR 0)
    (P11.TR 0) (P11.TRI 0) (P11.BP 0) (P11.nb 0)
    { m11RecordK.sylows.getD 0 default with
      normalGeneration := (m11RecordK.sylows.getD 0 default).normalGeneration.tail }) = true := by
  quickRfl

example : (!ngB 11 4 3960 (Root11.c0.S 0) (Root11.c0.SI 0) (Root11.c0.S 1) (Root11.c0.SI 1)
    (N11s0.S 0) (N11s0.BP 0) (N11s0.LR 0)
    ((m11RecordK.sylows.getD 0 default).normalGeneration.getD 0 default)) = true := by
  quickRfl

example : (!ngB 11 4 7920 (Root11.c0.S 0) (Root11.c0.SI 0) (Root11.c0.S 1) (Root11.c0.SI 1)
    (N11s0.S 0) (N11s0.BP 0) (N11s0.LR 0)
    { (m11RecordK.sylows.getD 0 default).normalGeneration.getD 0 default with
      conjugators := [1] :: ((m11RecordK.sylows.getD 0 default).normalGeneration.getD 0
        default).conjugators.tail }) = true := by
  quickRfl

example : (!elemOK 11 4 [0, 0, 2, 3, 4, 5, 6, 7, 8, 9, 10]) = true := by
  quickRfl

example : (!repK 11 4 2 (P11.LR 0) (P11.TRI 0) (P11.BP 0) (P11.nb 0)
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]) = true := by
  quickRfl

end CertificateChecks.KernelMathieu
