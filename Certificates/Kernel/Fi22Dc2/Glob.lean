module

public import Certificates.Data.Kernel.Fi22Dc2.Defs
public import Certificates.Data.Kernel.SporLatDc2Check
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.Fi22Dc2

open CFSG.KC.SLD2

theorem glob : globOK C D = true := by
  quickRfl

theorem frest : fRestOK C D = true := by
  quickRfl

theorem ridx : rootIdxOK C D = true := by
  quickRfl

theorem bo0 : borbOK C D (D.bo.getD 0 default) = true := by
  quickRfl

theorem bo1 : borbOK C D (D.bo.getD 1 default) = true := by
  quickRfl

theorem perm : permOK = true := by
  quickRfl

theorem hwB : hwOK = true := by
  quickRfl

theorem sepB : (D.sep == [0, 1, 2, 3, 6, 4].map P) = true := by
  quickRfl

theorem lens : (Nat.beq D.bo.length 2 && Nat.beq D.R1.length 45 && Nat.beq D.roots.length 73) =
    true := by
  quickRfl

end CFSG.KD.Fi22Dc2

end
