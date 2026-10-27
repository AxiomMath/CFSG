module

public import Certificates.Data.NT44Model.Inputs
public import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Kernel.NT44.Pack2
public meta import Certificates.Data.NT44Model.Inputs
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelNT44

open CFSG.GH74.GLS.NT44.PermutationNative

meta def posM : Array (Array Nat) := #[Array.ofFn (n := 2688) fun y =>
  ((pts ()).toList.findIdx? (· == y.val)).getD 0]

end CertificateChecks.KernelNT44

end

#kmisc_packarrs CertificateChecks.KernelNT44.nt44Pos CertificateChecks.KernelNT44.posM 9

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelNT44

open CFSG.KC.Enum (pg)
open CFSG.KS (mask)
open CFSG.KC.LQT.P (allN)

@[expose] noncomputable def posAt (Pts Pos x : Nat) : Bool :=
  Nat.blt (pg 12 (mask 12) Pts x) 2688 && Nat.beq (pg 9 (mask 9) Pos (pg 12 (mask 12) Pts x)) x

theorem nt44_pos : allN 448 (posAt (nt44Pts 0) (nt44Pos 0)) = true := by quickRfl

theorem nt44_pos_neg : (!posAt (nt44Pts 0) (nt44Pos 0 + 1) 0) = true := by
  quickRfl

end CertificateChecks.KernelNT44

end
