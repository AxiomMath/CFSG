module

public import Certificates.Kernel.Sporadic.ONC.Defs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ONC

open CFSG.KC.Enum CFSG.KS CFSG.KS.ON CFSG.KS.PEnum CFSG.KS.ONC

set_option Elab.async false

theorem let_table : Bool.rec (motive := fun _ => Bool) true false
    (letS ML (fun l x => LJ l (Nat.succ x)) (key ONW.K) (nat_lit 245520) (nat_lit 5)) = true := by
  quickRfl

theorem let_matrix : Bool.rec (motive := fun _ => Bool) true false
    (letS (fun _ => ONE) LJ (key ONW.K) (nat_lit 245520) (nat_lit 5)) = true := by
  quickRfl

theorem slp_inverse : Bool.rec (motive := fun _ => Bool) true false
    (slpK CFSG.Sporadic.ON.Native.prog (nat_lit 26) (fun j => List.getD ONW.LA j (nat_lit 0))
      (fun j => List.getD ONW.LB j (nat_lit 0)) (fun _ => ONE) ML
      CFSG.Sporadic.ON.Native.sel.toList) = true := by
  quickRfl

theorem slp_final : Bool.rec (motive := fun _ => Bool) true false
    (slpK CFSG.Sporadic.ON.Native.prog (nat_lit 26) (fun j => List.getD ONW.LA j (nat_lit 0))
      (fun j => List.getD ONW.LB j (nat_lit 0)) MV (fun j => ML (Nat.succ j))
      CFSG.Sporadic.ON.Native.sel.toList) = true := by
  quickRfl

end CertificateChecks.KernelSpor.ONC

end
