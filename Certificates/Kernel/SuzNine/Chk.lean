module

public import Certificates.Kernel.SuzNine.Data
public import Certificates.Data.Kernel.SuzNine.Defs
public import Certificates.Kernel.Sporadic.SuzInv.Text1
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 500

public section

namespace CertificateChecks.KernelSuzNine

open CFSG.KC.SuzNine CFSG.KS.Raw

@[expose] noncomputable def HG (k : Nat) : Nat := CertificateChecks.KernelSpor.SuzInvT1.F (Nat.add 18 k)

theorem g_chk : CFSG.KC.Enum.allN 4 (fun j => CFSG.KC.Ord.andB (lettersK 10 (UW.getD j []))
    (CFSG.KC.Ord.andB (CFSG.KC.LQT.P.allL ((UW.getD j []).map CFSG.KS.Mathieu.icode) fun c =>
        Nat.beq (Nat.land c 1) 0)
      (Nat.beq (UGT j) (wordK 1782 11 (CFSG.KS.mask 11) (CFSG.KC.Enum.pidn 1782 11) HG HG
        (UW.getD j []))))) = true := by quickRfl

theorem ext_chk : CFSG.KC.Ord.andB (CFSG.KC.Enum.allN 6 fun t =>
      Nat.beq (fldK idKey t) ([0, 1, 2, 3, 4, 8].getD t 0))
    (CFSG.KC.Ord.andB (CFSG.KC.Enum.allN 4 fun j => CFSG.KC.Enum.allN 6 fun t =>
      Nat.beq (fldK idKey (Nat.add (Nat.mul 6 (Nat.succ j)) t)) (fldK (UGT j) (fldK idKey t)))
      (Nat.beq (Nat.shiftRight idKey 330) 0)) = true := by quickRfl

theorem fix_chk : CFSG.KC.Enum.allN 4 (fun j => CFSG.KC.Ord.andB
    (CFSG.KC.LQT.P.allL [818, 827, 1095, 1187, 1637, 1754] fun p =>
      CFSG.KC.LQT.P.anyL [818, 827, 1095, 1187, 1637, 1754] fun q => Nat.beq (fldK (UGT j) p) q)
    (CFSG.KC.LQT.P.allL [1095, 1187, 1637, 1754] fun p =>
      CFSG.KC.LQT.P.anyL [1095, 1187, 1637, 1754] fun q => Nat.beq (fldK (UGT j) p) q)) = true := by
  quickRfl

theorem z_chk : Nat.beq (actK idKey (CertificateChecks.KernelSpor.SuzInvT1.F 0)) (UE 120) = true := by
  quickRfl

end CertificateChecks.KernelSuzNine

end
