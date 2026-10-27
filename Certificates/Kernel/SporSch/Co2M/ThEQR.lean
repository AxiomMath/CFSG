
module

public import Certificates.Kernel.SporSch.Co2M.ThEMD
public import Certificates.Data.Kernel.SporSch.Co2LE
public meta import Certificates.Kernel.SporSch.Co2M.EnumGen
public meta import CFSG.Sporadic.Co2Schreier.ThirdCheckInputs
meta import Certificates.Kernel.Misc.Perm.HexCmd
import CFSG.Certificates.Kernel.Common.Harness
import Certificates.Kernel.Misc.Perm.HexCmd

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.Co2M

open CFSG.Sporadic.Co2Schreier CFSG.Sporadic.Co2Cert

meta def thQGRows : Array (Array Nat) :=
  (quArrsOf (gArrsOf co2PosTable witRec)).map fun a =>
    Gen.rowsOf (Gen.matOf thVecsM (Gen.basisOf thVecsM) a)

meta def thQRecs : Array (Array Nat) :=
  Gen.enumRecs thVecsM (thQGRows.map fun r =>
    (List.range 22).foldl (fun a i => a ||| (r[i]! <<< (22 * i))) 0) 1024

end CertificateChecks.KernelSporSch.Co2M

#kmisc_packarrs CertificateChecks.KernelSporSch.Co2M.TQG CertificateChecks.KernelSporSch.Co2M.thQGRows 22
#kmisc_packarrs CertificateChecks.KernelSporSch.Co2M.TQR CertificateChecks.KernelSporSch.Co2M.thQRecs 22

namespace CertificateChecks.KernelSporSch.Co2M

open CFSG.KC.Enum CFSG.KS CFSG.KS.Co2M CFSG.KS.Co2LE

theorem te_qg : allN 10 (fun j => Nat.beq (TQG j) (teQT.getD j (0, 0)).1) = true := by quickRfl

theorem te_qhead : bAnd(Nat.beq (eM TQR 0) I22, Nat.beq (mR TQR 10 0) 1) = true := by quickRfl

theorem te_qrecs0 : allN 256 (fun k => recK TQR TQG (PV 0) 10 1024 k) = true := by quickRfl

theorem te_qrecs1 : allN 256 (fun k => recK TQR TQG (PV 0) 10 1024 (Nat.add 256 k)) = true := by
  quickRfl

theorem te_qrecs2 : allN 256 (fun k => recK TQR TQG (PV 0) 10 1024 (Nat.add 512 k)) = true := by
  quickRfl

theorem te_qrecs3 : allN 256 (fun k => recK TQR TQG (PV 0) 10 1024 (Nat.add 768 k)) = true := by
  quickRfl

theorem te_qsq_ok : allN 10 (fun i => Nat.beq (mmK (TQG i) (TQG i)) I22) = true := by quickRfl

theorem te_qcomm_ok : allN 10 (fun i => allN 10 (fun j =>
    Nat.beq (mmK (TQG j) (TQG i)) (mmK (TQG i) (TQG j)))) = true := by
  quickRfl

end CertificateChecks.KernelSporSch.Co2M

end
