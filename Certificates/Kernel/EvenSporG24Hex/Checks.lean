module

public import Certificates.Kernel.EvenSporG24Hex.Data
public import Certificates.Kernel.EvenSporG24.TblText
import all Init.Data.List.SplitOn.Basic
import Certificates.Kernel.EvenSporG24Hex.Fast

public section

namespace CertificateChecks.KernelG24Hex

open CFSG.KC.EvenSporG24Hex CertificateChecks.EvenSporG24

set_option maxRecDepth 400000 in
set_option maxHeartbeats 0 in
theorem dataOK_true : dataOK tblL D.U D.W D.GE D.PG = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem linesOK_true : linesOK D.U D.W = true := by
  rw [linesOK_eq]
  decide +kernel

set_option maxHeartbeats 0 in
theorem keysOK_true : keysOK D.U D.W = true := by
  rw [keysOK_eq]
  decide +kernel

set_option maxHeartbeats 0 in
theorem lcOK_true : lcOK D.U D.W D.LC = true := by
  rw [lcOK_eq]
  decide +kernel

end CertificateChecks.KernelG24Hex
