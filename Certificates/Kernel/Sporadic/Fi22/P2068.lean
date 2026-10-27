module

public import Certificates.Kernel.Sporadic.Fi22.P2068R
public import Certificates.Kernel.Misc.Perm.HexCmd
public meta import CFSG.Sporadic.FischerOddCore.Fi22ExtCoverRecords
import CFSG.Certificates.Kernel.Common.Harness
public meta import CFSG.Sporadic.FischerOddCore.Fi24R2Data

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Fi22LabD

open CFSG.Sporadic.FischerOddCore

meta def rootsM : Array (Array Nat) := fi22ExtRootsRec.map fun r => #[r]

meta def hexv (c : UInt8) : Nat := if c.toNat < 58 then c.toNat - 48 else c.toNat - 55

meta def posM : Array (Array Nat) := Id.run do
  let b := fi22ExtInvRecText.toUTF8
  let mut pos := Array.replicate 262144 6143
  for k in [0:6143] do
    let o := (k / 128) * 9601 + 5 * (k % 128 * 15 + 14)
    let v := (List.range 5).foldl (fun acc t => acc * 16 + hexv (b.get! (o + t))) 0
    pos := pos.set! v k
  return (Array.range 32).map fun L => pos.extract (8192 * L) (8192 * L + 8192)

end CertificateChecks.KernelSpor.Fi22LabD

#kmisc_packarrs CertificateChecks.KernelSpor.Fi22LabR.T
  CertificateChecks.KernelSpor.Fi22LabD.rootsM 20
#kmisc_packarrs CertificateChecks.KernelSpor.Fi22LabP.T
  CertificateChecks.KernelSpor.Fi22LabD.posM 16

end
