module

public import CFSG.Certificates.Kernel.Common.Loop
import Certificates.Kernel.Sporadic.OddCore.RowsCmd
import Certificates.Kernel.Misc.Perm.HexCmd
meta import Certificates.Data.McLCentOver

namespace CertificateChecks.KernelMaxD2.McLP

open CFSG.PSL3Four.Native Certificates.MaxD2Perm Certificates.MaxD2Heis Certificates.MclCentOver

meta def coM : Array (Array Nat) := cGens mclFiveDataP
meta def coiM : Array (Array Nat) := cGensI mclFiveDataP
meta def xtM : Array (Array Nat) :=
  ((List.range (4 * mclFiveDataP.repW.length)).map fun k => xT mclFiveDataP (k / 4) (k % 4)).toArray
meta def xtiM : Array (Array Nat) := xtM.map (invTab 275)
meta def chbM : Array Nat :=
  let b := mclFiveDataP.gT[1]!
  let rT := (hrEnum mclFiveDataP).tabs
  let nG := nGens mclFiveDataP
  #[(List.range rT.size).find? (fun r => rT[r]! == b) |>.getD 0] ++
    ((List.range nG.size).map fun i =>
      (List.range 5).find? (fun k => comp 275 nG[i]! b ==
        comp 275 (Certificates.FusD2Perm.powT 275 b k) nG[i]!) |>.getD 0).toArray

end CertificateChecks.KernelMaxD2.McLP

public section

#kmisc_packarrs CertificateChecks.KernelMaxD2.McLP.CO CertificateChecks.KernelMaxD2.McLP.coM 9
#kmisc_packarrs CertificateChecks.KernelMaxD2.McLP.COI CertificateChecks.KernelMaxD2.McLP.coiM 9
#kmisc_packarrs CertificateChecks.KernelMaxD2.McLP.XT CertificateChecks.KernelMaxD2.McLP.xtM 9
#kmisc_packarrs CertificateChecks.KernelMaxD2.McLP.XTI CertificateChecks.KernelMaxD2.McLP.xtiM 9
#krows CertificateChecks.KernelMaxD2.McLP.CHB CertificateChecks.KernelMaxD2.McLP.chbM

end
