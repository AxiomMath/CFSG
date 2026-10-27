module

public import CFSG.Certificates.Kernel.Common.Loop
import Certificates.Kernel.Sporadic.OddCore.RowsCmd
import Certificates.Kernel.Misc.Perm.HexCmd
meta import Certificates.Data.HSOverData
meta import Certificates.Data.HSFiveU35Data
meta import Certificates.Data.MaxD2Heis

namespace CertificateChecks.KernelMaxD2.HSW0

open CFSG.PSL3Four.Native Certificates.MaxD2Perm Certificates.MaxD2Heis Certificates.HSOver

meta def wM : Array Nat := wT hsFiveDataR hsOverW0W
meta def wiM : Array Nat := invTab 100 wM
meta def gaM : Array Nat := wT hsFiveDataP hsOverGAW
meta def gbM : Array Nat := wT hsFiveDataP hsOverGBW
meta def gbiM : Array Nat := invTab 100 gbM
meta def pwM : Array (Array Nat) := #[wM, wiM, gaM, gbM, gbiM]

meta def posIn (T : Array (Array Nat)) (x : Array Nat) : Nat :=
  ((indexOf T).get? x).getD 0

meta def hwM : Array Nat :=
  let rT := (hrEnum Certificates.HSU35.dataU).tabs
  let nT := (nEnum hsOverDataP).tabs
  let nI := indexOf nT
  let rG := rGens hsFiveDataP
  let nG := nGens hsOverDataP
  let x := conjTab 100 wM wiM gaM
  let l := ((List.range nT.size).find? fun l =>
    (nI.get? (comp 100 (comp 100 gbiM nT[l]!) x)).isSome).getD 0
  #[posIn rT (conjTab 100 wM wiM rG[0]!), posIn rT (conjTab 100 wM wiM rG[1]!)] ++
    nG.map (fun g => posIn nT (conjTab 100 wM wiM g)) ++
    #[l, posIn nT (comp 100 (comp 100 gbiM nT[l]!) x)]

end CertificateChecks.KernelMaxD2.HSW0

public section

#kmisc_packarrs CertificateChecks.KernelMaxD2.HSW0.PW CertificateChecks.KernelMaxD2.HSW0.pwM 7
#krows CertificateChecks.KernelMaxD2.HSW0.HW CertificateChecks.KernelMaxD2.HSW0.hwM

end
