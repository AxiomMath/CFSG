module

public import Certificates.Kernel.Sporadic.OddCore.PEnumCmd
public import Certificates.Kernel.Misc.Perm.HexCmd
public import CFSG.Sporadic.SuzOddCore.ThreeLocalCheckInputs
meta import CFSG.Sporadic.SuzOddCore.ThreeLocalCheckInputs

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.OddCore.S2308M

open CFSG.Sporadic.SuzOddCore CFSG.Monster.B.Co2.Native CFSG.PSL3Four.Native

meta def fM : Array (Array Nat) := fullExtArrs
meta def tM : Array (Array Nat) := tFullOf fullExtArrs
meta def wM : Array Nat := wordA 22880 certStrongArrs certStrongInvs zWord

meta def rows (L : Array (Array Nat)) : Array (Array Nat) :=
  (L.map fun t => (List.range 715).toArray.map fun j => t.extract (32 * j) (32 * j + 32)).flatten

meta def fxM : Array (Array Nat) := rows fM
meta def fxiM : Array (Array Nat) := rows (fM.map (invCand 22880))
meta def txM : Array (Array Nat) := rows tM
meta def wxM : Array (Array Nat) := rows #[wM]
meta def zxM : Array (Array Nat) := rows #[zArr]
meta def gxM : Array (Array Nat) := rows #[fusionTransArr]
meta def gxiM : Array (Array Nat) := rows #[invCand 22880 fusionTransArr]

meta def tcM : Array (Array Nat) := tCompOf tM
meta def id280 : Array Nat := idTab 280

meta def diffPt (t u : Array Nat) : Nat :=
  ((List.range 22880).find? fun i => t[i]! != u[i]!).getD 0

meta def witM : List Nat :=
  let z := zArr
  let z2 := compA 22880 z z
  [diffPt z (idA 22880)] ++
    ((List.range 81).map fun k => if k / 9 < k % 9 then diffPt (centerFull (k / 9))
      (centerFull (k % 9)) else 0) ++
    ((List.range 8).map fun j =>
      let c := compA 22880 certStrongArrs[j + 2]! (compA 22880 z certStrongInvs[j + 2]!)
      if eqA 22880 c z then 0 else 1)

end CertificateChecks.KernelSpor.OddCore.S2308M

#kmisc_packarrs CertificateChecks.KernelSpor.S2308FX CertificateChecks.KernelSpor.OddCore.S2308M.fxM 15
#kmisc_packarrs CertificateChecks.KernelSpor.S2308FXI CertificateChecks.KernelSpor.OddCore.S2308M.fxiM 15
#kmisc_packarrs CertificateChecks.KernelSpor.S2308TX CertificateChecks.KernelSpor.OddCore.S2308M.txM 15
#kmisc_packarrs CertificateChecks.KernelSpor.S2308WX CertificateChecks.KernelSpor.OddCore.S2308M.wxM 15
#kmisc_packarrs CertificateChecks.KernelSpor.S2308ZX CertificateChecks.KernelSpor.OddCore.S2308M.zxM 15
#kmisc_packarrs CertificateChecks.KernelSpor.S2308GX CertificateChecks.KernelSpor.OddCore.S2308M.gxM 15
#kmisc_packarrs CertificateChecks.KernelSpor.S2308GXI CertificateChecks.KernelSpor.OddCore.S2308M.gxiM 15
#kpenum CertificateChecks.KernelSpor.S2308CE 280 9 false CertificateChecks.KernelSpor.OddCore.S2308M.tcM
  CertificateChecks.KernelSpor.OddCore.S2308M.tcM CertificateChecks.KernelSpor.OddCore.S2308M.id280 729
#knatlist CertificateChecks.KernelSpor.S2308W CertificateChecks.KernelSpor.OddCore.S2308M.witM

end
