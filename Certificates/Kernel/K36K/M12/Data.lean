module

public import CFSG.Certificates.Kernel.Common.Loop
import Certificates.Kernel.Sporadic.OddCore.PEnumCmd
import Certificates.Kernel.Misc.Perm.HexCmd
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo
meta import Certificates.Data.K36SporM12

namespace CertificateChecks.KernelK36K.M12

open Certificates.CoreD2Perm Certificates.K36Spor Certificates.FusD2Perm

meta def gpM : Array (Array Nat) := gsT m12SData.base
meta def gpiM : Array (Array Nat) := giT m12SData.base
meta def gtM : Array (Array Nat) := gT m12SData.base
meta def gtiM : Array (Array Nat) := gTi m12SData.base
meta def egM : Array (Array Nat) := eGens m12SData.base
meta def idT : Array Nat := CFSG.PSL3Four.Native.idTab 12
meta def xM (i : Nat) : Exc := m12SData.exc.getD i default
meta def cM (i : Nat) : Array (Array Nat) := cT m12SData (xM i)
meta def ciM (i : Nat) : Array (Array Nat) := cTi m12SData (xM i)
meta def yM (i : Nat) : Array (Array Nat) := #[wT m12SData.base (xM i).yW]
meta def yiM (i : Nat) : Array (Array Nat) := (yM i).map (CFSG.PSL3Four.Native.invTab 12)
meta def fM (i : Nat) : Array (Array Nat) :=
  ((xM i).fWc.map (wordT 12 (cM i) (ciM i))).toArray
meta def fyM (i : Nat) : Array (Array Nat) :=
  ((xM i).fyWc.map (wordT 12 (cM i) (ciM i))).toArray
meta def c0M : Array (Array Nat) := cM 0
meta def ci0M : Array (Array Nat) := ciM 0
meta def c1M : Array (Array Nat) := cM 1
meta def ci1M : Array (Array Nat) := ciM 1
meta def y0M : Array (Array Nat) := yM 0
meta def yi0M : Array (Array Nat) := yiM 0
meta def y1M : Array (Array Nat) := yM 1
meta def yi1M : Array (Array Nat) := yiM 1
meta def f0M : Array (Array Nat) := fM 0
meta def fy0M : Array (Array Nat) := fyM 0
meta def f1M : Array (Array Nat) := fM 1
meta def fy1M : Array (Array Nat) := fyM 1

end CertificateChecks.KernelK36K.M12

public section

#kmisc_packarrs CertificateChecks.KernelK36K.M12.GP CertificateChecks.KernelK36K.M12.gpM 4
#kmisc_packarrs CertificateChecks.KernelK36K.M12.GPI CertificateChecks.KernelK36K.M12.gpiM 4
#kmisc_packarrs CertificateChecks.KernelK36K.M12.GT CertificateChecks.KernelK36K.M12.gtM 4
#kmisc_packarrs CertificateChecks.KernelK36K.M12.GTI CertificateChecks.KernelK36K.M12.gtiM 4
#kmisc_packarrs CertificateChecks.KernelK36K.M12.Y0 CertificateChecks.KernelK36K.M12.y0M 4
#kmisc_packarrs CertificateChecks.KernelK36K.M12.Y0I CertificateChecks.KernelK36K.M12.yi0M 4
#kmisc_packarrs CertificateChecks.KernelK36K.M12.Y1 CertificateChecks.KernelK36K.M12.y1M 4
#kmisc_packarrs CertificateChecks.KernelK36K.M12.Y1I CertificateChecks.KernelK36K.M12.yi1M 4
#kmisc_packarrs CertificateChecks.KernelK36K.M12.F0 CertificateChecks.KernelK36K.M12.f0M 4
#kmisc_packarrs CertificateChecks.KernelK36K.M12.FY0 CertificateChecks.KernelK36K.M12.fy0M 4
#kmisc_packarrs CertificateChecks.KernelK36K.M12.F1 CertificateChecks.KernelK36K.M12.f1M 4
#kmisc_packarrs CertificateChecks.KernelK36K.M12.FY1 CertificateChecks.KernelK36K.M12.fy1M 4

#kpenum CertificateChecks.KernelK36K.M12.RE 12 4 false CertificateChecks.KernelK36K.M12.egM
  CertificateChecks.KernelK36K.M12.egM CertificateChecks.KernelK36K.M12.idT 27
#kpenum CertificateChecks.KernelK36K.M12.RN0 12 4 false CertificateChecks.KernelK36K.M12.c0M
  CertificateChecks.KernelK36K.M12.ci0M CertificateChecks.KernelK36K.M12.idT 432
#kpenum CertificateChecks.KernelK36K.M12.RN1 12 4 false CertificateChecks.KernelK36K.M12.c1M
  CertificateChecks.KernelK36K.M12.ci1M CertificateChecks.KernelK36K.M12.idT 432

#kc_repo #kc_json_gz CertificateChecks.KernelK36K.M12.W
  "Certificates/Kernel/K36K/M12/data/fix.json.gz" 365 7545025512333229701
  (x0k0 : Nat) (x0o0 : Nat) (x0HW : List (List Nat)) (x0OL : List Nat) (x0OW : List (List Nat))
  (x1k0 : Nat) (x1o0 : Nat) (x1HW : List (List Nat)) (x1OL : List Nat) (x1OW : List (List Nat))

end
