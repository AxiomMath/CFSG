module

public import CFSG.Certificates.Kernel.Common.Loop
import Certificates.Kernel.Sporadic.OddCore.RowsCmd
import Certificates.Kernel.Misc.Perm.HexCmd
meta import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.McLLem45Data
meta import Certificates.Data.McLFiveLocalP

namespace CertificateChecks.KernelMaxD2.McLP

open Certificates.MaxD2Perm Certificates.MaxD2Heis
open CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

meta def l45W : Array (Array Nat) := #[wT mclFiveDataP McLLem45.wordW]

meta def l45R : Array (Array Nat) := (hrEnum mclFiveDataP).tabs

meta def l45L : Array (Array Nat) := McLLem45.orbitList mclFiveDataP McLLem45.tree

meta def l45IX : Array Nat := l45L.map fun t => (l45R.findIdx? (· == t)).getD 0

meta def l45CV : Array Nat := l45R.map fun t => (l45L.findIdx? (· == t)).getD 0

end CertificateChecks.KernelMaxD2.McLP

public section

#kmisc_packarrs CertificateChecks.KernelMaxD2.McLP.WL CertificateChecks.KernelMaxD2.McLP.l45W 9
#krows CertificateChecks.KernelMaxD2.McLP.IX CertificateChecks.KernelMaxD2.McLP.l45IX
#krows CertificateChecks.KernelMaxD2.McLP.CV CertificateChecks.KernelMaxD2.McLP.l45CV

end
