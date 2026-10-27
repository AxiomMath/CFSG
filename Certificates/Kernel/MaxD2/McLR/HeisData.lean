module

public import CFSG.Certificates.Kernel.Common.Loop
import Certificates.Kernel.Sporadic.OddCore.RowsCmd
import Certificates.Kernel.Sporadic.RowsWCmd
import Certificates.Kernel.Misc.Perm.HexCmd
meta import Certificates.Data.Kernel.MaxD2.GenHeis
meta import Certificates.Data.McLFiveLocalR
import Certificates.Data.Kernel.MaxD2.GenHeis

namespace CertificateChecks.KernelMaxD2.McLR

open CFSG.KS.MaxD2 Certificates.MaxD2Perm Certificates.MaxD2Heis

meta def preH : Gen.Pre := Gen.pre mclFiveDataR 9

meta def psH : Array (Nat × Nat) :=
  Gen.pairsBy (Gen.mkeys mclFiveDataR 9 preH) (Gen.counts mclFiveDataR 9 preH)

meta def zpM : Array Nat := Gen.zPos mclFiveDataR
meta def zxM : Array Nat := Gen.zIdx mclFiveDataR
meta def czM : Array Nat := Gen.commHints mclFiveDataR
meta def lM : Array Nat := Gen.labels mclFiveDataR
meta def mkM : Array Nat := Gen.mkeys mclFiveDataR 9 preH
meta def preR : Gen.Pre := { preH with rT := Gen.hrTabs mclFiveDataR }

meta def ttM : Array (Array Nat) :=
  #[wT mclFiveDataR mclFiveDataR.tW,
    CFSG.PSL3Four.Native.invTab 275 (wT mclFiveDataR mclFiveDataR.tW)]
meta def chM : Array Nat := Gen.centHints mclFiveDataR preR
meta def nhM : Array Nat := Gen.normHints mclFiveDataR preR
meta def miscM : Array Nat :=
  #[Gen.numLabels mclFiveDataR, psH.size, Gen.torusPos mclFiveDataR preR,
    Gen.movesWit mclFiveDataR preR / 2, Gen.movesWit mclFiveDataR preR % 2]
meta def pqM : Array Nat := Gen.pairPos preH.rep.size psH
meta def piM : Array Nat := psH.map (·.1)
meta def pjM : Array Nat := psH.map (·.2)
meta def rb2M : Array Nat := Gen.pairImgsL mclFiveDataR preH psH
meta def h2M : Array Nat := Gen.pairHintsL mclFiveDataR 9 preH psH

end CertificateChecks.KernelMaxD2.McLR

public section

#kmisc_packarrs CertificateChecks.KernelMaxD2.McLR.TT CertificateChecks.KernelMaxD2.McLR.ttM 9
#krows CertificateChecks.KernelMaxD2.McLR.CH CertificateChecks.KernelMaxD2.McLR.chM
#krows CertificateChecks.KernelMaxD2.McLR.NH CertificateChecks.KernelMaxD2.McLR.nhM
#krows CertificateChecks.KernelMaxD2.McLR.ZP CertificateChecks.KernelMaxD2.McLR.zpM
#krows CertificateChecks.KernelMaxD2.McLR.ZX CertificateChecks.KernelMaxD2.McLR.zxM
#krows CertificateChecks.KernelMaxD2.McLR.CZ CertificateChecks.KernelMaxD2.McLR.czM
#krows CertificateChecks.KernelMaxD2.McLR.L CertificateChecks.KernelMaxD2.McLR.lM
#krowsw CertificateChecks.KernelMaxD2.McLR.MK 64 CertificateChecks.KernelMaxD2.McLR.mkM
#krows CertificateChecks.KernelMaxD2.McLR.MISC CertificateChecks.KernelMaxD2.McLR.miscM
#krows CertificateChecks.KernelMaxD2.McLR.PQ CertificateChecks.KernelMaxD2.McLR.pqM
#krows CertificateChecks.KernelMaxD2.McLR.PI CertificateChecks.KernelMaxD2.McLR.piM
#krows CertificateChecks.KernelMaxD2.McLR.PJ CertificateChecks.KernelMaxD2.McLR.pjM
#krows CertificateChecks.KernelMaxD2.McLR.RB2 CertificateChecks.KernelMaxD2.McLR.rb2M
#krows CertificateChecks.KernelMaxD2.McLR.H2 CertificateChecks.KernelMaxD2.McLR.h2M

end
