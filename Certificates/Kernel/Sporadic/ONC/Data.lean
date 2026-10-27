module

public import Certificates.Data.CFSGNative.ON.Certificate
public import Certificates.Data.Kernel.Spor.PEnum
public import Certificates.Kernel.Sporadic.OddCore.RowsCmd
public import Certificates.Kernel.Sporadic.OddCore.TBfsCmd
public meta import Certificates.Data.CFSGNative.ON.Certificate

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ONC

open CFSG.Sporadic.ON.Native CFSG.Perm.Native CFSG.Sporadic.Th.Native
open CFSG.Sporadic.SmallF2.Native (lettersOf labelsOf)

meta def orbM : VOrbit := orbitData ()

meta def negM : Table :=
  let idx := indexOf orbM.keys
  negTable orbM fun x => idx.getD x nPts

meta def tabM (t : Table) : Array Nat := t.map (·.toNat)

meta def lettersM : Array Table := lettersOf nPts sel (runSLP nPts prog (regs0 orbM)).1

meta def ltM : Array Nat := (lettersM.map tabM).flatten
meta def lv0M : Array Nat := levelLetters lettersM chainBase 0
meta def lv1M : Array Nat := levelLetters lettersM chainBase 1
meta def lv2M : Array Nat := levelLetters lettersM chainBase 2

meta def repsM : Table := lineReps negM
meta def lineM : Table := lineOfT negM repsM
meta def rpM : Array Nat := tabM repsM
meta def lfM : Array Nat := tabM lineM

meta def llM : Array Table := lineLetters lettersM repsM lineM
meta def labsM : Array Nat := labelsOf nLines (subTreesOf llM lv1M)

end CertificateChecks.KernelSpor.ONC

#krows CertificateChecks.KernelSpor.ONC.LT CertificateChecks.KernelSpor.ONC.ltM
#krows CertificateChecks.KernelSpor.ONC.RP CertificateChecks.KernelSpor.ONC.rpM
#krows CertificateChecks.KernelSpor.ONC.LF CertificateChecks.KernelSpor.ONC.lfM
#krows CertificateChecks.KernelSpor.ONC.LB CertificateChecks.KernelSpor.ONC.labsM

#ktbfs CertificateChecks.KernelSpor.ONC.CT0 245520 0 CertificateChecks.KernelSpor.ONC.lettersM
  CertificateChecks.KernelSpor.ONC.lv0M
#ktbfs CertificateChecks.KernelSpor.ONC.CT1 245520 2 CertificateChecks.KernelSpor.ONC.lettersM
  CertificateChecks.KernelSpor.ONC.lv1M
#ktbfs CertificateChecks.KernelSpor.ONC.CT2 245520 4 CertificateChecks.KernelSpor.ONC.lettersM
  CertificateChecks.KernelSpor.ONC.lv2M

#ktbfs CertificateChecks.KernelSpor.ONC.ST0 122760 0 CertificateChecks.KernelSpor.ONC.llM
  CertificateChecks.KernelSpor.ONC.lv1M
#ktbfs CertificateChecks.KernelSpor.ONC.ST1 122760 1 CertificateChecks.KernelSpor.ONC.llM
  CertificateChecks.KernelSpor.ONC.lv1M
#ktbfs CertificateChecks.KernelSpor.ONC.ST2 122760 3 CertificateChecks.KernelSpor.ONC.llM
  CertificateChecks.KernelSpor.ONC.lv1M
#ktbfs CertificateChecks.KernelSpor.ONC.ST3 122760 11 CertificateChecks.KernelSpor.ONC.llM
  CertificateChecks.KernelSpor.ONC.lv1M
#ktbfs CertificateChecks.KernelSpor.ONC.ST4 122760 28 CertificateChecks.KernelSpor.ONC.llM
  CertificateChecks.KernelSpor.ONC.lv1M

end
