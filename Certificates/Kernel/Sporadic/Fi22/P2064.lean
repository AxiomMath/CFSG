module

public import Certificates.Kernel.Sporadic.HexNumsGen
public import Certificates.Kernel.Misc.Perm.HexCmd
public import CFSG.Sporadic.FischerOddCore.Fi22CTIRecords
public meta import CFSG.Sporadic.FischerOddCore.Fi22CTIRecords
public meta import CFSG.Sporadic.FischerOddCore.Fi22CTICheckInputs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Assembly.Defs
public import CFSG.Sporadic.FischerOddCore.Fi22SylowRecords
public meta import CFSG.Sporadic.FischerOddCore.Fi22SylowRecords

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelSpor.Fi22CtiT.Par CFSG.Sporadic.FischerOddCore.ctiParText
#ks_hexnums CertificateChecks.KernelSpor.Fi22CtiT.Par CFSG.Sporadic.FischerOddCore.ctiParText 3 12
#ks_chars CertificateChecks.KernelSpor.Fi22CtiT.Lab CFSG.Sporadic.FischerOddCore.ctiLabText
#ks_hexnums CertificateChecks.KernelSpor.Fi22CtiT.Lab CFSG.Sporadic.FischerOddCore.ctiLabText 1 4
#ks_chars CertificateChecks.KernelSpor.Fi22CtiT.Nxt CFSG.Sporadic.FischerOddCore.ctiNxtText
#ks_hexnums CertificateChecks.KernelSpor.Fi22CtiT.Nxt CFSG.Sporadic.FischerOddCore.ctiNxtText 3 12
#ks_chars CertificateChecks.KernelSpor.Fi22CtiT.Cid CFSG.Sporadic.FischerOddCore.ctiCidsText
#ks_hexnums CertificateChecks.KernelSpor.Fi22CtiT.Cid CFSG.Sporadic.FischerOddCore.ctiCidsText 3 12
#ks_chars CertificateChecks.KernelSpor.Fi22CtiT.Reps CFSG.Sporadic.FischerOddCore.ctiRepsText
#ks_hexnums CertificateChecks.KernelSpor.Fi22CtiT.Reps CFSG.Sporadic.FischerOddCore.ctiRepsText 3 12
#ks_chars CertificateChecks.KernelSpor.Fi22CtiT.Zi CFSG.Sporadic.FischerOddCore.ctiZiText
#ks_hexnums CertificateChecks.KernelSpor.Fi22CtiT.Zi CFSG.Sporadic.FischerOddCore.ctiZiText 3 12
#ks_chars CertificateChecks.KernelSpor.Fi22CtiT.S5 CFSG.Sporadic.FischerOddCore.ctiS5Text
#ks_hexnums CertificateChecks.KernelSpor.Fi22CtiT.S5 CFSG.Sporadic.FischerOddCore.ctiS5Text 3 10

namespace CertificateChecks.KernelSpor.Fi22CtiT

open CFSG.KS.Raw CFSG.KS.HexNums CFSG.Sporadic.FischerOddCore

theorem par_eq : hexNums 3 ctiParText = unpack 1024 12 Par.F := hexNums_of Par.eq Par.ok
theorem lab_eq : hexNums 1 ctiLabText = unpack 1024 4 Lab.F := hexNums_of Lab.eq Lab.ok
theorem nxt_eq : hexNums 3 ctiNxtText = unpack 10240 12 Nxt.F := hexNums_of Nxt.eq Nxt.ok
theorem cid_eq : hexNums 3 ctiCidsText = unpack 1024 12 Cid.F := hexNums_of Cid.eq Cid.ok
theorem reps_eq : hexNums 3 ctiRepsText = unpack 512 12 Reps.F := hexNums_of Reps.eq Reps.ok
theorem zi_eq : hexNums 3 ctiZiText = unpack 1024 12 Zi.F := hexNums_of Zi.eq Zi.ok
theorem s5_eq : hexNums 3 ctiS5Text = unpack 6144 10 S5.F := hexNums_of S5.eq S5.ok

end CertificateChecks.KernelSpor.Fi22CtiT

namespace CertificateChecks.KernelSpor.Fi22CtiD

open CFSG.Monster.B.Co2.Native CFSG.Sporadic.FischerOddCore CFSG.Sporadic.FischerOddCore.Native

meta def qM : Array (Array Nat) := ctiQArr ++ ctiQArr.map (invCand 3510) ++ #[ctiZ]

meta def eM : Array (Array Nat) := mulTree 3510 ctiQArr ctiPar ctiLab

meta def kM : Array (Array Nat) := eM.map fun e => #[e[0]!, e[1]!, e[2]!, e[3]!, e[6]!, e[4]!]

meta def key (i : Nat) : Nat := CFSG.KS.RawGen.pack 12 kM[i]!

meta def sM : Array (Array Nat) :=
  ((List.range 1024).toArray.qsort fun a b => key a < key b).map fun i => #[i]

meta def mM : Array (Array Nat) := (List.range 9).toArray.map fun k =>
  (List.range 10).toArray.map fun j =>
    let x := conjArr 3510 (ctiG k) (ctiGi k) ctiQArr[j]!
    ((List.range 1024).find? fun i => eqA 3510 eM[i]! x).getD 1024

end CertificateChecks.KernelSpor.Fi22CtiD

#kmisc_packarrs CertificateChecks.KernelSpor.Fi22CtiQ.T CertificateChecks.KernelSpor.Fi22CtiD.qM 12
#kmisc_packarrs CertificateChecks.KernelSpor.Fi22CtiK.T CertificateChecks.KernelSpor.Fi22CtiD.kM 12
#kmisc_packarrs CertificateChecks.KernelSpor.Fi22CtiS.T CertificateChecks.KernelSpor.Fi22CtiD.sM 12
#kmisc_packarrs CertificateChecks.KernelSpor.Fi22CtiM.T CertificateChecks.KernelSpor.Fi22CtiD.mM 12

end
