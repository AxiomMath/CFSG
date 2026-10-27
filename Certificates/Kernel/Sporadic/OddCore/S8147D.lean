module

public import Certificates.Kernel.Sporadic.BfsDataCmd
public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.Misc.Perm.HexCmd
public import CFSG.RankThree.Native.SuzFiveCheckInputs
meta import CFSG.RankThree.Native.SuzFiveCheckInputs
import all CFSG.RankThree.Native.SuzFiveData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelSpor.SFvT CFSG.RankThree.Native.suzFiveHex

#kmisc_hexflat CertificateChecks.KernelSpor.SFvT CFSG.RankThree.Native.suzFiveHex 3 1782 11 18

namespace CertificateChecks.KernelSpor.S8147

open CFSG.RankThree.Native CFSG.Sporadic.SuzOddCore

meta def keysM : List Nat := suzFiveKeys
meta def r6 : List Nat := List.range 6
meta def r5 : List Nat := List.range 5

meta def qgM : Array (Array Nat) := suzFiveQArrs
meta def cg0 : Array (Array Nat) := suzFiveCArrs 0
meta def cg1 : Array (Array Nat) := suzFiveCArrs 1
meta def cg2 : Array (Array Nat) := suzFiveCArrs 2
meta def cg3 : Array (Array Nat) := suzFiveCArrs 3
meta def cg4 : Array (Array Nat) := suzFiveCArrs 4
meta def cg5 : Array (Array Nat) := suzFiveCArrs 5
meta def dg0 : Array (Array Nat) := suzFiveDArrs 0
meta def dg1 : Array (Array Nat) := suzFiveDArrs 1
meta def dg2 : Array (Array Nat) := suzFiveDArrs 2
meta def dg3 : Array (Array Nat) := suzFiveDArrs 3
meta def dg4 : Array (Array Nat) := suzFiveDArrs 4
meta def dg5 : Array (Array Nat) := suzFiveDArrs 5

meta def ogM (i : Nat) : Array (Array Nat) := (suzFiveDArrs i).map (restrictArr suzFiveOrbits[i]!)
meta def og0 : Array (Array Nat) := ogM 0
meta def og1 : Array (Array Nat) := ogM 1
meta def og2 : Array (Array Nat) := ogM 2
meta def og3 : Array (Array Nat) := ogM 3
meta def og4 : Array (Array Nat) := ogM 4
meta def og5 : Array (Array Nat) := ogM 5

meta def linesM : Array (Array Nat) := (List.range 6).toArray.map suzFiveLineArr

end CertificateChecks.KernelSpor.S8147

#kbfs_data CertificateChecks.KernelSpor.SFQ 1782 11 CertificateChecks.KernelSpor.S8147.qgM
  CertificateChecks.KernelSpor.S8147.keysM 25
#kbfs_data CertificateChecks.KernelSpor.SFC0 1782 11 CertificateChecks.KernelSpor.S8147.cg0
  CertificateChecks.KernelSpor.S8147.keysM 48
#kbfs_data CertificateChecks.KernelSpor.SFC1 1782 11 CertificateChecks.KernelSpor.S8147.cg1
  CertificateChecks.KernelSpor.S8147.keysM 40
#kbfs_data CertificateChecks.KernelSpor.SFC2 1782 11 CertificateChecks.KernelSpor.S8147.cg2
  CertificateChecks.KernelSpor.S8147.keysM 40
#kbfs_data CertificateChecks.KernelSpor.SFC3 1782 11 CertificateChecks.KernelSpor.S8147.cg3
  CertificateChecks.KernelSpor.S8147.keysM 48
#kbfs_data CertificateChecks.KernelSpor.SFC4 1782 11 CertificateChecks.KernelSpor.S8147.cg4
  CertificateChecks.KernelSpor.S8147.keysM 48
#kbfs_data CertificateChecks.KernelSpor.SFC5 1782 11 CertificateChecks.KernelSpor.S8147.cg5
  CertificateChecks.KernelSpor.S8147.keysM 40
#kbfs_data CertificateChecks.KernelSpor.SFD0 1782 11 CertificateChecks.KernelSpor.S8147.dg0
  CertificateChecks.KernelSpor.S8147.keysM 40
#kbfs_data CertificateChecks.KernelSpor.SFD1 1782 11 CertificateChecks.KernelSpor.S8147.dg1
  CertificateChecks.KernelSpor.S8147.keysM 20
#kbfs_data CertificateChecks.KernelSpor.SFD2 1782 11 CertificateChecks.KernelSpor.S8147.dg2
  CertificateChecks.KernelSpor.S8147.keysM 20
#kbfs_data CertificateChecks.KernelSpor.SFD3 1782 11 CertificateChecks.KernelSpor.S8147.dg3
  CertificateChecks.KernelSpor.S8147.keysM 40
#kbfs_data CertificateChecks.KernelSpor.SFD4 1782 11 CertificateChecks.KernelSpor.S8147.dg4
  CertificateChecks.KernelSpor.S8147.keysM 40
#kbfs_data CertificateChecks.KernelSpor.SFD5 1782 11 CertificateChecks.KernelSpor.S8147.dg5
  CertificateChecks.KernelSpor.S8147.keysM 20
#kbfs_data CertificateChecks.KernelSpor.SFO0 6 3 CertificateChecks.KernelSpor.S8147.og0
  CertificateChecks.KernelSpor.S8147.r6 40
#kbfs_data CertificateChecks.KernelSpor.SFO1 5 3 CertificateChecks.KernelSpor.S8147.og1
  CertificateChecks.KernelSpor.S8147.r5 20
#kbfs_data CertificateChecks.KernelSpor.SFO2 5 3 CertificateChecks.KernelSpor.S8147.og2
  CertificateChecks.KernelSpor.S8147.r5 20
#kbfs_data CertificateChecks.KernelSpor.SFO3 6 3 CertificateChecks.KernelSpor.S8147.og3
  CertificateChecks.KernelSpor.S8147.r6 40
#kbfs_data CertificateChecks.KernelSpor.SFO4 6 3 CertificateChecks.KernelSpor.S8147.og4
  CertificateChecks.KernelSpor.S8147.r6 40
#kbfs_data CertificateChecks.KernelSpor.SFO5 5 3 CertificateChecks.KernelSpor.S8147.og5
  CertificateChecks.KernelSpor.S8147.r5 20

#kmisc_packarrs CertificateChecks.KernelSpor.SFL12 CertificateChecks.KernelSpor.S8147.linesM 12

end
