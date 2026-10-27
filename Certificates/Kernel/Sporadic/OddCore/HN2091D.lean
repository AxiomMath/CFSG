module

public import Certificates.Kernel.Sporadic.OddCore.HND2
public import Certificates.Kernel.Sporadic.OddCore.ChainCheckGlue
public import Certificates.Kernel.Sporadic.OddCore.BfsLCmd
public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Kernel.Sporadic.OddCore.RowsCmd
public import CFSG.Sporadic.HNOddCore.SCheckInputs
meta import CFSG.Sporadic.HNOddCore.SCheckInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.HN2091

open CFSG.Sporadic.HNOddCore CFSG.Sporadic.HNOddCore.Native CFSG.Sporadic.HNOddCore.InvData

meta def base12A : Array Nat := (base12.map Fin.val).toArray
meta def c1S : Array (Array Nat) := strongArrs 12 (natArrs c1Nat) g1Words
meta def c4S : Array (Array Nat) := strongArrs 12 (natArrs c4Nat) g4Words
meta def c6S : Array (Array Nat) := strongArrs 12 (natArrs c6Nat) g6Words
meta def c4cS : Array (Array Nat) := strongArrs 12 (natArrs (c4Nat.push tauList)) g4cWords
@[expose] def c1D : List (List Int) := (g1Words.extract 9 g1Words.size).toList
@[expose] def c4D : List (List Int) := (g4Words.extract 9 g4Words.size).toList
@[expose] def c6D : List (List Int) := (g6Words.extract 10 g6Words.size).toList
@[expose] def c4cD : List (List Int) := (g4cWords.extract 10 g4cWords.size).toList

meta def s1M : Array (Array Nat) := s1Perms
meta def s4M : Array (Array Nat) := s4J
meta def s6M : Array (Array Nat) := s6Perms
meta def o10 : Array Nat := o1Lists[0]!
meta def o11 : Array Nat := o1Lists[1]!
meta def o12 : Array Nat := o1Lists[2]!
meta def o60 : Array Nat := o6Lists[0]!
meta def o61 : Array Nat := o6Lists[1]!
meta def f4L : Array Nat := bfsList f4Arr.size s4J 0
meta def s1C : Array Nat := s1Perms.flatten
meta def s4C : Array Nat := s4J.flatten
meta def s6C : Array Nat := s6Perms.flatten

end CertificateChecks.KernelSpor.HN2091

#ks_rawchain CertificateChecks.KernelSpor.HNC1 12 4 16 CertificateChecks.KernelSpor.HN2091.c1S
  CertificateChecks.KernelSpor.HN2091.base12A 9 CertificateChecks.KernelSpor.HN2091.c1D
#ks_rawchain CertificateChecks.KernelSpor.HNC4 12 4 16 CertificateChecks.KernelSpor.HN2091.c4S
  CertificateChecks.KernelSpor.HN2091.base12A 9 CertificateChecks.KernelSpor.HN2091.c4D
#ks_rawchain CertificateChecks.KernelSpor.HNC6 12 4 16 CertificateChecks.KernelSpor.HN2091.c6S
  CertificateChecks.KernelSpor.HN2091.base12A 10 CertificateChecks.KernelSpor.HN2091.c6D
#ks_rawchain CertificateChecks.KernelSpor.HNC4C 12 4 16 CertificateChecks.KernelSpor.HN2091.c4cS
  CertificateChecks.KernelSpor.HN2091.base12A 10 CertificateChecks.KernelSpor.HN2091.c4cD

#krows CertificateChecks.KernelSpor.HS1R CertificateChecks.KernelSpor.HN2091.s1C
#krows CertificateChecks.KernelSpor.HS4R CertificateChecks.KernelSpor.HN2091.s4C
#krows CertificateChecks.KernelSpor.HS6R CertificateChecks.KernelSpor.HN2091.s6C

#kbfsl CertificateChecks.KernelSpor.HO1_0 1156 CertificateChecks.KernelSpor.HN2091.s1M
  CertificateChecks.KernelSpor.HN2091.o10
#kbfsl CertificateChecks.KernelSpor.HO1_1 1156 CertificateChecks.KernelSpor.HN2091.s1M
  CertificateChecks.KernelSpor.HN2091.o11
#kbfsl CertificateChecks.KernelSpor.HO1_2 1156 CertificateChecks.KernelSpor.HN2091.s1M
  CertificateChecks.KernelSpor.HN2091.o12
#kbfsl CertificateChecks.KernelSpor.HO6_0 8800 CertificateChecks.KernelSpor.HN2091.s6M
  CertificateChecks.KernelSpor.HN2091.o60
#kbfsl CertificateChecks.KernelSpor.HO6_1 8800 CertificateChecks.KernelSpor.HN2091.s6M
  CertificateChecks.KernelSpor.HN2091.o61
#kbfsl CertificateChecks.KernelSpor.HF4 800 CertificateChecks.KernelSpor.HN2091.s4M
  CertificateChecks.KernelSpor.HN2091.f4L

end
