module

public import Certificates.Kernel.Sporadic.RawGenSch
public import Certificates.Kernel.SporSch.Th.GenV4
public import Certificates.Kernel.Misc.Perm.HexCmd
public import CFSG.Quasithin.Recognition.RuRank3PSLInputs
meta import CFSG.Quasithin.Recognition.RuRank3PSLInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelPSL26

open CFSG.Quasithin.RuRank3 CFSG.Monster.B.Co2.Native CFSG.Sporadic.RuSchreier

meta def sP : Array (Array Nat) := psl26Strong

meta def bP : Array Nat := ruBaseArr 26 [0, 1, 2]

meta def dM : Array (Array Nat) := psl26D

meta def dIdx (a : Array Nat) (i : Nat) : Nat :=
  ((List.range 26).find? fun j => eqA 26 psl26D[j]! (compA 26 a psl26D[i]!)).getD 26

meta def dwM : List Nat :=
  [psl26X, psl26S, invCand 26 psl26X, invCand 26 psl26S].flatMap fun a =>
    (List.range 26).map (dIdx a)

end CertificateChecks.KernelPSL26

#ks_rawchain_sl2 CertificateChecks.KernelPSL26.P26 26 5 2 8 0
  CertificateChecks.KernelPSL26.sP CertificateChecks.KernelPSL26.bP 3
  CFSG.Quasithin.RuRank3.psl26Words

#kmisc_packarrs CertificateChecks.KernelPSL26.PD CertificateChecks.KernelPSL26.dM 5

#kss_natlist CertificateChecks.KernelPSL26.DW CertificateChecks.KernelPSL26.dwM

end
