module

public import Certificates.Data.J2Fix280
public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.Misc.Perm.HexCmd
public meta import Certificates.Data.J2Fix280
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

open CFSG.RankThree.PartTwo.J2Residue.C280 in
meta def parArr : Array Nat := Array.ofFn (n := 280) fun i =>
  ((List.range 280).find? (fun p => words[p]! == (words[i.val]!).tail)).getD 0

open CFSG.RankThree.PartTwo.J2Residue.C280 in
meta def letArr : Array Nat := Array.ofFn (n := 280) fun i => (words[i.val]!).headD 0

open CFSG.RankThree.PartTwo.J2Residue.C280 in
meta def wcArr : Array Nat := Array.ofFn (n := 280) fun i =>
  (words[i.val]!).foldr (fun k c => 2 * c + k) 1

meta def invArr (a : Array Nat) : Array Nat := Array.ofFn (n := 315) fun j =>
  ((List.range 315).find? (fun x => a[x]! == j.val)).getD 0

meta def abInv : Array (Array Nat) :=
  CFSG.ComponentClassification.J2Cover.autStrong.map invArr

meta def zInv : Array Nat := invArr CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.zArr

#ks_perm CertificateChecks.KernelJ2Fix280.PAR 9 parArr
#ks_perm CertificateChecks.KernelJ2Fix280.LET 9 letArr
#ks_perm CertificateChecks.KernelJ2Fix280.WC 40 wcArr
#kmisc_packarrs CertificateChecks.KernelJ2Fix280.AI abInv 9
#ks_perm CertificateChecks.KernelJ2Fix280.ZI 9 zInv
