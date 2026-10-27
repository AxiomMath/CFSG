module

public import Certificates.Kernel.HS100.FiveData
public import Certificates.Data.Kernel.PairFreeK
public import Certificates.Kernel.SporSch.Mathieu.Gen
meta import Certificates.Kernel.LocalComp.BfsGen
meta import CFSG.RankThree.Native.HSMcLFiveData
import CFSG.Certificates.Kernel.Common.Harness
meta import CFSG.RankThree.Native.HSMcLSmallData

namespace CertificateChecks.KernelHS100.PairE

meta def comp (t u : Array Nat) : Array Nat := u.map fun i => t[i]!

meta def pts (gs : List (Array Nat)) : Array (Array Nat) :=
  (CFSG.KC.BfsGen.search 100 7 gs.toArray).1

meta def one : Array Nat := Array.range 100

meta def invs (gs : List (Array Nat)) : List Nat :=
  let P := pts gs
  (List.range P.size).filter fun i => comp P[i]! P[i]! == one && P[i]! != one

meta def fives (gs : List (Array Nat)) (x : Array Nat) : List Nat :=
  let P := pts gs
  let line := [one, x, comp x x, comp x (comp x x), comp x (comp x (comp x x))]
  (List.range P.size).filter fun i =>
    let p := P[i]!
    comp p (comp p (comp p (comp p p))) == one && p != one && !line.contains p

open CFSG.RankThree.Native in
meta def i0 : Array Nat := (invs hs100FiveC0Gens.toList).toArray
open CFSG.RankThree.Native in
meta def i2 : Array Nat := (invs hs100FiveC2Gens.toList).toArray
open CFSG.RankThree.Native in
meta def i23 : Array Nat := (invs hs100FiveC23Gens.toList).toArray
open CFSG.RankThree.Native in
meta def f0 : Array Nat := (fives hs100FiveC0Gens.toList hs100FiveLines[0]!).toArray
open CFSG.RankThree.Native in
meta def f2 : Array Nat := (fives hs100FiveC2Gens.toList hs100FiveLines[2]!).toArray
open CFSG.RankThree.Native in
meta def f23 : Array Nat := (fives hs100FiveC23Gens.toList hs100FiveLines[23]!).toArray

end CertificateChecks.KernelHS100.PairE

public section

set_option maxRecDepth 400000

#kss_list CertificateChecks.KernelHS100.I0 CertificateChecks.KernelHS100.PairE.i0
#kss_list CertificateChecks.KernelHS100.I2 CertificateChecks.KernelHS100.PairE.i2
#kss_list CertificateChecks.KernelHS100.I23 CertificateChecks.KernelHS100.PairE.i23
#kss_list CertificateChecks.KernelHS100.F0 CertificateChecks.KernelHS100.PairE.f0
#kss_list CertificateChecks.KernelHS100.F2 CertificateChecks.KernelHS100.PairE.f2
#kss_list CertificateChecks.KernelHS100.F23 CertificateChecks.KernelHS100.PairE.f23

namespace CertificateChecks.KernelHS100

open CFSG.KC.PairFree

theorem pair0 : pairFreeK 100 7 C0.N C0.T (FV.F 2) I0 F0 = true := by quickRfl

theorem pair2 : pairFreeK 100 7 C2.N C2.T (FV.F 4) I2 F2 = true := by quickRfl

theorem pair23 : pairFreeK 100 7 C23.N C23.T (FV.F 25) I23 F23 = true := by quickRfl

end CertificateChecks.KernelHS100

end
