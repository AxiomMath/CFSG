module

public import Certificates.Kernel.SporSch.HN.GenF5
public import Certificates.Kernel.Sporadic.RawGen
public import CFSG.Certificates.Kernel.SporSch.HNF5Sound
public import CFSG.Certificates.Kernel.SporSch.AnyN
public import Certificates.Data.Kernel.SporSch.Closure
public import CFSG.Certificates.Kernel.Spor.RawSlSound
public import CFSG.Sporadic.Schreier.Co3SecondImageCheckInputs
public import CFSG.Sporadic.HNSchreier.SeedsCheckInputs
meta import CFSG.Sporadic.HNSchreier.SeedsCheckInputs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Spor.RawSound

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelSporSch.HNSeedA CFSG.Sporadic.HN.Native.seedA
#ks_chars CertificateChecks.KernelSporSch.HNSeedB CFSG.Sporadic.HN.Native.seedB

namespace CertificateChecks.KernelSporSch.HNSeeds

open CFSG.Sporadic.HNSchreier.Native

meta def ltm (l : Nat) : Nat := if l = 1 then 0 else 1

meta def spec : List (Nat × Nat × Nat) :=
  [(1, 0, 0), (0, 2, 0), (1, 1, 0), (0, 4, 1), (0, 5, 1), (0, 0, 1), (1, 7, 0)] ++
  (List.range 21).map (fun t => (0, 8 + t, 7)) ++ [(1, 0, 0)] ++
  (List.range 11).map (fun t => (0, 30 + t, ltm (gWord.getD (t + 1) 0))) ++ [(1, 0, 0)] ++
  (List.range 17).map (fun t => (0, 42 + t, ltm (gInvWord.getD (t + 1) 0))) ++
  [(0, 41, 59), (0, 0, 59), (0, 61, 1), (0, 62, 41), (1, 63, 0)] ++
  (List.range 18).map (fun t => (0, 64 + t, 63))

end CertificateChecks.KernelSporSch.HNSeeds

#kss_f5table CertificateChecks.KernelSporSch.HNT CFSG.Sporadic.HNSchreier.Native.rowsA
  CFSG.Sporadic.HNSchreier.Native.rowsB CertificateChecks.KernelSporSch.HNSeeds.spec

namespace CertificateChecks.KernelSporSch.HNSeeds

open CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch CFSG.Sporadic.He.Native CFSG.Sporadic.HNSchreier.Native
open CertificateChecks.KernelSporSch

@[expose] noncomputable def sl (k i : Nat) : Nat := slice5 HNT.MT k i

@[expose] noncomputable def ltc (l : Nat) : Nat := nIf(Nat.beq l 1, 0, 1)

theorem payA : pay5K (sl 0) HNSeedA.chars = true := by quickRfl
theorem payB : pay5K (sl 1) HNSeedB.chars = true := by quickRfl

theorem can0 : allBlk 0 (canonAll HNT.MT) 21 = true := by quickRfl
theorem can1 : allBlk 21 (canonAll HNT.MT) 21 = true := by quickRfl
theorem can2 : allBlk 42 (canonAll HNT.MT) 21 = true := by quickRfl
theorem can3 : allBlk 63 (canonAll HNT.MT) 20 = true := by quickRfl

theorem sAB : allN 21 (fun u => bAnd(Nat.beq (HNT.OP (Nat.add 9 u)) 0,
    bAnd(Nat.beq (HNT.L (Nat.add 9 u)) (Nat.add 8 u), Nat.beq (HNT.R (Nat.add 9 u)) 7))) = true := by
  quickRfl
theorem sG : allN 11 (fun u => bAnd(Nat.beq (HNT.OP (Nat.add 31 u)) 0,
    bAnd(Nat.beq (HNT.L (Nat.add 31 u)) (Nat.add 30 u),
      Nat.beq (HNT.R (Nat.add 31 u)) (ltc (gWord.getD (Nat.succ u) 0))))) = true := by quickRfl
theorem sGi : allN 17 (fun u => bAnd(Nat.beq (HNT.OP (Nat.add 43 u)) 0,
    bAnd(Nat.beq (HNT.L (Nat.add 43 u)) (Nat.add 42 u),
      Nat.beq (HNT.R (Nat.add 43 u)) (ltc (gInvWord.getD (Nat.succ u) 0))))) = true := by quickRfl
theorem sX : allN 18 (fun u => bAnd(Nat.beq (HNT.OP (Nat.add 65 u)) 0,
    bAnd(Nat.beq (HNT.L (Nat.add 65 u)) (Nat.add 64 u), Nat.beq (HNT.R (Nat.add 65 u)) 63))) = true := by
  quickRfl

theorem id3 : allN 133 (fun i => Nat.beq (sl 3 i) (idRow5 i)) = true := by quickRfl
theorem id6 : allN 133 (fun i => Nat.beq (sl 6 i) (idRow5 i)) = true := by quickRfl
theorem id29 : allN 133 (fun i => Nat.beq (sl 29 i) (idRow5 i)) = true := by quickRfl
theorem id60 : allN 133 (fun i => Nat.beq (sl 60 i) (idRow5 i)) = true := by quickRfl
theorem id82 : allN 133 (fun i => Nat.beq (sl 82 i) (idRow5 i)) = true := by quickRfl

theorem ne0 : anyN 133 (fun i => Bool.not (Nat.beq (sl 0 i) (idRow5 i))) = true := by quickRfl
theorem ne1 : anyN 133 (fun i => Bool.not (Nat.beq (sl 1 i) (idRow5 i))) = true := by quickRfl
theorem ne9 : anyN 133 (fun i => Bool.not (Nat.beq (sl 9 i) (idRow5 i))) = true := by quickRfl
theorem ne18 : anyN 133 (fun i => Bool.not (Nat.beq (sl 18 i) (idRow5 i))) = true := by quickRfl
theorem ne63 : anyN 133 (fun i => Bool.not (Nat.beq (sl 63 i) (idRow5 i))) = true := by quickRfl

end CertificateChecks.KernelSporSch.HNSeeds

end
