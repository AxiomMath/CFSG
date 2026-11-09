module

public import Certificates.Kernel.SporSch.HN.GenF5
public import Certificates.Kernel.SporSch.HN.GenF5T
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
  [(2, 0, 0), (2, 0, 0), (1, 0, 0), (0, 2, 0), (1, 1, 0), (0, 4, 1), (0, 5, 1), (0, 0, 1),
    (0, 7, 7), (0, 8, 8), (0, 9, 7), (0, 10, 10), (0, 11, 7), (0, 12, 12), (1, 0, 0)] ++
  (List.range 11).map (fun t => (0, 14 + t, ltm (gWord.getD (t + 1) 0))) ++ [(1, 0, 0)] ++
  (List.range 17).map (fun t => (0, 26 + t, ltm (gInvWord.getD (t + 1) 0))) ++
  [(0, 25, 43), (0, 0, 43), (0, 45, 1), (0, 46, 25),
    (0, 47, 47), (0, 48, 48), (0, 49, 49), (0, 50, 50), (0, 51, 48), (0, 52, 47)]

meta def mats : List (Array (Array Nat)) := Id.run do
  let mut M : Array (Array (Array Nat)) := #[]
  for (op, l, r) in spec do
    M := M.push (if M.size == 0 then rowsA else if M.size == 1 then rowsB
      else if op == 0 then CFSG.KS.SporSchGenF5.mul5 M[l]! M[r]! else M[l]!)
  return M.toList

end CertificateChecks.KernelSporSch.HNSeeds

#kss_f5tree CertificateChecks.KernelSporSch.HNT CertificateChecks.KernelSporSch.HNSeeds.mats
  CertificateChecks.KernelSporSch.HNSeeds.spec

namespace CertificateChecks.KernelSporSch.HNSeeds

open CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch CFSG.Sporadic.He.Native CFSG.Sporadic.HNSchreier.Native
open CertificateChecks.KernelSporSch

@[expose] noncomputable def sl (k i : Nat) : Nat := slice5 HNT.MT k i

@[expose] noncomputable def ltc (l : Nat) : Nat := nIf(Nat.beq l 1, 0, 1)

theorem payA : pay5K (sl 0) HNSeedA.chars = true := by quickRfl
theorem payB : pay5K (sl 1) HNSeedB.chars = true := by quickRfl

theorem blk0 : krBlk HNT.MT HNT.OP HNT.L HNT.R 0 9 = true := by quickRfl
theorem blk1 : krBlk HNT.MT HNT.OP HNT.L HNT.R 9 9 = true := by quickRfl
theorem blk2 : krBlk HNT.MT HNT.OP HNT.L HNT.R 18 9 = true := by quickRfl
theorem blk3 : krBlk HNT.MT HNT.OP HNT.L HNT.R 27 9 = true := by quickRfl
theorem blk4 : krBlk HNT.MT HNT.OP HNT.L HNT.R 36 9 = true := by quickRfl
theorem blk5 : krBlk HNT.MT HNT.OP HNT.L HNT.R 45 9 = true := by quickRfl

theorem id3 : allN 133 (fun i => Nat.beq (sl 3 i) (idRow5 i)) = true := by quickRfl
theorem id6 : allN 133 (fun i => Nat.beq (sl 6 i) (idRow5 i)) = true := by quickRfl
theorem id13 : allN 133 (fun i => Nat.beq (sl 13 i) (idRow5 i)) = true := by quickRfl
theorem id44 : allN 133 (fun i => Nat.beq (sl 44 i) (idRow5 i)) = true := by quickRfl
theorem id53 : allN 133 (fun i => Nat.beq (sl 53 i) (idRow5 i)) = true := by quickRfl

theorem ne0 : anyN 133 (fun i => Bool.not (Nat.beq (sl 0 i) (idRow5 i))) = true := by quickRfl
theorem ne1 : anyN 133 (fun i => Bool.not (Nat.beq (sl 1 i) (idRow5 i))) = true := by quickRfl
theorem ne8 : anyN 133 (fun i => Bool.not (Nat.beq (sl 8 i) (idRow5 i))) = true := by quickRfl
theorem ne12 : anyN 133 (fun i => Bool.not (Nat.beq (sl 12 i) (idRow5 i))) = true := by quickRfl
theorem ne47 : anyN 133 (fun i => Bool.not (Nat.beq (sl 47 i) (idRow5 i))) = true := by quickRfl

end CertificateChecks.KernelSporSch.HNSeeds

end
