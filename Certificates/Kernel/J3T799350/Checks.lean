module

public import Certificates.Kernel.J3T799350.Data
public import Certificates.Data.Kernel.J3Tk
public import CFSG.RankThree.PartTwo.Sec8.Hering611S4Data
public import Certificates.Kernel.SporSch.PairJ3.Chain
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ3T799350

open CFSG.KC.J3Tk CFSG.KC.Enum CFSG.RankThree.PartTwo.Sec8.Hering611.J3T
open CertificateChecks.KernelSporSch (PJ3.S PJ3.SI)

@[expose] noncomputable def slpS (j : Nat) : Bool :=
  chunksK RT MT PR PM 57 ((chunks.drop (Nat.mul 8 j)).take 8) (Nat.mul 8 j)

theorem slp0 : slpS 0 = true := by quickRfl
theorem slp1 : slpS 1 = true := by quickRfl
theorem slp2 : slpS 2 = true := by quickRfl
theorem slp3 : slpS 3 = true := by quickRfl
theorem slp4 : slpS 4 = true := by quickRfl
theorem slp5 : slpS 5 = true := by quickRfl
theorem slp6 : slpS 6 = true := by quickRfl
theorem slp7 : slpS 7 = true := by quickRfl
theorem slp8 : slpS 8 = true := by quickRfl
theorem slp9 : slpS 9 = true := by quickRfl
theorem slp10 : slpS 10 = true := by quickRfl
theorem slp11 : slpS 11 = true := by quickRfl
theorem slp12 : slpS 12 = true := by quickRfl
theorem slp13 : slpS 13 = true := by quickRfl
theorem slp14 : slpS 14 = true := by quickRfl
theorem slp15 : slpS 15 = true := by quickRfl
theorem slp16 : slpS 16 = true := by quickRfl
theorem slp17 : slpS 17 = true := by quickRfl
theorem slp18 : slpS 18 = true := by quickRfl

theorem cover : coverK PR (ends chunks) = true := by quickRfl

theorem coverMid : coverM PM 57 (ends chunks) = true := by quickRfl

@[expose] noncomputable def enumS (e j : Nat) : Bool :=
  enumPartK RT ET j3TData e (Nat.mul 512 j) 512

theorem eh : allBlk 0 (fun e => enumHeadK RT ET j3TData e) 11 = true := by quickRfl

theorem e0 : enumS 0 0 = true := by quickRfl
theorem e1a : enumS 1 0 = true := by quickRfl
theorem e1b : enumS 1 1 = true := by quickRfl
theorem e1c : enumS 1 2 = true := by quickRfl
theorem e1d : enumS 1 3 = true := by quickRfl
theorem e2a : enumS 2 0 = true := by quickRfl
theorem e2b : enumS 2 1 = true := by quickRfl
theorem e2c : enumS 2 2 = true := by quickRfl
theorem e2d : enumS 2 3 = true := by quickRfl
theorem e2e : enumS 2 4 = true := by quickRfl
theorem e2f : enumS 2 5 = true := by quickRfl
theorem e3a : enumS 3 0 = true := by quickRfl
theorem e3b : enumS 3 1 = true := by quickRfl
theorem e4a : enumS 4 0 = true := by quickRfl
theorem e4b : enumS 4 1 = true := by quickRfl
theorem e5 : enumS 5 0 = true := by quickRfl
theorem e6a : enumS 6 0 = true := by quickRfl
theorem e6b : enumS 6 1 = true := by quickRfl
theorem e7a : enumS 7 0 = true := by quickRfl
theorem e7b : enumS 7 1 = true := by quickRfl
theorem e8 : enumS 8 0 = true := by quickRfl
theorem e9a : enumS 9 0 = true := by quickRfl
theorem e9b : enumS 9 1 = true := by quickRfl
theorem e9c : enumS 9 2 = true := by quickRfl
theorem e10 : enumS 10 0 = true := by quickRfl

theorem facts : factsK RT ET PJ3.S PJ3.SI j3TData j3TData.facts words = true := by quickRfl

@[expose] noncomputable def loopS (j : Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => false)
    (fun l _ ih j => Nat.rec (motive := fun _ => Bool) (loopK RT ET j3TData l) (fun i _ => ih i) j)
    j3TData.loops j

theorem l0 : loopS 0 = true := by quickRfl
theorem l1 : loopS 1 = true := by quickRfl
theorem l2 : loopS 2 = true := by quickRfl
theorem l3 : loopS 3 = true := by quickRfl
theorem l4 : loopS 4 = true := by quickRfl
theorem l5 : loopS 5 = true := by quickRfl
theorem l6 : loopS 6 = true := by quickRfl
theorem l7 : loopS 7 = true := by quickRfl
theorem l8 : loopS 8 = true := by quickRfl
theorem l9 : loopS 9 = true := by quickRfl
theorem l10 : loopS 10 = true := by quickRfl

end CertificateChecks.KernelJ3T799350

end
