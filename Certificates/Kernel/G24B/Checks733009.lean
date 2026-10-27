module

public import Certificates.Kernel.G24B.Recs
public import Certificates.Data.G24ModelFrameData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 100000

namespace CFSG.KD.G24B

open CFSG.KC.Misc.G24 CFSG.KLie.CT CFSG.Quasithin.St84.G24MF

@[expose] noncomputable def bitProdK (G b : Nat → Nat) (n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (oneF2 28)
    (fun i acc => Bool.rec (motive := fun _ => Nat) acc (mulF2 28 acc (G i)) (Nat.beq (b i) 1)) n

@[expose] def vAt {k : Nat} (M : Fin 3 → Matrix (Fin k) (Fin k) (ZMod 2)) (g i j : Nat) : Nat :=
  if h : g < 3 ∧ i < k ∧ j < k then (M ⟨g, h.1⟩ ⟨i, h.2.1⟩ ⟨j, h.2.2⟩).val else 0

@[expose] noncomputable def bitN (c t : Nat) : Nat := Bool.rec (motive := fun _ => Nat) 0 1 (CFSG.KLie.CT.bit c t)

@[expose] noncomputable def conjK (g X P E : Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool) (Nat.beq (mulF2 28 P X) (mulF2 28 X E))
    (Nat.beq (mulF2 28 X P) (mulF2 28 E X)) (Nat.beq g 0)

@[expose] noncomputable def frK {k : Nat} (GQ GA : List Nat)
    (M : Fin 3 → Matrix (Fin k) (Fin k) (ZMod 2)) (nz : Nat) : Bool :=
  allN 3 fun g => allN k fun j => anyN (Nat.pow 2 nz) fun c =>
    conjK g (nthV GA g) (nthV GQ j)
      (mulF2 28 (bitProdK (nthV GQ) (fun i => vAt M g i j) k)
        (bitProdK (fun t => nthV GQ (Nat.add k t)) (bitN c) nz))

@[expose] noncomputable def fzK {nz : Nat} (GQ GA : List Nat)
    (MZ : Fin 3 → Matrix (Fin nz) (Fin nz) (ZMod 2)) (k : Nat) : Bool :=
  allN 3 fun g => allN nz fun t =>
    conjK g (nthV GA g) (nthV GQ (Nat.add k t))
      (bitProdK (fun s => nthV GQ (Nat.add k s)) (fun s => vAt MZ g s t) nz)

theorem ch733009_frames1 : frK GQ1 GA1 matV1 2 = true := by quickRfl
theorem ch733009_centre1 : fzK GQ1 GA1 matZ1 8 = true := by quickRfl
theorem ch733009_frames2 : frK GQ2 GA2 matV2 4 = true := by quickRfl
theorem ch733009_centre2 : fzK GQ2 GA2 matZ2 6 = true := by quickRfl

end CFSG.KD.G24B

end
