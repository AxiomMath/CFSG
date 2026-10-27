module

public import Certificates.Kernel.ThCent.LDefs
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.SliceRange
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanD2CoreDefs

public section

namespace CFSG.KD.ThCent.L

open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSevenNative

@[expose] def regs7 : List Nat := [2, 3, 24, 25, 31, 34, 39, 40, 41, 42]

theorem pair7_ok : pair7 = true := by quickRfl

#kc_slice_range CFSG.KD.ThCent.L.conj7F conj7_ 0 7

theorem dist7_ok : dist7 = true := by quickRfl

theorem E7_length : L7.E.length = 1176 := by decide +kernel

theorem E7_words : L7.E.map (fun e => e.1) = list7.words.toList := by decide +kernel

theorem E7_wit : L7.E.map (fun e => e.2.1) =
    list7.wit.toList.map (fun l => l.map fun j => (list7.words[j]!, list7.words[list7.inv[j]!]!)) := by
  decide +kernel

theorem E7_regs : (L7.E.all fun e => e.1.all (fun r => regs7.elem r) &&
    e.2.1.all fun p => p.1.all (fun r => regs7.elem r) && p.2.all (fun r => regs7.elem r)) = true := by
  decide +kernel

theorem conj7_regs : ((List.range 49).all fun i => (conj7[i]!).all fun r => regs7.elem r) = true := by
  decide +kernel

end CFSG.KD.ThCent.L

end
