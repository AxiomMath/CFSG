module

public import Certificates.Kernel.ThCent.LDefs
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.SliceRange
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanD2CoreDefs

public section

namespace CFSG.KD.ThCent.L

open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThFiveNative

@[expose] def regs5 : List Nat := [19, 25, 82, 84, 94, 99, 105, 114, 115, 116, 117]

theorem cube5_ok : cube5 = true := by quickRfl

#kc_slice_range CFSG.KD.ThCent.L.conj5F conj5_ 0 5
#kc_slice_range CFSG.KD.ThCent.L.row5F row5_ 0 5

theorem distC_ok : distC = true := by quickRfl

theorem RC_length : L5.RC.length = 125 := by decide +kernel

theorem E5_length : L5.E.length = 3000 := by decide +kernel

theorem E5_words : L5.E.map (fun e => e.1) = list5.words.toList := by decide +kernel

theorem E5_wit : L5.E.map (fun e => e.2.1) =
    list5.wit.toList.map (fun l => l.map fun j => (list5.words[j]!, list5.words[list5.inv[j]!]!)) := by
  decide +kernel

theorem E5_regs : (L5.E.all fun e => e.1.all (fun r => regs5.elem r) &&
    e.2.1.all fun p => p.1.all (fun r => regs5.elem r) && p.2.all (fun r => regs5.elem r)) = true := by
  decide +kernel

theorem conj5_regs : ((List.range 125).all fun i => (conj5[i]!).all fun r => regs5.elem r) =
    true := by
  decide +kernel

end CFSG.KD.ThCent.L

end
