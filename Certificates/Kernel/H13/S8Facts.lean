module

public import CFSG.Quasithin.H13.L32NS8Inputs
import Certificates.Kernel.H13.S8A
public import Certificates.Kernel.H13.S8Stab
public import Certificates.Kernel.H13.ElemsS8
import CFSG.Certificates.Kernel.Census.CatFacts.PkEnum

public section

namespace CertificateChecks.KernelH13

open CFSG.Quasithin.H13.Mat8Cert CFSG.Quasithin.H13.S8Cert CFSG.KC.Mat8P

set_option maxRecDepth 100000 in
theorem s8L_length : D.s8L.length = 40320 := by decide +kernel

theorem s8_stabIB_true : stabIB = true := by
  rw [stabIB, s8E_eq, List.all_map]
  have hf : ((fun y => iiList.all fun v => !(mv8 y v == v) || (y.take 4).all (· < 16)) ∘
      unpackM) = fun p => stabY (unpackM p) := by
    funext p
    simp only [Function.comp_def, stabY, mv8_toR]
  rw [hf]
  apply CFSG.Certificates.Kernel.PkEnum.all_of_chunks _ _ 2016 20 (by rw [s8L_length])
  intro j hj
  have h : stabChunk j = true := by
    interval_cases j
    · exact stabChunk0
    · exact stabChunk1
    · exact stabChunk2
    · exact stabChunk3
    · exact stabChunk4
    · exact stabChunk5
    · exact stabChunk6
    · exact stabChunk7
    · exact stabChunk8
    · exact stabChunk9
    · exact stabChunk10
    · exact stabChunk11
    · exact stabChunk12
    · exact stabChunk13
    · exact stabChunk14
    · exact stabChunk15
    · exact stabChunk16
    · exact stabChunk17
    · exact stabChunk18
    · exact stabChunk19
  exact h

theorem s8Check_true : s8Check = true := by
  rw [s8Check, s8_basicB_true, s8_stabIB_true, s8_orbB_true, s8_zB_true, s8_nB_true, s8_wB_true,
    s8_fB_true]
  rfl

end CertificateChecks.KernelH13

end
