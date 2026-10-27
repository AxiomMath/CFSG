module

public import Certificates.Kernel.GMS78.W105Chk

public section

namespace CertificateChecks.KernelGMS78.W

open CFSG.KC.GMSW CFSG.ComponentClassification.GMS78.RuAsm

open CFSG in
open CFSG.Sporadic.Bridge CFSG.Sporadic.Bridge.VecSurj CFSG.ComponentClassification.GMS78.RuPi7
  CFSG.ComponentClassification.GMS78.RuAsm in
theorem certificate105 : ∀ p ∈ ruAlignMulPairs ++ ruAlignTransPairs ++ ruAlignNormPairs,
    wordProd (img pi7RuSpec (seedG CFSG.Sporadic.Ru.Native.ruData)) (ruAsmNatWord p.1) =
      wordProd (img pi7RuSpec (seedG CFSG.Sporadic.Ru.Native.ruData)) (ruAsmNatWord p.2) := fun p hp => by
  by_cases h0 : pairRelK p = []
  · rw [pairRelK_eq, List.append_eq_nil_iff, List.reverse_eq_nil_iff, List.map_eq_nil_iff,
      List.map_eq_nil_iff, List.map_eq_nil_iff] at h0
    rw [ruAsmNatWord, ruAsmNatWord, h0.1, h0.2]
  · have hmem := mem_mkPairsK hp h0
    rw [← relsEqK_eq RAl_bind, pairRelK_eq] at hmem
    exact pair_eq RAl_bd RAl_all RAl_len hmem

end CertificateChecks.KernelGMS78.W

end
