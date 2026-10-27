module

public import Certificates.Kernel.GMS78.W106Chk

public section

namespace CertificateChecks.KernelGMS78.W

open CFSG.KC.GMSW CFSG.ComponentClassification.GMS78.RuAsm

theorem a0_ne : ∀ k < 7, CFSG.Sporadic.Bridge.wordProd
    (CFSG.Sporadic.Bridge.VecSurj.img CFSG.ComponentClassification.GMS78.RuPi7.pi7RuSpec
      (CFSG.Sporadic.Bridge.VecSurj.seedG CFSG.Sporadic.Ru.Native.ruData))
    (ruAsmNatWord (ruA0PowWord (k + 1))) ≠ 1 := by
  intro k hk
  have hh := homM RA0_roots RA0_invs RV_bd RV_all RV_len
  have hmem : (ruA0PowWord (k + 1)).map finLetK ++ [(9 + k, false)] ∈ RV := by
    rw [relsEqK_eq RV_bind, mkNeK_eq]
    exact List.mem_map.2 ⟨k, List.mem_range.2 (by simpa using hk), by simp [hk]⟩
  rw [ruAsmNatWord, ← wordProd_finLetK]
  refine wordProd_ne_one_M (by norm_num) RA0_share hh.1 ?_ (by omega) (hh.2 _ hmem) ?_
  · intro l hl
    obtain ⟨l', -, rfl⟩ := List.mem_map.1 hl
    have := l'.1.isLt
    change l'.1.val + 2 < 9
    omega
  · interval_cases k
    · exact RA0_ne0
    · exact RA0_ne1
    · exact RA0_ne2
    · exact RA0_ne3
    · exact RA0_ne4
    · exact RA0_ne5
    · exact RA0_ne6

end CertificateChecks.KernelGMS78.W

end
