module

public import Certificates.Kernel.Sporadic.RawGen
public import CFSG.Certificates.Kernel.Spor.RawSound
public import Certificates.Kernel.Misc.Perm.U33Base
meta import Certificates.Kernel.Misc.Perm.U33Base
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Monster.B.Co2.PermArr

public section

set_option maxRecDepth 400000

#ks_rawchain CertificateChecks.KernelMisc.U33C 28 5 28 CFSG.Quasithin.u33Strong
  CertificateChecks.KernelMisc.U33.baseArr 5 CertificateChecks.KernelMisc.U33.derivs

namespace CertificateChecks.KernelMisc.U33C

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Quasithin CFSG.Certificates.Native
open CertificateChecks.KernelMisc.U33

theorem perm : allN 9 (fun j => permOK 28 5 (mask 5) (28 * 5) (S j) (SI j)) = true := by
  quickRfl

theorem binds : Binds 28 5 S 9 4 BP u33Strong baseArr := by
  refine ⟨by norm_num, by norm_num, by norm_num, by decide +kernel, ?_, by decide +kernel,
    by decide +kernel⟩
  decide +kernel

theorem words_eq : u33RawWords = CFSG.Sporadic.Schreier.Co3.Native.wordsArr 5 9 derivs := by
  decide +kernel

theorem facts : u33Gens.size = 5 ∧ CFSG.YGroups.ModelNative.permsOK 28 u33Gens = true ∧
    u33Gens.size ≤ u33Strong.size ∧ (∀ i < u33Gens.size, u33Strong[i]! = u33Gens[i]!) ∧
    rawChainOK 28 (u33Strong.extract 0 u33Gens.size) u33Strong (u33Base.map Fin.val).toArray
      u33RawWords 1 = true ∧
    rawOrbitSizes 28 u33Strong (u33Base.map Fin.val).toArray = [28, 27, 2, 4] := by
  have hsz : u33Gens.size = 5 := by decide +kernel
  have hS : u33Strong.size = 9 := by decide +kernel
  have heq : ∀ i < u33Gens.size, u33Strong[i]! = u33Gens[i]! := by decide +kernel
  have hch : rawChainOK 28 (u33Strong.extract 0 u33Gens.size) u33Strong
      (u33Base.map Fin.val).toArray u33RawWords 1 = true := by
    rw [hsz, words_eq]
    exact rawChainK_sound (NS := 1) (CH := 28) binds head hl (by norm_num) hs
  refine ⟨hsz, ?_, by rw [hsz, hS]; norm_num, heq, hch, ?_⟩
  · have hinv := hch
    simp only [rawChainOK, Bool.and_eq_true] at hinv
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, h3⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hinv
    unfold CFSG.YGroups.ModelNative.permsOK
    refine CFSG.Monster.B.Co2.allLt_iff.2 fun c hc => ?_
    have hc9 : c < u33Strong.size := by rw [hS]; omega
    have h := CFSG.Monster.B.Co2.allLt_spec h3 hc9
    have hm : (rawInvs 28 u33Strong)[c]! =
        CFSG.Monster.B.Co2.Native.invCand 28 u33Strong[c]! := by
      rw [rawInvs, getElem!_pos (u33Strong.map _) c (by simpa using hc9), Array.getElem_map,
        getElem!_pos u33Strong c hc9]
    rwa [hm, heq c hc] at h
  · change rawOrbitSizes 28 u33Strong baseArr = _
    rw [rawOrbitSizesK_sound binds perm hl]
    decide +kernel

end CertificateChecks.KernelMisc.U33C

end
