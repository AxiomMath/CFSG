module

public import CFSG.Certificates.Kernel.Fi22.LettersSound
public import Certificates.Kernel.Sporadic.ON.Gen
import Certificates.Kernel.Sporadic.StrList
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Misc.KernelRfl

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi22.Letters

open CFSG.KS.Fi22L

@[expose] noncomputable def rl (s : Nat) : Bool := ruleChkK ljPacked slpPacked (Nat.add s (nat_lit 4))

@[expose] noncomputable def iv (j : Nat) : Bool := invChkK ljPacked slpPacked j

end CertificateChecks.KernelFi22.Letters

#kon_slices CertificateChecks.KernelFi22.Letters.rl 0 133
#kon_join CertificateChecks.KernelFi22.Letters.rlAll CertificateChecks.KernelFi22.Letters.rl 133
#kon_slices CertificateChecks.KernelFi22.Letters.iv 0 16
#kon_join CertificateChecks.KernelFi22.Letters.ivAll CertificateChecks.KernelFi22.Letters.iv 16

namespace CertificateChecks.KernelFi22.Letters

open CFSG.KS.Fi22L CFSG.KS.TW CFSG.Sporadic.Fi22.Native CFSG.Sporadic.Th.Native

set_option Elab.async false

theorem gen_ok : genChkK ljPacked = true := by quickRfl

theorem wr_ok : wrChkK slpPacked = true := by quickRfl

theorem words_ok : (chainWords ()).toList =
    (List.range 16).map fun j => ((exF slpPacked 136 (wrOf slpPacked j)).map chOf).map letterOf := by
  simp only [chainWords, wordOf, String.toList_append, strToList]
  kernelRfl

theorem words_get : (chainWords ()).size = 16 ∧ ∀ j < 16,
    (chainWords ())[j]! = ((exF slpPacked 136 (wrOf slpPacked j)).map chOf).map letterOf := by
  have hs : (chainWords ()).size = 16 := by
    have := congrArg List.length words_ok
    simpa using this
  refine ⟨hs, fun j hj => ?_⟩
  rw [getElem!_pos _ j (by rw [hs]; exact hj), ← Array.getElem_toList]
  simp only [words_ok, List.getElem_map, List.getElem_range]

theorem rules_ok : ∀ k, 4 ≤ k → k < 137 → ruleChkK ljPacked slpPacked k = true := by
  intro k h1 h2
  have h := rlAll (k - 4) (by change k - 4 < 133; omega)
  unfold rl at h
  have e : Nat.add (k - 4) 4 = k := by
    simp only [Nat.add_eq]
    omega
  rwa [e] at h

theorem letters : (chainLetters orbL).size = 32 ∧
    (∀ l < 32, TR 3510 (chainLetters orbL)[l]! (LJk ljPacked slpPacked l)) ∧
      chainLetters orbL = LJA ljPacked slpPacked :=
  letters_sound gen_ok rules_ok ivAll wr_ok words_get.1 words_get.2

end CertificateChecks.KernelFi22.Letters

end
