module

public import Certificates.Kernel.T8K.Checks
public import Certificates.Kernel.WordRelK.Rel
public import CFSG.Certificates.Kernel.T8K.Sound

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CertificateChecks.KernelT8K.Facts

open CFSG.Monster.B.TwoA.Sp8.WordRel CFSG.Open MonsterB.P0Rank CFSG.KC.T8K
  CertificateChecks.KernelWordRelK.Tab


theorem elemAbelian : ∀ gs ∈ [gensA1, gensA2, gensA4'],
    IsElemAbelian 2 (Subgroup.closure {g | ∃ c ∈ gs, g = wordX (nfWord c)}) := by
  intro gs hgs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hgs
  rcases hgs with rfl | rfl | rfl
  · exact isElemAbelian_of_commPL Checks.commA1
  · exact isElemAbelian_of_commPL Checks.commA2
  · exact isElemAbelian_of_commPL Checks.commA4

theorem xConj (τ : ℕ) :
    wordX xWord * wordX (tWord τ) * (wordX xWord)⁻¹ = wordX (tWord (colsAct xT9 τ)) :=
  conj_of_conjT KernelWordRelK.Rel.tab_all Checks.conjX τ

theorem yConj (τ : ℕ) :
    wordX yWord * wordX (tWord τ) * (wordX yWord)⁻¹ = wordX (tWord (colsAct yT9 τ)) :=
  conj_of_conjT KernelWordRelK.Rel.tab_all Checks.conjY τ

end CertificateChecks.KernelT8K.Facts

end
