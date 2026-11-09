module

public import Certificates.Kernel.LyGlue.BaseRel

set_option maxRecDepth 100000

public section

namespace CertificateChecks.KernelLy

open CFSG.KC.Enum CFSG.KS CFSG.KC.LyGlue CFSG.Sporadic.Recognition.LyonsSims Equiv Subgroup
  CFSG.Sporadic.Recognition CFSG.Certificates.Kernel.PkCV CFSG.Sporadic.Th

theorem txyBp_txG (hM : Ly0.ModelChecks) {j : Nat} (hj : j < 5)
    (h1 : ∀ l ∈ Ly1080.txyWords.getD j [], l ≠ 0 ∧ l.natAbs ≤ 4)
    (h2 : ∀ l ∈ Ly243.txyWords.getD j [], l ≠ 0 ∧ l.natAbs ≤ 4) :
    wordG (wordLetter Ly0.uG) (Ly1080.txyWords.getD j []) =
      wordG (wordLetter Glue.txG) (Ly243.txyWords.getD j []) := by
  rw [← prodP_uEs hM.tab _ h1, ← prodP_txE hM.tab _ h2]
  exact lyBase3_spec hM (allN_spec k_agree j hj)

end CertificateChecks.KernelLy

end
