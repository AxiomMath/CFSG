module

public import CFSG.Sporadic.Recognition.LyonsAmalgamGlueFacts
public import Certificates.Kernel.LyGlue.Facts4

set_option maxRecDepth 100000

public section

namespace CertificateChecks.KernelLy

open CFSG.KC.Enum CFSG.KS CFSG.KC.LyGlue CFSG.Sporadic.Recognition.LyonsSims Equiv Subgroup
  CFSG.Sporadic.Recognition CFSG.Certificates.Kernel.PkCV CFSG.Sporadic.Th

noncomputable abbrev Hb : Subgroup (Perm (Fin Ly0.deg)) := closure (Glue.txyBp '' {l | l < 5})

theorem txyWords_getD {j : Nat} (hj : j < 5) :
    Ly1080.txyWords[j]! = Ly1080.txyWords.getD j [] := by
  interval_cases j <;> rfl

theorem xG_eq_word (hM : Ly0.ModelChecks) : Ly0.xG = Ly0.wG Ly0.gens0 Ly0.wordX :=
  Ly0.eq_of_rep (Ly0.rep_X hM.tab hM.struct) (by
    rw [← (Ly0.structCheck_spec hM.struct).2.2.2.2.2.1]
    exact Ly0.rep_word0 hM.tab _ fun l hl => Ly0.decodeWord_mem _ l hl)
end CertificateChecks.KernelLy

end
