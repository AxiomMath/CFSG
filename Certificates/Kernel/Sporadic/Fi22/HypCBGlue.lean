module

public import Certificates.Kernel.Sporadic.Fi22.HypCBSound
public import Certificates.Kernel.Sporadic.Fi22.HypCB2
public import Certificates.Kernel.Sporadic.Fi22.HypCB3
public import Certificates.Kernel.Sporadic.Fi22.HypCB4
public import Certificates.Kernel.Sporadic.Fi22.HypCB5

public section

namespace CertificateChecks.KernelSpor.Fi22CB

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw.Orb CFSG.Monster.B.Fischer CFSG.Sporadic.FischerOddCore
open CFSG.ComponentClassification.M12Cover CFSG.Sporadic.Schreier

theorem prep_ext {k : ℕ} (hk : k < 6) :
    PRep 3510 12 (Fi22ExtT.L (21 + k)) (fi22ExtRep k) := by
  have h := rep_fi22ExtRep hk
  rw [Fi22E2067.ext_eq (L := 21 + k) (by omega)] at h
  exact prep_of_rep h

theorem fourClassesLarge_CP1 :
    FourClassesLarge ↥(centralizerIn fi22P (fi22ExtRep 1)) := by
  have hg := Fi22R1.gensAll
  simp only [Fi22R1.gensOK, bAnd_eq, Bool.and_eq_true] at hg
  obtain ⟨ca, cb, -, hpb, -, hpa, -, sa, sb, -, -⟩ := hg
  obtain ⟨g₁, m1, h1⟩ := Fi22R1.exists_mem_P ca hpa sa
  obtain ⟨g₂, m2, h2⟩ := Fi22R1.exists_mem_P cb hpb sb
  exact Fi22R1.fourClassesLarge_R1_centralizerIn fi22P h1 h2 Fi22R1.prep_T m1 m2

theorem fourClassesLarge_C2
    {H : Subgroup (Equiv.Perm (Fin 3510))} (hPH : fi22P ≤ H) :
    FourClassesLarge ↥(centralizerIn H (fi22ExtRep 2)) :=
  fourClassesLarge_of_lettersOK (prep_ext (k := 2) (by norm_num)) Fi22CB2.lettersAll
    Fi22CB2.baseAll H hPH

theorem fourClassesLarge_CR3 :
    FourClassesLarge ↥(centralizerIn fi22R (fi22ExtRep 3)) :=
  fourClassesLarge_of_lettersOK (prep_ext (k := 3) (by norm_num)) Fi22CB3.lettersAll
    Fi22CB3.baseAll fi22R fi22P_le_R

theorem fourClassesLarge_CR4 :
    FourClassesLarge ↥(centralizerIn fi22R (fi22ExtRep 4)) :=
  fourClassesLarge_of_lettersOK (prep_ext (k := 4) (by norm_num)) Fi22CB4.lettersAll
    Fi22CB4.baseAll fi22R fi22P_le_R

theorem fourClassesLarge_CR5 :
    FourClassesLarge ↥(centralizerIn fi22R (fi22ExtRep 5)) :=
  fourClassesLarge_of_lettersOK (prep_ext (k := 5) (by norm_num)) Fi22CB5.lettersAll
    Fi22CB5.baseAll fi22R fi22P_le_R

theorem fourClassesLarge_CP2 :
    FourClassesLarge ↥(centralizerIn fi22P (fi22ExtRep 2)) :=
  fourClassesLarge_C2 le_rfl

theorem fourClassesLarge_CR2 :
    FourClassesLarge ↥(centralizerIn fi22R (fi22ExtRep 2)) :=
  fourClassesLarge_C2 fi22P_le_R

end CertificateChecks.KernelSpor.Fi22CB

end
