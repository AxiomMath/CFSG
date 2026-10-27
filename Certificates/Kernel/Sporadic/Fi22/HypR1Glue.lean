module

public import Certificates.Kernel.Sporadic.Fi22.HypR1Sound
import CFSG.Certificates.Kernel.Enum.ZCSound
public import CFSG.Sporadic.FischerOddCore.Fi22Ext
public import Certificates.Kernel.Sporadic.Fi22.C2068Base

public section

namespace CertificateChecks.KernelSpor.Fi22R1

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw.Orb CFSG.Monster.B.Fischer CFSG.Sporadic.FischerOddCore
open CFSG.ComponentClassification.M12Cover CFSG.Sporadic.Schreier

theorem exists_mem_P
    {a ai nw : Nat} (hc : Fi22X.cn a = true) (hp : permOK 3510 12 (mask 12) nw a ai = true)
    (hs : Fi22X.siftP a = true) : ∃ g ∈ fi22P, PRep 3510 12 a g := by
  obtain ⟨g, hg, -⟩ := CFSG.KC.EnumSound.permOK_perm hp
  refine ⟨g, (fi22InP_iff (rep_unpack hg)).1 ?_, hg⟩
  rw [Fi22LabA.fi22InP_eq rfl hc]
  exact hs

theorem prep_T : PRep 3510 12 T (fi22ExtRep 1) := by
  have h := rep_fi22ExtRep (k := 1) (by norm_num)
  rw [Fi22E2067.ext_eq (L := 21 + 1) (by norm_num)] at h
  exact prep_of_rep h

theorem fourClassesLarge_CR1 :
    FourClassesLarge ↥(centralizerIn fi22R (fi22ExtRep 1)) := by
  have hg := gensAll
  simp only [gensOK, bAnd_eq, Bool.and_eq_true] at hg
  obtain ⟨ca, cb, -, hpb, -, hpa, -, sa, sb, -, -⟩ := hg
  obtain ⟨g₁, m1, h1⟩ := exists_mem_P ca hpa sa
  obtain ⟨g₂, m2, h2⟩ := exists_mem_P cb hpb sb
  exact fourClassesLarge_R1_centralizerIn fi22R h1 h2 prep_T (fi22P_le_R m1) (fi22P_le_R m2)

end CertificateChecks.KernelSpor.Fi22R1

end
