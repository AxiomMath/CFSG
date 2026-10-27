
module

public import Certificates.Kernel.Sporadic.OddCore.HND1
public import Certificates.Kernel.Sporadic.OddCore.HND2
public import Certificates.Kernel.Sporadic.OddCore.HND3
public import Certificates.Kernel.Sporadic.OddCore.HND4
public import Certificates.Kernel.Sporadic.OddCore.HN2093

public section

namespace CertificateChecks.KernelSpor.HND

open CFSG.Sporadic.HNOddCore CFSG.Sporadic.HNOddCore.InvData CFSG.Sporadic.HNOddCore.Native

theorem cls_shape : (clsLists.size == 29 && (clsLists.foldl (fun s a => s + a.size) 0) == 880 &&
    witRep.size == 39 && nonRep.size == 9) = true := by
  rw [HN2093.clsLists_eq]
  decide +kernel

theorem facts2084 : dataChecks = true := by
  have h1 := fixSizes
  have h2 := s1_shape
  have h3 := s4_shape
  have h4 := s6_shape
  have h5 := cs_shape
  have h6 := qp_shape
  have h7 := cpar_shape
  have h8 := cl_shape
  have h9 := vpar_shape
  have h10 := vl_shape
  have h11 := pg_shape
  have h12 := par_shape
  have h13 := pl_shape
  have h14 := pc_shape
  have h15 := cls_shape
  simp only [Bool.and_eq_true] at h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
  simp only [dataChecks, actSizesOK, twoSizesOK, sylowSizesOK, Bool.and_eq_true]
  refine ⟨⟨⟨h1, ?_⟩, ?_⟩, ?_⟩
  · exact ⟨⟨⟨⟨⟨h2.1, h2.2⟩, h3.1⟩, h3.2⟩, h4.1⟩, h4.2⟩
  · exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h5.1, h5.2⟩, h6.1⟩, h6.2⟩, h7.1⟩, h7.2⟩, h8.1⟩, h8.2⟩, h9.1⟩, h9.2⟩,
      h10.1⟩, h10.2⟩
  · exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h11.1, h11.2⟩, h12.1⟩, h12.2⟩, h13.1⟩, h13.2⟩, h14.1⟩, h14.2⟩,
      h15.1.1.1⟩, h15.1.1.2⟩, h15.1.2⟩, h15.2⟩

end CertificateChecks.KernelSpor.HND

end
