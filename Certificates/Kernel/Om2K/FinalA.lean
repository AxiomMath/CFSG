module

public import Certificates.Kernel.Om2K.Gen
public import Certificates.Kernel.Om2K.Words
public import Certificates.Kernel.Om2K.EnumGlue
public import Certificates.Kernel.Om2K.Sub

public section

namespace CertificateChecks.KernelOm2

open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om2Check

theorem certA : CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om2Check.om2CheckA () = true := by
  unfold om2CheckA
  simp only [Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨gen_k, words_k⟩, rel_k⟩, enum_k⟩, orbit_k⟩, sub_k⟩, r0_k⟩

end CertificateChecks.KernelOm2

end
