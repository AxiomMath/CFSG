module

public import Certificates.Kernel.Ronan148.He148003
public import Certificates.Kernel.Co2Chain.He12635

public section

namespace CertificateChecks.KernelRonan148.He148003

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.Monster.B.Co2.Native
open CFSG.RankThree.PartTwo.Sec4.Ronan148R CFSG.AGLEmbeddingD2.Wilson.ThetaSpor.He
open CertificateChecks.KernelLC.HeFix

theorem heN0Check_true : heN0Check () = true := by
  obtain ⟨eN, lN⟩ := wordEqK_sound CertificateChecks.KernelCo2Chain.He12635.hS kPL2 kW
  obtain ⟨eX, lX⟩ := wordEqK_sound CertificateChecks.KernelCo2Chain.He12635.hS kPL2 kX
  obtain ⟨eI, iI⟩ := invEqK_sound kI
  have hc := kC
  simp only [Bool.and_eq_true] at hc
  obtain ⟨⟨cN, cI⟩, cX⟩ := hc
  have eN' : heThreeArr heN0W = unpack 8330 14 (HN 0) := eN
  have eX' : heThreeBA = unpack 8330 14 (HN 1) := eX
  have cXI := canonK_pcomp cX cI
  have cF := canonK_pcomp cN cXI
  have cFI := canonK_pcomp cF cI
  simp only [heN0Check]
  rw [eN', eX', eI, iI, lN, lX, compA_unpack cX cI, compA_unpack cN cXI, compA_unpack cF cX,
    compA_unpack cX cF, compA_unpack cX cX, compA_unpack cF cI, compA_unpack cN cFI, hidA,
    eqA_unpack (canonK_pcomp cF cX) (canonK_pcomp cX cF), eqA_unpack cF hid, eqA_unpack cF cX,
    eqA_unpack cF (canonK_pcomp cX cX),
    eqA_unpack (canonK_pcomp cN cFI) (canonK_pcomp cX cF)]
  simp only [Bool.true_and]
  exact kR

end CertificateChecks.KernelRonan148.He148003

end
