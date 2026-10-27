module

public import Certificates.Kernel.GLQ.Co1Scal
public import Certificates.Kernel.TcGen.F2Glue
public import CFSG.Certificates.Kernel.OpsHomRels

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelGLQ.Co1ScalK

open CFSG.KC.OpsK CFSG.KC.OpsHom CFSG.SectionRank.Native CFSG.Sporadic.GLQ CFSG.Blueprint
open CFSG.RankThree.PartOne.KS.ScalFive CFSG.RankThree.PartOne.KS.Co1Scal CertificateChecks.KernelTc

noncomputable abbrev H2 : Hom (ops2 24) (opsF2K 24) := hom2 24 (by norm_num)

theorem lt_iQ : ∀ j, co1Data.iQ j < co1Data.nreg := by decide +kernel

theorem facts14987 : co1ScalCheck = true := by
  have hk := kCo15
  unfold checkCo15 at hk
  simp only [Bool.and_eq_true] at hk
  obtain ⟨⟨h2, h3⟩, hk⟩ := hk
  rw [powN_eq _ _ _ _ (by norm_num)] at h2 h3
  rw [forceB_eq, powN_eq _ _ _ _ (by norm_num), runK_eq] at hk
  have hlt : co1Data.prog.all (Instr.lt co1Data.nreg) = true := by decide +kernel
  have eA : (ops2 24).decode NativeSporadic.Co1Seed1 = H2.U C1A.M := c1A
  have eB : (ops2 24).decode NativeSporadic.Co1Seed2 = H2.U C1B.M := c1B
  have hinit : initRegsN (ops2 24) co1Data.nreg ((ops2 24).decode NativeSporadic.Co1Seed1,
      (ops2 24).decode NativeSporadic.Co1Seed1)
      ((ops2 24).decode NativeSporadic.Co1Seed2,
        (ops2 24).pow ((ops2 24).decode NativeSporadic.Co1Seed2) 2) =
      (initRegsN (opsF2K 24) co1Data.nreg (C1A.M, C1A.M)
        (C1B.M, (opsF2K 24).pow C1B.M 2)).map H2.UU := by
    rw [eA, eB, (H2.pow_U 2 trivial).1]
    exact H2.initRegsN_U co1Data.nreg (C1A.M, C1A.M) (C1B.M, (opsF2K 24).pow C1B.M 2)
  obtain ⟨hrun, hsize, hP⟩ := H2.runProgN_U co1Data.nreg co1Data.prog hlt
    (initRegsN (opsF2K 24) co1Data.nreg (C1A.M, C1A.M) (C1B.M, (opsF2K 24).pow C1B.M 2))
    (by unfold initRegsN; exact Array.size_ofFn) (H2.initRegsN_P ⟨trivial, trivial⟩ ⟨trivial, trivial⟩)
  unfold co1ScalCheck co1Regs
  rw [hlt, Bool.true_and, hinit, hrun, H2.scRelsOK_U co1Data hP (by rw [hsize]; decide)
    (by rw [hsize]; decide) (by rw [hsize]; decide) (fun j => by rw [hsize]; exact lt_iQ j),
    eA, eB, H2.scPowOK_U trivial, H2.scPowOK_U trivial]
  unfold powOK
  rw [h2, h3]
  exact hk

end CertificateChecks.KernelGLQ.Co1ScalK

end
