module

public import Certificates.Kernel.GLQ.LyScal
public import Certificates.Kernel.MatCert.GlueLy
public import CFSG.Certificates.Kernel.OpsHomRels

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelGLQ.LyScalK

open CFSG.KC.OpsK CFSG.KC.OpsHom CFSG.SectionRank.Native CFSG.Sporadic.GLQ CFSG.Blueprint
open CFSG.RankThree.PartOne.KS.ScalFive CFSG.RankThree.PartOne.KS.LyScal
open CertificateChecks.KernelMC CertificateChecks.KernelSporSch

theorem lt_iQ : ∀ j, lyData.iQ j < lyData.nreg := by decide +kernel

theorem facts14986 : lyScalCheck = true := by
  have hk := kLy5
  unfold checkLy5 at hk
  rw [forceB_eq, powN_eq _ _ _ _ (by norm_num), runK_eq] at hk
  have hPA : HL.P LyBS.A := vldL LyBS.vA
  have hPB : HL.P LyBS.B := vldL LyBS.vB
  obtain ⟨eB4, pB4⟩ := HL.pow_U 4 hPB
  have hlt : lyData.prog.all (Instr.lt lyData.nreg) = true := by decide +kernel
  have hinit : initRegsN (opsP 5 111) lyData.nreg ((opsP 5 111).decode NativeSporadic.LySeed1,
      (opsP 5 111).decode NativeSporadic.LySeed1)
      ((opsP 5 111).decode NativeSporadic.LySeed2,
        (opsP 5 111).pow ((opsP 5 111).decode NativeSporadic.LySeed2) 4) =
      (initRegsN OL lyData.nreg (LyBS.A, LyBS.A) (LyBS.B, OL.pow LyBS.B 4)).map HL.UU := by
    rw [lyA, lyB, eB4]
    exact HL.initRegsN_U lyData.nreg (LyBS.A, LyBS.A) (LyBS.B, OL.pow LyBS.B 4)
  obtain ⟨hrun, hsize, hP⟩ := HL.runProgN_U lyData.nreg lyData.prog hlt
    (initRegsN OL lyData.nreg (LyBS.A, LyBS.A) (LyBS.B, OL.pow LyBS.B 4)) (by simp [initRegsN])
    (HL.initRegsN_P ⟨hPA, hPA⟩ ⟨hPB, pB4⟩)
  unfold lyScalCheck lyRegs
  rw [hlt, Bool.true_and, hinit, hrun, HL.scRelsOK_U lyData hP (by rw [hsize]; decide)
    (by rw [hsize]; decide) (by rw [hsize]; decide) (fun j => by rw [hsize]; exact lt_iQ j)]
  exact hk

end CertificateChecks.KernelGLQ.LyScalK

end
