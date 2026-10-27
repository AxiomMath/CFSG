module

public import Certificates.Data.Kernel.HSGraph6100

public section

namespace CertificateChecks.KernelHSGraph6100

open Certificates.Kernel.HSIdent Certificates.Kernel.HSGraph6100
  CFSG.Sporadic.Recognition CFSG.Sporadic.Recognition.HSGraph
  CFSG.ComponentClassification.WittDesign

theorem srg_ok : srgK rowOf = true := by decide +kernel

theorem distinct_ok : distinctK hexMask = true := by decide +kernel

theorem psiInv_left_ok : ∀ i, psiInvFun (HSGraph.psiFun i) = i := by decide +kernel

theorem psiInv_right_ok : ∀ i, HSGraph.psiFun (psiInvFun i) = i := by decide +kernel

theorem psi_ok : psiK psiList = true := by decide +kernel

theorem sig_ok : sigK sigN = true := by decide +kernel

theorem sigInv_ok : ∀ i, sigNF sigN (sigNF sigN i) = i := by decide +kernel

theorem sign_ok : Equiv.Perm.sign (sigPerm sigN sigInv_ok) = -1 := by decide +kernel

end CertificateChecks.KernelHSGraph6100
