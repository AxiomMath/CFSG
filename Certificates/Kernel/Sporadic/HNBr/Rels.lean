module

public import Certificates.Kernel.VecCert.HomBoundP
public import CFSG.Sporadic.HN.F5Group
public import Certificates.Data.CFSGNative.HN.Data
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.HaradaNorton
public import Certificates.Kernel.Sporadic.HNBr.Data
public import CFSG.Certificates.Kernel.Orders.HN.Rels
import Certificates.Kernel.Sporadic.HNBr.Checks
import Certificates.Kernel.Sporadic.HNBr.Seed
import CFSG.Certificates.Kernel.Orders.HN.RelsBind
import CFSG.Certificates.Kernel.Bounds.HNAlt.RelsTC
import all CFSG.Blueprint.NativeSporadic
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
import CFSG.Certificates.Kernel.Common.Harness
import Certificates.Kernel.Sporadic.BrChain
import Certificates.Kernel.Sporadic.OrdCommon
public import CFSG.Sporadic.Th.F2Spec

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.HNRels

open CFSG.KC.Ord CFSG.KS.Ord CFSG.Sporadic.F5 CFSG.KD.BrHN CertificateChecks.KernelVec

local notation "Dt" => CFSG.Sporadic.HN.Native.hnData

theorem mA_eq : mA Dt = ordMat 5 133 13 1729 (RH 16) := by
  have hr := BrChain.run_chain_to (run := decRun P1 256 17976 5 133 13 1729 RM (RH 16)) (fun _ => rfl)
      (decRun_append P1 256 17976 5 133 13 1729 RM (RH 16)) dL (fun k => DA1.getD k 0) 5 1 70759
      rfl rfl D1.all
  have h := seed_sound (hnb := rfl) consts seed1_bytes (by decide +kernel) hr d1_end
  change CFSG.Blueprint.NativeSporadic.decode 5 133 1 CFSG.Sporadic.HN.Native.seedA = _
  rw [HNSeedA.eq, h]

theorem mB_eq : mB Dt = ordMat 5 133 13 1729 (RH 24) := by
  have hr := BrChain.run_chain_to (run := decRun P2 256 17976 5 133 13 1729 RM (RH 24)) (fun _ => rfl)
      (decRun_append P2 256 17976 5 133 13 1729 RM (RH 24)) dL (fun k => DA2.getD k 0) 5 1 70759
      rfl rfl D2.all
  have h := seed_sound (hnb := rfl) consts seed2_bytes (by decide +kernel) hr d2_end
  change CFSG.Blueprint.NativeSporadic.decode 5 133 1 CFSG.Sporadic.HN.Native.seedB = _
  rw [HNSeedB.eq, h]

theorem regs : RegsInP 5 133 13 1729 229957 L H 5 RH 25 := by
  have h0 : RegsInP 5 133 13 1729 229957 L H 5 RH 6 := regsIn_rootsP hroots
  exact slpSeg_soundP (hnb := rfl) (by decide) consts hs h0

theorem hr : ∀ r < lenRels CFSG.KD.OrdHN.rels,
    relOK RH (mulR 5 13 1729 133 9 L H CM RM) CFSG.KD.OrdHN.rels 5 ONE r = true ∨
      ∃ s < r, relDupOK CFSG.KD.OrdHN.rels s r = true := by
  intro r hr
  have hn : lenRels CFSG.KD.OrdHN.rels = 19 := Nat.eq_of_beq_eq_true relN
  rw [hn] at hr
  exact Or.inl (R.all r hr)

theorem gens_eq : TauCeti.Sporadic.hnPresentation.generatorCount = 5 := by
  simp [TauCeti.GroupPresentation.generatorCount, TauCeti.Sporadic.hnPresentation_generatorNames]

theorem le_range : ∃ φ : TauCeti.Sporadic.hnPresentation.Group →*
      GL (Fin (CFSG.Sporadic.HN.Native.hnData ()).d) (ZMod 5),
    J CFSG.Sporadic.HN.Native.hnData ≤ φ.range := by
  have hab := (andB_iff _ _).1 hAB
  have hA := (andB_iff _ _).1 hab.1
  have hB := (andB_iff _ _).1 hab.2
  have hre : TauCeti.Sporadic.hnPresentation.relatorLetters = CFSG.KD.OrdHN.rels := by
    rw [CFSG.KC.HNA.rels_eq, CFSG.KD.OrdHN.rels_eq]
  obtain ⟨φ, hφ⟩ := le_range_of_homP (d := (CFSG.Sporadic.HN.Native.hnData ()).d) TauCeti.Sporadic.hnPresentation (hnb := rfl)
    consts hre gens_eq hroots hinv relB hr regs (Nat.blt_eq.mp hA.1) (Nat.blt_eq.mp hA.2)
    (Nat.blt_eq.mp hB.1) (Nat.blt_eq.mp hB.2) mA_eq mB_eq
  exact ⟨φ, closure_dite_le hφ⟩

end CertificateChecks.KernelSpor.HNRels

end
