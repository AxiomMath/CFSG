module

public import Certificates.Kernel.VecCert.HomBoundP
public import CFSG.Sporadic.Ly.Setup
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Lyons
public import Certificates.Kernel.Sporadic.LyBr.Data
public import CFSG.Certificates.Kernel.Orders.Ly.Rels
import Certificates.Kernel.Sporadic.LyBr.Checks
import Certificates.Kernel.Sporadic.LyBr.Seed
import Certificates.Kernel.Sporadic.LyBr.Prog0
import Certificates.Kernel.Sporadic.LyBr.Prog1
import Certificates.Kernel.Sporadic.LyBr.Prog2
import CFSG.Certificates.Kernel.Orders.Ly.RelsBind
import CFSG.Certificates.Kernel.Bounds.LyAlt.RelsTC
import all CFSG.Blueprint.NativeSporadic
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
import CFSG.Certificates.Kernel.Common.Harness
import Certificates.Kernel.Sporadic.BrChain
import Certificates.Kernel.Sporadic.OrdCommon
public import CFSG.Sporadic.Ly.FaithSpec
public import CFSG.Sporadic.Ly.OrbitSpec

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.LyRels

open CFSG.KC.Ord CFSG.KS.Ord CFSG.KD.BrLy CertificateChecks.KernelVec

theorem mA_eq : CFSG.Sporadic.Ly.mA = ordMat 5 111 12 1332 (RH 314) := by
  have hr := BrChain.run_chain_to (run := decRun P1 256 18063 (nat_lit 5) (nat_lit 111) (nat_lit 12) (nat_lit 1332) RM (RH 314)) (fun _ => rfl)
      (decRun_append P1 256 18063 (nat_lit 5) (nat_lit 111) (nat_lit 12) (nat_lit 1332) RM (RH 314)) dL (fun k => DA1.getD k 0) 5 1 49287
      rfl rfl D1.all
  have h := seed_sound (hnb := rfl) consts seed1_bytes (by decide +kernel) hr d1_end
  change CFSG.Blueprint.NativeSporadic.decode 5 111 1 CFSG.Blueprint.NativeSporadic.LySeed1 = _
  rw [LySeedA.eq, h]

theorem mB_eq : CFSG.Sporadic.Ly.mB = ordMat 5 111 12 1332 (RH 3890) := by
  have hr := BrChain.run_chain_to (run := decRun P2 256 18063 (nat_lit 5) (nat_lit 111) (nat_lit 12) (nat_lit 1332) RM (RH 3890)) (fun _ => rfl)
      (decRun_append P2 256 18063 (nat_lit 5) (nat_lit 111) (nat_lit 12) (nat_lit 1332) RM (RH 3890)) dL (fun k => DA2.getD k 0) 5 1 49287
      rfl rfl D2.all
  have h := seed_sound (hnb := rfl) consts seed2_bytes (by decide +kernel) hr d2_end
  change CFSG.Blueprint.NativeSporadic.decode 5 111 1 CFSG.Blueprint.NativeSporadic.LySeed2 = _
  rw [LySeedB.eq, h]

abbrev Regs (S : Nat) : Prop :=
  RegsInP (nat_lit 5) (nat_lit 111) (nat_lit 12) (nat_lit 1332) (nat_lit 147852) L H (nat_lit 6) RH S

theorem seg {S0 S1 : Nat} {Cs : List Nat}
    (hS : Nat.beq (runSlp RH (mulR (nat_lit 5) (nat_lit 12) (nat_lit 1332) (nat_lit 111) (nat_lit 8)
      L H CM RM) (validM (nat_lit 5) (nat_lit 147852) L H) ONE Cs S0) S1 = true)
    (h0 : Regs S0) : Regs S1 :=
  @slpSeg_soundP (nat_lit 5) (nat_lit 111) (nat_lit 12) (nat_lit 1332) (nat_lit 8) L H CM RM ONE LV
    HV (nat_lit 147852) (nat_lit 6) S0 S1 RH Cs (by decide) consts rfl hS h0

theorem regs0 : Regs (nat_lit 7) :=
  regsIn_rootsP (d := nat_lit 111) (w := nat_lit 12) (S := nat_lit 1332) hroots

theorem regs : Regs (nat_lit 3891) :=
  seg (S0 := nat_lit 2599) hm2 <| seg (S0 := nat_lit 1303) hm1 <| seg (S0 := nat_lit 7) hm0 regs0

theorem hr : ∀ r < lenRels CFSG.KD.OrdLy.rels,
    relOK RH (mulR (nat_lit 5) (nat_lit 12) (nat_lit 1332) (nat_lit 111) (nat_lit 8) L H CM RM)
      CFSG.KD.OrdLy.rels (nat_lit 6) ONE r = true ∨
      ∃ s < r, relDupOK CFSG.KD.OrdLy.rels s r = true := by
  intro r hr
  have hn : lenRels CFSG.KD.OrdLy.rels = 53 := Nat.eq_of_beq_eq_true relN
  rw [hn] at hr
  exact Or.inl (R.all r hr)

theorem gens_eq : TauCeti.Sporadic.Lyons.presentation.generatorCount = nat_lit 6 := by
  simp [TauCeti.GroupPresentation.generatorCount,
    TauCeti.Sporadic.Lyons.presentation_generatorNames]

theorem le_range : ∃ φ : TauCeti.Sporadic.Lyons.presentation.Group →* GL (Fin 111) (ZMod 5),
    ∀ g : GL (Fin 111) (ZMod 5), g.val = CFSG.Sporadic.Ly.mA ∨ g.val = CFSG.Sporadic.Ly.mB →
      g ∈ φ.range := by
  have hab := (andB_iff _ _).1 hAB
  have hA := (andB_iff _ _).1 hab.1
  have hB := (andB_iff _ _).1 hab.2
  have hre : TauCeti.Sporadic.Lyons.presentation.relatorLetters = CFSG.KD.OrdLy.rels := by
    rw [CFSG.KC.LyA.rels_eq, CFSG.KD.OrdLy.rels_eq]
  exact le_range_of_homP TauCeti.Sporadic.Lyons.presentation (hnb := rfl)
    consts hre gens_eq hroots hinv relB hr regs (Nat.blt_eq.mp hA.1) (Nat.blt_eq.mp hA.2)
    (Nat.blt_eq.mp hB.1) (Nat.blt_eq.mp hB.2) mA_eq mB_eq

end CertificateChecks.KernelSpor.LyRels

end
