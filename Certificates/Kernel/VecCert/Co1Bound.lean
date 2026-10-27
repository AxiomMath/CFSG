module

public import Certificates.Kernel.VecCert.SlpChain
public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Data.CFSGNative.Co1.Data
public import CFSG.Certificates.Kernel.Orders.Co1.RelsBind
public import CFSG.Certificates.Kernel.Orders.Co1.GensBind
public import CFSG.Certificates.Kernel.Orders.Co1.Checks.R
public import CFSG.Certificates.Kernel.Orders.Co1.Checks.H
public import CFSG.Certificates.Kernel.Orders.Co1.Checks.D
public import CFSG.Certificates.Kernel.Orders.Co1.Checks.K
public import CFSG.Certificates.Kernel.Orders.Co1.Data.Pay
import Certificates.Kernel.Co1.Bridge
import all CFSG.Blueprint.NativeSporadic
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
public import CFSG.Perm.ChainSpec
public import CFSG.Sporadic.Th.F2Spec

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelVec.Co1SeedA CFSG.Sporadic.Co1.Native.seedA

#ks_chars CertificateChecks.KernelVec.Co1SeedB CFSG.Sporadic.Co1.Native.seedB

namespace CertificateChecks.KernelVec.Co1Bound

open CFSG.KC.Ord CFSG.KS.Ord CFSG.Sporadic.SmallF2 CFSG.KD.OrdCo1

local notation "Dt" => CFSG.Sporadic.Co1.Native.co1Data

theorem seed1_bytes : CFSG.KS.Bytes.bytesEqK Co1SeedA.chars P1 256 621 = true := by quickRfl

theorem seed2_bytes : CFSG.KS.Bytes.bytesEqK Co1SeedB.chars P2 256 621 = true := by quickRfl

theorem mA_eq : mA Dt = ordMat 2 24 6 144 (RW 1) := by
  have h := seed_sound (hnb := rfl) consts seed1_bytes (by decide) d1_0 d1_end
  change CFSG.Blueprint.NativeSporadic.decode 2 24 1 CFSG.Sporadic.Co1.Native.seedA = _
  rw [Co1SeedA.eq, h]

theorem mB_eq : mB Dt = ordMat 2 24 6 144 (RW 2) := by
  have h := seed_sound (hnb := rfl) consts seed2_bytes (by decide) d2_0 d2_end
  change CFSG.Blueprint.NativeSporadic.decode 2 24 1 CFSG.Sporadic.Co1.Native.seedB = _
  rw [Co1SeedB.eq, h]

theorem regs : RegsIn 24 6 144 3456 L H 8 RH 1399 := by
  have h : RegsIn 24 6 144 3456 L H 8 RH 9 := regsIn_roots hroots
  exact slpSeg_chain SWs hsSt consts rfl 29 SG.all h

theorem hr : ∀ r < lenRels rels, relOK RH (mulR 2 6 144 24 4 L H CM RM) rels 8 ONE r = true ∨
    ∃ s < r, relDupOK rels s r = true := by
  intro r hr
  have hn : lenRels rels = 45 := Nat.eq_of_beq_eq_true relN
  rw [hn] at hr
  exact Or.inl (R.all r hr)

theorem card_J_le :
    Nat.card (J Dt) ≤ (CFSG.Sporadic.Co1.Native.co1Data ()).orbSizes.prod := by
  obtain ⟨hfin, hcard⟩ := CertificateChecks.KernelCo1.co1
  have hfin' : Finite TauCeti.Sporadic.co1Presentation.Group := hfin
  have hcard' : Nat.card TauCeti.Sporadic.co1Presentation.Group ≤ 4157776806543360000 := hcard
  have hab := (andB_iff _ _).1 hAB
  have hab1 := (andB_iff _ _).1 hab.1
  have hab2 := (andB_iff _ _).1 hab.2
  have hA := (andB_iff _ _).1 hab1.1
  have hB := (andB_iff _ _).1 hab1.2
  have h := card_J_le_of_hom Dt TauCeti.Sporadic.co1Presentation (hnb := rfl) consts rels_eq gens_eq
    hroots hinv relB hr regs (lt_of_blt hA.1) (lt_of_blt hA.2)
    (lt_of_blt hB.1) (lt_of_blt hB.2) (Nat.eq_of_beq_eq_true hab2.1)
    (Nat.eq_of_beq_eq_true hab2.2) mA_eq mB_eq hcard'
  exact h.trans (by decide)

end CertificateChecks.KernelVec.Co1Bound

end
