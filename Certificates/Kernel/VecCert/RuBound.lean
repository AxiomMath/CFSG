module

public import Certificates.Kernel.VecCert.SlpChain
public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Data.CFSGNative.Ru.Data
public import CFSG.Certificates.Kernel.Orders.Ru.RelsBind
public import CFSG.Certificates.Kernel.Orders.Ru.GensBind
public import CFSG.Certificates.Kernel.Orders.Ru.Checks.R
public import CFSG.Certificates.Kernel.Orders.Ru.Checks.H
public import CFSG.Certificates.Kernel.Orders.Ru.Checks.D
public import CFSG.Certificates.Kernel.Orders.Ru.Checks.K
public import CFSG.Certificates.Kernel.Orders.Ru.Data.Pay
public import CFSG.Sporadic.Presentation.RuExact
import all CFSG.Blueprint.NativeSporadic
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
public import CFSG.Certificates.SeededRelations
public import CFSG.Certificates.WordSubgroupRel
public import CFSG.Perm.ChainSpec
public import CFSG.Sporadic.Presentation.Common
public import CFSG.Sporadic.Th.F2Spec

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelVec.RuSeedA CFSG.Sporadic.Ru.Native.seedA

#ks_chars CertificateChecks.KernelVec.RuSeedB CFSG.Sporadic.Ru.Native.seedB

namespace CertificateChecks.KernelVec.RuBound

open CFSG.KC.Ord CFSG.KS.Ord CFSG.Sporadic.SmallF2 CFSG.KD.OrdRu

local notation "Dt" => CFSG.Sporadic.Ru.Native.ruData

theorem seed1_bytes : CFSG.KS.Bytes.bytesEqK RuSeedA.chars P1 256 2349 = true := by quickRfl

theorem seed2_bytes : CFSG.KS.Bytes.bytesEqK RuSeedB.chars P2 256 2349 = true := by quickRfl

theorem mA_eq : mA Dt = ordMat 2 28 6 168 (RW 1) := by
  have h := seed_sound (hnb := rfl) consts seed1_bytes (by decide) d1_0 d1_end
  change CFSG.Blueprint.NativeSporadic.decode 2 28 1 CFSG.Sporadic.Ru.Native.seedA = _
  rw [RuSeedA.eq, h]

theorem mB_eq : mB Dt = ordMat 2 28 6 168 (RW 2) := by
  have h := seed_sound (hnb := rfl) consts seed2_bytes (by decide) d2_0 d2_end
  change CFSG.Blueprint.NativeSporadic.decode 2 28 1 CFSG.Sporadic.Ru.Native.seedB = _
  rw [RuSeedB.eq, h]

theorem regs : RegsIn 28 6 168 4704 L H 3 RH 303 := by
  have h0 : RegsIn 28 6 168 4704 L H 3 RH 4 := regsIn_roots hroots
  exact slpSeg_chain SWs hsSt consts rfl 7 SG.all h0

theorem hr : ∀ r < lenRels rels, relOK RH (mulR 2 6 168 28 4 L H CM RM) rels 3 ONE r = true ∨
    ∃ s < r, relDupOK rels s r = true := by
  intro r hr
  have hn : lenRels rels = 12 := Nat.eq_of_beq_eq_true relN
  rw [hn] at hr
  exact Or.inl (R.all r hr)

theorem card_J_le :
    Nat.card (J Dt) ≤ (CFSG.Sporadic.Ru.Native.ruData ()).orbSizes.prod := by
  obtain ⟨hfin, hcard⟩ := CFSG.Sporadic.Presentation.Ru.finite_card_le
  have hfin' : Finite TauCeti.Sporadic.ruPresentation.Group := hfin
  have hcard' : Nat.card TauCeti.Sporadic.ruPresentation.Group ≤ 145926144000 := hcard
  have hab := (andB_iff _ _).1 hAB
  have hab1 := (andB_iff _ _).1 hab.1
  have hab2 := (andB_iff _ _).1 hab.2
  have hA := (andB_iff _ _).1 hab1.1
  have hB := (andB_iff _ _).1 hab1.2
  have h := card_J_le_of_hom Dt TauCeti.Sporadic.ruPresentation (hnb := rfl) consts rels_eq gens_eq
    hroots hinv relB hr regs (lt_of_blt hA.1) (lt_of_blt hA.2)
    (lt_of_blt hB.1) (lt_of_blt hB.2) (Nat.eq_of_beq_eq_true hab2.1)
    (Nat.eq_of_beq_eq_true hab2.2) mA_eq mB_eq hcard'
  exact h.trans (by decide)

end CertificateChecks.KernelVec.RuBound

end
