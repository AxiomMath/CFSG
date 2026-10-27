module

public import Certificates.Kernel.VecCert.SlpChain
public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Data.CFSGNative.Co3.Data
public import CFSG.Certificates.Kernel.Orders.Co3.RelsBind
public import CFSG.Certificates.Kernel.Bounds.Co3Alt.Binding
public import CFSG.Certificates.Kernel.Orders.Co3.GensBind
public import CFSG.Certificates.Kernel.Orders.Co3.Checks.R
public import CFSG.Certificates.Kernel.Orders.Co3.Checks.H
public import CFSG.Certificates.Kernel.Orders.Co3.Checks.D
public import CFSG.Certificates.Kernel.Orders.Co3.Checks.K
public import CFSG.Certificates.Kernel.Orders.Co3.Data.Pay
public import CFSG.Sporadic.Presentation.Co3
import all CFSG.Blueprint.NativeSporadic
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
public import CFSG.Perm.ChainSpec
public import CFSG.Sporadic.Presentation.Common
public import CFSG.Sporadic.Th.F2Spec

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelVec.Co3SeedA CFSG.Sporadic.Co3.Native.seedA

#ks_chars CertificateChecks.KernelVec.Co3SeedB CFSG.Sporadic.Co3.Native.seedB

namespace CertificateChecks.KernelVec.Co3Bound

open CFSG.KC.Ord CFSG.KS.Ord CFSG.Sporadic.SmallF2 CFSG.KD.OrdCo3

local notation "Dt" => CFSG.Sporadic.Co3.Native.co3Data

theorem seed1_bytes : CFSG.KS.Bytes.bytesEqK Co3SeedA.chars P1 256 527 = true := by quickRfl

theorem seed2_bytes : CFSG.KS.Bytes.bytesEqK Co3SeedB.chars P2 256 527 = true := by quickRfl

theorem mA_eq : mA Dt = ordMat 2 22 6 132 (RW 1) := by
  have h := seed_sound (hnb := rfl) consts seed1_bytes (by decide) d1_0 d1_end
  change CFSG.Blueprint.NativeSporadic.decode 2 22 1 CFSG.Sporadic.Co3.Native.seedA = _
  rw [Co3SeedA.eq, h]

theorem mB_eq : mB Dt = ordMat 2 22 6 132 (RW 2) := by
  have h := seed_sound (hnb := rfl) consts seed2_bytes (by decide) d2_0 d2_end
  change CFSG.Blueprint.NativeSporadic.decode 2 22 1 CFSG.Sporadic.Co3.Native.seedB = _
  rw [Co3SeedB.eq, h]

theorem regs : RegsIn 22 6 132 2904 L H 7 RH 116 := by
  have h0 : RegsIn 22 6 132 2904 L H 7 RH 8 := regsIn_roots hroots
  exact slpSeg_chain SWs hsSt consts rfl 3 SG.all h0

theorem hr : ∀ r < lenRels rels, relOK RH (mulR 2 6 132 22 4 L H CM RM) rels 7 ONE r = true ∨
    ∃ s < r, relDupOK rels s r = true := by
  intro r hr
  have hn : lenRels rels = 24 := Nat.eq_of_beq_eq_true relN
  rw [hn] at hr
  exact Or.inl (R.all r hr)

theorem card_J_le :
    Nat.card (J Dt) ≤ (CFSG.Sporadic.Co3.Native.co3Data ()).orbSizes.prod := by
  obtain ⟨hfin, hcard⟩ := CFSG.Sporadic.Presentation.Co3.finite_card_le
  have hfin' : Finite TauCeti.Sporadic.co3Presentation.Group := hfin
  have hcard' : Nat.card TauCeti.Sporadic.co3Presentation.Group ≤ 495766656000 := hcard
  have hab := (andB_iff _ _).1 hAB
  have hab1 := (andB_iff _ _).1 hab.1
  have hab2 := (andB_iff _ _).1 hab.2
  have hA := (andB_iff _ _).1 hab1.1
  have hB := (andB_iff _ _).1 hab1.2
  have hre : TauCeti.Sporadic.co3Presentation.relatorLetters = rels := by
    rw [CFSG.KBRoute.Co3Alt.rels_eq, rels_eq]
  have h := card_J_le_of_hom Dt TauCeti.Sporadic.co3Presentation (hnb := rfl) consts hre gens_eq
    hroots hinv relB hr regs (lt_of_blt hA.1) (lt_of_blt hA.2)
    (lt_of_blt hB.1) (lt_of_blt hB.2) (Nat.eq_of_beq_eq_true hab2.1)
    (Nat.eq_of_beq_eq_true hab2.2) mA_eq mB_eq hcard'
  exact h.trans (by decide)

end CertificateChecks.KernelVec.Co3Bound

end
