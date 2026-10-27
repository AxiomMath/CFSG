module

public import Certificates.Kernel.Sporadic.OrdCommon
public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.Sporadic.SmallF2Rels
public import Certificates.Data.CFSGNative.Co2.Data
public import CFSG.Certificates.Kernel.Orders.Co2.RelsBind
public import CFSG.Certificates.Kernel.Orders.Co2.Checks.R
public import CFSG.Certificates.Kernel.Orders.Co2.Checks.H
public import CFSG.Certificates.Kernel.Orders.Co2.Checks.D
public import CFSG.Certificates.Kernel.Orders.Co2.Checks.K
public import CFSG.Certificates.Kernel.Orders.Co2.Data.Pay
public import CFSG.Certificates.Kernel.Orders.Co2.Data.Sel
import all CFSG.Blueprint.NativeSporadic
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Spor.OrdSound
public import CFSG.Perm.ChainSpec
public import CFSG.Sporadic.Th.F2Spec

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelSpor.Co2SeedA CFSG.Sporadic.Co2.Native.seedA

#ks_chars CertificateChecks.KernelSpor.Co2SeedB CFSG.Sporadic.Co2.Native.seedB

namespace CertificateChecks.KernelSpor.Co2Rels

open CFSG.KC.Ord CFSG.KS.Ord CFSG.Sporadic.SmallF2

local notation "Dt" => CFSG.Sporadic.Co2.Native.co2Data

local notation "Mt" =>
  Matrix (Fin CFSG.Sporadic.Co2.Native.co2Data.d) (Fin CFSG.Sporadic.Co2.Native.co2Data.d) (ZMod 2)

theorem seed1_bytes :
    CFSG.KS.Bytes.bytesEqK Co2SeedA.chars CFSG.KD.OrdCo2.P1 256 527 = true := by
  quickRfl

theorem seed2_bytes :
    CFSG.KS.Bytes.bytesEqK Co2SeedB.chars CFSG.KD.OrdCo2.P2 256 527 = true := by
  quickRfl

noncomputable abbrev X (g : Nat) : Mt := ordMat 2 22 6 132 (CFSG.KD.OrdCo2.RH g)

noncomputable abbrev Y (M : Nat) : Mt := ordMat 2 22 6 132 M

theorem hAB' : CFSG.KD.OrdCo2.RH 1 = CFSG.KD.OrdCo2.RW 1 ∧
    CFSG.KD.OrdCo2.RH 2 = CFSG.KD.OrdCo2.RW 2 := by
  have h := (andB_iff _ _).1 CFSG.KD.OrdCo2.hAB
  have h2 := (andB_iff _ _).1 h.2
  exact ⟨Nat.eq_of_beq_eq_true h2.1, Nat.eq_of_beq_eq_true h2.2⟩

theorem mA_eq : mA Dt = X 1 := by
  have h := seed_sound (hnb := rfl) CFSG.KD.OrdCo2.consts seed1_bytes (by decide)
    CFSG.KD.OrdCo2.d1_0 CFSG.KD.OrdCo2.d1_end
  change CFSG.Blueprint.NativeSporadic.decode 2 22 1 CFSG.Sporadic.Co2.Native.seedA = _
  rw [Co2SeedA.eq, h, ← hAB'.1]

theorem mB_eq : mB Dt = X 2 := by
  have h := seed_sound (hnb := rfl) CFSG.KD.OrdCo2.consts seed2_bytes (by decide)
    CFSG.KD.OrdCo2.d2_0 CFSG.KD.OrdCo2.d2_end
  change CFSG.Blueprint.NativeSporadic.decode 2 22 1 CFSG.Sporadic.Co2.Native.seedB = _
  rw [Co2SeedB.eq, h, ← hAB'.2]

theorem hom : (∀ g < 2, X (g + 1) * X (2 + 1 + g) = 1) ∧
    ∀ v ∈ CFSG.KD.OrdCo2.rels, (v.map fun x => Y (letM CFSG.KD.OrdCo2.RH 2 x)).prod = 1 := by
  refine rels_sound (hnb := rfl) CFSG.KD.OrdCo2.consts CFSG.KD.OrdCo2.hroots CFSG.KD.OrdCo2.hinv
    CFSG.KD.OrdCo2.relB fun r hr => ?_
  have hn : lenRels CFSG.KD.OrdCo2.rels = 10 := Nat.eq_of_beq_eq_true CFSG.KD.OrdCo2.relN
  rw [hn] at hr
  exact Or.inl (CFSG.KD.OrdCo2.R.all r hr)

theorem hL : ∀ g s, g < 2 →
    Y (letM CFSG.KD.OrdCo2.RH 2 (g, s)) = Bool.rec (X (2 + 1 + g)) (X (g + 1)) s := by
  intro g s _
  cases s <;> rfl

theorem relators : ∀ v ∈ TauCeti.Sporadic.co2Presentation.relatorLetters,
    CFSG.Sporadic.Bridge.wordProd (CFSG.Sporadic.Bridge.TwoGen.img2 (a Dt) (b Dt)) v = 1 := by
  rw [CFSG.KD.OrdCo2.rels_eq]
  exact SmallF2Rels.relators_of Dt _ X Y (letM CFSG.KD.OrdCo2.RH 2) mA_eq mB_eq
    (hom.1 0 (by norm_num)) (hom.1 1 (by norm_num)) hL (relsBounded_spec CFSG.KD.OrdCo2.relB) hom.2

end CertificateChecks.KernelSpor.Co2Rels

end
