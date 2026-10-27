module

public import Certificates.Kernel.Sporadic.OrdCommon
public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.Sporadic.SmallF2Rels
public import Certificates.Data.CFSGNative.HS.Data
public import CFSG.Certificates.Kernel.Bounds.HSAlt.RelsTC
public import CFSG.Certificates.Kernel.Orders.HS.RelsBind
public import CFSG.Certificates.Kernel.Orders.HS.Checks.R
public import CFSG.Certificates.Kernel.Orders.HS.Checks.H
public import CFSG.Certificates.Kernel.Orders.HS.Checks.D
public import CFSG.Certificates.Kernel.Orders.HS.Checks.K
public import CFSG.Certificates.Kernel.Orders.HS.Data.Pay
public import CFSG.Certificates.Kernel.Orders.HS.Data.Sel
import all CFSG.Blueprint.NativeSporadic
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Spor.OrdSound
public import CFSG.Perm.ChainSpec
public import CFSG.Sporadic.Th.F2Spec

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelSpor.HSSeedA CFSG.Sporadic.HS.Native.seedA

#ks_chars CertificateChecks.KernelSpor.HSSeedB CFSG.Sporadic.HS.Native.seedB

namespace CertificateChecks.KernelSpor.HSRels

open CFSG.KC.Ord CFSG.KS.Ord CFSG.Sporadic.SmallF2

local notation "Dt" => CFSG.Sporadic.HS.Native.hsData

local notation "Mt" =>
  Matrix (Fin CFSG.Sporadic.HS.Native.hsData.d) (Fin CFSG.Sporadic.HS.Native.hsData.d) (ZMod 2)

theorem seed1_bytes :
    CFSG.KS.Bytes.bytesEqK HSSeedA.chars CFSG.KD.OrdHS.P1 256 441 = true := by
  quickRfl

theorem seed2_bytes :
    CFSG.KS.Bytes.bytesEqK HSSeedB.chars CFSG.KD.OrdHS.P2 256 441 = true := by
  quickRfl

noncomputable abbrev X (g : Nat) : Mt := ordMat 2 20 6 120 (CFSG.KD.OrdHS.RH g)

noncomputable abbrev Y (M : Nat) : Mt := ordMat 2 20 6 120 M

theorem hAB' : CFSG.KD.OrdHS.RH 1 = CFSG.KD.OrdHS.RW 1 ∧
    CFSG.KD.OrdHS.RH 2 = CFSG.KD.OrdHS.RW 2 := by
  have h := (andB_iff _ _).1 CFSG.KD.OrdHS.hAB
  have h2 := (andB_iff _ _).1 h.2
  exact ⟨Nat.eq_of_beq_eq_true h2.1, Nat.eq_of_beq_eq_true h2.2⟩

theorem mA_eq : mA Dt = X 1 := by
  have h := seed_sound (hnb := rfl) CFSG.KD.OrdHS.consts seed1_bytes (by decide)
    CFSG.KD.OrdHS.d1_0 CFSG.KD.OrdHS.d1_end
  change CFSG.Blueprint.NativeSporadic.decode 2 20 1 CFSG.Sporadic.HS.Native.seedA = _
  rw [HSSeedA.eq, h, ← hAB'.1]

theorem mB_eq : mB Dt = X 2 := by
  have h := seed_sound (hnb := rfl) CFSG.KD.OrdHS.consts seed2_bytes (by decide)
    CFSG.KD.OrdHS.d2_0 CFSG.KD.OrdHS.d2_end
  change CFSG.Blueprint.NativeSporadic.decode 2 20 1 CFSG.Sporadic.HS.Native.seedB = _
  rw [HSSeedB.eq, h, ← hAB'.2]

theorem hom : (∀ g < 2, X (g + 1) * X (2 + 1 + g) = 1) ∧
    ∀ v ∈ CFSG.KD.OrdHS.rels, (v.map fun x => Y (letM CFSG.KD.OrdHS.RH 2 x)).prod = 1 := by
  refine rels_sound (hnb := rfl) CFSG.KD.OrdHS.consts CFSG.KD.OrdHS.hroots CFSG.KD.OrdHS.hinv
    CFSG.KD.OrdHS.relB fun r hr => ?_
  have hn : lenRels CFSG.KD.OrdHS.rels = 13 := Nat.eq_of_beq_eq_true CFSG.KD.OrdHS.relN
  rw [hn] at hr
  exact Or.inl (CFSG.KD.OrdHS.R.all r hr)

theorem hL : ∀ g s, g < 2 →
    Y (letM CFSG.KD.OrdHS.RH 2 (g, s)) = Bool.rec (X (2 + 1 + g)) (X (g + 1)) s := by
  intro g s _
  cases s <;> rfl

theorem relators : ∀ v ∈ TauCeti.Sporadic.hsPresentation.relatorLetters,
    CFSG.Sporadic.Bridge.wordProd (CFSG.Sporadic.Bridge.TwoGen.img2 (a Dt) (b Dt)) v = 1 := by
  rw [CFSG.KC.HSK.rels_eq, ← CFSG.KD.OrdHS.rels_eq]
  exact SmallF2Rels.relators_of Dt _ X Y (letM CFSG.KD.OrdHS.RH 2) mA_eq mB_eq
    (hom.1 0 (by norm_num)) (hom.1 1 (by norm_num)) hL (relsBounded_spec CFSG.KD.OrdHS.relB) hom.2

end CertificateChecks.KernelSpor.HSRels

end
