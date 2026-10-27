module

public import CFSG.Certificates.Kernel.Spor.RawSound
public import CFSG.Certificates.Kernel.Misc.HexFlatSound
public import CFSG.Certificates.Kernel.MonsterB.Co2PermSound
public import Certificates.Data.CFSGNative.MonsterB.Co2Data
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Data
public meta import Certificates.Kernel.Sporadic.RawGen
import Certificates.Kernel.Misc.Perm.HexCmd
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.EachUnfold
import CFSG.Certificates.Kernel.Common.ForallChunks
public import Mathlib.GroupTheory.Perm.Basic
public import Std.Data.HashMap

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelMonB.Co2P CFSG.Monster.B.Co2.Native.permutationsHex
#kmisc_hexflat CertificateChecks.KernelMonB.Co2P CFSG.Monster.B.Co2.Native.permutationsHex 3 2300 12 24
#ks_chars CertificateChecks.KernelMonB.Co2Q CFSG.Monster.B.Co2.Native.pairPermsHex
#kmisc_hexflat CertificateChecks.KernelMonB.Co2Q CFSG.Monster.B.Co2.Native.pairPermsHex 3 2300 12 2

public section

namespace CertificateChecks.KernelMonB

open CFSG.KS.Raw CFSG.KC.Enum CFSG.KC.Co2Mem CFSG.Monster.B.Co2

theorem unpack_getElem! {n w X k : Nat} (hk : k < n) :
    (unpack n w X)[k]! = pg w (CFSG.KS.mask w) X k := by
  rw [unpack, getElem!_pos _ _ (by simpa using hk), Array.getElem_ofFn]

theorem permutations_getElem! {i : Nat} (hi : i < 24) :
    (Native.permutations ())[i]! = unpack 2300 12 (Co2P.F i) := by
  rw [Native.permutations, getElem!_pos _ _ (by simpa using hi), Array.getElem_ofFn]
  change Native.hexTable 3 2300 (2300 * i) Native.permutationsHex = _
  rw [Co2P.eq]
  exact CFSG.KC.Misc.HexFlat.hexTable_sound Co2P.all i hi

theorem pairPerms_getElem! {i : Nat} (hi : i < 2) :
    (Native.pairPerms ())[i]! = unpack 2300 12 (Co2Q.F i) := by
  rw [Native.pairPerms, getElem!_pos _ _ (by simpa using hi), Array.getElem_ofFn]
  change Native.hexTable 3 2300 (2300 * i) Native.pairPermsHex = _
  rw [Co2Q.eq]
  exact CFSG.KC.Misc.HexFlat.hexTable_sound Co2Q.all i hi

@[expose] noncomputable def kPF (i : Nat) : Bool := permK 2300 12 (Co2P.F i)

#kc_each_unfold kPF 0 24 as CertificateChecks.KernelMonB.kP

#kc_forall_chunks kPermK (fun i => permK 2300 12 (Co2P.F i) = true) 24 CertificateChecks.KernelMonB.kP 1

theorem kPerm : ∀ i < 24, permK 2300 12 (Co2P.F i) = true := kPermK

theorem kPair : CFSG.KLie.CT.allN 2 (fun i => permK 2300 12 (Co2Q.F i)) = true := by quickRfl

theorem unpack_perm {X : Nat} (h : permK 2300 12 X = true) :
    (∀ k < 2300, (unpack 2300 12 X)[k]! < 2300) ∧
      ∀ a b, a < 2300 → b < 2300 → (unpack 2300 12 X)[a]! = (unpack 2300 12 X)[b]! → a = b := by
  obtain ⟨h1, h2⟩ := permK_sound h
  refine ⟨fun k hk => ?_, fun a b ha hb e => ?_⟩
  · rw [unpack_getElem! hk]
    exact h1 k hk
  · rw [unpack_getElem! ha, unpack_getElem! hb] at e
    exact h2 a b ha hb e

theorem permutations_perm {i : Nat} (hi : i < 24) :
    (∀ k < 2300, ((Native.permutations ())[i]!)[k]! < 2300) ∧
      ∀ a b, a < 2300 → b < 2300 →
        ((Native.permutations ())[i]!)[a]! = ((Native.permutations ())[i]!)[b]! → a = b := by
  rw [permutations_getElem! hi]
  exact unpack_perm (kPerm i hi)

theorem pairPerms_perm {i : Nat} (hi : i < 2) :
    (∀ k < 2300, ((Native.pairPerms ())[i]!)[k]! < 2300) ∧
      ∀ a b, a < 2300 → b < 2300 →
        ((Native.pairPerms ())[i]!)[a]! = ((Native.pairPerms ())[i]!)[b]! → a = b := by
  rw [pairPerms_getElem! hi]
  exact unpack_perm ((CFSG.KC.U6Orb.allN_iff _ _).1 kPair i hi)

end CertificateChecks.KernelMonB

end
