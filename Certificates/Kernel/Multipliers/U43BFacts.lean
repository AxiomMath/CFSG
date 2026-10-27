module

public import Certificates.Kernel.Multipliers.U43BChain
public import Certificates.Kernel.Multipliers.U43BAct
public import Certificates.Kernel.Multipliers.BindListSound
public import CFSG.Certificates.Kernel.Spor.RawSound
public import CFSG.Certificates.Kernel.LocalCompUnpack
public import CFSG.Certificates.Kernel.Misc.Coset.PG
public import Certificates.Kernel.Misc.Coset.XU43R
public import CFSG.LieType.Multipliers.U43BridgeInputs
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.LieType.Multipliers.U43Data

public section

namespace CertificateChecks.KernelU43B

open CFSG.CosetTable CFSG.KC.MiscCoset CFSG.LieType.Multipliers.U43 CFSG.KC.Enum CFSG.KS CFSG.KS.Raw
  CFSG.KC.BindList CFSG.Certificates CFSG.Certificates.Native

set_option maxRecDepth 400000

theorem perm : allN 7 (fun j => permOK 820 10 (mask 10) (820 * 10) (C.S j) (C.SI j)) = true := by
  quickRfl

theorem bind2 : bindListK 10 (mask 10) (C.S 2) chainS2.toList 0 = true := by quickRfl
theorem bind3 : bindListK 10 (mask 10) (C.S 3) chainS3.toList 0 = true := by quickRfl
theorem bind4 : bindListK 10 (mask 10) (C.S 4) chainS4.toList 0 = true := by quickRfl
theorem bind5 : bindListK 10 (mask 10) (C.S 5) chainS5.toList 0 = true := by quickRfl
theorem bind6 : bindListK 10 (mask 10) (C.S 6) chainS6.toList 0 = true := by quickRfl

theorem unpack_of_bind {P : ℕ} {t : Array ℕ} (ht : t.toList.length = 820)
    (hb : bindListK 10 (mask 10) P t.toList 0 = true) : t = unpack 820 10 P := by
  have := toArray_eq_unpack ht hb
  rwa [Array.toArray_toList] at this

theorem binds : Binds 820 10 C.S 7 3 C.BP chainS base := by
  have hb : base.size = 3 ∧ ∀ t < 3, base[t]! = pg 10 (mask 10) C.BP t := by decide +kernel
  refine ⟨by norm_num, by norm_num, by norm_num, by decide, fun j hj => ?_, hb.1, hb.2⟩
  interval_cases j
  exacts [unpack_of_bind (by decide) bindA, unpack_of_bind (by decide) bindB,
    unpack_of_bind (by decide) bind2, unpack_of_bind (by decide) bind3,
    unpack_of_bind (by decide) bind4, unpack_of_bind (by decide) bind5,
    unpack_of_bind (by decide) bind6]

theorem base_eq : (chainBase.map Fin.val).toArray = base := by decide

theorem words_eq : chainW = CFSG.Sporadic.Schreier.Co3.Native.wordsArr 2 7 der := by decide

theorem chain_check : rawChainOK 820 (chainS.extract 0 2) chainS (chainBase.map Fin.val).toArray
    chainW 4 = true := by
  rw [base_eq, words_eq]
  exact rawChainK_sound (NS := 13) (CH := 64) binds C.head C.hl (by norm_num) C.hs

theorem chain_orbits : (rawOrbitSizes 820 chainS (chainBase.map Fin.val).toArray).prod = 3265920 := by
  rw [base_eq, rawOrbitSizesK_sound binds perm C.hl]
  decide +kernel

theorem t : rels.map encW = CFSG.KBRoute.XU43R.rels := by decide +kernel
theorem w : CFSG.KBRoute.XU43R.T1.words = [encW [((1 : Fin 2), true)]] := by decide +kernel
theorem hp : (List.replicate 6 [((1 : Fin 2), true)]).flatten ∈ rels := by decide +kernel

theorem card_le : Finite (PG 2 rels) ∧ Nat.card (PG 2 rels) ≤ 3265920 := by
  have h := CertificateChecks.KernelMiscCoset.XU43R.t1
  unfold CFSG.KBRoute.XU43R.T1.ok at h
  have hi := zpowers_index_le_of_tableOk rels t h (by norm_num) CFSG.KBRoute.XU43R.top _ w
  exact card_le_of_zpowers_index rels _ (by norm_num) hp hi

end CertificateChecks.KernelU43B

end
