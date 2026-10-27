module

public import Certificates.Kernel.UnitarySix.Sec3.G3600Chk
public import Certificates.Kernel.UnitarySix.Sec3.G3600Tab
public import Certificates.Kernel.UnitarySix.Sec3.E3600
public import CFSG.Certificates.Kernel.U6Sec3TabSound
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.NativeData

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelU6.Sec3

open CFSG.KC.U6Sec3 CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Enum CFSG.Monster.B.Co2.Native
open CFSG.EvenSmallLie.UnitarySix.YamadaSec3 CFSG.RankThree.Native CFSG.KC.U6
open CFSG.Monster.B.Co2 (allLt_iff)

theorem tabs_k : tabsCheck = true := by
  unfold tabsCheck
  refine List.all_eq_true.2 fun k hk => ?_
  have hk' := List.mem_range.1 hk
  rw [tabC_eq hQ hQI (hCodes k hk') up_eq pos_eq (kTab k hk'), ← hG k hk', beq_self_eq_true,
    Bool.true_and, hG k hk']
  exact PermK.valid (kGP k hk')

theorem valid_w {a : Array ℕ} {w : List ℕ} (e : a = wA w) (hw : ∀ k ∈ w, k < 18)
    (hp : PermK (wK w) (wKI w) = true) : validA 693 a = true := by
  rw [e, (wK_spec hw).1]
  exact PermK.valid hp

theorem O_valid {c : ChainData} {kS nb BP NS : ℕ} {PS PSI LR TR TRI : ℕ → ℕ}
    (h : ChainK c kS nb BP NS PS PSI LR TR TRI)
    (hP : ∀ j < c.gens.length, PermK (PS j) (PSI j) = true) : c.O.all (validA 693) = true := by
  rw [h.O_all]
  exact List.all_eq_true.2 fun j hj => PermK.valid (hP j (List.mem_range.1 hj))

theorem valid_k : validCheck = true := by
  unfold validCheck
  simp only [Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨valid_w (w := wu₁) rfl (by decide) (perm_words _ (by simp)),
    valid_w (w := wu₂) rfl (by decide) (perm_words _ (by simp))⟩,
    valid_w (w := ww₀) rfl (by decide) (perm_words _ (by simp))⟩,
    valid_w (w := wj₀) rfl (by decide) (perm_words _ (by simp))⟩,
    valid_w (w := wab) rfl (by decide) (perm_words _ (by simp))⟩,
    valid_w (w := wba) rfl (by decide) (perm_words _ (by simp))⟩,
    valid_w (w := waba) rfl (by decide) (perm_words _ (by simp))⟩,
    valid_w (w := wbcb) rfl (by decide) (perm_words _ (by simp))⟩, O_valid chK1_K chK1_P⟩,
    O_valid chK2_K chK2_P⟩

theorem fix_k : fixCheck = true := by
  have hk := kFix
  simp only [Bool.and_eq_true] at hk
  unfold fixCheck
  simp only [Bool.and_eq_true]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [chS_K.O_all]
    simp only [unpack_get (by norm_num : 0 < 693)]
    exact hk.1.1
  · refine allLt_iff.2 fun p hp => ?_
    rw [chS_K.O_any]
    simp only [unpack_get hp]
    exact allN_spec hk.1.2 p hp
  · rw [chK1A1_K.O_all]
    simp only [unpack_get (by norm_num : 0 < 693)]
    exact hk.2

theorem sIntFix_k : sIntFix = true := by
  have hk := kSF
  unfold sIntFix
  rw [au₂, au₁, aw₀, (wK_spec (w := wu₂) (by decide)).1, (wK_spec (w := wu₁) (by decide)).1,
    (wK_spec (w := ww₀) (by decide)).1, chT2_K.O_all, chT1_K.O_all, unpack_get (by norm_num),
    unpack_get (by norm_num), unpack_get (by norm_num)]
  simp only [unpack_get (by norm_num : 381 < 693), unpack_get (by norm_num : 1 < 693)]
  exact hk

theorem labT1_k : labT1Check = true := by
  unfold labT1Check
  rw [Bool.and_eq_true]
  refine ⟨by decide, ?_⟩
  rw [chT1_K.O_all]
  refine List.all_eq_true.2 fun j hj => allLt_iff.2 fun p hp => ?_
  have hj' := PermK.canon (chT1_P j (List.mem_range.1 hj))
  rw [unpack_get hp, labT1_eq _ (canon_lt hj' hp), labT1_eq _ hp]
  exact allN_spec (List.all_eq_true.1 kLab j hj) p hp

end CertificateChecks.KernelU6.Sec3
