module

public import Certificates.Kernel.UnitarySix.Sec3.C3604
public import Certificates.Kernel.UnitarySix.Sec3.K3604
public import CFSG.Certificates.Kernel.U6Sec3ChainSound
import CFSG.Certificates.Kernel.RankThree.F2Perm

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelU6.Sec3

open CFSG.KC.U6Sec3 CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Enum CFSG.Monster.B.Co2.Native
open CFSG.EvenSmallLie.UnitarySix.YamadaSec3 CFSG.RankThree.Native CFSG.KC.U6

theorem eNative_k' : eNativeCheck = true := by
  have hk := kENat
  rw [Bool.and_eq_true] at hk
  have hr : (∀ w ∈ CFSG.EvenSmallLie.UnitarySix.tWords, ∀ c ∈ w, c.natAbs - 1 < 46) ∧
      ∀ w ∈ CFSG.EvenSmallLie.UnitarySix.kWords, ∀ c ∈ w, c.natAbs - 1 < 46 := by
    decide +kernel
  unfold eNativeCheck nativeT nativeK
  rw [Bool.and_eq_true, List.all_map, List.all_map]
  refine ⟨List.all_eq_true.2 fun w hw => ?_, List.all_eq_true.2 fun w hw => ?_⟩
  · have h := List.all_eq_true.1 hk.1 w hw
    rw [strictB_eq, Bool.and_eq_true] at h
    obtain ⟨e, hc⟩ := natK_spec w (hr.1 w hw)
    simp only [Function.comp_apply]
    unfold nativeWordA
    rw [e, Bool.and_eq_true, PermK.valid h.1]
    unfold lvS
    rw [chS_K.sift' hc]
    exact ⟨rfl, h.2⟩
  · have h := List.all_eq_true.1 hk.2 w hw
    rw [strictB_eq, Bool.and_eq_true] at h
    obtain ⟨e, hc⟩ := natK_spec w (hr.2 w hw)
    simp only [Function.comp_apply]
    unfold nativeWordA
    rw [e, Bool.and_eq_true, PermK.valid h.1]
    unfold lvK2
    rw [chK2_K.sift' hc]
    exact ⟨rfl, h.2⟩

theorem eTrans_of' (h : ∀ f < 693, eTransK f = true) : eTransCheck = true := by
  unfold eTransCheck
  rw [Bool.and_eq_true]
  refine ⟨by decide +kernel, List.all_eq_true.2 fun f hf => ?_⟩
  have hf' := List.mem_range.1 hf
  have hlen : f < qzWords.length := by
    have : qzWords.length = 693 := by decide +kernel
    omega
  have hq : ∀ k ∈ qzWords[f]!, k < 18 := qz_lt _ (by
    rw [getElem!_pos qzWords f hlen]
    exact List.getElem_mem hlen)
  have hk := h f hf'
  unfold eTransK at hk
  rw [strictB_eq, strictB_eq] at hk
  simp only [Bool.and_eq_true] at hk
  obtain ⟨⟨hp, h0⟩, hz⟩ := hk
  have hQ := (wK_spec hq).2
  have h14 := hc 14 (by norm_num)
  rw [Bool.and_eq_true, Bool.and_eq_true,
    CFSG.RankThree.Native.F2.validA_of_rep (rep_wA tabs_k _ hq), (wK_spec hq).1,
    unpack_get (by norm_num), hG 14 (by norm_num), conjInv_unpack hp h14, lvA1,
    chA1_K.sift' (canon_comp (PermK.canon_inv hp) (canon_comp h14 hQ))]
  refine ⟨⟨rfl, ?_⟩, ?_⟩
  · rw [beq_iff_eq]
    exact Nat.eq_of_beq_eq_true h0
  · rw [Bool.or_eq_true] at hz ⊢
    rcases hz with hz | hz
    · exact Or.inl (by rw [beq_iff_eq]; exact Nat.eq_of_beq_eq_true hz)
    · exact Or.inr hz

theorem eTrans_k' : eTransCheck = true := by
  refine eTrans_of' fun f hf => ?_
  have hs : ∀ s < 21, eTransRun (s * 32) 32 = true := by
    intro s hs
    interval_cases s
    exacts [kET0, kET1, kET2, kET3, kET4, kET5, kET6, kET7, kET8, kET9, kET10, kET11, kET12,
      kET13, kET14, kET15, kET16, kET17, kET18, kET19, kET20]
  rcases Nat.lt_or_ge f 672 with h | h
  · have h1 := hs (f / 32) (by omega)
    unfold eTransRun at h1
    have := allN_spec h1 (f % 32) (Nat.mod_lt f (by norm_num))
    have e : f / 32 * 32 + f % 32 = f := Nat.div_add_mod' f 32
    rwa [e] at this
  · have h1 := kET21
    unfold eTransRun at h1
    have := allN_spec h1 (f - 672) (by omega)
    have e : 672 + (f - 672) = f := by omega
    rwa [e] at this

end CertificateChecks.KernelU6.Sec3
