module

public import Certificates.Kernel.LocalComp.B0SuzChecks
public import CFSG.Certificates.Kernel.B0SuzKSound
public import CFSG.Certificates.Kernel.LocalCompPinSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.B0Suz

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.HexaK CFSG.KC.B0SuzK CFSG.KC.BfsPin
open CFSG.ComponentClassification.AS81.SuzB0 CFSG.Sporadic.SuzOddCore CFSG.PSL3Four.Native
open CertificateChecks.KernelSpor CertificateChecks.KernelLC

theorem t_eq : tTab = unpack 1782 11 T := SuzInv.run_eq1 (k := 0) (by norm_num)

theorem c_eq {k : Nat} (hk : k < 10) : cTab k = unpack 1782 11 (C k) := by
  have hic : invInnerGenCounts.getD 1 0 = 10 := rfl
  have his : invInnerStart 1 = 18 := rfl
  unfold cTab
  rw [getElem!_pos (invInnerGenArrs 1) k (by rw [invInnerGenArrs, Array.size_ofFn, hic]; exact hk)]
  simp only [invInnerGenArrs, Array.getElem_ofFn, his]
  exact SuzInv.run_eq1 (by omega)

theorem o_eq : outerTab = unpack 1782 11 OT := by
  have hfc : invFullGenCounts.getD 1 0 = 6 := rfl
  unfold outerTab
  rw [getElem!_pos (invFullGenArrs 1) 3 (by rw [invFullGenArrs, Array.size_ofFn, hfc]; norm_num)]
  simp only [invFullGenArrs, Array.getElem_ofFn]
  exact SuzInv.run_eq1 (by norm_num)

theorem noTS3_true : noTS3 = true := by
  have e : noTS3 = allBelow 64 ts := rfl
  rw [e]
  simp only [allBelow, List.all_eq_true, List.mem_range]
  exact fun a ha => tsAll a ha

theorem mat_true : (CFSG.PSL3Four.Native.enumOK 64 matTabs matEnum && matEnum.tabs.size == 25920) =
    true := by
  obtain ⟨hs, hg⟩ := binds_of_check kBindM
  have h := CFSG.KC.LocalComp.Pin.enumBFS_of_bfsK hs hg SuzB0M.ok (cap := 25920) (by decide)
  have e : matEnum = enumBFS 64 matTabs 25920 := rfl
  rw [e, Bool.and_eq_true, h.2, Array.size_ofFn]
  exact ⟨h.1, rfl⟩

theorem mat_tabs : matEnum.tabs = Array.ofFn (n := SuzB0M.N) fun j => unpack 64 7 (SuzB0M.T j.val) := by
  obtain ⟨hs, hg⟩ := binds_of_check kBindM
  exact (CFSG.KC.LocalComp.Pin.enumBFS_of_bfsK hs hg SuzB0M.ok (cap := 25920) (by decide)).2

theorem b0SuzCheck_true : b0SuzCheck = true := by
  have hin : ∀ i < 6, inM (qArr i) = true := fun i hi => by
    have h := allN_spec kInM i hi
    rw [Bool.and_eq_true] at h
    rw [OddCore.inM_eq (q_eq hi) h.1]
    exact h.2
  rw [b0SuzCheck_eq]
  exact b0SuzK_sound t_eq (fun i hi => q_eq hi) (fun k hk => c_eq hk) hin kBase
    (fun v hv => ruleAll v hv) kDist kConj mat_true noTS3_true

theorem q0SuzCheck_true : q0SuzCheck = true := by
  have k := kOut
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at k
  obtain ⟨⟨⟨hc, hs⟩, hb⟩, hcm⟩ := k
  have hin : inM outerTab = false := by
    rw [OddCore.inM_eq o_eq hc]
    exact hs
  rw [q0SuzCheck_eq]
  exact q0SuzK_sound o_eq t_eq (fun i hi => q_eq hi) hin kBase kQ0 mat_tabs
    (bfsK_canon SuzB0M.ok) (unpack_eq_of_bindArrK hb) hcm

theorem shatTypeCheck_true : shatTypeCheck = true := by
  rw [shatTypeCheck_eq]
  exact shatK_sound t_eq (fun i hi => q_eq hi) (fun k hk => c_eq hk) kBase kConj shatConstOK_true
    kShat

end CertificateChecks.KernelLC.B0Suz

end
