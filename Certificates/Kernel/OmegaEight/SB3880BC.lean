module

public import Certificates.Kernel.OmegaEight.SB3880VA
public import Certificates.Kernel.OmegaEight.SB3880VB

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8.SB3880

open CFSG.KC.Enum CFSG.KC.SB CFSG.EvenSmallLie.OmegaEight.SpBranch CertificateChecks.KernelO8.SB3871
  CertificateChecks.KernelO8.SB3872

theorem hvS : sVecOK vSArr = true :=
  sVecOK_of fun s hs => if h4 : s < 4 then vBlockA s h4 else vBlockB s (by omega) hs

theorem length_filter_contains {L : List ℕ} {N : ℕ} (hnd : L.Nodup) (hlt : ∀ c ∈ L, c < N) :
    ((List.range N).filter fun c => L.contains c).length = L.length := by
  have h1 : ((List.range N).filter fun c => L.contains c).Nodup := (List.nodup_range).filter _
  refine le_antisymm (h1.length_le_of_subset fun c hc => ?_)
    (hnd.length_le_of_subset fun c hc => ?_)
  · have := (List.mem_filter.1 hc).2
    simpa using this
  · exact List.mem_filter.2 ⟨List.mem_range.2 (hlt c hc), by simpa using hc⟩

theorem fpLit_nodup : fpLit.Nodup := by decide +kernel

theorem basic : s2BasicCheck = true := by
  unfold s2BasicCheck fpCount
  have hfp : ((List.range 65536).filter fun c => fpArr[c]!) =
      (List.range 65536).filter fun c => fpLit.contains c := by
    apply List.filter_congr
    intro c hc
    rw [fpArr_get, fpList_eq, decide_eq_true (List.mem_range.1 hc), Bool.true_and]
  rw [hfp, length_filter_contains fpLit_nodup (by decide +kernel), sMul_eqK, kInv_eq, kOrd4_eq]
  decide +kernel

end CertificateChecks.KernelO8.SB3880

end
