module

public import Certificates.Kernel.Fi22Core.Conj
public import CFSG.Certificates.Kernel.Spor.F3LaneSepSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi22C

open CFSG.F3.Native CFSG.KS CFSG.KS.F3L CFSG.KS.F3R CFSG.KC.Enum CFSG.Sporadic.Fi22.Native
  CFSG.Sporadic.Th.Native

@[expose] noncomputable def LsS : List V := sepIdx.toList.map KL

@[expose] noncomputable def WL : V := combL 77 SP LI LsS sepTerms

theorem sep_mats : sepIdx.map (fun r => orbL.keys[r]!) = (LsS.map (unlane 77)).toArray := by
  apply Array.ext'
  rw [Array.toList_map, LsS, List.map_map]
  apply List.map_congr_left
  intro r hr
  have hb : ∀ r ∈ sepIdx.toList, r < 3510 := by decide
  exact keys_get r (hb r hr)

theorem LsS_wf : ∀ L ∈ LsS, L.wf = true := by
  intro L hL
  unfold LsS at hL
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hL
  have hb : ∀ r ∈ sepIdx.toList, r < 3510 := by decide
  exact (canon_KL (hb r hr)).wf

set_option Elab.async false

theorem wl_wf : WL.wf = true := by decide +kernel

theorem vec_lt : (sepVec ()).p < 2 ^ 77 ∧ (sepVec ()).m < 2 ^ 77 := by decide

theorem sepK_ok : sepOK 77 (LsS.map (unlane 77)).toArray sepTerms (sepVec ()) (sepK ()) (sepP ())
    (sepTinv ()) sepTree = true := by
  have hd : 0 < 77 := by norm_num
  unfold sepOK
  rw [combM_unlane hd idM_eq LsS sepTerms (by decide), spinVecs_lane hd LsS_wf vec_lt.1 vec_lt.2
    sepTree (by decide)]
  change (_ && (mulVecM 77 (unlane 77 WL) (sepVec ())).isZero && _ && _ && _ && _ && _) = true
  rw [mulVec_unlane hd wl_wf vec_lt.1 vec_lt.2]
  simp only [mul_eq, eqM_eq, wfM_eq, ← Array.all_toList]
  decide +kernel

theorem sep_ok : sepOK 77 (sepIdx.map fun r => orbL.keys[r]!) sepTerms (sepVec ()) (sepK ())
    (sepP ()) (sepTinv ()) sepTree = true := by
  rw [sep_mats]
  exact sepK_ok

theorem product_ok : productChecks orbL = true := by
  have h := prod_ok
  unfold prodK at h
  simp only [bAnd_iff] at h
  obtain ⟨c1, c2, h3, n1, h2, n2⟩ := h
  rw [Bool.not_eq_true', ← Bool.not_eq_true, eqF_iff] at n1 n2
  have k1 := keys_get 1 (by norm_num)
  have k8 := keys_get 8 (by norm_num)
  have e8 : subRoot () = 8 := rfl
  unfold productChecks
  rw [e8, k1, k8, matA_eq, mul_eq', mul_eq']
  dsimp only
  rw [powM_eq', powM_eq', idM_eq]
  change (canonM 77 (unlane 77 P1L) && canonM 77 (unlane 77 P2L) &&
    eqM 77 (unlane 77 (powF P1L 3)) (unlane 77 LI) && !eqM 77 (unlane 77 P1L) (unlane 77 LI) &&
    eqM 77 (unlane 77 (powF P2L 2)) (unlane 77 LI) && !eqM 77 (unlane 77 P2L) (unlane 77 LI)) = true
  have cI := canons.2.2.2.1
  rw [canonM_unlane 77 (canonF_spec c1).wf, canonM_unlane 77 (canonF_spec c2).wf, eqF_iff.1 h3,
    eqF_iff.1 h2, eqM_self (unlane_size' _), ne_of_lane (canonF_spec c1) cI n1,
    ne_of_lane (canonF_spec c2) cI n2]
  rfl

end CertificateChecks.KernelFi22C

end
