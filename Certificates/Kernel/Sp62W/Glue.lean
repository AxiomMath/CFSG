module

public import Certificates.Kernel.Sp62W.ChecksWD
public import Certificates.Kernel.Sp62W.ChecksWD2
public import Certificates.Kernel.Sp62W.ChecksWL
public import Certificates.Kernel.Sp62W.ChecksWL2
public import Certificates.Kernel.Sp62W.ChecksV
public import Certificates.Kernel.Sp62L.Glue
public import CFSG.Certificates.Kernel.Sp62W.Sound
import CFSG.Certificates.Kernel.Common.ForallChunks
public import CFSG.Assembly.QuasithinDefs
public import CFSG.Quasithin.Recognition.RuTypeDefs

public section

namespace CertificateChecks.KernelSp62W

open CFSG.AGLEmbedding.KFactProofs.Sp62Local CFSG.Quasithin.G2U CFSG.KGroups.Sp6 CFSG.KC.Sp62W
  CFSG.KD.Sp62W CFSG.KC.Sp62L CertificateChecks.KernelSp62L

#kc_forall_chunks ch9441wd_s (fun j => stepSl WD 16 51840 7 j = true) 89
  CertificateChecks.KernelSp62W.ch9441wdS 1

#kc_forall_chunks ch9441wl_s (fun j => stepSl WL 14 51840 7 j = true) 89
  CertificateChecks.KernelSp62W.ch9441wlS 1

theorem contains_one (x : List ℕ) : [oneC].contains x = (x == oneC) := by
  apply Bool.eq_iff_iff.2
  rw [List.contains_iff_mem, beq_iff_eq, List.mem_singleton]

theorem chkWD_ok : chkWD = true := by
  obtain ⟨hsz, hcl, hdi, hrec⟩ := table_ok (R := WD) (gens := gensWD) (o := 16) (k := 7)
    (Sb := 13) (Ss := 89) (St := 13) rfl (by norm_num) (by norm_num) (by decide +kernel)
    ch9441wd_g ch9441wd_h (by norm_num) ch9441wd_b (by norm_num) ch9441wd_s (by norm_num) ch9441wd_t
  refine tabCheck_of_table hsz hcl hdi (fun t ht => (hrec t ht).1) (by decide +kernel) ?_
  have hm := mems_of hsz hrec (by decide +kernel) ch9441wd_m
  have hc := cen_of hsz hrec (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by norm_num) ch9441wd_c
  rw [List.all_append, Bool.and_eq_true] at hm
  unfold propWD propWD1 propWD2 propWD3 propWD4
  rw [hm.1, hm.2, Bool.true_and, Bool.true_and, (of_replayB ch9440rt_).1, Bool.and_eq_true]
  constructor
  · refine allCheck_mono hc fun x hx => ?_
    rw [Bool.and_eq_true, contains_one] at hx
    exact hx.1
  · refine allCheck_mono hc fun x hx => ?_
    rw [Bool.and_eq_true] at hx
    have h2 := hx.2
    rw [Bool.or_eq_true] at h2 ⊢
    rcases h2 with h | h
    · exact Or.inl h
    · right
      rw [List.contains_iff_mem] at h
      have hZ : [oneC, cZ, cZ2].all (inTab SD.ET.toArray) = true := by decide +kernel
      exact List.all_eq_true.1 hZ x h

theorem chkWL_ok : chkWL = true := by
  obtain ⟨hsz, hcl, hdi, hrec⟩ := table_ok (R := WL) (gens := gensWL) (o := 14) (k := 7)
    (Sb := 13) (Ss := 89) (St := 13) rfl (by norm_num) (by norm_num) (by decide +kernel)
    ch9441wl_g ch9441wl_h (by norm_num) ch9441wl_b (by norm_num) ch9441wl_s (by norm_num) ch9441wl_t
  exact tabCheck_of_table hsz hcl hdi (fun t ht => (hrec t ht).1) (by decide +kernel)
    (mems_of hsz hrec (by decide +kernel) ch9441wl_m)

theorem chkV_ok : chkV = true := by
  obtain ⟨hsz, hcl, hdi, hrec⟩ := table_ok (R := VR) (gens := gensV) (o := 20) (k := 2)
    (Sb := 7) (Ss := 13) (St := 7) rfl (by norm_num) (by norm_num) (by decide +kernel)
    ch9441v_g ch9441v_h (by norm_num) ch9441v_b (by norm_num) ch9441v_s (by norm_num) ch9441v_t
  refine tabCheck_of_table hsz hcl hdi (fun t ht => (hrec t ht).1) (by decide +kernel) ?_
  have hm := mems_of hsz hrec (by decide +kernel) ch9441v_m
  rw [List.all_append, Bool.and_eq_true] at hm
  unfold propV propV1 propV2
  rw [hm.1, Bool.true_and, List.all_eq_true]
  intro g hg
  rw [Bool.and_eq_true, List.all_eq_true]
  refine ⟨List.all_eq_true.1 (by decide +kernel : gensWD.all genB = true) g hg, fun x hx => ?_⟩
  exact List.all_eq_true.1 hm.2 _ (List.mem_flatMap.2 ⟨g, hg, List.mem_map.2 ⟨x, hx, rfl⟩⟩)

end CertificateChecks.KernelSp62W

end
