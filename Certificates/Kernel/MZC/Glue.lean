module

public import CFSG.Certificates.Kernel.Enum.ZCVKC
public import Certificates.Kernel.MZC.Bind
public import Certificates.Kernel.MZC.R225
public import Certificates.Kernel.MZC.R227
public import Certificates.Kernel.MZC.R235
public import CFSG.Sporadic.Mathieu.M22
public import CFSG.Sporadic.Schreier.M23Base

public section

namespace CertificateChecks.MZCK

open CFSG.KC.Enum CFSG.KC.EnumSound CFSG.KD.MZC CFSG.KS
  CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal

theorem m22_two_part :
    ¬ 2 ^ (7 + 1) ∣ Nat.card ↥(Subgroup.closure ({PermGens.m22a, PermGens.m22b} :
      Set (Equiv.Perm (Fin 22)))) := by
  rw [← PermGens.M22_eq, CFSG.Sporadic.Mathieu.card_M22]
  norm_num

theorem m23_two_part :
    ¬ 2 ^ (7 + 1) ∣ Nat.card ↥(Subgroup.closure ({PermGens.m23a, PermGens.m23b} :
      Set (Equiv.Perm (Fin 23)))) := by
  rw [← PermGens.M23_eq, CFSG.Sporadic.Schreier.m23_card]
  norm_num

theorem zcw_m22_5 :
    ZCW ↥CFSG.Blueprint.NativeSporadic.M22 5 := by
  open CFSG.KD.M225 M225 in
  exact zcw_kcB (n := 22) (w := 5) (by norm_num) (by norm_num) (by norm_num) a225 ai225 b225 bi225
    idn_eq l_all Nat.prime_five z_letters z_word z_pow z_p z_ne zp_lt w_all (nC := 2)
    (P1 := g2 P1) (P1I := g2 P1I) (P2 := g2 P2) (P2I := g2 P2I) (O1 := g1 O1) (O2 := g1 O2)
    (W1 := g1 H1W) (L1 := g1 H1L) (W2 := g1 H2W) (L2 := g1 H2L) c_words c_pow1 c_pow2 c_comm
    (HT := hTo HT HO) (NH := g1 NH) (nR := len2 REPS) (REP := g2 REPS) (NC1 := g3 NC1)
    (NC2 := g3 NC2) (K3 := g1 K3) (K3P := g1 K3P) (KZ := g1 KZ) c_enum c_nh c_nc c_k3 c_kz
    (XC := g1 XC) (XN := g1 XN) c_v c_cov syl_gens s_all (Nat.eq_of_beq_eq_true nS_eq)
    m22_two_part

theorem zcw_m22_7 :
    ZCW ↥CFSG.Blueprint.NativeSporadic.M22 7 := by
  open CFSG.KD.M227 M227 in
  exact zcw_kcB (n := 22) (w := 5) (by norm_num) (by norm_num) (by norm_num) a227 ai227 b227 bi227
    idn_eq l_all (by norm_num) z_letters z_word z_pow z_p z_ne zp_lt w_all (nC := 1)
    (P1 := g2 P1) (P1I := g2 P1I) (P2 := g2 P2) (P2I := g2 P2I) (O1 := g1 O1) (O2 := g1 O2)
    (W1 := g1 H1W) (L1 := g1 H1L) (W2 := g1 H2W) (L2 := g1 H2L) c_words c_pow1 c_pow2 c_comm
    (HT := hTo HT HO) (NH := g1 NH) (nR := len2 REPS) (REP := g2 REPS) (NC1 := g3 NC1)
    (NC2 := g3 NC2) (K3 := g1 K3) (K3P := g1 K3P) (KZ := g1 KZ) c_enum c_nh c_nc c_k3 c_kz
    (XC := g1 XC) (XN := g1 XN) c_v c_cov syl_gens s_all (Nat.eq_of_beq_eq_true nS_eq)
    m22_two_part

theorem zcw_m23_5 :
    ZCW ↥CFSG.Blueprint.NativeSporadic.M23 5 := by
  open CFSG.KD.M235 M235 in
  exact zcw_kcB (n := 23) (w := 5) (by norm_num) (by norm_num) (by norm_num) a235 ai235 b235 bi235
    idn_eq l_all Nat.prime_five z_letters z_word z_pow z_p z_ne zp_lt w_all (nC := 2)
    (P1 := g2 P1) (P1I := g2 P1I) (P2 := g2 P2) (P2I := g2 P2I) (O1 := g1 O1) (O2 := g1 O2)
    (W1 := g1 H1W) (L1 := g1 H1L) (W2 := g1 H2W) (L2 := g1 H2L) c_words c_pow1 c_pow2 c_comm
    (HT := hTo HT HO) (NH := g1 NH) (nR := len2 REPS) (REP := g2 REPS) (NC1 := g3 NC1)
    (NC2 := g3 NC2) (K3 := g1 K3) (K3P := g1 K3P) (KZ := g1 KZ) c_enum c_nh c_nc c_k3 c_kz
    (XC := g1 XC) (XN := g1 XN) c_v c_cov syl_gens s_all (Nat.eq_of_beq_eq_true nS_eq)
    m23_two_part

end CertificateChecks.MZCK

end
