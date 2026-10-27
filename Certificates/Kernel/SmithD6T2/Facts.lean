module

public import Certificates.Kernel.SmithD6T2.Checks
public import CFSG.Certificates.Kernel.SmithD6T2Sound

public section

namespace CertificateChecks.SmithD6T2

open CFSG.SmithD6 CFSG.KC.SmithD6T2 CFSG.KD.SmithD6T2

theorem split_codes {p w : Nat} (hp : p < 4096) (hp0 : p ≠ 0) (hpq : qf p = false)
    (hw : w < 4096) (hpw : bf p w = false) (hwq : qf w = true) :
    ∃ s < 4096, s ≠ 0 ∧ qf s = false ∧ bf p s = false ∧ bf w s = true :=
  d6_split ptTree_ok split_ok hp hp0 hpq hw hpw hwq

theorem pair_reach_codes {a b : Nat} (ha : a < 4096) (hb : b < 4096) (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (hab : a ≠ b) (haq : qf a = false) (hbq : qf b = false) (habf : bf a b = false) :
    Relation.ReflTransGen d6PairStep (a, b) (1, 2) :=
  d6_pair_reach ptTree_ok rsTree_ok ha hb ha0 hb0 hab haq hbq habf

theorem pt_count_codes :
    ((Finset.range 4096).filter fun x => x ≠ 0 ∧ qf x = false).card = 2079 :=
  d6_pt_count ptCnt_eq

theorem perp_count_codes {p : Nat} (hp : p < 4096) (hp0 : p ≠ 0) (hpq : qf p = false) :
    ((Finset.range 4096).filter fun x => x ≠ 0 ∧ x ≠ p ∧ qf x = false ∧ bf p x = false).card =
      1054 :=
  d6_perp_count ptTree_ok rsCnt_eq hp hp0 hpq

end CertificateChecks.SmithD6T2

end
