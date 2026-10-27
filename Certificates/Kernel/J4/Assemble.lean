module

public import Certificates.Kernel.J4.ChecksK
public import Certificates.Kernel.J4.ChecksKW
public import Certificates.Kernel.J4.ChecksFL
public import Certificates.Kernel.J4.ChecksMW0
public import Certificates.Kernel.J4.ChecksMW1
public import Certificates.Kernel.J4.ChecksMW2
public import Certificates.Kernel.J4.ChecksMW3
public import Certificates.Kernel.J4.ChecksMW4
import Certificates.Kernel.LceSTab.Assemble

public section

#loop_join CertificateChecks.KernelBounds.J4.kwAll CFSG.KJ4.R.runK_append CertificateChecks.KernelBounds.J4.kw 0 12
#loop_join CertificateChecks.KernelBounds.J4.mwAll CFSG.KJ4.R.runM_append CertificateChecks.KernelBounds.J4.mw 0 50
#loop_join CertificateChecks.KernelBounds.J4.mtAll CFSG.KJ4.R.runT_append CertificateChecks.KernelBounds.J4.mt 0 9
#loop_join CertificateChecks.KernelBounds.J4.fl1All CFSG.KJ4.R.runF_append CertificateChecks.KernelBounds.J4.fl1_ 0 7
#loop_join CertificateChecks.KernelBounds.J4.fl2All CFSG.KJ4.R.runF_append CertificateChecks.KernelBounds.J4.fl2_ 0 7
#loop_join CertificateChecks.KernelBounds.J4.fl3All CFSG.KJ4.R.runF_append CertificateChecks.KernelBounds.J4.fl3_ 0 7
#loop_join CertificateChecks.KernelBounds.J4.fl4All CFSG.KJ4.R.runF_append CertificateChecks.KernelBounds.J4.fl4_ 0 7
#loop_join CertificateChecks.KernelBounds.J4.fl5All CFSG.KJ4.R.runF_append CertificateChecks.KernelBounds.J4.fl5_ 0 7
#loop_join CertificateChecks.KernelBounds.J4.fl6All CFSG.KJ4.R.runF_append CertificateChecks.KernelBounds.J4.fl6_ 0 7

namespace CertificateChecks.KernelBounds.J4

open CFSG.KJ4.R CFSG.KJ4.RUN CFSG.KJ4.S

set_option maxRecDepth 100000

theorem kwOk : Nat.beq (runK kd
    (List.append (List.append (List.append KW0 (List.append KW1 KW2)) (List.append KW3 (List.append KW4 KW5))) (List.append (List.append KW6 (List.append KW7 KW8)) (List.append KW9 (List.append KW10 KW11))))
    (mkC (nat_lit 0) (nat_lit 1))) (mkC kd.NF kd.ND) = true := kwAll

theorem mwOk : Nat.beq (runM md kd
    (List.append (List.append (List.append (List.append (List.append MW0 (List.append MW1 MW2)) (List.append MW3 (List.append MW4 MW5))) (List.append (List.append MW6 (List.append MW7 MW8)) (List.append MW9 (List.append MW10 MW11)))) (List.append (List.append (List.append MW12 (List.append MW13 MW14)) (List.append MW15 (List.append MW16 MW17))) (List.append (List.append MW18 (List.append MW19 MW20)) (List.append (List.append MW21 MW22) (List.append MW23 MW24))))) (List.append (List.append (List.append (List.append MW25 (List.append MW26 MW27)) (List.append MW28 (List.append MW29 MW30))) (List.append (List.append MW31 (List.append MW32 MW33)) (List.append MW34 (List.append MW35 MW36)))) (List.append (List.append (List.append MW37 (List.append MW38 MW39)) (List.append MW40 (List.append MW41 MW42))) (List.append (List.append MW43 (List.append MW44 MW45)) (List.append (List.append MW46 MW47) (List.append MW48 MW49))))))
    (mkC (nat_lit 0) (nat_lit 1))) (mkC md.NF md.ND) = true := mwAll

theorem mtOk : Nat.beq (runT md kd
    (List.append (List.append (List.append MT0 MT1) (List.append MT2 MT3)) (List.append (List.append MT4 MT5) (List.append MT6 (List.append MT7 MT8))))
    (nat_lit 0)) (nat_lit 89) = true := mtAll

theorem fl1Ok : Nat.beq (runF kd (nat_lit 1)
    (List.append (List.append FL1_0 (List.append FL1_1 FL1_2)) (List.append (List.append FL1_3 FL1_4) (List.append FL1_5 FL1_6))) (nat_lit 0)) (fullOf kd) = true := fl1All

theorem fl2Ok : Nat.beq (runF kd (Nat.succ (nat_lit 1))
    (List.append (List.append FL2_0 (List.append FL2_1 FL2_2)) (List.append (List.append FL2_3 FL2_4) (List.append FL2_5 FL2_6))) (nat_lit 0)) (fullOf kd) = true := fl2All

theorem fl3Ok : Nat.beq (runF kd (Nat.succ (Nat.succ (nat_lit 1)))
    (List.append (List.append FL3_0 (List.append FL3_1 FL3_2)) (List.append (List.append FL3_3 FL3_4) (List.append FL3_5 FL3_6))) (nat_lit 0)) (fullOf kd) = true := fl3All

theorem fl4Ok : Nat.beq (runF kd (Nat.succ (Nat.succ (Nat.succ (nat_lit 1))))
    (List.append (List.append FL4_0 (List.append FL4_1 FL4_2)) (List.append (List.append FL4_3 FL4_4) (List.append FL4_5 FL4_6))) (nat_lit 0)) (fullOf kd) = true := fl4All

theorem fl5Ok : Nat.beq (runF kd (Nat.succ (Nat.succ (Nat.succ (Nat.succ (nat_lit 1)))))
    (List.append (List.append FL5_0 (List.append FL5_1 FL5_2)) (List.append (List.append FL5_3 FL5_4) (List.append FL5_5 FL5_6))) (nat_lit 0)) (fullOf kd) = true := fl5All

theorem fl6Ok : Nat.beq (runF kd (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (nat_lit 1))))))
    (List.append (List.append FL6_0 (List.append FL6_1 FL6_2)) (List.append (List.append FL6_3 FL6_4) (List.append FL6_5 FL6_6))) (nat_lit 0)) (fullOf kd) = true := fl6All

theorem forests : forAll kd
    [(List.append (List.append FL1_0 (List.append FL1_1 FL1_2)) (List.append (List.append FL1_3 FL1_4) (List.append FL1_5 FL1_6))), (List.append (List.append FL2_0 (List.append FL2_1 FL2_2)) (List.append (List.append FL2_3 FL2_4) (List.append FL2_5 FL2_6))), (List.append (List.append FL3_0 (List.append FL3_1 FL3_2)) (List.append (List.append FL3_3 FL3_4) (List.append FL3_5 FL3_6))), (List.append (List.append FL4_0 (List.append FL4_1 FL4_2)) (List.append (List.append FL4_3 FL4_4) (List.append FL4_5 FL4_6))), (List.append (List.append FL5_0 (List.append FL5_1 FL5_2)) (List.append (List.append FL5_3 FL5_4) (List.append FL5_5 FL5_6))), (List.append (List.append FL6_0 (List.append FL6_1 FL6_2)) (List.append (List.append FL6_3 FL6_4) (List.append FL6_5 FL6_6)))]
    (nat_lit 1) = true := by
  rw [forAll_cons, forAll_cons, forAll_cons, forAll_cons, forAll_cons, forAll_cons, forAll_nil]
  exact andB_intro fl1All (andB_intro fl2All (andB_intro fl3All (andB_intro fl4All (andB_intro fl5All (andB_intro fl6All (rfl))))))

theorem j4_ok : j4Ok kd md
    (List.append (List.append (List.append KW0 (List.append KW1 KW2)) (List.append KW3 (List.append KW4 KW5))) (List.append (List.append KW6 (List.append KW7 KW8)) (List.append KW9 (List.append KW10 KW11))))
    (List.append (List.append (List.append (List.append (List.append MW0 (List.append MW1 MW2)) (List.append MW3 (List.append MW4 MW5))) (List.append (List.append MW6 (List.append MW7 MW8)) (List.append MW9 (List.append MW10 MW11)))) (List.append (List.append (List.append MW12 (List.append MW13 MW14)) (List.append MW15 (List.append MW16 MW17))) (List.append (List.append MW18 (List.append MW19 MW20)) (List.append (List.append MW21 MW22) (List.append MW23 MW24))))) (List.append (List.append (List.append (List.append MW25 (List.append MW26 MW27)) (List.append MW28 (List.append MW29 MW30))) (List.append (List.append MW31 (List.append MW32 MW33)) (List.append MW34 (List.append MW35 MW36)))) (List.append (List.append (List.append MW37 (List.append MW38 MW39)) (List.append MW40 (List.append MW41 MW42))) (List.append (List.append MW43 (List.append MW44 MW45)) (List.append (List.append MW46 MW47) (List.append MW48 MW49))))))
    (List.append (List.append (List.append MT0 MT1) (List.append MT2 MT3)) (List.append (List.append MT4 MT5) (List.append MT6 (List.append MT7 MT8))))
    [(List.append (List.append FL1_0 (List.append FL1_1 FL1_2)) (List.append (List.append FL1_3 FL1_4) (List.append FL1_5 FL1_6))), (List.append (List.append FL2_0 (List.append FL2_1 FL2_2)) (List.append (List.append FL2_3 FL2_4) (List.append FL2_5 FL2_6))), (List.append (List.append FL3_0 (List.append FL3_1 FL3_2)) (List.append (List.append FL3_3 FL3_4) (List.append FL3_5 FL3_6))), (List.append (List.append FL4_0 (List.append FL4_1 FL4_2)) (List.append (List.append FL4_3 FL4_4) (List.append FL4_5 FL4_6))), (List.append (List.append FL5_0 (List.append FL5_1 FL5_2)) (List.append (List.append FL5_3 FL5_4) (List.append FL5_5 FL5_6))), (List.append (List.append FL6_0 (List.append FL6_1 FL6_2)) (List.append (List.append FL6_3 FL6_4) (List.append FL6_5 FL6_6)))] = true := by
  unfold j4Ok
  exact andB_intro k_setup (andB_intro k_hdr (andB_intro k_pts (andB_intro k_lam (andB_intro kwOk
    (andB_intro (by quickRfl) (andB_intro forests (andB_intro k_chains (andB_intro k_range
    (andB_intro m_setup (andB_intro mwOk mtOk))))))))))

end CertificateChecks.KernelBounds.J4

end
