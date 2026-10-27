module

public import Certificates.Kernel.SmithL6K.Pins
public import Certificates.Kernel.SmithL6K.ChecksT
public import CFSG.Certificates.Kernel.SmithL6KTSound

public section

namespace CertificateChecks.KernelSmithL6K

open CFSG.SmithL6 CFSG.SmithL6.K

theorem hC : ∀ k < 1953, fldW 12 tcP k = codeOf (tvPair k) := fun _ hk => fld_tcP hk

theorem hI : ∀ n < 4096, fldW 11 idxP n = tvIdxTab[n]! := fun _ hn => fld_idxP hn

theorem reach_conv : Reach 1953 1953 (· == 0) (fun g u v => tvImg g u == v) :=
  convReach hC hI ftr_ok

theorem reach_stab : Reach 1953 1953 (fun a => a == stabRep (stabCls a))
    (fun g u v => tvImg g 0 == 0 && tvImg g u == v && stabCls u == stabCls v) :=
  stabReach hC hI str_ok reps_ok reps_cls

theorem ptFix_holds : chkPtFix = true := chkPtFix_of_fixK hC hI fix_ok

theorem tvArrInj_holds : chkTvArrInj = true :=
  chkTvArrInj_of (fun _ hk => tvCols_eq hk) (fun _ hk => tvPair_code hk) dec_ok

theorem stabCard_holds : chkStabCard = true := chkStabCard_of hC card_ok

theorem stabComm_holds : chkStabComm = true := chkStabComm_of hC hI comm_ok

end CertificateChecks.KernelSmithL6K
