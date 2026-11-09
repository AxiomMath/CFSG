module

public import Certificates.Kernel.Sporadic.McLC.Defs
import CFSG.Certificates.Kernel.Common.Harness
import Certificates.Kernel.Sporadic.ON.Gen
import Certificates.Kernel.Sporadic.McLC.SchSplit

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.McLC

open CFSG.KC.Enum

theorem kOK_ok : kOK = true := by quickRfl
theorem wordOK_ok : allN 3 (fun j => wordOK (Nat.add j 2)) = true := by quickRfl
theorem invL_ok : invL = true := by quickRfl
theorem tree_ok : allN 3 tree = true := by quickRfl
theorem schR_ok : allN 2 (fun i => schR (Nat.succ i)) = true := by quickRfl
theorem term_ok : term = true := by quickRfl
theorem trAll_ok : trAll = true := by quickRfl
theorem repOK_ok : repOK = true := by quickRfl

end CertificateChecks.KernelSpor.McLC

#kon_slices CertificateChecks.KernelSpor.McLC.sch0 0 1

namespace CertificateChecks.KernelSpor.McLC

open CFSG.KC.Enum CFSG.KS.PC

set_option Elab.async false

theorem sch01_q0 : schSlK LJ BJ NL PTSJ POSJ PARJ LABJ CNTJ QB QL (nat_lit 3) (nat_lit 0)
    (nat_lit 48) (nat_lit 12) = true := by
  quickRfl

theorem sch01_q1 : schSlK LJ BJ NL PTSJ POSJ PARJ LABJ CNTJ QB QL (nat_lit 3) (nat_lit 0)
    (nat_lit 60) (nat_lit 12) = true := by
  quickRfl

theorem sch01_q2 : schSlK LJ BJ NL PTSJ POSJ PARJ LABJ CNTJ QB QL (nat_lit 3) (nat_lit 0)
    (nat_lit 72) (nat_lit 12) = true := by
  quickRfl

theorem sch01_q3 : schSlK LJ BJ NL PTSJ POSJ PARJ LABJ CNTJ QB QL (nat_lit 3) (nat_lit 0)
    (nat_lit 84) (nat_lit 12) = true := by
  quickRfl

theorem sch01 : sch0 (nat_lit 1) = true := by
  unfold sch0
  exact schSlK_split _ (nat_lit 24) (nat_lit 24) _ rfl
    (schSlK_split _ (nat_lit 12) (nat_lit 12) _ rfl sch01_q0 sch01_q1)
    (schSlK_split _ (nat_lit 12) (nat_lit 12) _ rfl sch01_q2 sch01_q3)

theorem sch02_q0 : schSlK LJ BJ NL PTSJ POSJ PARJ LABJ CNTJ QB QL (nat_lit 3) (nat_lit 0)
    (nat_lit 96) (nat_lit 12) = true := by
  quickRfl

theorem sch02_q1 : schSlK LJ BJ NL PTSJ POSJ PARJ LABJ CNTJ QB QL (nat_lit 3) (nat_lit 0)
    (nat_lit 108) (nat_lit 12) = true := by
  quickRfl

theorem sch02_q2 : schSlK LJ BJ NL PTSJ POSJ PARJ LABJ CNTJ QB QL (nat_lit 3) (nat_lit 0)
    (nat_lit 120) (nat_lit 12) = true := by
  quickRfl

theorem sch02_q3 : schSlK LJ BJ NL PTSJ POSJ PARJ LABJ CNTJ QB QL (nat_lit 3) (nat_lit 0)
    (nat_lit 132) (nat_lit 12) = true := by
  quickRfl

theorem sch02 : sch0 (nat_lit 2) = true := by
  unfold sch0
  exact schSlK_split _ (nat_lit 24) (nat_lit 24) _ rfl
    (schSlK_split _ (nat_lit 12) (nat_lit 12) _ rfl sch02_q0 sch02_q1)
    (schSlK_split _ (nat_lit 12) (nat_lit 12) _ rfl sch02_q2 sch02_q3)

theorem sch03_q0 : schSlK LJ BJ NL PTSJ POSJ PARJ LABJ CNTJ QB QL (nat_lit 3) (nat_lit 0)
    (nat_lit 144) (nat_lit 12) = true := by
  quickRfl

theorem sch03_q1 : schSlK LJ BJ NL PTSJ POSJ PARJ LABJ CNTJ QB QL (nat_lit 3) (nat_lit 0)
    (nat_lit 156) (nat_lit 12) = true := by
  quickRfl

theorem sch03_q2 : schSlK LJ BJ NL PTSJ POSJ PARJ LABJ CNTJ QB QL (nat_lit 3) (nat_lit 0)
    (nat_lit 168) (nat_lit 12) = true := by
  quickRfl

theorem sch03_q3 : schSlK LJ BJ NL PTSJ POSJ PARJ LABJ CNTJ QB QL (nat_lit 3) (nat_lit 0)
    (nat_lit 180) (nat_lit 12) = true := by
  quickRfl

theorem sch03 : sch0 (nat_lit 3) = true := by
  unfold sch0
  exact schSlK_split _ (nat_lit 24) (nat_lit 24) _ rfl
    (schSlK_split _ (nat_lit 12) (nat_lit 12) _ rfl sch03_q0 sch03_q1)
    (schSlK_split _ (nat_lit 12) (nat_lit 12) _ rfl sch03_q2 sch03_q3)

theorem sch04_q0 : schSlK LJ BJ NL PTSJ POSJ PARJ LABJ CNTJ QB QL (nat_lit 3) (nat_lit 0)
    (nat_lit 192) (nat_lit 12) = true := by
  quickRfl

theorem sch04_q1 : schSlK LJ BJ NL PTSJ POSJ PARJ LABJ CNTJ QB QL (nat_lit 3) (nat_lit 0)
    (nat_lit 204) (nat_lit 12) = true := by
  quickRfl

theorem sch04_q2 : schSlK LJ BJ NL PTSJ POSJ PARJ LABJ CNTJ QB QL (nat_lit 3) (nat_lit 0)
    (nat_lit 216) (nat_lit 12) = true := by
  quickRfl

theorem sch04_q3 : schSlK LJ BJ NL PTSJ POSJ PARJ LABJ CNTJ QB QL (nat_lit 3) (nat_lit 0)
    (nat_lit 228) (nat_lit 12) = true := by
  quickRfl

theorem sch04 : sch0 (nat_lit 4) = true := by
  unfold sch0
  exact schSlK_split _ (nat_lit 24) (nat_lit 24) _ rfl
    (schSlK_split _ (nat_lit 12) (nat_lit 12) _ rfl sch04_q0 sch04_q1)
    (schSlK_split _ (nat_lit 12) (nat_lit 12) _ rfl sch04_q2 sch04_q3)

end CertificateChecks.KernelSpor.McLC

end
