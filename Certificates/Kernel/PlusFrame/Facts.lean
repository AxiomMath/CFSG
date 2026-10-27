module

public import Certificates.Kernel.PlusFrame.Checks
public import Certificates.Kernel.PlusQuandle.Checks
public import CFSG.Certificates.Kernel.PlusFrameSound

public section

namespace CertificateChecks.KernelPlusFr

open CFSG.KC.PlusFrameK CertificateChecks.KernelPlusQ CFSG.OddTranspositions.PartThree.PlusFrame

theorem autK_all {a : Nat} (ha : a < 60) : autK R DS DA a = true := by
  have hc : a / 5 < 12 := by omega
  have h1 : 5 * (a / 5) ≤ a := Nat.mul_div_le a 5
  have h2 : a < 5 * (a / 5) + 5 := by omega
  interval_cases hq : a / 5
  · exact autK_of_autOK ch1383004a_0 h1 h2
  · exact autK_of_autOK ch1383004a_1 h1 h2
  · exact autK_of_autOK ch1383004a_2 h1 h2
  · exact autK_of_autOK ch1383004a_3 h1 h2
  · exact autK_of_autOK ch1383004a_4 h1 h2
  · exact autK_of_autOK ch1383004a_5 h1 h2
  · exact autK_of_autOK ch1383004a_6 h1 h2
  · exact autK_of_autOK ch1383004a_7 h1 h2
  · exact autK_of_autOK ch1383004a_8 h1 h2
  · exact autK_of_autOK ch1383004a_9 h1 h2
  · exact autK_of_autOK ch1383004a_10 h1 h2
  · exact autK_of_autOK ch1383004a_11 h1 h2

theorem aut : autCheck () = true :=
  autCheck_of rows_ok ch1383004_ds ch1383004_da fun _ ha => autK_all ha

end CertificateChecks.KernelPlusFr
