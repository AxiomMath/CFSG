module

public import Certificates.Kernel.J4.Data
public import Certificates.Data.Kernel.J4Fix

public section

namespace CertificateChecks.KernelBounds.J4

open CFSG.KJ4.R CFSG.KJ4.RUN

@[expose] noncomputable def FLs : List (List Nat) :=
  [(List.append (List.append FL1_0 (List.append FL1_1 FL1_2)) (List.append (List.append FL1_3 FL1_4) (List.append FL1_5 FL1_6))), (List.append (List.append FL2_0 (List.append FL2_1 FL2_2)) (List.append (List.append FL2_3 FL2_4) (List.append FL2_5 FL2_6))), (List.append (List.append FL3_0 (List.append FL3_1 FL3_2)) (List.append (List.append FL3_3 FL3_4) (List.append FL3_5 FL3_6))), (List.append (List.append FL4_0 (List.append FL4_1 FL4_2)) (List.append (List.append FL4_3 FL4_4) (List.append FL4_5 FL4_6))), (List.append (List.append FL5_0 (List.append FL5_1 FL5_2)) (List.append (List.append FL5_3 FL5_4) (List.append FL5_5 FL5_6))), (List.append (List.append FL6_0 (List.append FL6_1 FL6_2)) (List.append (List.append FL6_3 FL6_4) (List.append FL6_5 FL6_6)))]

theorem fix_ok : j4Fix kd FLs = true := by quickRfl

end CertificateChecks.KernelBounds.J4

end
