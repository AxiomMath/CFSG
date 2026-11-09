module

public import Certificates.Kernel.HMathieu.T24
public import Certificates.Kernel.HMathieu.T22
public import Certificates.Kernel.HMathieu.T12
public import Certificates.Data.Kernel.HMathieu.PredQK
public import Certificates.Kernel.HMathieu.C7075

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelHMathieu.C260400

open CFSG.KC.HMathieu CertificateChecks.KernelHMathieu

@[expose] noncomputable def blkCoc (i : Nat) : Bool :=
  C7075.gRowR 191 (fun st y => (T24.Mc.getD y [] :: st.1, fixLstQ (T24.Mc.getD y []) st.2))
    (fun _ _ st => predQK 11 true st.1 st.2) 5 [] [191] (2 ^ 191 - 1) ([], List.range (2 ^ 11))
    T24.rows 0 i

@[expose] noncomputable def blkCode (i : Nat) : Bool :=
  C7075.gRowR 191 (fun st y => (T24.Md.getD y [] :: st.1, fixLstQ (T24.Md.getD y []) st.2))
    (fun _ _ st => predQK 11 true st.1 st.2) 5 [] [191] (2 ^ 191 - 1) ([], List.range (2 ^ 11))
    T24.rows 0 i

end CertificateChecks.KernelHMathieu.C260400

end

set_option maxHeartbeats 0

#kss_each CertificateChecks.KernelHMathieu.C260400.BC CertificateChecks.KernelHMathieu.C260400.blkCoc 191

#kss_each CertificateChecks.KernelHMathieu.C260400.BD CertificateChecks.KernelHMathieu.C260400.blkCode 191

public section

namespace CertificateChecks.KernelHMathieu.C260400

open CFSG.KC.HMathieu CertificateChecks.KernelHMathieu

theorem coc24 : gAllR 191 (fun st y => (T24.Mc.getD y [] :: st.1, fixLstQ (T24.Mc.getD y []) st.2))
    (fun _ _ st => predQK 11 true st.1 st.2) 6 [] [191] (2 ^ 191 - 1) ([], List.range (2 ^ 11))
    T24.rows 0 = true :=
  C7075.gAllR_succ_of_rows _ _ _ 5 _ _ _ _ _ _ (by decide +kernel) fun i hi => by
    have hi' : i < 191 := by rw [← T24.lenOK.2]; exact hi
    have hp := BC.all i hi'
    unfold blkCoc at hp
    exact hp

theorem code24 : gAllR 191 (fun st y => (T24.Md.getD y [] :: st.1, fixLstQ (T24.Md.getD y []) st.2))
    (fun _ _ st => predQK 11 true st.1 st.2) 6 [] [191] (2 ^ 191 - 1) ([], List.range (2 ^ 11))
    T24.rows 0 = true :=
  C7075.gAllR_succ_of_rows _ _ _ 5 _ _ _ _ _ _ (by decide +kernel) fun i hi => by
    have hi' : i < 191 := by rw [← T24.lenOK.2]; exact hi
    have hp := BD.all i hi'
    unfold blkCode at hp
    exact hp

set_option maxHeartbeats 0 in
theorem coc22 : gAllR 71 (fun st y => (T22.Mc.getD y [] :: st.1, fixLstQ (T22.Mc.getD y []) st.2))
    (fun _ _ st => predQK 10 true st.1 st.2) 5 [] [71] (2 ^ 71 - 1) ([], List.range (2 ^ 10))
    T22.rows 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem code22 : gAllR 71 (fun st y => (T22.Md.getD y [] :: st.1, fixLstQ (T22.Md.getD y []) st.2))
    (fun _ _ st => predQK 10 false st.1 st.2) 5 [] [71] (2 ^ 71 - 1) ([], List.range (2 ^ 10))
    T22.rows 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem w12 : gAllR 35 (fun st y => (T12.Mc.getD y [] :: st.1, fixLstQ (T12.Mc.getD y []) st.2))
    (fun _ _ st => predQK 10 true st.1 st.2) 4 [] [35] (2 ^ 35 - 1) ([], List.range (2 ^ 10))
    T12.rows 0 = true := by
  decide +kernel

end CertificateChecks.KernelHMathieu.C260400

end
