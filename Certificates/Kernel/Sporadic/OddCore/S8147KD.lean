module

public import Certificates.Kernel.Sporadic.OddCore.S8147D
public import Certificates.Data.Kernel.Spor.HNAOrb
public import Certificates.Data.Kernel.BfsPinSlice
public import Certificates.Data.Kernel.BfsPinBase
public import Certificates.Kernel.LocalQT.Tc.Gen
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.S8147

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KS.HNA
open CertificateChecks.KernelSpor

theorem hQ : (szOK 1782 11 && allN 2 (fun k => canonK 1782 11 (mask 11) (Nat.mul 1782 11)
    (SFQ.G k)) && Nat.beq (SFQ.T 0) (pidn 1782 11) && Nat.beq (SFQ.C 0) 1 &&
    Nat.beq (SFQ.C 1) 25) = true := by quickRfl
theorem dQ : distinctK 25 SFQ.T SFQ.S = true := by quickRfl
theorem kQ : keysSK 1782 11 [0, 1, 2, 3, 4, 8, 5, 6] 25 SFQ.T (listUp SFQ.SKT 25) = true := by
  quickRfl
theorem pQ : allN 2 (fun k => permOK 1782 11 (mask 11) (1782 * 11) (SFQ.G k)
    (pinvS 1782 11 (mask 11) (SFQ.G k))) = true := by quickRfl
theorem sQ : bAnd(canonSl 1782 11 SFQ.T 25 0, runSl 1782 11 2 SFQ.G SFQ.T SFQ.E 25 SFQ.C 0) = true := by
  quickRfl

theorem hD0 : (szOK 1782 11 && allN 2 (fun k => canonK 1782 11 (mask 11) (Nat.mul 1782 11)
    (SFD0.G k)) && Nat.beq (SFD0.T 0) (pidn 1782 11) && Nat.beq (SFD0.C 0) 1 &&
    Nat.beq (SFD0.C 9) 360) = true := by quickRfl
theorem dD0 : distinctK 360 SFD0.T SFD0.S = true := by quickRfl
theorem kD0 : keysSK 1782 11 [0, 1, 2, 3, 4, 8, 5, 6] 360 SFD0.T (listUp SFD0.SKT 360) = true := by
  quickRfl
theorem pD0 : allN 2 (fun k => permOK 1782 11 (mask 11) (1782 * 11) (SFD0.G k)
    (pinvS 1782 11 (mask 11) (SFD0.G k))) = true := by quickRfl

theorem hD1 : (szOK 1782 11 && allN 2 (fun k => canonK 1782 11 (mask 11) (Nat.mul 1782 11)
    (SFD1.G k)) && Nat.beq (SFD1.T 0) (pidn 1782 11) && Nat.beq (SFD1.C 0) 1 &&
    Nat.beq (SFD1.C 3) 60) = true := by quickRfl
theorem dD1 : distinctK 60 SFD1.T SFD1.S = true := by quickRfl
theorem kD1 : keysSK 1782 11 [0, 1, 2, 3, 4, 8, 5, 6] 60 SFD1.T (listUp SFD1.SKT 60) = true := by
  quickRfl
theorem pD1 : allN 2 (fun k => permOK 1782 11 (mask 11) (1782 * 11) (SFD1.G k)
    (pinvS 1782 11 (mask 11) (SFD1.G k))) = true := by quickRfl

theorem hD2 : (szOK 1782 11 && allN 2 (fun k => canonK 1782 11 (mask 11) (Nat.mul 1782 11)
    (SFD2.G k)) && Nat.beq (SFD2.T 0) (pidn 1782 11) && Nat.beq (SFD2.C 0) 1 &&
    Nat.beq (SFD2.C 3) 60) = true := by quickRfl
theorem dD2 : distinctK 60 SFD2.T SFD2.S = true := by quickRfl
theorem kD2 : keysSK 1782 11 [0, 1, 2, 3, 4, 8, 5, 6] 60 SFD2.T (listUp SFD2.SKT 60) = true := by
  quickRfl
theorem pD2 : allN 2 (fun k => permOK 1782 11 (mask 11) (1782 * 11) (SFD2.G k)
    (pinvS 1782 11 (mask 11) (SFD2.G k))) = true := by quickRfl

theorem hD3 : (szOK 1782 11 && allN 4 (fun k => canonK 1782 11 (mask 11) (Nat.mul 1782 11)
    (SFD3.G k)) && Nat.beq (SFD3.T 0) (pidn 1782 11) && Nat.beq (SFD3.C 0) 1 &&
    Nat.beq (SFD3.C 9) 360) = true := by quickRfl
theorem dD3 : distinctK 360 SFD3.T SFD3.S = true := by quickRfl
theorem kD3 : keysSK 1782 11 [0, 1, 2, 3, 4, 8, 5, 6] 360 SFD3.T (listUp SFD3.SKT 360) = true := by
  quickRfl
theorem pD3 : allN 4 (fun k => permOK 1782 11 (mask 11) (1782 * 11) (SFD3.G k)
    (pinvS 1782 11 (mask 11) (SFD3.G k))) = true := by quickRfl

theorem hD4 : (szOK 1782 11 && allN 2 (fun k => canonK 1782 11 (mask 11) (Nat.mul 1782 11)
    (SFD4.G k)) && Nat.beq (SFD4.T 0) (pidn 1782 11) && Nat.beq (SFD4.C 0) 1 &&
    Nat.beq (SFD4.C 9) 360) = true := by quickRfl
theorem dD4 : distinctK 360 SFD4.T SFD4.S = true := by quickRfl
theorem kD4 : keysSK 1782 11 [0, 1, 2, 3, 4, 8, 5, 6] 360 SFD4.T (listUp SFD4.SKT 360) = true := by
  quickRfl
theorem pD4 : allN 2 (fun k => permOK 1782 11 (mask 11) (1782 * 11) (SFD4.G k)
    (pinvS 1782 11 (mask 11) (SFD4.G k))) = true := by quickRfl

theorem hD5 : (szOK 1782 11 && allN 2 (fun k => canonK 1782 11 (mask 11) (Nat.mul 1782 11)
    (SFD5.G k)) && Nat.beq (SFD5.T 0) (pidn 1782 11) && Nat.beq (SFD5.C 0) 1 &&
    Nat.beq (SFD5.C 3) 60) = true := by quickRfl
theorem dD5 : distinctK 60 SFD5.T SFD5.S = true := by quickRfl
theorem kD5 : keysSK 1782 11 [0, 1, 2, 3, 4, 8, 5, 6] 60 SFD5.T (listUp SFD5.SKT 60) = true := by
  quickRfl
theorem pD5 : allN 2 (fun k => permOK 1782 11 (mask 11) (1782 * 11) (SFD5.G k)
    (pinvS 1782 11 (mask 11) (SFD5.G k))) = true := by quickRfl

@[expose] noncomputable def d0s (s : Nat) : Bool :=
  bAnd(canonSl 1782 11 SFD0.T 40 s, runSl 1782 11 2 SFD0.G SFD0.T SFD0.E 40 SFD0.C s)
@[expose] noncomputable def d1s (s : Nat) : Bool :=
  bAnd(canonSl 1782 11 SFD1.T 20 s, runSl 1782 11 2 SFD1.G SFD1.T SFD1.E 20 SFD1.C s)
@[expose] noncomputable def d2s (s : Nat) : Bool :=
  bAnd(canonSl 1782 11 SFD2.T 20 s, runSl 1782 11 2 SFD2.G SFD2.T SFD2.E 20 SFD2.C s)
@[expose] noncomputable def d3s (s : Nat) : Bool :=
  bAnd(canonSl 1782 11 SFD3.T 40 s, runSl 1782 11 4 SFD3.G SFD3.T SFD3.E 40 SFD3.C s)
@[expose] noncomputable def d4s (s : Nat) : Bool :=
  bAnd(canonSl 1782 11 SFD4.T 40 s, runSl 1782 11 2 SFD4.G SFD4.T SFD4.E 40 SFD4.C s)
@[expose] noncomputable def d5s (s : Nat) : Bool :=
  bAnd(canonSl 1782 11 SFD5.T 20 s, runSl 1782 11 2 SFD5.G SFD5.T SFD5.E 20 SFD5.C s)

theorem hO0 : (szOK 6 3 && allN 2 (fun k => canonK 6 3 (mask 3) (Nat.mul 6 3) (SFO0.G k)) &&
    Nat.beq (SFO0.T 0) (pidn 6 3) && Nat.beq (SFO0.C 0) 1 && Nat.beq (SFO0.C 9) 360) = true := by
  quickRfl
theorem dO0 : distinctK 360 SFO0.T SFO0.S = true := by quickRfl
theorem pO0 : allN 2 (fun k => permOK 6 3 (mask 3) (6 * 3) (SFO0.G k)
    (pinvS 6 3 (mask 3) (SFO0.G k))) = true := by quickRfl

theorem hO1 : (szOK 5 3 && allN 2 (fun k => canonK 5 3 (mask 3) (Nat.mul 5 3) (SFO1.G k)) &&
    Nat.beq (SFO1.T 0) (pidn 5 3) && Nat.beq (SFO1.C 0) 1 && Nat.beq (SFO1.C 3) 60) = true := by
  quickRfl
theorem dO1 : distinctK 60 SFO1.T SFO1.S = true := by quickRfl
theorem pO1 : allN 2 (fun k => permOK 5 3 (mask 3) (5 * 3) (SFO1.G k)
    (pinvS 5 3 (mask 3) (SFO1.G k))) = true := by quickRfl

theorem hO2 : (szOK 5 3 && allN 2 (fun k => canonK 5 3 (mask 3) (Nat.mul 5 3) (SFO2.G k)) &&
    Nat.beq (SFO2.T 0) (pidn 5 3) && Nat.beq (SFO2.C 0) 1 && Nat.beq (SFO2.C 3) 60) = true := by
  quickRfl
theorem dO2 : distinctK 60 SFO2.T SFO2.S = true := by quickRfl
theorem pO2 : allN 2 (fun k => permOK 5 3 (mask 3) (5 * 3) (SFO2.G k)
    (pinvS 5 3 (mask 3) (SFO2.G k))) = true := by quickRfl

theorem hO3 : (szOK 6 3 && allN 4 (fun k => canonK 6 3 (mask 3) (Nat.mul 6 3) (SFO3.G k)) &&
    Nat.beq (SFO3.T 0) (pidn 6 3) && Nat.beq (SFO3.C 0) 1 && Nat.beq (SFO3.C 9) 360) = true := by
  quickRfl
theorem dO3 : distinctK 360 SFO3.T SFO3.S = true := by quickRfl
theorem pO3 : allN 4 (fun k => permOK 6 3 (mask 3) (6 * 3) (SFO3.G k)
    (pinvS 6 3 (mask 3) (SFO3.G k))) = true := by quickRfl

theorem hO4 : (szOK 6 3 && allN 2 (fun k => canonK 6 3 (mask 3) (Nat.mul 6 3) (SFO4.G k)) &&
    Nat.beq (SFO4.T 0) (pidn 6 3) && Nat.beq (SFO4.C 0) 1 && Nat.beq (SFO4.C 9) 360) = true := by
  quickRfl
theorem dO4 : distinctK 360 SFO4.T SFO4.S = true := by quickRfl
theorem pO4 : allN 2 (fun k => permOK 6 3 (mask 3) (6 * 3) (SFO4.G k)
    (pinvS 6 3 (mask 3) (SFO4.G k))) = true := by quickRfl

theorem hO5 : (szOK 5 3 && allN 2 (fun k => canonK 5 3 (mask 3) (Nat.mul 5 3) (SFO5.G k)) &&
    Nat.beq (SFO5.T 0) (pidn 5 3) && Nat.beq (SFO5.C 0) 1 && Nat.beq (SFO5.C 3) 60) = true := by
  quickRfl
theorem dO5 : distinctK 60 SFO5.T SFO5.S = true := by quickRfl
theorem pO5 : allN 2 (fun k => permOK 5 3 (mask 3) (5 * 3) (SFO5.G k)
    (pinvS 5 3 (mask 3) (SFO5.G k))) = true := by quickRfl

@[expose] noncomputable def o0s (s : Nat) : Bool :=
  bAnd(canonSl 6 3 SFO0.T 40 s, runSl 6 3 2 SFO0.G SFO0.T SFO0.E 40 SFO0.C s)
@[expose] noncomputable def o1s (s : Nat) : Bool :=
  bAnd(canonSl 5 3 SFO1.T 20 s, runSl 5 3 2 SFO1.G SFO1.T SFO1.E 20 SFO1.C s)
@[expose] noncomputable def o2s (s : Nat) : Bool :=
  bAnd(canonSl 5 3 SFO2.T 20 s, runSl 5 3 2 SFO2.G SFO2.T SFO2.E 20 SFO2.C s)
@[expose] noncomputable def o3s (s : Nat) : Bool :=
  bAnd(canonSl 6 3 SFO3.T 40 s, runSl 6 3 4 SFO3.G SFO3.T SFO3.E 40 SFO3.C s)
@[expose] noncomputable def o4s (s : Nat) : Bool :=
  bAnd(canonSl 6 3 SFO4.T 40 s, runSl 6 3 2 SFO4.G SFO4.T SFO4.E 40 SFO4.C s)
@[expose] noncomputable def o5s (s : Nat) : Bool :=
  bAnd(canonSl 5 3 SFO5.T 20 s, runSl 5 3 2 SFO5.G SFO5.T SFO5.E 20 SFO5.C s)

end CertificateChecks.KernelSpor.S8147

set_option Elab.async false

#kqb_range CertificateChecks.KernelSpor.S8147.D0K CertificateChecks.KernelSpor.S8147.d0s 0 9
#kqb_all CertificateChecks.KernelSpor.S8147.D0K CertificateChecks.KernelSpor.S8147.d0s 9
#kqb_range CertificateChecks.KernelSpor.S8147.D1K CertificateChecks.KernelSpor.S8147.d1s 0 3
#kqb_all CertificateChecks.KernelSpor.S8147.D1K CertificateChecks.KernelSpor.S8147.d1s 3
#kqb_range CertificateChecks.KernelSpor.S8147.D2K CertificateChecks.KernelSpor.S8147.d2s 0 3
#kqb_all CertificateChecks.KernelSpor.S8147.D2K CertificateChecks.KernelSpor.S8147.d2s 3
#kqb_range CertificateChecks.KernelSpor.S8147.D3K CertificateChecks.KernelSpor.S8147.d3s 0 9
#kqb_all CertificateChecks.KernelSpor.S8147.D3K CertificateChecks.KernelSpor.S8147.d3s 9
#kqb_range CertificateChecks.KernelSpor.S8147.D4K CertificateChecks.KernelSpor.S8147.d4s 0 9
#kqb_all CertificateChecks.KernelSpor.S8147.D4K CertificateChecks.KernelSpor.S8147.d4s 9
#kqb_range CertificateChecks.KernelSpor.S8147.D5K CertificateChecks.KernelSpor.S8147.d5s 0 3
#kqb_all CertificateChecks.KernelSpor.S8147.D5K CertificateChecks.KernelSpor.S8147.d5s 3
#kqb_range CertificateChecks.KernelSpor.S8147.O0K CertificateChecks.KernelSpor.S8147.o0s 0 9
#kqb_all CertificateChecks.KernelSpor.S8147.O0K CertificateChecks.KernelSpor.S8147.o0s 9
#kqb_range CertificateChecks.KernelSpor.S8147.O1K CertificateChecks.KernelSpor.S8147.o1s 0 3
#kqb_all CertificateChecks.KernelSpor.S8147.O1K CertificateChecks.KernelSpor.S8147.o1s 3
#kqb_range CertificateChecks.KernelSpor.S8147.O2K CertificateChecks.KernelSpor.S8147.o2s 0 3
#kqb_all CertificateChecks.KernelSpor.S8147.O2K CertificateChecks.KernelSpor.S8147.o2s 3
#kqb_range CertificateChecks.KernelSpor.S8147.O3K CertificateChecks.KernelSpor.S8147.o3s 0 9
#kqb_all CertificateChecks.KernelSpor.S8147.O3K CertificateChecks.KernelSpor.S8147.o3s 9
#kqb_range CertificateChecks.KernelSpor.S8147.O4K CertificateChecks.KernelSpor.S8147.o4s 0 9
#kqb_all CertificateChecks.KernelSpor.S8147.O4K CertificateChecks.KernelSpor.S8147.o4s 9
#kqb_range CertificateChecks.KernelSpor.S8147.O5K CertificateChecks.KernelSpor.S8147.o5s 0 3
#kqb_all CertificateChecks.KernelSpor.S8147.O5K CertificateChecks.KernelSpor.S8147.o5s 3

end
