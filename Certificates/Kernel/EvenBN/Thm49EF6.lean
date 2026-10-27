module

public import Certificates.Data.Kernel.EvenBN.Thm49EF6
public import Certificates.Kernel.Misc.Tits.Text
public import Certificates.Kernel.SporSch.Tits.Common
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelT49

open CFSG.KC.Enum CFSG.KS CFSG.KD.T49

@[expose] noncomputable def w42 : F6W where
  F := fun j => CertificateChecks.KernelMisc.TitsText.F j
  FI := fun j => pinvS 1755 11 (mask 11) (CertificateChecks.KernelMisc.TitsText.F j)
  D := fun j => CertificateChecks.KernelMisc.TitsText.F (Nat.add 18 j)
  DI := fun j => pinvS 1755 11 (mask 11) (CertificateChecks.KernelMisc.TitsText.F (Nat.add 18 j))
  Z := CertificateChecks.KernelSporSch.TitsZ
  ew := [2, -1, -2, 1, 2, -1, 2]
  e1w := [2, 2, 1, -2, -2, -1, -2]
  e1iw := [2, 1, 2, 2, -1, -2, -2]
  fw := [-1, -1, -2, 1, 2, 2, 1, 2]
  fz := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 25,
    26, 27, 28, 29, 31, 32, 33, 34, 35, 37, 38, 39, 41, 42, 46, 47, 48, 50, 52, 53, 57, 58, 59, 60,
    62, 64, 68, 69, 70, 72, 74, 78, 80, 88, 89, 91, 95, 97, 101, 103, 111, 112, 114, 115, 117, 121,
    125, 134, 135, 137, 141, 142, 146, 153, 156, 174, 178, 185, 186, 189, 195, 198, 219, 223, 261,
    270]
  fzz := [0, 1, 2, 6, 8, 10, 14, 18, 26, 31, 46, 157, 199, 236, 263, 271, 285, 290, 292, 334, 347,
    352, 366, 411, 415, 484, 486]
  q0 := 3
  yp := 6
  r2 := 1
  o1 := [12299, 4206672, 22542, 4217021, 163856, 4358156, 28693, 4223101, 387106, 4581445, 32838,
    4227125, 24638, 4218922, 43034, 4237510, 256027, 69655, 4264010, 141360, 4335737, 4337696,
    108730, 4302877, 4321317, 86158, 4247771, 405563, 4599942, 55431, 4249664, 47201, 4345906,
    4292618, 65567, 4259993, 380956, 4575270, 4253704, 75822, 4270275, 290838, 448559, 120867,
    4315273, 274521, 4468837, 4470841, 131218, 198834, 4392999, 102541, 20499, 63556, 4258053,
    57518, 4251720, 16399, 4210791, 4288782, 399471, 45168, 4239455, 96297, 4290677, 280799,
    182350, 4376594, 364564, 80057, 4233372, 534616, 4728890, 4341812, 227388, 456737, 4354162,
    4235355, 106611]
  o2 := [2050, 4196369, 4198425, 34819, 51204, 6151, 4200457, 8197, 4202509]

theorem f6K_w42 : f6K w42 = true := by quickRfl

theorem f6K_neg_yp : (f6K { w42 with yp := 7 }).not = true := by quickRfl

theorem f6K_neg_fz : (f6K { w42 with fz := w42.fz.tail }).not = true := by quickRfl

theorem f6K_neg_o1 : (f6K { w42 with o1 := w42.o1.tail }).not = true := by quickRfl

theorem f6K_neg_o2 : (f6K { w42 with o2 := [] }).not = true := by quickRfl

theorem f6K_neg_f : (f6K { w42 with fw := [1] }).not = true := by quickRfl

end CertificateChecks.KernelT49

end
